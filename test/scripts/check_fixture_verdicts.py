#!/usr/bin/env python3
"""Run every fixture of a verdict table and hold each run to its row and to a
resource bound.

    test/scripts/check_fixture_verdicts.py [TABLE ...]

With no argument it runs both committed tables:

* test/fixtures/con-leche/expected.txt -- con-leche's test fixtures, verbatim;
* test/fixtures/dag-towers/expected.txt -- the DAG-tower fixtures.

A table line is ``<exit> <class> <con-leche exit> <path> [# note]``, with the
path relative to the table's directory; the table headers explain the columns.
Each fixture is run the way the Lean Kernel Arena runs a checker, with every
generation route and check on, and fails if

* the exit code differs from its row, or its row pairs a class with an exit
  code the class forbids (a kernel-rejected stream may never be accepted);
* the run printed a Lean runtime panic;
* its peak resident set exceeded ``--max-rss-mib`` (default 1024).  The peak
  is the kernel's own ``ru_maxrss`` for the child, read after it exits.
  A watchdog samples the child's RSS and kills it the moment it crosses the
  bound, so a runaway ends the run instead of the machine;
* it used more than ``--max-cpu-s`` seconds of CPU (default 120): the child
  runs under ``RLIMIT_CPU``.  This is a backstop against a walk that expands a
  tower without allocating, which never finishes rather than being slow --
  every fixture here takes well under a second when its walks are linear.

The bound is what makes the towers a gate.  Each is about 2^60 nodes as a tree
and a few hundred as a DAG, so a walk that forgets sharing even once cannot
stay under it, whatever the machine; a linear one stays two orders of magnitude
below it.

An accepted fixture is then run once more writing its output, which must be
accepted too and hold at most ``--max-output-ratio`` (default 100) times as
many records as the input plus ``OUTPUT_ALLOWANCE`` (the models of a small
nested block alone run to about 20,000 records): the output keeps the input's
sharing, so a tower carried into a generated declaration must not come out as
its tree, and a tree here would be larger by a factor of 2^50.

Every file under a table's directory that looks like a fixture (``*.ndjson``,
``*.ndjson.gz``) must have a row, and every row a file, so a fixture can be
neither added unchecked nor dropped silently.
"""

from __future__ import annotations

import argparse
import gzip
import os
from pathlib import Path
import resource
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_TABLES = (
    ROOT / "test/fixtures/con-leche/expected.txt",
    ROOT / "test/fixtures/dag-towers/expected.txt",
)
CHECKER_ARGS = (
    "--inductives",
    "--check-input",
    "--check-output",
    "--type-check-input",
    "--type-check-generated",
    "--no-output",
)
OUTPUT_ALLOWANCE = 50_000
PANIC_PREFIXES = ("PANIC at ", "PANIC: ", "INTERNAL PANIC:")
# The exit codes each class admits.  `reject` and `defect` never admit 0: a
# stream Lean's kernel rejects is never accepted, and a table cannot be edited
# to say otherwise.
CLASS_EXITS = {
    "accept": {0},
    "reject": {1},
    "scope": {2},
    "defect": {1, 3},
    "foreign": {3},
}


class TableError(Exception):
    pass


def read_table(table: Path) -> list[tuple[int, str, Path, str]]:
    rows = []
    seen: set[Path] = set()
    for number, raw in enumerate(table.read_text(encoding="utf-8").splitlines(), 1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        fields = line.split()
        if len(fields) != 4:
            raise TableError(f"{table}:{number}: expected 4 fields, got {len(fields)}")
        code, klass, _upstream, relative = fields
        if klass not in CLASS_EXITS:
            raise TableError(f"{table}:{number}: unknown class {klass!r}")
        if not code.isdigit() or int(code) not in CLASS_EXITS[klass]:
            raise TableError(f"{table}:{number}: class {klass} does not admit exit {code}")
        path = (table.parent / relative).resolve()
        if path in seen:
            raise TableError(f"{table}:{number}: {relative} is listed twice")
        seen.add(path)
        note = raw.split("#", 1)[1].strip() if "#" in raw else ""
        rows.append((int(code), klass, path, note))
    on_disk = {
        path.resolve()
        for pattern in ("*.ndjson", "*.ndjson.gz")
        for path in table.parent.rglob(pattern)
    }
    unlisted = sorted(on_disk - seen)
    missing = sorted(seen - on_disk)
    if unlisted:
        raise TableError(f"{table}: fixtures without a row: " +
                         ", ".join(str(p.relative_to(table.parent)) for p in unlisted))
    if missing:
        raise TableError(f"{table}: rows without a fixture: " +
                         ", ".join(str(p.relative_to(table.parent)) for p in missing))
    return rows


def rss_kib(pid: int) -> int:
    try:
        with open(f"/proc/{pid}/status", encoding="ascii") as status:
            for line in status:
                if line.startswith("VmRSS:"):
                    return int(line.split()[1])
    except (OSError, ValueError):
        pass
    return 0


def run_one(binary: Path, fixture: Path, work: Path, max_rss_kib: int,
            max_cpu_s: int, output: Path | None = None) -> tuple[int, int, bool, str]:
    """Run one fixture; return (exit, peak RSS KiB, killed by watchdog, stderr).
    With `output`, write the transformed export there instead of `--no-output`."""
    source = fixture
    if fixture.name.endswith(".gz"):
        source = work / fixture.name[: -len(".gz")]
        with gzip.open(fixture, "rb") as compressed, source.open("wb") as plain:
            shutil.copyfileobj(compressed, plain)
    stderr_path = work / "stderr"

    def limit_cpu() -> None:
        resource.setrlimit(resource.RLIMIT_CPU, (max_cpu_s, max_cpu_s + 5))

    environment = os.environ.copy()
    environment["TMPDIR"] = str(work)
    with stderr_path.open("wb") as stderr:
        child = subprocess.Popen(
            [str(binary), *CHECKER_ARGS, str(source)] if output is None else
            [str(binary), *CHECKER_ARGS[:-1], "-o", str(output), str(source)],
            stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=stderr,
            env=environment, preexec_fn=limit_cpu,
        )
    killed = threading.Event()
    exited = threading.Event()

    # The watchdog must not reap the child (`Popen.poll` would): the main thread
    # collects it with `os.wait4` for its resource usage.  Until then the pid
    # stays valid, as a zombie at worst, whose RSS reads as 0.
    def watchdog() -> None:
        while not exited.is_set():
            if rss_kib(child.pid) > max_rss_kib:
                killed.set()
                try:
                    os.kill(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                return
            time.sleep(0.02)

    watcher = threading.Thread(target=watchdog, daemon=True)
    watcher.start()
    _, status, usage = os.wait4(child.pid, 0)
    exited.set()
    child.returncode = os.waitstatus_to_exitcode(status)
    watcher.join()
    if source != fixture and output is None:
        source.unlink()
    text = stderr_path.read_text(encoding="utf-8", errors="replace")
    return child.returncode, usage.ru_maxrss, killed.is_set(), text


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("tables", nargs="*", type=Path)
    parser.add_argument("--max-rss-mib", type=int, default=1024)
    parser.add_argument("--max-cpu-s", type=int, default=120)
    parser.add_argument("--max-output-ratio", type=int, default=100)
    args = parser.parse_args(argv[1:])
    binary = Path(os.environ.get("LEAN_INDUCTIVE_MODELS_BIN",
                                 ROOT / ".lake/build/bin/lean-inductive-models"))
    if not binary.is_file() or not os.access(binary, os.X_OK):
        print(f"lean-inductive-models is not built: {binary}", file=sys.stderr)
        return 2
    tables = [t.resolve() for t in args.tables] or list(DEFAULT_TABLES)
    try:
        suites = [(table, read_table(table)) for table in tables]
    except (OSError, TableError) as error:
        print(error, file=sys.stderr)
        return 2
    max_rss_kib = args.max_rss_mib * 1024
    scratch = ROOT / "_tmp"
    scratch.mkdir(exist_ok=True)
    failed = 0
    total = 0
    worst = (0, None)
    worst_ratio = (0.0, None)
    with tempfile.TemporaryDirectory(prefix="fixture-verdicts.", dir=scratch) as raw_work:
        work = Path(raw_work)
        for table, rows in suites:
            counts: dict[str, int] = {}
            for expected, klass, fixture, _note in rows:
                total += 1
                relative = fixture.relative_to(table.parent)
                code, peak, killed, stderr = run_one(
                    binary, fixture, work, max_rss_kib, args.max_cpu_s)
                if peak > worst[0]:
                    worst = (peak, relative)
                problems = []
                panic = next((line.strip() for line in stderr.splitlines()
                              if line.strip().startswith(PANIC_PREFIXES)), None)
                if killed:
                    problems.append(f"killed at {max_rss_kib // 1024} MiB resident")
                elif peak > max_rss_kib:
                    problems.append(f"peak RSS {peak // 1024} MiB exceeds "
                                    f"{max_rss_kib // 1024} MiB")
                elif code in (-signal.SIGXCPU, -signal.SIGKILL):
                    problems.append(f"exceeded {args.max_cpu_s} s of CPU")
                if panic is not None:
                    problems.append(f"panicked: {panic}")
                if code != expected and not problems:
                    problems.append(f"expected exit {expected} ({klass}), got {code}")
                if not problems and code == 0:
                    written = work / "output.ndjson"
                    code, peak, killed, stderr = run_one(
                        binary, fixture, work, max_rss_kib, args.max_cpu_s, written)
                    source = work / fixture.name[: -len(".gz")] \
                        if fixture.name.endswith(".gz") else fixture
                    lines_in = sum(1 for _ in source.open("rb"))
                    lines_out = sum(1 for _ in written.open("rb")) if written.exists() else 0
                    if source != fixture:
                        source.unlink()
                    written.unlink(missing_ok=True)
                    worst_ratio = max(worst_ratio, (lines_out / max(lines_in, 1), relative))
                    if killed or peak > max_rss_kib:
                        problems.append(f"writing output: peak RSS over "
                                        f"{max_rss_kib // 1024} MiB")
                    elif code != 0:
                        problems.append(f"writing output: exit {code}")
                    elif lines_out > args.max_output_ratio * lines_in + OUTPUT_ALLOWANCE:
                        problems.append(f"output has {lines_out} records for {lines_in} "
                                        f"input records, over {args.max_output_ratio}x "
                                        f"+ {OUTPUT_ALLOWANCE}")
                if problems:
                    failed += 1
                    print(f"FAIL {table.parent.name}/{relative}: " + "; ".join(problems),
                          file=sys.stderr)
                    for line in stderr.splitlines()[:6]:
                        print(f"  {line}", file=sys.stderr)
                else:
                    counts[klass] = counts.get(klass, 0) + 1
            summary = ", ".join(f"{n} {k}" for k, n in sorted(counts.items()))
            print(f"{table.parent.name}: {summary} ({len(rows)} fixtures)")
    print(f"fixture verdicts: {total - failed} passed, {failed} failed; "
          f"largest peak RSS {worst[0] // 1024} MiB ({worst[1]}); "
          f"largest output/input ratio {worst_ratio[0]:.1f} ({worst_ratio[1]})")
    return int(failed != 0)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
