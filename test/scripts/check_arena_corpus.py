#!/usr/bin/env python3
"""Build models for, and validate, every published Lean Kernel Arena case."""

from __future__ import annotations

import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
import urllib.error
import urllib.request


ARENA_URL = "https://arena.lean-lang.org/lean-arena-tests.tar.gz"
CHECKER_ARGS = (
    "--inductives",
    "--check-input",
    "--check-output",
    "--type-check-input",
    "--type-check-output",
    "--no-output",
)
MAX_MEMBER_SIZE = 256 * 1024 * 1024
MAX_TOTAL_SIZE = 2 * 1024 * 1024 * 1024
MAX_ARCHIVE_SIZE = 512 * 1024 * 1024


class CorpusError(Exception):
    """An infrastructure error, distinct from a corpus verdict mismatch."""


def download(url: str, destination: Path) -> None:
    last_error: Exception | None = None
    request = urllib.request.Request(url, headers={"User-Agent": "lean-inductive-models-arena-ci/1"})
    for attempt in range(5):
        try:
            with urllib.request.urlopen(request, timeout=30) as response:
                if response.status != 200:
                    raise CorpusError(f"download returned HTTP {response.status}")
                length_header = response.headers.get("Content-Length")
                try:
                    length = int(length_header) if length_header is not None else None
                except ValueError as error:
                    raise CorpusError("download has an invalid Content-Length") from error
                if length is not None and length > MAX_ARCHIVE_SIZE:
                    raise CorpusError("download is larger than 512 MiB")
                with destination.open("wb") as output:
                    copied = 0
                    while chunk := response.read(1024 * 1024):
                        copied += len(chunk)
                        if copied > MAX_ARCHIVE_SIZE:
                            raise CorpusError("download is larger than 512 MiB")
                        output.write(chunk)
            return
        except (OSError, urllib.error.URLError, CorpusError) as error:
            last_error = error
            destination.unlink(missing_ok=True)
            if attempt != 4:
                time.sleep(min(2**attempt, 8))
    raise CorpusError(f"could not download {url}: {last_error}")


def validated_members(archive: tarfile.TarFile) -> list[tarfile.TarInfo]:
    seen: set[str] = set()
    counts = {"good": 0, "bad": 0}
    total_size = 0
    members: list[tarfile.TarInfo] = []
    for member in archive.getmembers():
        path = PurePosixPath(member.name)
        canonical = path.as_posix()
        valid_path = (
            canonical == member.name
            and not path.is_absolute()
            and len(path.parts) >= 2
            and path.parts[0] in counts
            and path.suffix == ".ndjson"
            and ".." not in path.parts
        )
        if not valid_path or not member.isfile():
            raise CorpusError(f"unsafe or unexpected archive member: {member.name!r}")
        if canonical in seen:
            raise CorpusError(f"duplicate archive member: {member.name!r}")
        if member.size > MAX_MEMBER_SIZE:
            raise CorpusError(f"archive member is too large: {member.name!r}")
        seen.add(canonical)
        counts[path.parts[0]] += 1
        total_size += member.size
        if total_size > MAX_TOTAL_SIZE:
            raise CorpusError("expanded archive is larger than 2 GiB")
        members.append(member)
    if not members or not all(counts.values()):
        raise CorpusError("archive must contain regular NDJSON files in good/ and bad/")
    return members


def extract_archive(archive_path: Path, destination: Path) -> None:
    try:
        with tarfile.open(archive_path, "r:gz") as archive:
            members = validated_members(archive)
            for member in members:
                target = destination.joinpath(*PurePosixPath(member.name).parts)
                target.parent.mkdir(parents=True, exist_ok=True)
                source = archive.extractfile(member)
                if source is None:
                    raise CorpusError(f"cannot read archive member: {member.name!r}")
                with source, target.open("xb") as output:
                    shutil.copyfileobj(source, output)
    except (OSError, tarfile.TarError) as error:
        raise CorpusError(f"invalid Arena archive: {error}") from error


def first_diagnostic(stderr: Path, stdout: Path) -> list[str]:
    source = stderr if stderr.stat().st_size else stdout
    if not source.stat().st_size:
        return []
    prefix = "" if source == stderr else "stdout: "
    with source.open(encoding="utf-8", errors="replace") as stream:
        return [f"  {prefix}{line.rstrip()}" for _, line in zip(range(8), stream)]


def run_corpus(binary: Path, corpus: Path, work: Path) -> int:
    logs = work / "logs"
    runtime = work / "runtime"
    logs.mkdir()
    runtime.mkdir()
    environment = os.environ.copy()
    environment["TMPDIR"] = str(runtime)
    good_accepted = 0
    bad_rejected = 0
    bad_errored = 0
    failed = 0
    total = 0
    for group in ("good", "bad"):
        for case in sorted((corpus / group).rglob("*.ndjson")):
            relative = case.relative_to(corpus)
            log_name = "_".join(relative.parts)
            stdout = logs / f"{log_name}.stdout"
            stderr = logs / f"{log_name}.stderr"
            with stdout.open("wb") as stdout_stream, stderr.open("wb") as stderr_stream:
                result = subprocess.run(
                    [str(binary), *CHECKER_ARGS, str(case)],
                    stdin=subprocess.DEVNULL,
                    stdout=stdout_stream,
                    stderr=stderr_stream,
                    env=environment,
                    check=False,
                )
            total += 1
            if group == "good" and result.returncode == 0:
                good_accepted += 1
                continue
            if group == "bad" and result.returncode == 1:
                bad_rejected += 1
                continue
            if group == "bad" and result.returncode == 3:
                # Arena calls this a checker error rather than a rejection. It
                # still proves the soundness property enforced here: the bad
                # proof was not accepted. A decline remains a failure because
                # this checker claims to handle the corpus.
                bad_errored += 1
                continue
            failed += 1
            expected = "0" if group == "good" else "1 or 3 (never 0, 2, or a signal)"
            print(
                f"FAIL {relative}: expected exit {expected}, got {result.returncode}",
                file=sys.stderr,
            )
            for line in first_diagnostic(stderr, stdout):
                print(line, file=sys.stderr)
    print(
        f"Arena corpus: {good_accepted} good accepted, {bad_rejected} bad rejected, "
        f"{bad_errored} bad checker errors, {failed} failed ({total} total)"
    )
    return int(failed != 0)


def main(argv: list[str]) -> int:
    if len(argv) > 2:
        print(f"usage: {argv[0]} [lean-arena-tests.tar.gz]", file=sys.stderr)
        return 2
    root = Path(__file__).resolve().parents[2]
    binary = Path(os.environ.get("LEAN_INDUCTIVE_MODELS_BIN", root / ".lake/build/bin/lean-inductive-models"))
    if not binary.is_file() or not os.access(binary, os.X_OK):
        print(f"lean-inductive-models is not built: {binary}", file=sys.stderr)
        return 2
    scratch = root / "_tmp"
    scratch.mkdir(exist_ok=True)
    try:
        with tempfile.TemporaryDirectory(prefix="arena-corpus.", dir=scratch) as raw_work:
            work = Path(raw_work)
            archive_path = Path(argv[1]).resolve() if len(argv) == 2 else work / "tests.tar.gz"
            if len(argv) == 1:
                download(os.environ.get("ARENA_TESTS_URL", ARENA_URL), archive_path)
            elif not archive_path.is_file():
                raise CorpusError(f"Arena archive not found: {archive_path}")
            corpus = work / "corpus"
            corpus.mkdir()
            extract_archive(archive_path, corpus)
            return run_corpus(binary.resolve(), corpus, work)
    except CorpusError as error:
        print(error, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
