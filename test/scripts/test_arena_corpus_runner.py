#!/usr/bin/env python3
"""Focused, network-free tests for the Arena corpus runner."""

from __future__ import annotations

import contextlib
import importlib.util
import io
from pathlib import Path
import shutil
import tarfile
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
RUNNER_PATH = ROOT / "test/scripts/check_arena_corpus.py"
SPEC = importlib.util.spec_from_file_location("check_arena_corpus", RUNNER_PATH)
assert SPEC is not None and SPEC.loader is not None
RUNNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNNER)


class ArenaRunnerTest(unittest.TestCase):
    def setUp(self) -> None:
        scratch = ROOT / "_tmp/python-tests"
        scratch.mkdir(parents=True, exist_ok=True)
        self.raw_work = tempfile.mkdtemp(prefix="arena-runner.", dir=scratch)
        self.work = Path(self.raw_work)

    def tearDown(self) -> None:
        shutil.rmtree(self.work)

    def fake_checker(self) -> Path:
        checker = self.work / "fake-checker.py"
        checker.write_text(
            """#!/usr/bin/env python3
import os
from pathlib import Path
import signal
import sys

expected = [
    "--inductives", "--check-input", "--check-output",
    "--type-check-input", "--type-check-output", "--no-output",
]
if sys.argv[1:-1] != expected:
    sys.exit(2)
outcome = Path(sys.argv[-1]).read_text().strip()
if outcome == "signal":
    os.kill(os.getpid(), signal.SIGTERM)
sys.exit(int(outcome))
""",
            encoding="utf-8",
        )
        checker.chmod(0o755)
        return checker

    def corpus(self, good: list[str], bad: list[str]) -> Path:
        corpus = self.work / "corpus"
        for group, outcomes in (("good", good), ("bad", bad)):
            directory = corpus / group
            directory.mkdir(parents=True)
            for index, outcome in enumerate(outcomes):
                (directory / f"case-{index}.ndjson").write_text(outcome, encoding="utf-8")
        return corpus

    def run_cases(self, good: list[str], bad: list[str]) -> tuple[int, str, str]:
        stdout = io.StringIO()
        stderr = io.StringIO()
        run_work = self.work / "run"
        run_work.mkdir()
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            result = RUNNER.run_corpus(
                self.fake_checker(), self.corpus(good, bad), run_work
            )
        return result, stdout.getvalue(), stderr.getvalue()

    def test_accepts_good_zero_and_reports_bad_one_and_three_separately(self) -> None:
        result, stdout, stderr = self.run_cases(["0"], ["1", "3"])
        self.assertEqual(result, 0)
        self.assertEqual(stderr, "")
        self.assertIn("1 good accepted, 1 bad rejected, 1 bad checker errors", stdout)

    def test_rejects_bad_zero_two_and_signal_and_nonzero_good(self) -> None:
        result, stdout, stderr = self.run_cases(["1"], ["0", "2", "signal"])
        self.assertEqual(result, 1)
        self.assertIn("4 failed", stdout)
        self.assertIn("got -15", stderr)
        self.assertIn("got 2", stderr)

    def make_archive(self, members: list[tuple[tarfile.TarInfo, bytes]]) -> Path:
        archive_path = self.work / "cases.tar.gz"
        with tarfile.open(archive_path, "w:gz") as archive:
            for member, data in members:
                member.size = len(data)
                archive.addfile(member, io.BytesIO(data))
        return archive_path

    def test_extracts_only_regular_good_and_bad_ndjson(self) -> None:
        members = [
            (tarfile.TarInfo("good/a.ndjson"), b"{}\n"),
            (tarfile.TarInfo("bad/b.ndjson"), b"{}\n"),
        ]
        destination = self.work / "safe"
        destination.mkdir()
        RUNNER.extract_archive(self.make_archive(members), destination)
        self.assertEqual((destination / "good/a.ndjson").read_bytes(), b"{}\n")
        self.assertEqual((destination / "bad/b.ndjson").read_bytes(), b"{}\n")

    def test_rejects_traversal_and_links_without_writing_outside(self) -> None:
        outside = self.work / "escape.ndjson"
        traversal = [
            (tarfile.TarInfo("good/a.ndjson"), b"{}\n"),
            (tarfile.TarInfo("bad/b.ndjson"), b"{}\n"),
            (tarfile.TarInfo("good/../../escape.ndjson"), b"bad"),
        ]
        destination = self.work / "traversal"
        destination.mkdir()
        with self.assertRaises(RUNNER.CorpusError):
            RUNNER.extract_archive(self.make_archive(traversal), destination)
        self.assertFalse(outside.exists())

        link = tarfile.TarInfo("good/link.ndjson")
        link.type = tarfile.SYMTYPE
        link.linkname = "../../escape.ndjson"
        unsafe_link = [
            (link, b""),
            (tarfile.TarInfo("bad/b.ndjson"), b"{}\n"),
        ]
        link_destination = self.work / "link"
        link_destination.mkdir()
        with self.assertRaises(RUNNER.CorpusError):
            RUNNER.extract_archive(self.make_archive(unsafe_link), link_destination)
        self.assertFalse(outside.exists())


if __name__ == "__main__":
    unittest.main()
