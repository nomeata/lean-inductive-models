# con-leche's test fixtures

Every test fixture of [con-leche](https://github.com/leanprover/con-leche), the
consistency-proven Lean checker, copied **verbatim** at revision
`78ded4b6fc9a4d9ab809e8ca2c75c56537c41bff` (2026-09-21), the revision the Lean
Kernel Arena runs.

con-leche is licensed under the Apache License 2.0; [`LICENSE`](LICENSE) is its
license file, copied unchanged. The files here are unmodified copies of
upstream's, at these paths:

| here | upstream |
| --- | --- |
| `e2e/*.ndjson`, `e2e/*.ndjson.gz` | `tests/e2e/` — its end-to-end fixtures |
| `e2e/src/*.lean` | `tests/e2e/src/` — the Lean sources some of them were exported from |
| `annot/*.ndjson` | `tests/annot/` — its sort-annotation fixtures |
| `upstream/e2e-expected.txt`, `upstream/annot-expected.txt` | `tests/` — upstream's expected exit codes, with its reasoning |
| `upstream/scripts/mk_*.py` | `scripts/` — the generators of the hand-written streams |

Not copied: `tests/arena/lean-arena-tests.tar.gz` is upstream's snapshot of the
Lean Kernel Arena corpus, which `test/scripts/check_arena_corpus.py` already
runs from the published archive; `tests/scale/gen.py` generates streams at a
size given on its command line rather than being a fixture; and
`tests/trust-surface/lexer.lean` is a fixture for con-leche's own source
scanner, not an export.

## Format

The exports are `lean4export` format 3.1.0, the format this tool reads. Two
kinds of stream are not conforming, and are recorded as such:

* the hand-written `annot/*.ndjson` streams and
  `e2e/sorry_use_{midstream,before_invalid}.ndjson` omit fields format 3.1.0
  requires (`hints` on a `def`, `all` on a `thm`), and add con-leche's own
  optional `pw` field on binders; this tool refuses to parse them;
* `e2e/malformed_midstream.ndjson` is truncated on purpose.

Streams written by con-leche's own generators (`upstream/scripts/`) mention
`Nat`, `Eq` and friends without declaring them, because con-leche supplies its
own prelude. Lean's kernel rejects those as `unknown constant`, and so does this
tool. The DAG towers among them are ported as complete kernel exports in
[`../dag-towers/`](../dag-towers/), which is where they test anything.

## Verdicts

[`expected.txt`](expected.txt) gives each fixture's expected exit code under
this tool and the class that justifies it — the verdict of Lean's kernel on the
stream as written — together with con-leche's own expectation for comparison.
`test/scripts/check_fixture_verdicts.py` runs every row and enforces the
pairing: nothing Lean's kernel rejects is ever accepted, and every run stays
under a resident-memory bound.

The table also records what this port found: the streams Lean's kernel accepts
that this tool does not yet model (class `defect`), and one out-of-scope decline
(class `scope`). A fixed defect moves to `accept`; `nested_pin_collide` and
`nested_pin_collide2` are two, a nested container whose own recursion collapses
at the occurrence (`test/fixtures/inductive-models/nest_pin_collapse.lean`).
