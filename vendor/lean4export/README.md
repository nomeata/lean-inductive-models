# Pinned lean4export patch

**You do not need this patch to build or use `lean-inductive-models`.** The tool
consumes NDJSON; `lean4export` produces it, and this patch does not change a
byte of what it produces. Export with stock upstream `lean4export` and the tool
accepts the result exactly as it accepts ours. `scripts/export-fixture.sh`, which
regenerates the committed fixtures, deliberately uses a stock unpatched
checkout. The patch is a **memory optimisation for one job of ours**: exporting
all of Mathlib in `scripts/ci-mathlib.sh` on a 16 GiB runner.

`compact-expr-interner.patch` applies only to lean4export revision
`caccfbebbc99077962b3321125b2375bb3fa22db`. Its SHA-256 is
`151c25f6adbfd915ce62786da33352c089653f62d5d3445cc3b38879de19deeb`.

## What it changes

The patch replaces only the expression-ID dictionary. Names, universe levels,
declaration traversal, JSON serialization, and the output format are unchanged.
The compact table uses the same cached `Expr.hash` and exact `Expr.eqv`, and its
array position is the first-seen expression ID. A fixed 100,000,000-entry limit
is above the pinned Mathlib export's observed 95,334,373 expression IDs. It
fails before publishing a new expression record if that limit or the packed
UInt32 link space is exhausted — it fails closed rather than emitting a wrong
ID.

## Why it exists

At that observed size, the chunked keys use about 763 MiB, packed next links
about 364 MiB, and the fixed 2^25 packed heads 128 MiB. Chunks are at most
8 MiB for keys and 4 MiB for links, so allocation never overlaps two complete
tables. The replaced standard table's 2^27 pointer buckets and roughly
95 million association nodes have a 3.8 GiB lower bound before resize overlap.
So the table costs about 1.2 GiB instead of at least 3.8 GiB, and the doubling
step that would transiently hold both tables is gone.

That is the whole reason. The Mathlib gate's export phase peaks at 7.92 GiB of
RSS as patched (`docs/maintainers/Testing.md` records the phase baselines), and
generation has to run on the same 16 GiB runner afterwards. Nothing enforces a
number: CI imposes no per-process memory limit, and this repository's 12 GiB
figure was never a workflow limit — it is a **design criterion** benchmarked
against `lean4checker`, which parses and kernel-checks the same corpus in about
9 GB.

## Checking it

Run `test/scripts/check-lean4export-patch.sh` for the pin/integrity gate: the
patch's SHA-256, that `scripts/ci-mathlib.sh` still pins the reviewed revision
and SHA and still applies the patch, and that the patch introduces no
native-language boundary.

Set `LEAN4EXPORT_DIFFERENTIAL=1` to additionally build the stock and patched
pinned exporters and compare their bytes on the small committed source fixture.
That is the check backing the claim at the top: on the fixture the two exports
are byte-for-byte identical (9,396 lines), and the deliberately one-entry table
fails closed instead of colliding. It needs network access and the
`leanprover/lean4:v4.29.1` toolchain, and takes a couple of minutes.
