# Maintainer build and test guide

The user-facing build is simply `lake build`; `lake test` runs the primary
fixture-backed suite. This document records the complete maintainer matrix and
the resource-sensitive commands used by CI.

Keep scratch files on project-local disk:

```console
mkdir -p _tmp/build-tmp
export TMPDIR="$PWD/_tmp/build-tmp"
```

Build targets serially. Even with `-Kjobs=1`, passing several roots to one Lake
invocation can overlap their final native links.

```bash
build_serially() {
  local target
  for target in "$@"; do
    lake -Kjobs=1 build "$target"
  done
}
```

The compile-only proof oracles are:

```bash
compile_only_targets=(
  OneLayerProjectionPrototype
  OneLayerRecursorProof
)
```

The executable correctness targets are:

```bash
correctness_targets=(
  test clitest generationflagstest checktest kernelchecktest ordertest
  familyadapterplantest familyadaptershadowtest familyadapterconstructiontest
  incrementalordertest namingtest drivernamingtest privatealiastest sourcereplayaliastest
  simplenamingtest rulektest defaultctoriotatest sourcestructuresyntaxtest
  composedrecursorsyntaxtest mainclitest projectiontest projectiontransportcensustest
  indexedfibrediagnostictest
  mutualonelayerdiagnostictest structureetatest
  deepimaxboxtest psigmaprimetest exactsortlifttest
  tightpsigmaprimeroutetest vanishingerasuretest
  transparentowneraliasestest exportsyntaxnormalizationtest
  basisvalidationtest sourcespooltest
)
```

The canonical aggregate interface builds those roots one at a time and runs
every executable and repository check script with its required arguments:

```console
test/scripts/run-correctness.sh
```

The individual execution matrix, useful when isolating a failure, is:

```console
lake exe test "$PWD"
lake exe clitest
lake exe generationflagstest
lake exe checktest "$PWD"
lake exe kernelchecktest "$PWD"
lake exe familyadapterplantest
lake exe familyadaptershadowtest
lake exe familyadapterconstructiontest
lake exe ordertest "$PWD"
lake exe incrementalordertest "$PWD"
lake exe namingtest
lake exe drivernamingtest
lake exe privatealiastest
lake exe sourcereplayaliastest
lake exe simplenamingtest
lake exe rulektest
lake exe defaultctoriotatest "$PWD"
lake exe sourcestructuresyntaxtest "$PWD"
lake exe composedrecursorsyntaxtest "$PWD"
lake exe mainclitest "$PWD"
lake exe projectiontest
lake exe projectiontransportcensustest "$PWD"
lake exe indexedfibrediagnostictest "$PWD"
lake exe mutualonelayerdiagnostictest "$PWD"
lake exe structureetatest
lake exe deepimaxboxtest
lake exe psigmaprimetest
lake exe exactsortlifttest
lake exe tightpsigmaprimeroutetest
lake exe vanishingerasuretest
lake exe transparentowneraliasestest
lake exe exportsyntaxnormalizationtest
lake exe basisvalidationtest
lake exe sourcespooltest "$PWD"
PYTHONDONTWRITEBYTECODE=1 python3 test/scripts/test_family_adapter_fixture_generator.py
python3 test/scripts/generate_family_adapter_fixtures.py \
  --output test/fixtures/inductive-models/family_adapter_generated.lean --check
test/scripts/check_arena_corpus.py
test/scripts/check-hard-nested-a.sh
test/scripts/check-hard-nested-c.sh
test/scripts/check-mathlib-result.sh
test/scripts/check-lean4export-patch.sh
test/scripts/check-ci-serialized-builds.sh
```

Two of those targets test the built binary rather than the library: `test`
(its `runCli` section) and `mainclitest` spawn
`.lake/build/bin/lean-inductive-models` as a subprocess. Both therefore declare
`needs := #[`@/«lean-inductive-models»]` in `lakefile.lean`, so `lake exe test`
and `lake exe mainclitest` rebuild the CLI before running and cannot assert the
CLI contract against a stale executable. Do not remove those `needs`: without
them the CLI checks silently pass or fail against whatever binary happens to be
on disk.

The out-of-process checks — `check_arena_corpus.py`,
`check-hard-nested-a.sh`, `check-hard-nested-c.sh` — spawn the same binary but
are not Lake targets, so they still require an explicit
`lake build lean-inductive-models` first (`run-correctness.sh` does this, and
each script fails loudly when the binary is absent).

`mainclitest` exercises the public process boundary, including independent
input/generated kernel-check flags and constructive model-before-owner output.
The Arena corpus runner accepts every
published `good/` case and requires each `bad/` case to be rejected or to stop
at the documented internal-invariant boundary; unsupported exit 2 is a corpus
failure.

`ordertest` compares the compatibility retained-array path, declaration-event
collection, and sink-free compact discard over the
same generation fixtures and exercises planned declaration-wise source
replay. `mainclitest` selects compact discard explicitly with `--no-output`;
`--type-check-generated` checks each exact generated island directly in process,
while `--no-type-check-generated` invokes no generated checker. It pins exit-2 precedence,
noncanonical parser fallback equivalence, cleanup of the
input-only source snapshot workspace, and ordinary fallback before input is
consumed when `_tmp` is unusable. The snapshot exists only to preserve exact
stdin/FIFO input for parser-compatible fallback; generated logical output is
never serialized through it.

`projectiontransportcensustest` is the progress meter for removing dependent
transport from intrinsic projection rules. It generates every committed
`test/fixtures/inductive-models` export with all generation branches enabled
and pins, exhaustively, each `T._model.proj_j.iota` whose statement mentions
`Eq.rec` — separating the generator's canonical right-hand-side transport from
`Eq.rec` the source itself authored in the constructor telescope. A new row is
a regression; a missing row is progress and the maintainer deletes it from
`expectedCensus` by hand. It also pins the fixtures that the maximal
configuration cannot run today, so the census cannot silently stop being
exhaustive.

`memoryprobe`, `envprobe`, and `levelfuzz` are diagnostics, not correctness
suites. The focused CI workflow splits the matrix across fixture, focused, and
CLI jobs and limits each process to 12 GiB. The Mathlib workflow
uses its separately documented 10/12 GiB phase envelopes and artifact gates.
Its generation pass uses transactional declaration-stream named output with
the generated-island gate disabled; a separate artifact-validation invocation uses
`--type-check-input --no-output` to check the serialized export as input after
generation exits. The existing 10 GiB generation cap is
unchanged; the streamed generation and serialized input validation remain
strictly separate processes.

## Fixture regeneration

Human-readable sources and committed exports live in
`test/fixtures/inductive-models/`. Regenerate them
with the pinned exporter:

`test/fixtures/rejected/` is separate and deliberately outside every fixture
sweep: it holds malformed exports that exist to be *refused*, so no generation
or census target should attempt to model them. `kernelchecktest` names each one
directly. `const_universe_arity.ndjson` is the published Arena corpus'
`bad/constlevels`, reduced to the records its crashing theorem needs; its
`Eq.casesOn` occurrence carries no universe levels, which used to reach Lean's
kernel and kill the process with SIGSEGV rather than be rejected.

```console
test/scripts/export-inductive-models.sh prim_shapes
```

`LEAN4EXPORT_DIFFERENTIAL=1 test/scripts/check-lean4export-patch.sh` compares a
stock and patched small export byte for byte. The CI and Mathlib workflow files
remain the authority for hosted-runner resource limits and artifact retention.
