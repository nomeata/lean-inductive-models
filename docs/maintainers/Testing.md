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
  test monotest clitest supervisortest generationflagstest checktest ordertest
  incrementalordertest namingtest drivernamingtest privatealiastest
  simplenamingtest rulektest defaultctoriotatest sourcestructuresyntaxtest
  composedrecursorsyntaxtest mainclitest projectiontest indexedfibrediagnostictest
  structureetatest
  deepimaxboxtest psigmaprimetest exactsortlifttest
  tightpsigmaprimeroutetest vanishingerasuretest
  transparentowneraliasestest exportsyntaxnormalizationtest
  basisvalidationtest stagedwritertest
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
lake exe monotest "$PWD"
lake exe clitest
lake exe supervisortest --run-tests "$PWD/.lake/build/bin/supervisortest"
lake exe generationflagstest
lake exe checktest "$PWD"
lake exe ordertest "$PWD"
lake exe incrementalordertest "$PWD"
lake exe namingtest
lake exe drivernamingtest
lake exe privatealiastest
lake exe simplenamingtest
lake exe rulektest
lake exe defaultctoriotatest "$PWD"
lake exe sourcestructuresyntaxtest "$PWD"
lake exe composedrecursorsyntaxtest "$PWD"
lake exe mainclitest "$PWD"
lake exe projectiontest
lake exe indexedfibrediagnostictest "$PWD"
lake exe structureetatest
lake exe deepimaxboxtest
lake exe psigmaprimetest
lake exe exactsortlifttest
lake exe tightpsigmaprimeroutetest
lake exe vanishingerasuretest
lake exe transparentowneraliasestest
lake exe exportsyntaxnormalizationtest
lake exe basisvalidationtest
lake exe stagedwritertest "$PWD"
test/scripts/check_arena_corpus.py
test/scripts/check-hard-nested-a.sh
test/scripts/check-hard-nested-c.sh
test/scripts/check-mathlib-result.sh
test/scripts/check-lean4export-patch.sh
test/scripts/check-ci-serialized-builds.sh
```

`mainclitest` exercises the public process boundary, including universe
monomorphization and default final-output kernel replay. `monotest` exercises
the underlying universe pass directly. The Arena corpus runner accepts every
published `good/` case and requires each `bad/` case to be rejected or to stop
at the documented internal-invariant boundary; unsupported exit 2 is a corpus
failure.

`ordertest` compares four retention policies over the same generation
fixtures: the full-AST oracle, the test-only full-AST shadow spool, the
AST-dropping physical spool, and sink-free compact discard. `mainclitest`
selects compact discard explicitly with `--no-output --no-type-check-output`;
`--no-output --type-check-output` is intentionally a legacy/full-AST control.

`memoryprobe`, `envprobe`, and `levelfuzz` are diagnostics, not correctness
suites. The focused CI workflow splits the matrix across fixture, focused, and
monomorphization jobs and limits each process to 12 GiB. The Mathlib workflow
uses its separately documented 10/12 GiB phase envelopes and artifact gates.

## Fixture regeneration

Human-readable sources and committed exports live in
`test/fixtures/inductive-models/` and `test/fixtures/mono/`. Regenerate them
with the pinned exporter:

```console
test/scripts/export-inductive-models.sh prim_shapes
test/scripts/export-mono.sh mono_proj
```

`LEAN4EXPORT_DIFFERENTIAL=1 test/scripts/check-lean4export-patch.sh` compares a
stock and patched small export byte for byte. The CI and Mathlib workflow files
remain the authority for hosted-runner resource limits and artifact retention.
