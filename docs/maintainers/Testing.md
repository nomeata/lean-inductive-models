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
  emissionordercensustest
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
lake exe emissionordercensustest "$PWD"
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
test/scripts/check-checker-imports.sh
```

Two of those targets test the built binary rather than the library: `test`
(its `runCli` section) and `mainclitest` spawn
`.lake/build/bin/lean-inductive-models` as a subprocess. Both therefore declare
`needs := #[`@/«lean-inductive-models»]` in `lakefile.lean`, so `lake exe test`
and `lake exe mainclitest` rebuild the CLI before running and cannot assert the
CLI contract against a stale executable. Do not remove those `needs`: without
them the CLI checks silently pass or fail against whatever binary happens to be
on disk.

`check-checker-imports.sh` needs no build at all: it reads the `import` lines
under `src/InductiveModels/` and fails if the structural checker
(`InductiveModels.Check`) reaches the generator — `Gen`, `Nested`, `Simple`,
`Mutual`, `Driver` or `Model` — transitively. `README.md` claims the
correspondence check is independent of the kernel verdict, and independence is
a claim about reach rather than about care: a checker that can call the
generator has to be re-argued after every change, while one that cannot import
it is settled. The script also pins the checker's whole transitive closure to
its declared foundation, so a *new* generator module is caught on the day it is
imported rather than on the day someone remembers to extend the list. Adding a
genuinely new foundation module to `Check` therefore means editing
`allowed_closure` in that script, on purpose.

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

`projectiontransportcensustest` checks the intrinsic projection contract as an
invariant rather than as an allowlist. It generates every committed
`test/fixtures/inductive-models` export with all generation branches enabled
and requires, of every `T._model.proj_j.iota` without exception, that its
right-hand side is the constructor's field-`j` binder — the loose `Expr.bvar`
that the modeled constructor's `numParams + numFields` telescope binds at
position `numParams + j`. There is no table to append a row to: a right-hand
side that is anything else is a defect in the route that produced it, and the
suite names the fixture, owner and field. Source-authored `Eq.rec` in a
constructor telescope or projection codomain is unrelated syntax the model
reproduces exactly, and is counted rather than restricted. The suite still
pins the fixtures that the maximal configuration cannot run today, so the
invariant cannot silently stop being exhaustive.

`emissionordercensustest` bounds a **known defect**: generated output is not
currently guaranteed to be replayable in record order. Lean's kernel starts
from an empty environment and adds one declaration at a time, but
`Driver.installInputCanonicalBasis` installs an input's own canonical-basis
records (`Eq`, `Nat`, `PUnit`, the `PSigma'` bundle, `Nonempty`, the `Quot`
bundle with `Quot.sound`, `Classical.choice`, `Iff`, `propext`) into the replay
environment *before* the stream is consumed, so a generated island can be
emitted against a basis member that the output only declares later. An output
is dirty exactly when its input declares a canonical-basis member after the
first owner that consumes it; every genuine input fixture is itself clean, so
this is a property of what the filter emits rather than of what it reads.
Today that is **1143 records across 15 of the 78 committed fixtures** —
`arm_f_zip`, `mutual_structure_projections`, `prim_carve`, `prim_graph`,
`prim_graph_pre`, `prim_idx`, `prim_late_eq`, `prim_shapes`, `prim_w`,
`private_constructor`, `tight_prop_field_late`, `w_core`, `w_late_iff`, and the
filtered `nested_iota` and `nested_shapes` — reaching `Eq`, `Eq.refl`,
`PSigma'`, `PUnit` and the `Quot` bundle ahead of the record that declares them.
The suite walks each generated stream in record order from an empty
declared-name set, using `KernelCheck.inputReferences` as the dependency set,
and pins the exact per-fixture counts in `expectedForwardReferences`. It fails
both when a fixture becomes dirty and when a listed fixture becomes clean or
changes count without the list being updated: the list is a progress meter
toward zero, not an exemption.

**The fix is pending a contract decision the project owner has not made** —
either the filter emits every island after everything that island consumes, or
the output contract states that the stream is a set of records carrying a
dependency schedule rather than a replayable sequence — so nothing in the test
tree works around the defect and no existing gate is relaxed for it.
`--type-check-input` does not detect it: `typeCheckExport` replays in
`KernelCheck.replayOrder`, a depth-first topological sort, so record order never
reaches Lean's kernel. The same suite therefore also asserts that a deliberately
order-broken export is still *accepted*. That assertion is the weaker property
on purpose and is not an endorsement — it records that acceptance by
`--type-check-input` is no evidence that an output replays in record order, and
it fails the moment replay is made order-sensitive, which forces the allowlist
above to be driven to empty before such a change can land.

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
