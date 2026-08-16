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

`emissionordercensustest` checks **emission order as an invariant**: no
generated record references a name the output stream has not declared yet, in
any committed fixture, under the maximal generation configuration. Lean's kernel
starts from an empty environment and adds one declaration at a time, so this is
exactly the property that makes the emitted stream replayable as written, and
it is what lets any prefix of an output — a stream truncated at a record
boundary, which is what standard output leaves behind when a later transition
fails — replay on its own.

The suite walks each generated stream in record order from an empty
declared-name set, using `KernelCheck.inputReferences` as the dependency set.
There is no allowlist and no row to append. A run the filter *rejects* is
failed rather than counted clean, because `runFilter` answers an unreplayable
record by returning the input, which is clean by construction.

The one construct that used to break the invariant was the fixed canonical
basis — `Eq`, `Nat`, `PUnit`, the `PSigma'` bundle, `Nonempty`, the `Quot`
bundle with `Quot.sound`, `Classical.choice`, `Iff`, `propext`. An input which
declared one of those *after* the first owner that consumed it left the output
referring to it ahead of the record that declared it: **1143 records across 15
of the 78 committed fixtures**, in `arm_f_zip`, `mutual_structure_projections`,
`prim_carve`, `prim_graph`, `prim_graph_pre`, `prim_idx`, `prim_late_eq`,
`prim_shapes`, `prim_w`, `private_constructor`, `tight_prop_field_late`,
`w_core`, `w_late_iff`, and the filtered `nested_iota` and `nested_shapes`.
Generation now writes its own canonical declaration at the first point one is
needed, whatever the input reserves, and drops the input's own record where it
stands once `Driver.canonicalBasisRecordMatches` has established that it is
that same declaration; a record which is *not* that declaration rejects the run
rather than being silently replaced. `basisvalidationtest` covers both halves,
including the rejection.

`--type-check-input` still does not see record order at all: `typeCheckExport`
replays in `KernelCheck.replayOrder`, a depth-first topological sort. The same
suite therefore also asserts that a deliberately order-broken export is still
*accepted*. That assertion is the weaker property on purpose and is not an
endorsement — it records that acceptance by `--type-check-input` is no evidence
that an export replays in record order, which is why the invariant above has to
be checked directly. Making replay order-sensitive is a separate contract
decision; it is no longer blocked by this repository's own output, and the
commit that takes it deletes that assertion.

`memoryprobe`, `envprobe`, and `levelfuzz` are diagnostics, not correctness
suites. The focused CI workflow splits the matrix across fixture, focused, and
CLI jobs and sets no per-process memory limit of its own: the runner's 16 GiB
and the job timeout are what bound it. It used to cap each process at 12 GiB
with `ulimit -v`, which bounds **virtual address space** rather than resident
memory. Those were always different quantities and since the v4.33.0 toolchain
they are unrelated: a v4.33.0 `lean` frontend reserves about 12.8 GiB of
address space at startup for allocator arenas — eleven-plus 1 GiB anonymous
mappings, and `MIMALLOC_ARENA_RESERVE` does not change it — while its peak RSS
is unchanged at roughly 2.0 GiB. Under a 12 GiB `ulimit -v` no module builds at
all, aborting with `failed to create thread`; a cap high enough for `lean` to
start no longer says anything about memory. **RSS is the quantity of interest.**

The Mathlib workflow keeps enforced per-phase budgets, and enforces them as
cgroup v2 `memory.max` limits — `systemd-run --scope -p MemoryMax=…
-p MemorySwapMax=0` — rather than as address-space ceilings. `memory.max`
accounts page cache as well as anonymous memory, but the kernel reclaims cache
under pressure and only OOM-kills on genuine anonymous growth, so streaming the
~5.9 GB output sibling does not trip a budget while a real leak does. The
budgets are 6 GiB for the build and cache phases (measured peak 2.91 GiB),
12 GiB for the Mathlib export (measured peak 7.80 GiB), and 12 GiB for the
model worker. `scripts/ci-mathlib.sh` picks the strongest mechanism the runner
actually supports by probing each one for real — a per-user scope, a `sudo`
system scope dropping back to the calling user, or, where no cgroup can be
created, running unbudgeted and failing the phase afterwards on peak RSS from
`TIME_BIN -v`. Which one applied is printed as `memory budgets: enforced by …`,
and every phase reports its peak RSS against its budget either way.

The generation pass uses transactional declaration-stream named output with
the generated-island gate disabled; a separate artifact-validation invocation uses
`--type-check-input --no-output` to check the serialized export as input after
generation exits. Generation's measured 13.91 GiB peak RSS does not yet fit the
12 GiB worker budget — that budget is the target it has to reach, not a
description of what it costs today. The streamed generation and serialized
input validation remain strictly separate processes.

## Fixture regeneration

Human-readable sources and committed exports live in
`test/fixtures/inductive-models/`. Regenerate them
with the pinned exporter:

`test/fixtures/rejected/` is separate and deliberately outside every fixture
sweep: it holds malformed exports that exist to be *refused*, so no generation
or census target should attempt to model them. `kernelchecktest` names each one
directly. `const_universe_arity.ndjson` is the published Arena corpus'
`bad/constlevels`, reduced to the records its crashing theorem needs; its
`Eq.casesOn` occurrence carries no universe levels. Under Lean 4.29.1 that
occurrence reached `type_checker::whnf_core` through a `let` value the kernel
only ever reduces, and killed the process with SIGSEGV. Lean 4.30.0 taught
`type_checker::is_delta` to check a constant's universe-level arity, so from
4.33.0 the kernel itself refuses the record — reporting a `let-declaration
type mismatch 'x'` rather than crashing. `kernelchecktest` pins that message.

```console
test/scripts/export-inductive-models.sh prim_shapes
```

`LEAN4EXPORT_DIFFERENTIAL=1 test/scripts/check-lean4export-patch.sh` compares a
stock and patched small export byte for byte. The CI and Mathlib workflow files
remain the authority for hosted-runner resource limits and artifact retention.
