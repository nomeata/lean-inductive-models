# Maintainer build and test guide

The user-facing build is simply `lake build`; `lake test` runs the primary
fixture-backed suite. This document records the complete maintainer matrix and
the resource-sensitive commands used by CI.

Keep scratch files on project-local disk:

```console
mkdir -p _tmp/build-tmp
export TMPDIR="$PWD/_tmp/build-tmp"
```

Bound Lake's build parallelism:

```console
export LEAN_NUM_THREADS=4
```

**Lake 5.0.0 has no job-count flag.** `-j/--jobs` was dropped in the toolchain
bump, and `-K key=value` only sets a configuration-file option for a lakefile to
read back with `get_config?` — this lakefile reads none. The `-Kjobs=1` that
scripts, CI and this guide used to pass was therefore inert: it produced a
byte-for-byte identical, fully parallel build. Any instruction to build "with
one job" that relied on it had no effect.

Lake schedules its build jobs as Lean tasks, so the Lean runtime's thread pool
is the control that exists, and `LEAN_NUM_THREADS` sizes it. Measured on a
96-core host, clean `lake build lean-inductive-models`:

| setting | wall | user | CPU/wall | peak summed PSS |
| --- | --- | --- | --- | --- |
| none | 39.4 s | 160.5 s | 4.58x | 3.00 GiB |
| `-Kjobs=1` | 39.3 s | 160.1 s | 4.59x | 2.96 GiB |
| `LEAN_NUM_THREADS=4` | 54.0 s | 155.8 s | 3.25x | 2.41 GiB |
| `LEAN_NUM_THREADS=2` | 89.7 s | 156.8 s | 1.97x | 1.90 GiB |
| `LEAN_NUM_THREADS=1` | 164.8 s | 158.1 s | 1.08x | 1.92 GiB |

Peak memory is the sum of proportional set sizes over the whole process tree,
which is what a cgroup charges; summed RSS is far larger (13.7 GiB unbounded)
but nearly all of that is the same mapped `.olean` pages counted once per
reader. **4 is the bound and 1 is not**: serializing costs 4.2x wall to save
0.5 GiB out of the 6 GiB build budget, and the budget is enforced as a cgroup
limit, so there is nothing left for serialization to protect. The variable
bounds the Lean runtime as a whole, so it also caps each `lean` child's own
threads — free here, since a single `lean` frontend on the heaviest module runs
at 1.22x CPU/wall at every setting.

One root per Lake invocation is a separate, weaker property, and worth keeping
for what it actually gives: at most one target *link* live, and a named target
when a build fails. It is not serialization — inside one invocation Lake still
runs up to `LEAN_NUM_THREADS` jobs at once.

```bash
build_bounded() {
  local target
  for target in "$@"; do
    lake build "$target"
  done
}
```

The compile-only targets — two proof oracles and three test-only libraries — are:

```bash
compile_only_targets=(
  FamilyAdapterConstruction
  FamilyAdapterPlan
  FamilyAdapterShadow
  OneLayerProjectionPrototype
  OneLayerRecursorProof
)
```

The three `FamilyAdapter*` libraries are not oracles: they are the parked
family-adapter experiment, which lives in `test/FamilyAdapterPlan.lean`,
`test/FamilyAdapterShadow.lean` and `test/FamilyAdapterConstruction.lean` and is
declared as its own `lean_lib` per layer rather than as modules of
`InductiveModels`. Nothing under `src/` imports any of them and the experiment
emits nothing, so charging the shipped library and the `lean-inductive-models`
executable for compiling them bought nothing. `Driver` reaches an observation
only through `InductiveModels.IslandObserver`, an opaque `EDecl → Iso → MetaM α`
callback: production supplies none, and `test/FamilyAdapterShadowTest.lean`
supplies the one that calls `deriveShadowPlan` and `ShadowReport.observe`. So
`Driver` names no adapter type, and only `familyadapterplantest`,
`familyadaptershadowtest` and `familyadapterconstructiontest` build these.

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
  basisvalidationtest arenaformattest
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
lake exe arenaformattest "$PWD"
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
collection, and sink-free compact discard over the same generation fixtures.
`mainclitest` selects compact discard explicitly with `--no-output`;
`--type-check-generated` checks each exact generated island directly in process,
while `--no-type-check-generated` invokes no generated checker. It pins exit-2
precedence, noncanonical input equivalence, and — in every mode, including with
a hostile `_tmp` and an ambient `TMPDIR` — that the run opens no file it was not
given on the command line.

`arenaformattest` pins the export format itself: both readers agree on every
record spelling the Kernel Arena accepts, sparse and repeated arena IDs behave
as the exporter's parser does, and the persistent declaration-stream writer is
byte-identical to whole-export rendering.

`test` runs each fixture with `typeCheckGenerated` at its default, so every
accepted island goes through `checkGeneratedIn`, and `runOne` reads the verdict
(`Report.generatedKernelRejected`, and `Report.unreplayable` beside it). It did
not always: for a while the suite compared counts, declines, statements,
ordering and the round trip and dropped the kernel's answer on the floor, so a
model Lean refused could match every other axis and be reported green. The
fixture that found this is `w_dependent_field`, whose `WDep` is a
one-constructor owner with a dependent ordinary field on the legacy W arm —
its projection ι related two terms of different types, the CLI rejected it, and
this suite did not look. If a fixture is ever expected to fail the kernel, it
belongs in a diagnostic suite that says so, not in this table.

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
suites. `.github/workflows/ci.yml` is the only workflow file, and it holds
five jobs on one trigger set — push to `main`, every pull request, a Monday
03:17 UTC cron, and manual dispatch. Four of them are fast: an Arena corpus job
and a three-way `fixtures`/`focused`/`cli` matrix, each capped at 30 minutes.
The fifth is the `mathlib` job, which runs `scripts/ci-mathlib.sh` and is
budgeted at 50–70 minutes on a cold runner against an 8-hour cap. It runs on
pull requests too, deliberately: the full corpus is the only place a
regression that needs 100M interned nodes shows up, and generation's peak RSS
sits 0.64 GiB under its budget, so a change that costs memory has to be caught
while it is still a diff. Its concurrency group is per ref, so `main` and a
pull request each keep one run and the newest run on a ref cancels the older.
The four fast jobs report independently, so no pull request waits on the gate
for its quick signal. If pull-request volume ever makes the hour unreasonable,
gate the job on a label rather than dropping it to manual dispatch; the
workflow comment carries the exact `if:` to use.

The `LEAN_NUM_THREADS` bound is stated in each fast job rather than once at
workflow level, and `test/scripts/check-ci-serialized-builds.sh` asserts that
`ci.yml` has no workflow-level `env:` at all. A workflow-level `env:` is
inherited by every job and cannot be unset by one, so hoisting the bound would
push a thread ceiling onto the Mathlib gate's cache, export and generation
phases — which run without one by design, and whose peak RSS figures below were
measured that way. The same guard asserts that `ci.yml` is the sole workflow
file and that it invokes the gate script exactly once.

The fast jobs set no per-process memory limit of their own: the runner's 16 GiB
and the job timeout are what bound it. It used to cap each process at 12 GiB
with `ulimit -v`, which bounds **virtual address space** rather than resident
memory. Those were always different quantities and since the v4.33.0 toolchain
they are unrelated: a v4.33.0 `lean` frontend reserves about 12.8 GiB of
address space at startup for allocator arenas — eleven-plus 1 GiB anonymous
mappings, and `MIMALLOC_ARENA_RESERVE` does not change it — while its peak RSS
is unchanged at roughly 2.0 GiB. Under a 12 GiB `ulimit -v` no module builds at
all, aborting with `failed to create thread`; a cap high enough for `lean` to
start no longer says anything about memory. **RSS is the quantity of interest.**

The Mathlib job keeps per-phase budgets, and where the runner lets it,
enforces them as cgroup v2 `memory.max` limits — `systemd-run --scope
-p MemoryMax=… -p MemorySwapMax=0` — rather than as address-space ceilings. `memory.max`
accounts page cache as well as anonymous memory, but the kernel reclaims cache
under pressure and only OOM-kills on genuine anonymous growth, so streaming the
~5.9 GB output sibling does not trip a budget while a real leak does. The
budgets are 6 GiB for the build and cache phases (measured peak 2.91 GiB),
12 GiB for the Mathlib export (measured peak 7.79 GiB), and 12 GiB for the
model worker (measured peaks 11.36 GiB generating and 8.19 GiB rechecking). Its two Lake build phases now run under the same
`LEAN_NUM_THREADS` bound as CI, so the build budget is met by a stated ceiling
rather than by whatever parallelism the runner happened to offer; the cache,
export and generation phases are left unbounded, being a download and two
single measured workers. `scripts/ci-mathlib.sh` picks the strongest mechanism the runner
actually supports by probing each one for real — a per-user scope, a `sudo`
system scope dropping back to the calling user, or, where no cgroup can be
created, running unbudgeted and failing the phase afterwards on peak RSS from
`TIME_BIN -v`. Which one applied is printed as `memory budgets: enforced by …`,
and every phase reports its peak RSS against its budget either way. Read that
line before trusting a budget: only the two scope mechanisms *enforce*
anything. The `measure` fallback compares after the fact, and `TIME_BIN -v`
reports the largest single process rather than the process tree's sum, so it
cannot catch a build phase whose Lake children only exceed 6 GiB together, and
a genuine runaway takes the runner down before the comparison ever runs. A
phase whose measurement cannot be read at all is now a hard failure rather than
a skipped check.

The generation pass uses transactional declaration-stream named output with
the generated-island gate disabled; a separate artifact-validation invocation uses
`--type-check-input --no-output` to check the serialized export as input after
generation exits. Generation's measured 11.36 GiB peak RSS now fits the 12 GiB
worker budget, but with 0.64 GiB — 5.3% — to spare, which is a number to defend
rather than to spend: a 16 GiB runner also has to hold the OS, the gzip feeder
and the page cache behind the ~5.9 GB output sibling, and the interner's
power-of-two key table sits at roughly 75% of a 134.2M-entry capacity at this
corpus' ~99.9M interned nodes, so the next doubling costs about 1.6 GB in one
step. The streamed generation and serialized input validation remain strictly
separate processes.

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
stock and patched small export byte for byte. `.github/workflows/ci.yml`
remains the authority for hosted-runner resource limits and artifact retention.
