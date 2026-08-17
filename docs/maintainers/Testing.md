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
read back with `get_config?` — a TOML lakefile cannot read one at all. The `-Kjobs=1` that
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
which counts a shared page once; summed RSS is far larger (13.7 GiB unbounded)
but nearly all of that is the same mapped `.olean` pages counted once per
reader. **4 is the bound and 1 is not**: serializing costs 4.2x wall to save
0.5 GiB out of the 6 GiB build budget, which the phase is nowhere near. The variable
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

The compile-only targets are the two proof oracles — the `lean_lib`s under
`test/` that no suite module imports, so nothing builds them as a side effect of
building the test binary:

```bash
compile_only_targets=(
  OneLayerProjectionPrototype
  OneLayerRecursorProof
)
```

The build-matrix guard derives that list rather than reading a written one: a
`lean_lib` under `test/` no suite module imports is compile-only, so a new
test-only library has to be named there or it is never compiled at all.

There is **one** test executable, and it takes the suite name as its first
argument: `lake exe test SUITE [ROOT]`. Every suite used to be a `lean_exe` of
its own, and each of those linked the whole library into a separate ~230 MB
binary -- 39 targets and 8.5 GB of `.lake/build/bin` for one program's worth of
code. Running `lake exe test` with no suite prints the registry. Each
invocation runs exactly one suite in its own process, as before: several suites
install search paths and import environments, and their independence is worth
more than a process.

The suite names are the old target names without the `test` suffix, and
`test/TestMain.lean` is the registry they come from. The correctness suites
are:

```bash
correctness_suites=(
  fixtures cli generationflags check kernelcheck order
  incrementalorder naming drivernaming privatealias sourcereplayalias
  simplenaming rulek defaultctoriota sourcestructuresyntax
  composedrecursorsyntax maincli projection projectiontransportcensus
  emissionordercensus
  indexedfibrediagnostic
  mutualonelayerdiagnostic structureeta
  deepimaxbox psigmaprime exactsortlift
  tightpsigmaprimeroute vanishingerasure
  transparentowneralias exportsyntaxnormalization
  basisvalidation arenaformat
)
```

The canonical aggregate interface builds the roots one at a time and runs every
suite and repository check script with its required arguments:

```console
test/scripts/run-correctness.sh
```

The individual execution matrix, useful when isolating a failure, is:

```console
lake exe test fixtures "$PWD"
lake exe test cli "$PWD"
lake exe test generationflags "$PWD"
lake exe test check "$PWD"
lake exe test kernelcheck "$PWD"
lake exe test order "$PWD"
lake exe test incrementalorder "$PWD"
lake exe test naming "$PWD"
lake exe test drivernaming "$PWD"
lake exe test privatealias "$PWD"
lake exe test sourcereplayalias "$PWD"
lake exe test simplenaming "$PWD"
lake exe test rulek "$PWD"
lake exe test defaultctoriota "$PWD"
lake exe test sourcestructuresyntax "$PWD"
lake exe test composedrecursorsyntax "$PWD"
lake exe test maincli "$PWD"
lake exe test projection "$PWD"
lake exe test projectiontransportcensus "$PWD"
lake exe test emissionordercensus "$PWD"
lake exe test indexedfibrediagnostic "$PWD"
lake exe test mutualonelayerdiagnostic "$PWD"
lake exe test structureeta "$PWD"
lake exe test deepimaxbox "$PWD"
lake exe test psigmaprime "$PWD"
lake exe test exactsortlift "$PWD"
lake exe test tightpsigmaprimeroute "$PWD"
lake exe test vanishingerasure "$PWD"
lake exe test transparentowneralias "$PWD"
lake exe test exportsyntaxnormalization "$PWD"
lake exe test basisvalidation "$PWD"
lake exe test arenaformat "$PWD"
test/scripts/check_arena_corpus.py
test/scripts/check-hard-nested-a.sh
test/scripts/check-hard-nested-c.sh
test/scripts/check-mathlib-result.sh
test/scripts/check-ci-serialized-builds.sh
test/scripts/check-checker-imports.sh
test/scripts/check-no-known-gap.sh
```

Two of those suites test the built binary rather than the library: `fixtures`
(its `runCli` section) and `maincli` spawn
`.lake/build/bin/lean-inductive-models` as a subprocess. The `test` target
therefore declares `needs = ["@/lean-inductive-models"]` in `lakefile.toml`, so
`lake exe test` rebuilds the CLI before running any suite and cannot assert the
CLI contract against a stale executable. Do not remove that `needs`: without it
the CLI checks silently pass or fail against whatever binary happens to be on
disk.

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

`check-no-known-gap.sh` reads the same tree for a different claim.  `README.md`
says the coverage ledger has **no known gap**: no shape an arm ought to reach
and does not.  The mechanical form of that is that no decline site names
`Decline.ShapeScope.incomplete`, so the script reads every `.shapeUnsupported`
site in `src/InductiveModels/` and fails if one does.  It counts the
`.outOfScope` sites too, so a refactor that moved the scope off the
constructor's own line makes the script fail rather than silently forbid
nothing.  The verdict itself is deliberately kept in the type: a future guard
narrower than its arm must be recordable as a gap, and the day that happens the
right edit is to rewrite the ledger and this check together, not to reach for
`outOfScope` because it is the one the build accepts.

The out-of-process checks — `check_arena_corpus.py`,
`check-hard-nested-a.sh`, `check-hard-nested-c.sh` — spawn the same binary but
are not Lake targets, so they still require an explicit
`lake build lean-inductive-models` first (`run-correctness.sh` does this, and
each script fails loudly when the binary is absent).

`maincli` exercises the public process boundary, including independent
input/generated kernel-check flags and constructive model-before-owner output.
The Arena corpus runner accepts every
published `good/` case and requires each `bad/` case to be rejected or to stop
at the documented internal-invariant boundary; unsupported exit 2 is a corpus
failure.

`order` compares the compatibility retained-array path, declaration-event
collection, and sink-free compact discard over the same generation fixtures.
`maincli` selects compact discard explicitly with `--no-output`;
`--type-check-generated` checks each exact generated island directly in process,
while `--no-type-check-generated` invokes no generated checker. It pins exit-2
precedence, noncanonical input equivalence, and — in every mode, including with
a hostile `_tmp` and an ambient `TMPDIR` — that the run opens no file it was not
given on the command line.

`arenaformat` pins the export format itself: both readers agree on every
record spelling the Kernel Arena accepts, sparse and repeated arena IDs behave
as the exporter's parser does, and the persistent declaration-stream writer is
byte-identical to whole-export rendering.

`fixtures` runs each fixture with `typeCheckGenerated` at its default, so every
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

`projectiontransportcensus` checks the intrinsic projection contract as an
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

`emissionordercensus` checks **emission order as an invariant**: no
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
rather than being silently replaced. `basisvalidation` covers both halves,
including the rejection.

`--type-check-input` sees record order. `typeCheckExport` used to replay in
`KernelCheck.replayOrder`, a depth-first topological sort, so it computed its
way around every emission-order defect, and the same suite pinned that by
requiring a deliberately order-broken export to still be *accepted*. With the
census at zero that schedule is gone: replay follows the stream, Lean's kernel
rejects the record which names a constant no earlier record declares, and the
weaker assertion was deleted in the commit which made it false. A dependency
cycle is rejected the same way, at the record which closes it, so there is no
separate cycle pass either. The census stays, because it covers the generated
output under the maximal configuration whether or not `--type-check-input` is
passed, and reports every offending record rather than the first.

The `memoryprobe` suite and the `envprobe` and `levelfuzz` executables are
diagnostics, not correctness suites; `memoryprobe` is registered in
`test/TestMain.lean` apart from `correctnessSuites` for that reason. `.github/workflows/ci.yml` is the only workflow file, and it holds
five jobs on one trigger set — push to `main`, every pull request, a Monday
03:17 UTC cron, and manual dispatch. Four of them are fast: an Arena corpus job
and a three-way `fixtures`/`focused`/`cli` matrix, each capped at 30 minutes.
The fifth is the `mathlib` job, which runs `scripts/ci-mathlib.sh` and is
budgeted at 30–50 minutes on a cold runner against an 8-hour cap — the single
pass dropped the 5.9 GB output write and the artifact re-read that cost 19:44
of the old 55:50. It runs on pull requests too, deliberately: the full corpus is
the only place a regression that needs 100M interned nodes shows up, so a change
that only breaks at that scale has to be caught while it is still a diff. Its concurrency group is per ref, so `main` and a
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
phases, which run without one by design and whose recorded peak RSS figures
were taken that way. The same guard asserts that `ci.yml` is the sole workflow
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

The Mathlib job sets no memory limit and takes no memory measurement. It used
to run every phase under `TIME_BIN -v` and fail the run when a phase's peak RSS
crossed a per-phase budget; the budgets, the measurement and the `TIME_BIN`
resolution shim are all gone. CI is a pass/fail gate, and the runner's own
ceiling already stops a runaway.

The 12 GiB figure those budgets carried is worth keeping, but as a **design
criterion rather than a CI verdict**. The reference point is `lean4checker`,
which parses and kernel-checks this same Mathlib in about **9 GB**. This tool
parses the same corpus *and* generates models from it, so staying near that
number is evidence the design is sound and drifting well past it is evidence it
is not — independent of what any runner happens to survive. The baseline as of
this writing, for the whole single-pass gate over the pinned export:

| phase | peak RSS |
| --- | --- |
| `lake build lean-inductive-models`, cold | 2.91 GiB |
| `lake build` in the pinned lean4export | 1.46 GiB |
| `lake exe cache get` | 0.95 GiB |
| Mathlib export | **11.45 GiB** |
| generation, single pass | **7.39 GiB**, 11:49 wall |

The export phase is the one number that went **up**, and deliberately. It was
7.92 GiB while the gate patched `lean4export`'s expression interner; the patch
is gone and the gate builds the pinned revision as upstream ships it, so the
phase costs what stock costs. Measured here on the same host, same pinned
Mathlib, exporter revision `caccfbe`, `lake env lean4export Mathlib | gzip -1`:

| exporter | peak RSS | retired instructions | wall |
| --- | --- | --- | --- |
| stock | 11.45 GiB | 2.025e12 | 3:31 |
| patched | 7.77 GiB | 3.102e12 | 4:35 |

Read the RSS and the instruction count; **wall time on this host is not
comparable** — it is shared, and repeated runs of identical work swing by tens
of percent. The instruction counts are `perf stat -e instructions` over the
whole export and are stable. The compact interner bought 3.68 GiB of resident
memory for 1.53x the instructions, which is the trade it was designed to make
and is not one this repository has to make for someone else's binary. Both
exports are byte-identical: the two gzip files agree on SHA-256
(`28de0ef1…c03a0`, 1,115,721,571 bytes), over all of Mathlib rather than over
the small fixture the old differential check used.

11.45 GiB is comfortable rather than roomy on a 16 GiB runner. What makes it
fine is that the gate is single-pass: the export writes a gzip and exits, and
generation reads that file afterwards, so the export phase has the runner to
itself and its peak never coexists with generation's.

The single pass measures *lower* than the two-phase shape it replaced, which
was 11.39 GiB generating plus 8.22 GiB rechecking, and faster than either. That
is not a surprise once stated: `--no-output` takes the no-output compact path,
which retains value-only verdict certificates and never opens a generated-output
workspace, so the declaration-stream writer's persistent maps and the retained
compact record arrays behind the old plateau are simply not allocated. Turning
the generated-island kernel gate on costs less than they did. The tool now sits
*under* `lean4checker`'s ~9 GB for this corpus while doing strictly more, which
is the direction the criterion wants.

Measured locally against the pinned export
(`gzip -dc mathlib.ndjson.gz | lean-inductive-models - --no-output
--no-type-check-input --type-check-generated`, `LEAN_NUM_THREADS=4`), reporting
`generated kernel checks: 6639` and `output check: 6882 model families checked`.
To take the measurement deliberately, run exactly that under `/usr/bin/time -v`;
nothing in CI will do it for you. One thing keeps the number from being as
roomy as it looks: the interner's key array is a power-of-two table sitting at
roughly 75% of a 134.2M-entry capacity at this corpus' ~99.9M interned nodes, so
a corpus that crosses the load factor doubles the table and costs about 1.6 GB
in one step.

The gate's two Lake build phases run under the same `LEAN_NUM_THREADS` bound as
the fast jobs; the cache, export and generation phases have no thread ceiling,
being a download and two single workers.

`scripts/ci-mathlib.sh` runs the export through the tool in **one pass**:

```
gzip -dc mathlib.ndjson.gz |
  lean-inductive-models - --no-output --no-type-check-input --type-check-generated
```

It is deliberately about a dozen lines of work: clone Mathlib at the pinned
revision, fetch its cache, clone stock lean4export at its pinned revision, build
both, export, and run that one pass. The pinned revisions are correctness and
stay; everything else that used to be here was scaffolding for phases that no
longer exist.

The export is still serialized to a compressed file rather than piped live into
the generator. That is not scaffolding: the export and generation peaks are
roughly 11.5 and 7.4 GiB, which do not coexist on a 16 GiB runner and would not
fit if they did, and gzip also keeps the 5.6 GB uncompressed export off the
disk. Both large pipelines report
`PIPESTATUS`, so a failed exporter or a truncated stream fails the gate instead
of producing a plausible-looking run.

What the gate proves: over the full corpus, nothing declines, Lean's kernel
accepts every generated island as it is produced, every generated model family
passes the structural output check, every generated statement matches its exact
exported owner interface, and universe planning never escapes.
`scripts/check-mathlib-result.sh` enforces all of that from the log.

What it deliberately does not prove, and what covers those properties instead:

* **The input export's own kernel validity** — `--no-type-check-input`. The
  pinned Mathlib export is an assumption of this gate, not a claim of it. The
  flag is still exercised on a real corpus elsewhere:
  `test/scripts/check_arena_corpus.py` runs every published Lean Kernel Arena
  case with `--type-check-input --type-check-generated`.
* **Serialization round-tripping** — `--no-output`. The gate used to write a
  5.9 GB artifact and re-read it under `--type-check-input`, at 19:44 and
  8.22 GiB. Round-tripping is covered by axis 4 of the `fixtures`
  suite — `parse (render (parse t)) = parse t`, structurally — and by
  `lake exe test maincli`, which writes exports to real paths and reads them
  back. Note that `check_arena_corpus.py` does *not* cover this: it runs with
  `--no-output` too.

That trade is not a reduction in kernel coverage. The old artifact re-read was
the *only* kernel check in the run — generation ran with
`--no-type-check-generated` and reported `generated kernel checks: 0`. The
single pass moves the kernel to island time, so the corpus now gets kernel
coverage of the generated declarations that nothing had at this scale before,
and `scripts/check-mathlib-result.sh` requires that count to be positive rather
than merely requiring an accepting verdict.

## Fixture regeneration

Human-readable sources and committed exports live in
`test/fixtures/inductive-models/`. Regenerate them
with the pinned exporter:

`test/fixtures/rejected/` is separate and deliberately outside every fixture
sweep: it holds malformed exports that exist to be *refused*, so no generation
or census target should attempt to model them. `kernelcheck` names each one
directly. `const_universe_arity.ndjson` is the published Arena corpus'
`bad/constlevels`, reduced to the records its crashing theorem needs; its
`Eq.casesOn` occurrence carries no universe levels. Under Lean 4.29.1 that
occurrence reached `type_checker::whnf_core` through a `let` value the kernel
only ever reduces, and killed the process with SIGSEGV. Lean 4.30.0 taught
`type_checker::is_delta` to check a constant's universe-level arity, so from
4.33.0 the kernel itself refuses the record — reporting a `let-declaration
type mismatch 'x'` rather than crashing. `kernelcheck` pins that message.

```console
test/scripts/export-inductive-models.sh prim_shapes
```

`.github/workflows/ci.yml` remains the authority for hosted-runner resource
limits and artifact retention.
