import InductiveModels.Driver

/-!
# Emission order, censused — and the replay that does not depend on it

Run from the repository root: `lake exe emissionordercensustest [ROOT]`.

This suite pins a **known defect**. It does not fix it, and nothing here should
be read as saying the defect is acceptable.

## The defect

Generated output is emitted as one stream of records. Lean's kernel builds an
environment by adding declarations one at a time, so a stream that is meant to
be replayable *as written* must never mention a constant before the record that
declares it. The output stream does not currently meet that.

`Driver.installInputCanonicalBasis` installs an input's own canonical-basis
records — `Eq`, `Nat`, `PUnit`, the `PSigma'` bundle, `Nonempty`, the `Quot`
bundle with `Quot.sound`, `Classical.choice`, `Iff`, `propext` — into the
replay environment *before* the stream is consumed, so a generated island may
be emitted against a basis member that the output only declares later, at the
raw ordinal the input put it at. An output is dirty exactly when its input
declares a canonical-basis member *after* the first owner that consumes it;
inputs whose basis precedes every consumer are clean. The genuine input
fixtures themselves have no forward reference at all — this is a property of
what the filter emits, not of what it reads.

## What this file measures

`forwardReferences` walks the generated records in emission order from an
**empty** declared-name set — the state Lean's kernel actually starts in — and
reports every record whose kernel dependency set reaches a name the stream has
not declared yet. The dependency set is `KernelCheck.inputReferences`, which is
the project's own answer to "which constants does the kernel need in place
before it will accept this record"; using it rather than a second, private
traversal is what makes this census measure exactly the property that
`KernelCheck.replayOrder` reorders around.

`expectedForwardReferences` below is a **progress meter toward zero**, in the
manner of `test/ProjectionTransportCensusTest.lean`'s `expectedUnrunnable`. It
is an exact list, so the suite fails in every direction: a fixture that becomes
dirty is a new defect, and a fixture that becomes clean, or whose count moves,
is progress that has to be recorded rather than absorbed. Rows are removed, not
edited upward, unless a maintainer deliberately writes down why.

The fix is a contract decision that has not been made: either the filter emits
each island after everything it consumes, or the output contract says in so
many words that the stream is a set of records with a declared dependency
schedule rather than a sequence. That decision belongs to the project owner,
so this file only bounds and displays the gap.

## Why the second half is here

`--type-check-input` does *not* see this defect, because
`InductiveModels.typeCheckExport` does not replay in record order: it replays in
`KernelCheck.replayOrder`, a depth-first topological sort of the same
`inputReferences` edges. `orderInsensitiveReplayAccepts` pins that.

**That assertion is deliberately the weaker property, and it is not an
endorsement.** It says only what is true today: an export whose records are in
a broken order is still accepted, so the acceptance of any generated output by
`--type-check-input` is *no evidence* that the output is replayable in record
order. Its purpose is to fail loudly if someone later makes replay
order-sensitive — at which point the census above stops being a progress meter
and becomes a set of real rejections that must be dealt with before that change
can land. A maintainer who wants replay to be order-sensitive should expect to
delete this assertion and empty the allowlist in the same commit.
-/

set_option maxRecDepth 4096

open Lean Meta InductiveModels

/-- Every generation branch on, so the census sees the maximal output stream
rather than one suite's slice. This matches
`ProjectionTransportCensusTest.censusGeneration`. -/
def censusGeneration : Cli.Config :=
  { nested := true, mutualModels := true, simple := true, basic := true }

/-- One record that mentions a constant the stream has not declared yet. -/
structure ForwardReference where
  /-- Position in the emitted stream. -/
  index : Nat
  /-- The names this record itself declares. -/
  names : List Name
  /-- Referenced names not yet declared at this point, sorted. -/
  missing : Array Name

def ForwardReference.describe (reference : ForwardReference) : String :=
  let shown := reference.missing.toList.take 3
  let ellipsis := if reference.missing.size > 3 then ", …" else ""
  s!"record {reference.index} ({reference.names}) needs \
    {", ".intercalate (shown.map toString)}{ellipsis}"

/-- Walk `decls` in emission order from an empty declared-name set and report
every record referencing a name not yet declared.

A record's own names are excluded: a mutual inductive block, and the recursors
the kernel derives from it, legitimately mention the block's own members, and
the kernel accepts the whole block as one declaration.

`KernelCheck.inputReferences` is empty for a record the replay skips — unsafe
and partial declarations are never submitted to the kernel — so such a record
contributes no forward reference here either, exactly as it contributes no
dependency edge to `KernelCheck.replayOrder`. -/
def forwardReferences (decls : Array EDecl) : Array ForwardReference := Id.run do
  let mut declared : Std.HashSet Name := {}
  let mut result : Array ForwardReference := #[]
  for index in [:decls.size] do
    let record := decls[index]!
    let own := record.names
    let mut missing : Array Name := #[]
    for name in KernelCheck.inputReferences record do
      unless declared.contains name || own.contains name do
        missing := missing.push name
    unless missing.isEmpty do
      result := result.push
        { index, names := own, missing := missing.qsort (·.toString < ·.toString) }
    for name in own do
      declared := declared.insert name
  return result

structure FixtureCensus where
  /-- Records in the generated stream that reference a not-yet-declared name. -/
  forwardReferencing : Nat := 0
  /-- The first such record, for the console line. -/
  first? : Option String := none
  /-- Records in the stream. -/
  records : Nat := 0
  /-- The same walk over the *input* export, which is expected to be clean. -/
  inputForwardReferencing : Nat := 0
  ran : Bool := true

def censusFixture (path : String) : IO FixtureCensus := do
  let .ok x := parse (← IO.FS.readFile path)
    | throw <| IO.userError s!"cannot parse {path}"
  let inputForwardReferencing := (forwardReferences x.decls).size
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := path, fileMap := default, maxHeartbeats := 0, maxRecDepth := 8192 }
  let decls? ← try
      let ((decls, _), _) ← Core.CoreM.toIO
        (MetaM.run' (runFilter x false censusGeneration)) context { env }
      pure (some decls)
    catch _ => pure none
  let some decls := decls? | return { ran := false, inputForwardReferencing }
  let references := forwardReferences decls
  return { forwardReferencing := references.size,
           first? := references[0]?.map (·.describe),
           records := decls.size,
           inputForwardReferencing }

/-- The committed corpus, as (label prefix, directory) pairs, as in
`ProjectionTransportCensusTest`. -/
def fixtureDirectories : Array (String × String) :=
  #[("", "test/fixtures/inductive-models"),
    ("filtered/", "test/fixtures/inductive-models/filtered")]

/-- **The progress meter.** Every fixture whose generated output currently
contains at least one record referencing a not-yet-declared name, with its
exact count.

Every row is a defect. The target is the empty array. Removing a row is the
only edit that needs no justification; adding one, or raising a count, records
that the output stream got further from being replayable as written and must be
argued for in the commit message. -/
def expectedForwardReferences : Array (String × Nat) :=
  #[("arm_f_zip", 7),
    ("filtered/nested_iota", 69),
    ("filtered/nested_shapes", 69),
    ("mutual_structure_projections", 13),
    ("prim_carve", 288),
    ("prim_graph", 67),
    ("prim_graph_pre", 7),
    ("prim_idx", 101),
    ("prim_late_eq", 9),
    ("prim_shapes", 65),
    ("prim_w", 222),
    ("private_constructor", 7),
    ("tight_prop_field_late", 4),
    ("w_core", 47),
    ("w_late_iff", 168)]

/-- Fixtures the maximal generation configuration cannot run to completion,
pinned for the same reason as in `ProjectionTransportCensusTest`: the census
must not silently stop being exhaustive. -/
def expectedUnrunnable : Array String := #[]

/-- A deliberately order-broken export: the same records, emitted back to
front.

Reversal is used rather than a hand-written stream because it is derived from a
committed fixture, so this assertion cannot drift away from the real format. -/
def orderBroken (x : Export) : Export := { x with decls := x.decls.reverse }

/-- `--type-check-input` replays via `KernelCheck.replayOrder`, a depth-first
topological sort, so record order does not reach Lean's kernel.

This asserts the *weaker* property on purpose — see the header. It first
establishes that the reversed export really is order-broken (otherwise the
acceptance below would say nothing), then that `typeCheckExport` accepts it
anyway. If replay is ever made order-sensitive this assertion fails, which is
the intended signal: `expectedForwardReferences` must be driven to empty before
such a change can land. -/
def orderInsensitiveReplayAccepts (root : String) : IO (Array String) := do
  let path := s!"{root}/test/fixtures/inductive-models/prim_shapes.ndjson"
  let .ok x := parse (← IO.FS.readFile path)
    | throw <| IO.userError s!"cannot parse {path}"
  let mut failures : Array String := #[]
  let straight := (forwardReferences x.decls).size
  unless straight == 0 do
    failures := failures.push
      s!"prim_shapes.ndjson is itself order-broken in {straight} records: \
         a genuine input fixture is the control for this assertion"
  let broken := orderBroken x
  let brokenCount := (forwardReferences broken.decls).size
  if brokenCount == 0 then
    failures := failures.push
      "reversing prim_shapes.ndjson produced no forward reference, so the \
       acceptance below would not witness order-insensitivity: pick an input \
       whose reversal is genuinely order-broken"
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<emission-order-census-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Core.CoreM.toIO (MetaM.run' (typeCheckExport broken)) context { env }
  match result with
  | .ok () => pure ()
  | .error message =>
    failures := failures.push
      s!"typeCheckExport rejected an order-broken export: {message}. Replay has \
         become order-sensitive; expectedForwardReferences is now a list of real \
         rejections and must be driven to empty"
  unless failures.isEmpty do return failures
  IO.println s!"order-insensitive replay: an export reversed into \
    {brokenCount} forward-referencing records is still accepted by \
    typeCheckExport (this pins today's weaker property, not an endorsement)"
  return #[]

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let root := args.head?.getD "."
  let mut paths : Array (String × String) := #[]
  for (prefix_, directory) in fixtureDirectories do
    for entry in ← System.FilePath.readDir s!"{root}/{directory}" do
      if entry.path.extension == some "ndjson" then
        paths := paths.push (prefix_ ++ entry.path.fileStem.getD "", entry.path.toString)
  paths := paths.qsort (fun left right => left.1 < right.1)

  let mut failures : Array String := #[]
  let mut dirty : Array (String × Nat) := #[]
  let mut unrunnable : Array String := #[]
  let mut records := 0
  let mut forwardReferencing := 0
  for (fixture, path) in paths do
    let result ← censusFixture path
    records := records + result.records
    forwardReferencing := forwardReferencing + result.forwardReferencing
    unless result.ran do unrunnable := unrunnable.push fixture
    unless result.inputForwardReferencing == 0 do
      failures := failures.push
        s!"{fixture}: the *input* export has {result.inputForwardReferencing} \
           forward-referencing records; this census is about generated output, \
           and a dirty input is a separate defect in the fixture or its exporter"
    if result.forwardReferencing > 0 then
      dirty := dirty.push (fixture, result.forwardReferencing)
      IO.println s!"  {fixture}: {result.forwardReferencing} forward-referencing \
        records, first at {result.first?.getD "?"}"

  unrunnable := unrunnable.qsort (· < ·)
  if unrunnable != expectedUnrunnable.qsort (· < ·) then
    failures := failures.push
      s!"unrunnable fixtures are {unrunnable}, expected {expectedUnrunnable}: \
         update expectedUnrunnable"
  if dirty != expectedForwardReferences then
    failures := failures.push
      s!"emission-order census is {dirty}, expected {expectedForwardReferences}: \
         a fixture became dirty, became clean, or changed count — update \
         expectedForwardReferences and say in the commit message which"

  failures := failures ++ (← orderInsensitiveReplayAccepts root)

  IO.println s!"emission order census: {forwardReferencing} of {records} \
    generated records reference a name the stream has not declared yet, across \
    {dirty.size} of {paths.size - unrunnable.size} fixtures"
  for failure in failures do IO.eprintln s!"FAIL: {failure}"
  return if failures.isEmpty then 0 else 1
