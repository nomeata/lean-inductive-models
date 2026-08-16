import InductiveModels.Driver

/-!
# Emission order, as an invariant — and the replay that does not depend on it

Run from the repository root: `lake exe emissionordercensustest [ROOT]`.

## The invariant

Generated output is emitted as one stream of records. Lean's kernel builds an
environment by adding declarations one at a time, so a stream that is meant to
be replayable *as written* must never mention a constant before the record that
declares it. The invariant this suite pins is that the output stream meets that
exactly: **no generated record references a name the stream has not declared
yet**, in any committed fixture, under the maximal generation configuration.

There is no allowlist here and no row to append. The one construct that used to
break it was the fixed canonical basis — `Eq`, `Nat`, `PUnit`, the `PSigma'`
bundle, `Nonempty`, the `Quot` bundle with `Quot.sound`, `Classical.choice`,
`Iff`, `propext`. An input which declared one of those *after* the first owner
that consumed it left the output referring to it before the record that
declared it, in 1143 records across 15 of the 78 fixtures. Generation now writes
its own canonical declaration at the first point one is needed, whatever the
input reserves, and drops the input's own record where it stands once it has
been checked to be that same declaration
([`InductiveModels.canonicalBasisRecordMatches`]); there is no other source of a
forward reference, so a new one is a defect in the route that produced it and
this suite names the fixture and the record.

## What this file measures

`forwardReferences` walks the generated records in emission order from an
**empty** declared-name set — the state Lean's kernel actually starts in — and
reports every record whose kernel dependency set reaches a name the stream has
not declared yet. The dependency set is `KernelCheck.inputReferences`, which is
the project's own answer to "which constants does the kernel need in place
before it will accept this record"; using it rather than a second, private
traversal is what makes this suite measure exactly the property that
`KernelCheck.replayOrder` reorders around.

`expectedUnrunnable` remains, for the same reason it does in
`test/ProjectionTransportCensusTest.lean`: it is about *exhaustiveness* rather
than about ordering, and a fixture that starts or stops running under the
maximal configuration has to be noticed or the invariant would quietly stop
covering the corpus. The input exports are checked to be clean too — a dirty
input is a separate defect in the fixture or its exporter, not something this
suite may absorb.

## Why the second half is here

`--type-check-input` does *not* see record order at all, because
`InductiveModels.typeCheckExport` does not replay in it: it replays in
`KernelCheck.replayOrder`, a depth-first topological sort of the same
`inputReferences` edges. `orderInsensitiveReplayAccepts` pins that, by taking a
genuine input fixture, reversing it, and requiring the reversal to be both
order-broken and accepted.

That assertion is deliberately the *weaker* property and it is still not an
endorsement. It says that acceptance of any export by `--type-check-input` is
**no evidence** that the export is replayable in record order — which is why the
invariant above has to be checked separately and directly. It is kept, rather
than deleted along with the allowlist it used to protect, because that
distinction is exactly as true now as it was before: the two halves of this file
assert two different things about the same stream.

Making replay order-sensitive is a separate contract decision. With the census
above at zero it is no longer blocked by this repository's own output; a
maintainer who takes it should expect this assertion to fail, which is the
intended signal, and should delete it in that same commit.
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
  /-- Why the filter rejected the input, if it did. -/
  unreplayable? : Option String := none

/-- **A rejected run is not a clean run.** `runFilter` answers an unreplayable
source record by returning the *input* declarations with the reason in the
report, and the input is clean by construction — so a rejection would otherwise
walk zero forward references and read as a pass. The reason is carried out and
failed on instead. -/
def censusFixture (path : String) : IO FixtureCensus := do
  let .ok x := parse (← IO.FS.readFile path)
    | throw <| IO.userError s!"cannot parse {path}"
  let inputForwardReferencing := (forwardReferences x.decls).size
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := path, fileMap := default, maxHeartbeats := 0, maxRecDepth := 8192 }
  let filtered? ← try
      let ((decls, report), _) ← Core.CoreM.toIO
        (MetaM.run' (runFilter x false censusGeneration)) context { env }
      pure (some (decls, report))
    catch _ => pure none
  let some (decls, report) := filtered? | return { ran := false, inputForwardReferencing }
  let references := forwardReferences decls
  return { forwardReferencing := references.size,
           first? := references[0]?.map (·.describe),
           records := decls.size,
           inputForwardReferencing,
           unreplayable? := report.unreplayable }

/-- The committed corpus, as (label prefix, directory) pairs, as in
`ProjectionTransportCensusTest`. -/
def fixtureDirectories : Array (String × String) :=
  #[("", "test/fixtures/inductive-models"),
    ("filtered/", "test/fixtures/inductive-models/filtered")]

/-- Fixtures the maximal generation configuration cannot run to completion,
pinned for the same reason as in `ProjectionTransportCensusTest`: the invariant
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
the intended signal, and the maintainer making that change deletes it. -/
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
         become order-sensitive, so this assertion no longer states a property \
         of this tool and the commit that made replay order-sensitive should \
         delete it"
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
  let mut unrunnable : Array String := #[]
  let mut records := 0
  let mut forwardReferencing := 0
  for (fixture, path) in paths do
    let result ← censusFixture path
    records := records + result.records
    forwardReferencing := forwardReferencing + result.forwardReferencing
    unless result.ran do unrunnable := unrunnable.push fixture
    if let some why := result.unreplayable? then
      failures := failures.push
        s!"{fixture}: the filter rejected an input record — {why}; a rejected run \
           generates nothing and would read as a clean stream here"
    unless result.inputForwardReferencing == 0 do
      failures := failures.push
        s!"{fixture}: the *input* export has {result.inputForwardReferencing} \
           forward-referencing records; this suite is about generated output, \
           and a dirty input is a separate defect in the fixture or its exporter"
    unless result.forwardReferencing == 0 do
      failures := failures.push
        s!"{fixture}: {result.forwardReferencing} generated records reference a \
           name the stream has not declared yet, first at \
           {result.first?.getD "?"}: the output is no longer replayable in \
           record order, which is a defect in the route that emitted it"

  unrunnable := unrunnable.qsort (· < ·)
  if unrunnable != expectedUnrunnable.qsort (· < ·) then
    failures := failures.push
      s!"unrunnable fixtures are {unrunnable}, expected {expectedUnrunnable}: \
         update expectedUnrunnable"

  failures := failures ++ (← orderInsensitiveReplayAccepts root)

  IO.println s!"emission order: {records - forwardReferencing} of {records} \
    generated records declare every name they reference before referencing it, \
    across {paths.size - unrunnable.size} fixtures"
  for failure in failures do IO.eprintln s!"FAIL: {failure}"
  return if failures.isEmpty then 0 else 1
