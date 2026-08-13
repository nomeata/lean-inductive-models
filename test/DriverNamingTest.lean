import Modelgen.Driver
import Modelgen.Check
import Modelgen.Naming
import Modelgen.Order

open Lean Meta Modelgen Modelgen.Naming

structure FixtureResult where
  output : Array EDecl
  report : Report

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then
    { state with passed := state.passed + 1 }
  else
    { state with failed := state.failed.push label }

def noGeneration : Modelgen.Cli.Config :=
  { nested := false, mutualModels := false, simple := false, basic := false }

def runExport (label : String) (input : Export) (checkRecursors : Bool)
    (generation : Modelgen.Cli.Config) : IO FixtureResult := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<driver-naming-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((output, report), _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (runFilter input checkRecursors generation)) context { env }
  unless report.stmtErrors.isEmpty do
    throw <| IO.userError s!"{label}: generated statements differ: {report.stmtErrors}"
  return { output, report }

def runFixture (path : String) (generation : Modelgen.Cli.Config) : IO FixtureResult := do
  let text ← IO.FS.readFile path
  let .ok input := Modelgen.parse text (analyse := false)
    | throw <| IO.userError s!"cannot parse {path}"
  runExport path input false generation

def postponeRecords (input : Export) (postpone : EDecl → Bool) : Export :=
  { input with
    decls := input.decls.filter (fun declaration => !postpone declaration) ++
      input.decls.filter postpone }

def flipFirstRecursorSafety (input : Export) : Option (Export × Name) := do
  let index ← input.decls.findIdx? fun declaration => match declaration with
    | .induct _ _ (_ :: _) => true
    | _ => false
  let .induct types constructors (recursor :: recursors) := input.decls[index]! | none
  let changed := { recursor with isUnsafe := !recursor.isUnsafe }
  let declaration := EDecl.induct types constructors (changed :: recursors)
  return ({ input with decls := input.decls.set! index declaration }, recursor.name)

def FixtureResult.hasName (result : FixtureResult) (name : Name) : Bool :=
  result.output.any fun declaration => declaration.names.contains name

def FixtureResult.generated (result : FixtureResult) (owner : Name) : Bool :=
  result.report.generated.any (fun entry => entry.1 == owner)

def FixtureResult.declined (result : FixtureResult) (owner : Name) : Bool :=
  result.report.declined.any (fun entry => entry.1 == owner)

def FixtureResult.hasExactCarrier (result : FixtureResult) (owner : Name) : Bool :=
  result.hasName (modelName owner)

def FixtureResult.hasLegacyCarrier (result : FixtureResult) (owner : Name) : Bool :=
  result.hasName (Name.str (modelName owner) "self")

def declarationIndex? (output : Export) (name : Name) : Option Nat :=
  output.decls.findIdx? (·.names.contains name)

def declarationBefore (output : Export) (first second : Name) : Bool :=
  match declarationIndex? output first, declarationIndex? output second with
  | some i, some j => i < j
  | _, _ => false

def generatedOwnersExact (result : FixtureResult) : Bool :=
  result.report.generated.all fun entry =>
    result.hasExactCarrier entry.1 && !result.hasLegacyCarrier entry.1

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut state : TestState := {}

  let safetyText ← IO.FS.readFile "test/fixtures/modelgen/nested_iota_arm.ndjson"
  let .ok safetyInput := Modelgen.parse safetyText (analyse := false)
    | throw <| IO.userError "cannot parse test/fixtures/modelgen/nested_iota_arm.ndjson"
  let some (wrongSafety, recursorName) := flipFirstRecursorSafety safetyInput
    | throw <| IO.userError "no recursor to mutate in test/fixtures/modelgen/nested_iota_arm.ndjson"
  let safetyResult ← runExport "mutated recursor safety" wrongSafety true noGeneration
  state := state.check "kernel-regenerated recursor safety is checked"
    (safetyResult.report.recMismatch.contains recursorName)

  let carve ← runFixture "test/fixtures/modelgen/prim_carve.ndjson"
    { noGeneration with simple := true, basic := true }
  let skeleton := `Bif._model._impl.skel
  state := state.check "arm-C parent survives exact support closure"
    (carve.generated `Bif && !carve.declined `Bif && carve.hasExactCarrier `Bif)
  state := state.check "arm-C skeleton is modeled at its exact carrier"
    (carve.generated skeleton && carve.hasExactCarrier skeleton &&
      !carve.hasLegacyCarrier skeleton)

  let w ← runFixture "test/fixtures/modelgen/prim_w.ndjson"
    { noGeneration with simple := true, basic := true }
  state := state.check "W parent survives exact support closure"
    (w.generated `Wt && !w.declined `Wt && w.hasExactCarrier `Wt)
  state := state.check "W support closure emits exact carriers"
    (generatedOwnersExact w)

  -- The W target is replayed before the input's exact Iff block and propext.
  -- Its first basis wait drains at Eq; the late wait must remain atomic until
  -- Iff, both of its kernel-owned declarations, and propext are all installed.
  let lateText ← IO.FS.readFile "test/fixtures/modelgen/w_late_iff.ndjson"
  let .ok lateInput := Modelgen.parse lateText (analyse := false)
    | throw <| IO.userError "cannot parse test/fixtures/modelgen/w_late_iff.ndjson"
  let lateW ← runExport "late W logical basis" lateInput false
    { noGeneration with simple := true, basic := true }
  let lateOutput : Export := { lateInput with decls := lateW.output }
  let lateOrdered ← match Order.reorder lateOutput with
    | .ok output => pure output
    | .error error => throw <| IO.userError s!"cannot order late W output: {repr error}"
  let lateOutputCheck := Check.checkReport lateOrdered
  let .ok lateSerialized := Modelgen.parse lateOrdered.render (analyse := false)
    | throw <| IO.userError "cannot parse serialized late W output"
  let lateInputCheck := Check.checkReport lateSerialized
  state := state.check "W target retries after the complete later logical basis"
    (lateW.generated `LateW && !lateW.declined `LateW)
  state := state.check "late W ordered output and serialized input check exactly"
    (lateOutputCheck.violations.isEmpty && lateInputCheck.violations.isEmpty &&
      lateOutputCheck.familiesChecked > 0 &&
      lateOutputCheck.familiesChecked == lateInputCheck.familiesChecked)
  state := state.check "late W dependencies precede its model and owner"
    (declarationBefore lateOrdered `Eq `Iff &&
      declarationBefore lateOrdered `Iff `propext &&
      declarationBefore lateOrdered `propext (modelName `LateW) &&
      declarationBefore lateOrdered (modelName `LateW) `LateW)
  state := state.check "late W retains each reordered source record exactly once"
    ([`LateW, `Eq, `Iff, `propext].all fun name =>
      (lateOrdered.decls.filter (·.names.contains name)).size == 1)

  let graph ← runFixture "test/fixtures/modelgen/prim_graph.ndjson"
    { noGeneration with simple := true, basic := true }
  state := state.check "spliced Nonempty is modeled once at its exact carrier"
    (graph.generated `Nonempty && graph.hasExactCarrier `Nonempty &&
      !graph.hasLegacyCarrier `Nonempty)

  -- This mutual export deliberately orders its recursor records MC, MA, MB,
  -- rather than member order. Exact-name alignment must still match each model
  -- recursor with its own ordered rule list.
  let mutualResult ← runFixture "test/fixtures/modelgen/prim_late_basis.ndjson"
    { noGeneration with mutualModels := true, simple := true }
  let tag := `MA._model._impl.tag
  state := state.check "export recursor order is aligned by exact name"
    mutualResult.report.stmtErrors.isEmpty
  state := state.check "mutual implementation composes through simple naming"
    (mutualResult.generated tag && mutualResult.hasExactCarrier tag &&
      !mutualResult.hasLegacyCarrier tag)

  -- Put canonical Eq physically behind the direct, mutual, nested and
  -- composed owners. The reserved-name guards must remain strict; source
  -- scheduling, not a prelude splice, is what makes every construction work.
  let lateEqText ← IO.FS.readFile "test/fixtures/modelgen/prim_late_basis.ndjson"
  let .ok lateEqSource := Modelgen.parse lateEqText (analyse := false)
    | throw <| IO.userError "cannot parse the late-Eq source fixture"
  let lateEqInput := postponeRecords lateEqSource fun declaration =>
    declaration.names.contains `Eq
  let lateEq ← runExport "canonical Eq after selected owners" lateEqInput false
    { noGeneration with nested := true, mutualModels := true, simple := true, basic := true }
  state := state.check "late canonical Eq is scheduled before representative owners"
    (lateEq.generated `Pre && lateEq.generated `MA && lateEq.generated `Nd &&
      !lateEq.report.declined.any fun (_, reason) => reason.endsWith "name taken (Eq)")

  -- The graph fixture's infinitary recursive field derives its own funext.
  -- Supply only the exact quotient bundle and Quot.sound from the companion
  -- fixture, physically after every graph owner.  With no source `funext` to
  -- short-circuit the route, recursive support closure must use the scheduled
  -- quotient while ensureFunext's reserved-name checks remain untouched.
  let graphText ← IO.FS.readFile "test/fixtures/modelgen/prim_graph.ndjson"
  let .ok graphSource := Modelgen.parse graphText (analyse := false)
    | throw <| IO.userError "cannot parse the graph source fixture"
  let quotientText ← IO.FS.readFile "test/fixtures/modelgen/prim_graph_pre.ndjson"
  let .ok quotientSource := Modelgen.parse quotientText (analyse := false)
    | throw <| IO.userError "cannot parse the quotient support fixture"
  let quotientSupport := quotientSource.decls.filter fun declaration =>
    declaration.names.any fun name => name == `Quot || (`Quot).isPrefixOf name
  let lateQuotInput := { graphSource with decls := graphSource.decls ++ quotientSupport }
  let lateQuot ← runExport "canonical Quot after recursive owner" lateQuotInput false
    { noGeneration with simple := true, basic := true }
  let lateQuotOutput : Export := { lateQuotInput with decls := lateQuot.output }
  state := state.check "late source Quot closes recursive funext support"
    (lateQuot.generated `Ac && !lateQuot.declined `Ac &&
      declarationBefore lateQuotOutput `Quot `Ac &&
      !lateQuot.report.declined.any fun (_, reason) => reason.endsWith "name taken (Quot)")

  let composed ← runFixture "test/fixtures/modelgen/nested_iota.ndjson"
    { noGeneration with nested := true, mutualModels := true, simple := true }
  state := state.check "nested-mutual-simple composition reaches every stage"
    (composed.report.generated.size ≥ 3)
  state := state.check "composed generated owners use exact carriers only"
    (generatedOwnersExact composed)

  IO.println s!"driver naming: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1
