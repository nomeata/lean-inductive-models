import Modelgen.Driver
import Modelgen.Naming

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

def FixtureResult.declineReason? (result : FixtureResult) (owner : Name) : Option String :=
  (result.report.declined.find? fun entry => entry.1 == owner).map (·.2)

def FixtureResult.hasExactCarrier (result : FixtureResult) (owner : Name) : Bool :=
  result.hasName (modelName owner)

def FixtureResult.hasLegacyCarrier (result : FixtureResult) (owner : Name) : Bool :=
  result.hasName (Name.str (modelName owner) "self")

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

  -- Red-boundary pin: the W target is replayed before the input's exact Iff
  -- block and propext. The basis wait drains at Eq, but the old late set does
  -- not recognise Iff, so it loses the target rather than retrying it after
  -- the logical interface arrives.
  let lateW ← runFixture "test/fixtures/modelgen/w_late_iff.ndjson"
    { noGeneration with simple := true, basic := true }
  state := state.check "W target currently declines at the later exact Iff block"
    (!lateW.generated `LateW && lateW.declineReason? `LateW ==
      some "prim model name taken (Iff)")

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

  let composed ← runFixture "test/fixtures/modelgen/nested_iota.ndjson"
    { noGeneration with nested := true, mutualModels := true, simple := true }
  state := state.check "nested-mutual-simple composition reaches every stage"
    (composed.report.generated.size ≥ 3)
  state := state.check "composed generated owners use exact carriers only"
    (generatedOwnersExact composed)

  IO.println s!"driver naming: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1
