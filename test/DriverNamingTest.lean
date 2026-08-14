import InductiveModels.Driver
import InductiveModels.Naming

open Lean Meta InductiveModels InductiveModels.Naming

structure FixtureResult where
  output : Array EDecl
  report : Report

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def noGeneration : InductiveModels.Cli.Config :=
  { nested := false, mutualModels := false, simple := false, basic := false }

def runExport (label : String) (input : Export) (checkRecursors : Bool)
    (generation : InductiveModels.Cli.Config) : IO FixtureResult := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<driver-naming-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((output, report), _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (runFilter input checkRecursors generation)) context { env }
  unless report.stmtErrors.isEmpty do
    throw <| IO.userError s!"{label}: generated statements differ: {report.stmtErrors}"
  return { output, report }

def runFixture (path : String) (generation : InductiveModels.Cli.Config) : IO FixtureResult := do
  let text ← IO.FS.readFile path
  let .ok input := InductiveModels.parse text
    | throw <| IO.userError s!"cannot parse {path}"
  runExport path input false generation

def flipFirstRecursorSafety (input : Export) : Option (Export × Name) := do
  let index ← input.decls.findIdx? fun declaration => match declaration with
    | .induct _ _ (_ :: _) => true
    | _ => false
  let .induct types constructors (recursor :: recursors) := input.decls[index]! | none
  let changed := { recursor with isUnsafe := !recursor.isUnsafe }
  return ({ input with decls := input.decls.set! index
    (.induct types constructors (changed :: recursors)) }, recursor.name)

def FixtureResult.hasName (result : FixtureResult) (name : Name) : Bool :=
  result.output.any fun declaration => declaration.names.contains name

def FixtureResult.generated (result : FixtureResult) (owner : Name) : Bool :=
  result.report.generated.any (fun entry => entry.1 == owner)

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

  let emptyRecord := EDecl.induct [] [] []
  let emptyInput : Export := { metaLine := .null, decls := #[emptyRecord] }
  let emptyResult ← runExport "empty inductive declaration record" emptyInput false noGeneration
  state := state.check "ordinary filtering retains a nameless inductive record"
    (emptyResult.output == #[emptyRecord] && emptyResult.report == {})

  let passThrough : Array (String × InductiveModels.Cli.Config) := #[
    ("nested_iota.ndjson", legacyGenerationConfig false),
    ("nested_shapes.ndjson", legacyGenerationConfig false),
    ("nat_char_equations.ndjson", legacyGenerationConfig false)]
  for (fixture, generation) in passThrough do
    let path := s!"test/fixtures/inductive-models/filtered/{fixture}"
    let text ← IO.FS.readFile path
    let .ok input := InductiveModels.parse text
      | throw <| IO.userError s!"cannot parse {path}"
    let result ← runExport s!"pass-through {fixture}" input false generation
    state := state.check s!"{fixture} filtering is a byte-order fixed point"
      (result.report.generated.isEmpty && result.output == input.decls)

  let partialText ← IO.FS.readFile
    "test/fixtures/inductive-models/filtered/nested_iota.ndjson"
  let .ok partialInput := InductiveModels.parse partialText
    | throw <| IO.userError "cannot parse partially filtered nested_iota"
  let allBranches ← runExport "partially filtered nested_iota with every branch"
    partialInput false {}
  state := state.check "partially filtered output gains missing simple models"
    (allBranches.output != partialInput.decls && [`N, `List, `Box].all allBranches.generated)

  let safetyText ← IO.FS.readFile "test/fixtures/inductive-models/nested_iota_arm.ndjson"
  let .ok safetyInput := InductiveModels.parse safetyText
    | throw <| IO.userError "cannot parse nested_iota_arm"
  let some (wrongSafety, recursorName) := flipFirstRecursorSafety safetyInput
    | throw <| IO.userError "nested_iota_arm has no recursor"
  let safetyResult ← runExport "mutated recursor safety" wrongSafety true noGeneration
  state := state.check "kernel-regenerated recursor safety is checked"
    (safetyResult.report.recMismatch.contains recursorName)

  let carve ← runFixture "test/fixtures/inductive-models/prim_carve.ndjson"
    (legacyGenerationConfig true)
  let skeleton := `Bif._model._impl.skel
  state := state.check "arm-C skeleton uses exact carriers"
    (carve.generated `Bif && carve.generated skeleton &&
      carve.hasExactCarrier skeleton && !carve.hasLegacyCarrier skeleton)

  let w ← runFixture "test/fixtures/inductive-models/prim_w.ndjson"
    (legacyGenerationConfig true)
  state := state.check "W support closure emits exact carriers"
    ([`Acc, `Nonempty].all w.generated && [`Acc, `Nonempty].all w.hasExactCarrier &&
      [`Acc, `Nonempty].all (fun owner => !w.hasLegacyCarrier owner))

  let graph ← runFixture "test/fixtures/inductive-models/prim_graph.ndjson"
    (legacyGenerationConfig true)
  state := state.check "spliced Nonempty is modeled once at its exact carrier"
    (graph.report.generated.countP (·.1 == `Nonempty) == 1 &&
      graph.hasExactCarrier `Nonempty && !graph.hasLegacyCarrier `Nonempty)

  let mutual ← runFixture "test/fixtures/inductive-models/prim_late_basis.ndjson"
    (legacyGenerationConfig true)
  let tag := `MA._model._impl.tag
  state := state.check "mutual implementation composes through simple naming"
    (mutual.generated tag && mutual.hasExactCarrier tag && !mutual.hasLegacyCarrier tag)

  let composed ← runFixture "test/fixtures/inductive-models/nested_iota.ndjson"
    (legacyGenerationConfig true)
  state := state.check "nested-mutual-simple composition reaches every stage"
    ([`N, `N._model.LList, `N._model.LList._model._impl.tag].all composed.generated)
  state := state.check "composed generated owners use exact carriers only"
    (generatedOwnersExact composed)

  if state.failed.isEmpty then
    IO.println s!"driver naming: {state.passed}/{state.passed} passed"
    return 0
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  IO.eprintln s!"driver naming: {state.passed}/{state.passed + state.failed.size} passed"
  return 1
