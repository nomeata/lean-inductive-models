import InductiveModels.Driver
import InductiveModels.Naming

open Lean Meta InductiveModels InductiveModels.Naming

structure FixtureResult where
  input : Export
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

def noGeneration : InductiveModels.Cli.Config :=
  { nested := false, mutualModels := false, simple := false, basic := false }

def readInput (path : String) : IO Export := do
  let text ← IO.FS.readFile path
  let .ok input := InductiveModels.parse text
    | throw <| IO.userError s!"cannot parse {path}"
  return input

def runInput (input : Export) (generation : InductiveModels.Cli.Config) : IO FixtureResult := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<simple-naming-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((output, report), _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (runFilter input false generation)) context { env }
  unless report.stmtErrors.isEmpty do
    throw <| IO.userError s!"generated statements differ: {report.stmtErrors}"
  return { input, output, report }

def runFixture (path : String) (generation : InductiveModels.Cli.Config) : IO FixtureResult := do
  runInput (← readInput path) generation

/-- Test-only prerequisite-first source variant. Every selected prerequisite is
moved as one complete declaration record, in its original relative order, just
before `owner`; all unrelated source records retain their relative order. -/
def withCompletePrerequisitesBefore (input : Export) (prerequisites : Array Name)
    (owner : Name) : IO Export := do
  let ownerIndices := (Array.range input.decls.size).filter fun index =>
    input.decls[index]!.names.contains owner
  unless ownerIndices.size == 1 do
    throw <| IO.userError s!"expected one complete {owner} record, got {ownerIndices}"
  let mut prerequisiteIndices := #[]
  for prerequisite in prerequisites do
    let indices := (Array.range input.decls.size).filter fun index =>
      input.decls[index]!.names.contains prerequisite
    unless indices.size == 1 do
      throw <| IO.userError s!"expected one complete {prerequisite} record, got {indices}"
    prerequisiteIndices := prerequisiteIndices.push indices[0]!
  unless (Array.range prerequisiteIndices.size).all fun index =>
      index == 0 || prerequisiteIndices[index - 1]! < prerequisiteIndices[index]! do
    throw <| IO.userError s!"prerequisites are not in source order: {prerequisiteIndices}"
  let moved := prerequisiteIndices.map (input.decls[·]!)
  let retained := (Array.range input.decls.size).foldl (init := #[]) fun records index =>
    if prerequisiteIndices.contains index then records else records.push input.decls[index]!
  let some ownerIndex := retained.findIdx? (·.names.contains owner)
    | throw <| IO.userError s!"moving prerequisites lost owner {owner}"
  let declarations :=
    retained.extract 0 ownerIndex ++ moved ++ retained.extract ownerIndex retained.size
  return { input with decls := declarations }

def withCompletePrerequisiteBefore (input : Export) (prerequisite owner : Name) : IO Export :=
  withCompletePrerequisitesBefore input #[prerequisite] owner

def FixtureResult.hasName (result : FixtureResult) (name : Name) : Bool :=
  result.output.any (fun declaration => declaration.names.contains name)

def FixtureResult.hasDescendant (result : FixtureResult) (root : Name) : Bool :=
  result.output.any fun declaration => declaration.names.any (root.isPrefixOf ·)

def FixtureResult.noLegacySlots (result : FixtureResult) (owner : Name) : Bool :=
  let root := modelName owner
  !result.hasName (Name.str root "self") &&
  !result.hasName (Name.str root "ctor_0") &&
  !result.hasName (Name.str root "rec_0") &&
  !result.hasName (Name.str root "iota_0_0")

def FixtureResult.declinedWithoutModel (result : FixtureResult) (owner : Name)
    (reason : String) : Bool :=
  result.report.declined.contains (owner, reason) &&
    (result.input.decls.find? (·.names.contains owner)).any fun sourceBlock =>
      let modelRoots := sourceBlock.names.toArray.map modelName
      result.output.all fun declaration => declaration.names.all fun name =>
        modelRoots.all fun root => !root.isPrefixOf name

def FixtureResult.hasInterface (result : FixtureResult) (owner recursor : Name)
    (constructors : Array Name) (numRules : Nat) : Bool :=
  result.hasName (modelName owner) &&
  constructors.all (result.hasName ∘ modelName) &&
  result.hasName (modelName recursor) &&
  (Array.range numRules).all fun j => result.hasName (iotaName recursor j)

def inputConstructors (input : Export) (owner : Name) : Array Name :=
  input.decls.flatMap fun declaration => match declaration with
    | .induct _ constructors _ =>
        (constructors.filter (·.induct == owner)).toArray.map (·.name)
    | _ => #[]

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut state : TestState := {}
  let simpleOnly := { noGeneration with simple := true }

  let shapesInput ← readInput "test/fixtures/inductive-models/prim_shapes.ndjson"
  let shapesRaw ← runInput shapesInput simpleOnly
  let shapes ← runInput (← withCompletePrerequisiteBefore shapesInput `Eq `Tri) simpleOnly
  state := state.check "raw Type routes before Eq decline without partial models"
    (shapesRaw.declinedWithoutModel `Tri "prim model name taken (Eq)" &&
      shapesRaw.declinedWithoutModel `IdxP "prim model name taken (Eq)")
  state := state.check "Type route has declaration-local interface"
    (shapes.hasInterface `Tri `Tri.rec #[`Tri.a, `Tri.b, `Tri.c] 3)
  state := state.check "Type route has no legacy indexed slots" (shapes.noLegacySlots `Tri)
  state := state.check "indexed Church route has declaration-local interface"
    (shapes.hasInterface `IdxP `IdxP.rec #[`IdxP.at_a, `IdxP.at_b] 2)
  state := state.check "indexed Church route has no legacy slots"
    (shapes.noLegacySlots `IdxP)

  let graphInput ← readInput "test/fixtures/inductive-models/prim_graph.ndjson"
  let graphRaw ← runInput graphInput simpleOnly
  let graph ← runInput (← withCompletePrerequisiteBefore graphInput `Eq `Ac) simpleOnly
  state := state.check "raw graph owner before Eq declines without a partial model"
    (graphRaw.declinedWithoutModel `Ac "prim model name taken (Eq)")
  state := state.check "graph route has declaration-local interface"
    (graph.hasInterface `Ac `Ac.rec #[`Ac.intro] 1)
  state := state.check "graph helpers are implementation descendants"
    (graph.hasDescendant `Ac._model._impl && graph.hasName `Ac._model._impl.graph &&
      !graph.hasName `Ac._model.graph)
  state := state.check "graph route has no legacy slots" (graph.noLegacySlots `Ac)

  let carveInput ← readInput "test/fixtures/inductive-models/prim_carve.ndjson"
  let carveRaw ← runInput carveInput simpleOnly
  let carve ← runInput (← withCompletePrerequisiteBefore carveInput `Eq `Bif) simpleOnly
  state := state.check "raw carve owner before Eq declines without a partial model"
    (carveRaw.declinedWithoutModel `Bif "prim model name taken (Eq)")
  state := state.check "carve route has declaration-local interface"
    (carve.hasInterface `Bif `Bif.rec #[`Bif.b0, `Bif.b2] 2)
  state := state.check "skeleton helpers are implementation descendants"
    (carve.hasName `Bif._model._impl.skel && !carve.hasName `Bif._model.skel)
  state := state.check "carve route has no legacy slots" (carve.noLegacySlots `Bif)

  let wInput ← readInput "test/fixtures/inductive-models/prim_w.ndjson"
  let wRaw ← runInput wInput simpleOnly
  let w ← runInput (← withCompletePrerequisiteBefore wInput `Eq `Wt) simpleOnly
  state := state.check "raw W owner before Eq declines without a partial model"
    (wRaw.declinedWithoutModel `Wt "prim model name taken (Eq)")
  state := state.check "W route has declaration-local interface"
    (w.hasInterface `Wt `Wt.rec #[`Wt.leaf, `Wt.one, `Wt.two, `Wt.mix, `Wt.gap, `Wt.alt] 6)
  state := state.check "W helpers are implementation descendants"
    (w.hasName `Wt._model._impl.wD && w.hasName `Wt._model._impl.wF &&
      !w.hasName `Wt._model.wD)
  state := state.check "W route has no legacy slots" (w.noLegacySlots `Wt)

  let basicNonempty ← runFixture "test/fixtures/inductive-models/prim_graph_pre.ndjson"
    { noGeneration with basic := true }
  state := state.check "basic Nonempty has declaration-local interface"
    (basicNonempty.hasInterface `Nonempty `Nonempty.rec #[`Nonempty.intro] 1)
  state := state.check "basic Nonempty has no legacy slots"
    (basicNonempty.noLegacySlots `Nonempty)

  let accInput ← readInput "test/fixtures/inductive-models/w_core.ndjson"
  let basicAccRaw ← runInput accInput { noGeneration with basic := true }
  let accSupportInput ← withCompletePrerequisitesBefore accInput
    #[`Nat, `Nonempty, `Classical.choice] `Acc
  let basicAcc ← runInput accSupportInput { noGeneration with basic := true }
  state := state.check "raw basic Acc before its complete support declines without a partial model"
    (basicAccRaw.declinedWithoutModel `Acc
      "prim model prerequisite occurs later in the input stream")
  state := state.check "basic Acc has declaration-local interface"
    (basicAcc.hasInterface `Acc `Acc.rec #[`Acc.intro] 1)
  state := state.check "basic Acc has no legacy slots" (basicAcc.noLegacySlots `Acc)

  let privateInput ← readInput "test/fixtures/inductive-models/private_constructor.ndjson"
  let privateRaw ← runInput privateInput simpleOnly
  let privateCtor ← runInput
    (← withCompletePrerequisiteBefore privateInput `Eq `Off) simpleOnly
  let privateCtors := inputConstructors privateCtor.input `Off
  state := state.check "raw private-constructor owner before Eq declines without a partial model"
    (privateRaw.declinedWithoutModel `Off "prim model name taken (Eq)")
  state := state.check "private constructor keeps its exact raw exported name"
    (privateCtors.size == 1 && privateCtor.hasName (modelName privateCtors[0]!))
  state := state.check "private-constructor route has no legacy slots"
    (privateCtor.noLegacySlots `Off)

  let composed ← runFixture "test/fixtures/inductive-models/prim_late_basis.ndjson"
    { noGeneration with mutualModels := true, simple := true }
  state := state.check "an original _model component composes"
    (composed.hasName `MA._model._impl.tag._model &&
      composed.hasName `MA._model._impl.tag.rec._model &&
      !composed.hasName `MA._model._impl.tag._model.self)

  IO.println s!"simple naming: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1
