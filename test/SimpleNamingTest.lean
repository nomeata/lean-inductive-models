import Modelgen.Driver
import Modelgen.Naming

open Lean Meta Modelgen Modelgen.Naming

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

def noGeneration : Modelgen.Cli.Config :=
  { nested := false, mutualModels := false, simple := false, basic := false }

def runFixture (path : String) (generation : Modelgen.Cli.Config) : IO FixtureResult := do
  let text ← IO.FS.readFile path
  let .ok input := Modelgen.parse text (analyse := false)
    | throw <| IO.userError s!"cannot parse {path}"
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<simple-naming-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((output, report), _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (runFilter input false generation)) context { env }
  unless report.stmtErrors.isEmpty do
    throw <| IO.userError s!"{path}: generated statements differ: {report.stmtErrors}"
  return { input, output, report }

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

  let shapes ← runFixture "test/fixtures/modelgen/prim_shapes.ndjson" simpleOnly
  state := state.check "Type route has declaration-local interface"
    (shapes.hasInterface `Tri `Tri.rec #[`Tri.a, `Tri.b, `Tri.c] 3)
  state := state.check "Type route has no legacy indexed slots" (shapes.noLegacySlots `Tri)
  state := state.check "indexed Church route has declaration-local interface"
    (shapes.hasInterface `IdxP `IdxP.rec #[`IdxP.at_a, `IdxP.at_b] 2)
  state := state.check "indexed Church route has no legacy slots"
    (shapes.noLegacySlots `IdxP)

  let graph ← runFixture "test/fixtures/modelgen/prim_graph.ndjson" simpleOnly
  state := state.check "graph route has declaration-local interface"
    (graph.hasInterface `Ac `Ac.rec #[`Ac.intro] 1)
  state := state.check "graph helpers are implementation descendants"
    (graph.hasDescendant `Ac._model._impl && graph.hasName `Ac._model._impl.graph &&
      !graph.hasName `Ac._model.graph)
  state := state.check "graph route has no legacy slots" (graph.noLegacySlots `Ac)

  let carve ← runFixture "test/fixtures/modelgen/prim_carve.ndjson" simpleOnly
  state := state.check "carve route has declaration-local interface"
    (carve.hasInterface `Bif `Bif.rec #[`Bif.b0, `Bif.b2] 2)
  state := state.check "skeleton helpers are implementation descendants"
    (carve.hasName `Bif._model._impl.skel && !carve.hasName `Bif._model.skel)
  state := state.check "carve route has no legacy slots" (carve.noLegacySlots `Bif)

  let w ← runFixture "test/fixtures/modelgen/prim_w.ndjson" simpleOnly
  state := state.check "W route has declaration-local interface"
    (w.hasInterface `Wt `Wt.rec #[`Wt.leaf, `Wt.one, `Wt.two, `Wt.mix, `Wt.gap, `Wt.alt] 6)
  state := state.check "W helpers are implementation descendants"
    (w.hasName `Wt._model._impl.wD && w.hasName `Wt._model._impl.wF &&
      !w.hasName `Wt._model.wD)
  state := state.check "W route has no legacy slots" (w.noLegacySlots `Wt)

  let basicNonempty ← runFixture "test/fixtures/modelgen/prim_graph_pre.ndjson"
    { noGeneration with basic := true }
  state := state.check "basic Nonempty has declaration-local interface"
    (basicNonempty.hasInterface `Nonempty `Nonempty.rec #[`Nonempty.intro] 1)
  state := state.check "basic Nonempty has no legacy slots"
    (basicNonempty.noLegacySlots `Nonempty)

  let basicAcc ← runFixture "test/fixtures/modelgen/w_core.ndjson" { noGeneration with basic := true }
  state := state.check "basic Acc has declaration-local interface"
    (basicAcc.hasInterface `Acc `Acc.rec #[`Acc.intro] 1)
  state := state.check "basic Acc has no legacy slots" (basicAcc.noLegacySlots `Acc)

  let privateCtor ← runFixture "test/fixtures/mono/mono_offname.ndjson" simpleOnly
  let privateCtors := inputConstructors privateCtor.input `Off
  state := state.check "private constructor keeps its exact raw exported name"
    (privateCtors.size == 1 && privateCtor.hasName (modelName privateCtors[0]!))
  state := state.check "private-constructor route has no legacy slots"
    (privateCtor.noLegacySlots `Off)

  let composed ← runFixture "test/fixtures/modelgen/prim_late_basis.ndjson"
    { noGeneration with mutualModels := true, simple := true }
  state := state.check "an original _model component composes"
    (composed.hasName `MA._model._impl.tag._model &&
      composed.hasName `MA._model._impl.tag.rec._model &&
      !composed.hasName `MA._model._impl.tag._model.self)

  IO.println s!"simple naming: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1
