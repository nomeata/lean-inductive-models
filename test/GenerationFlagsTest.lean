import InductiveModels.Driver

namespace GenerationFlagsTest

open Lean Meta InductiveModels

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

def runExport (parsed : Export) (generation : InductiveModels.Cli.Config) : IO (Array EDecl × InductiveModels.Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<generation-flags-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (runFilter parsed false generation)) context { env }
  unless result.2.stmtErrors.isEmpty do
    throw <| IO.userError s!"generated statements differ: {result.2.stmtErrors}"
  return result

def readFixture (path : String) : IO Export := do
  let text ← IO.FS.readFile path
  let .ok parsed := InductiveModels.parse text
    | throw <| IO.userError s!"cannot parse {path}"
  return parsed

def runFixtureOutput (path : String) (generation : InductiveModels.Cli.Config) :
    IO (Array EDecl × InductiveModels.Report) := do
  runExport (← readFixture path) generation

def runFixture (path : String) (generation : InductiveModels.Cli.Config) : IO InductiveModels.Report := do
  return (← runFixtureOutput path generation).2

def generatedNames (report : InductiveModels.Report) : Array Name :=
  report.generated.map (·.1)

def hasGeneratedSuffix (report : InductiveModels.Report) (suffix : String) : Bool :=
  (generatedNames report).any fun name => (toString name).endsWith suffix

def outputNames (decls : Array EDecl) : Array Name :=
  decls.flatMap fun decl => decl.names.toArray

def hasAll (names required : Array Name) : Bool :=
  required.all names.contains

def hasNone (names forbidden : Array Name) : Bool :=
  forbidden.all fun name => !names.contains name

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut state : TestState := {}

  -- Input `Nonempty` is basic, while `Ac` and its generated `.below` family
  -- are ordinary simple declarations.
  let basicOnly ← runFixture "test/fixtures/inductive-models/prim_graph_pre.ndjson" { noGeneration with basic := true }
  state := state.check "basic selects input Nonempty"
    ((generatedNames basicOnly).contains `Nonempty)
  state := state.check "basic excludes ordinary Ac"
    (!(generatedNames basicOnly).contains `Ac)
  let simpleOnly ← runFixture "test/fixtures/inductive-models/prim_graph_pre.ndjson" { noGeneration with simple := true }
  state := state.check "simple selects ordinary Ac" ((generatedNames simpleOnly).contains `Ac)
  state := state.check "simple excludes input Nonempty"
    (!(generatedNames simpleOnly).contains `Nonempty)

  -- The graph arm splices Nonempty. It is present in both outputs, but only
  -- the basic closure recursively models it.
  let graphSimple ← runFixture "test/fixtures/inductive-models/prim_graph.ndjson" { noGeneration with simple := true }
  state := state.check "simple alone leaves spliced Nonempty unmodelled"
    (!(generatedNames graphSimple).contains `Nonempty &&
      graphSimple.spliced.any fun (_, names) => names.contains `Nonempty)
  let graphClosed ← runFixture "test/fixtures/inductive-models/prim_graph.ndjson"
    { noGeneration with simple := true, basic := true }
  state := state.check "basic closes a simple model's spliced Nonempty"
    ((generatedNames graphClosed).contains `Nonempty)

  -- The carve arm marks its spliced skeleton as `Iso.requires`. Without basic, the
  -- parent model remains valid and is not withdrawn merely because the
  -- skeleton itself has no model.
  let carveSimple ← runFixture "test/fixtures/inductive-models/prim_carve.ndjson" { noGeneration with simple := true }
  state := state.check "simple without basic keeps the carve-arm parent"
    ((generatedNames carveSimple).contains `Bif)
  state := state.check "simple without basic leaves the required skeleton unmodelled"
    (!(generatedNames carveSimple).contains `Bif._model._impl.skel &&
      carveSimple.spliced.any fun (_, names) => names.contains `Bif._model._impl.skel)

  -- Nested, mutual and simple are separate stages. A later stage cannot fire
  -- when the stage producing its input is disabled.
  let nestedOnly ← runFixture "test/fixtures/inductive-models/nested_iota.ndjson" { noGeneration with nested := true }
  state := state.check "nested models the input" ((generatedNames nestedOnly).contains `Tree)
  state := state.check "nested alone does not model its mutual output"
    (!hasGeneratedSuffix nestedOnly "._model._impl.0")

  let nestedMutual ← runFixture "test/fixtures/inductive-models/nested_iota.ndjson"
    { noGeneration with nested := true, mutualModels := true }
  state := state.check "mutual models the nested model"
    (hasGeneratedSuffix nestedMutual "._model._impl.0")
  state := state.check "mutual without simple leaves tag and aux unmodelled"
    (!hasGeneratedSuffix nestedMutual "._model._impl.tag" &&
      !hasGeneratedSuffix nestedMutual "._model._impl.aux")

  let nestedSimpleWithoutMutual ← runFixture "test/fixtures/inductive-models/nested_iota.ndjson"
    { noGeneration with nested := true, simple := true }
  state := state.check "simple cannot skip the disabled mutual stage"
    (!hasGeneratedSuffix nestedSimpleWithoutMutual "._model._impl.tag" &&
      !hasGeneratedSuffix nestedSimpleWithoutMutual "._model._impl.aux")

  let nestedThroughSimple ← runFixture "test/fixtures/inductive-models/nested_iota.ndjson"
    { noGeneration with nested := true, mutualModels := true, simple := true }
  state := state.check "simple models mutual tag output"
    (hasGeneratedSuffix nestedThroughSimple "._model._impl.tag")
  state := state.check "simple models mutual aux output"
    (hasGeneratedSuffix nestedThroughSimple "._model._impl.aux")

  -- A plain mutual input is independently controlled by `mutualModels`.
  let mutualOff ← runFixture "test/fixtures/inductive-models/mutual_nonrec.ndjson" { noGeneration with simple := true }
  state := state.check "simple does not model a disabled mutual input"
    (!(generatedNames mutualOff).contains `OA)
  let mutualOnly ← runFixture "test/fixtures/inductive-models/mutual_nonrec.ndjson"
    { noGeneration with mutualModels := true }
  state := state.check "mutual models a plain mutual input"
    ((generatedNames mutualOnly).contains `OA)
  state := state.check "plain mutual alone leaves tag and aux unmodelled"
    (!hasGeneratedSuffix mutualOnly "._model._impl.tag" &&
      !hasGeneratedSuffix mutualOnly "._model._impl.aux")
  let mutualSimple ← runFixture "test/fixtures/inductive-models/mutual_nonrec.ndjson"
    { noGeneration with mutualModels := true, simple := true }
  state := state.check "simple composes over a plain mutual model"
    (hasGeneratedSuffix mutualSimple "._model._impl.tag" &&
      hasGeneratedSuffix mutualSimple "._model._impl.aux")

  -- Public mutual names belong to the exact declaration they model.  They do
  -- not depend on which member happens to head the block or on a flattened
  -- constructor/recursor slot.
  let (shapeDecls, _) ← runFixtureOutput "test/fixtures/inductive-models/mutual_shapes.ndjson"
    { noGeneration with mutualModels := true }
  let shapeNames := outputNames shapeDecls
  state := state.check "mutual exact member/constructor/recursor names"
    (hasAll shapeNames #[
      Naming.modelName `A, Naming.modelName `B, Naming.modelName `C,
      Naming.modelName `A.a0, Naming.modelName `A.aB,
      Naming.modelName `B.bC,
      Naming.modelName `C.c0, Naming.modelName `C.cA, Naming.modelName `C.cf,
      Naming.modelName `A.rec, Naming.modelName `B.rec, Naming.modelName `C.rec,
      Naming.iotaName `A.rec 0, Naming.iotaName `A.rec 1,
      Naming.iotaName `B.rec 0,
      Naming.iotaName `C.rec 0, Naming.iotaName `C.rec 1, Naming.iotaName `C.rec 2,
      Naming.modelName `PA, Naming.modelName `PB, Naming.modelName `PC,
      Naming.modelName `PA.node, Naming.modelName `PA.rec,
      `A._model._impl.tag, `A._model._impl.aux])
  state := state.check "mutual has no old indexed public slots"
    (hasNone shapeNames #[
      `A._model.self, `B._model.self, `C._model.self,
      `A._model.ctor_0, `A._model.rec_0, `A._model.iota_0_0,
      `PA._model.ctor_0, `PA._model.rec_0])

  let (indexDecls, _) ← runFixtureOutput "test/fixtures/inductive-models/mutual_index.ndjson"
    { noGeneration with mutualModels := true }
  let indexNames := outputNames indexDecls
  state := state.check "indexed mutual declarations keep declaration-local names"
    (hasAll indexNames #[
      Naming.modelName `MA, Naming.modelName `MB, Naming.modelName `MC,
      Naming.modelName `MA.step, Naming.modelName `MB.wrap,
      Naming.modelName `MA.rec, Naming.modelName `MB.rec, Naming.modelName `MC.rec,
      Naming.iotaName `MA.rec 0, Naming.iotaName `MB.rec 0])
  state := state.check "indexed mutual has no old flattened slots"
    (hasNone indexNames #[
      `MA._model.self, `MA._model.ctor_0, `MA._model.rec_0,
      `MA._model.iota_0_0])

  -- A declaration which merely occupies an old implementation-shaped name is
  -- unrelated to the new public contract and must not key or block the model.
  let (keyDecls, keyReport) ← runFixtureOutput "test/fixtures/inductive-models/mutual_keying.ndjson"
    { noGeneration with mutualModels := true }
  let keyNames := outputNames keyDecls
  state := state.check "old carrier-shaped input does not block mutual modelling"
    ((generatedNames keyReport).contains `KA && (generatedNames keyReport).contains `GA)
  state := state.check "keying fixture uses exact public names"
    (hasAll keyNames #[
      Naming.modelName `KA, Naming.modelName `KB,
      Naming.modelName `KA.mk, Naming.modelName `KB.z, Naming.modelName `KB.back,
      Naming.modelName `KA.rec, Naming.modelName `KB.rec] &&
      hasNone keyNames #[`KA._model.ctor_0, `KA._model.rec_0])

  -- Private names stay raw: constructing a public model name never strips the
  -- private prefix or derives ownership from the head member's spelling.
  let privateRoot : Name := `OA
  let privateOA := (`_private.MutualNaming).mkNum 0 |>.str "OA"
  let privateInput ← readFixture "test/fixtures/inductive-models/mutual_nonrec.ndjson"
  let privateAliases :=
    privateInput.decls.foldl (init := Naming.AliasMap.empty) fun aliases declaration =>
      declaration.names.foldl (init := aliases) fun aliases name =>
        if privateRoot.isPrefixOf name then
          aliases.insert name (name.replacePrefix privateRoot privateOA)
        else
          aliases
  let privateInput :=
    { privateInput with
      decls := privateInput.decls.map (EDecl.renameAliases privateAliases) }
  let (privateDecls, privateReport) ← runExport privateInput
    { noGeneration with mutualModels := true }
  let privateNames := outputNames privateDecls
  state := state.check "private mutual owner is keyed by its raw name"
    ((generatedNames privateReport).contains privateOA &&
      privateNames.contains (Naming.modelName privateOA) &&
      privateNames.contains (Naming.modelName (Name.str privateOA "fromB")) &&
      privateNames.contains (Naming.modelName (Name.str privateOA "rec")))

  -- The mutual pass also consumes the specialised block emitted by the nested
  -- pass.  Even in that composed route, names are local to the specialised
  -- declarations rather than numbered below the original root.
  let (composedDecls, _) ← runFixtureOutput "test/fixtures/inductive-models/nested_iota.ndjson"
    { noGeneration with nested := true, mutualModels := true }
  let composedNames := outputNames composedDecls
  let nestedImpl := `Tree._model._impl
  let nested0 := nestedImpl.mkNum 0
  let nested1 := nestedImpl.mkNum 1
  let nested0Rec := Name.str nested0 "rec"
  let nested1Rec := Name.str nested1 "rec"
  let nested0Model := Naming.modelName nested0
  state := state.check "nested-to-mutual composition uses exact public names"
    (hasAll composedNames #[
      nested0Model, Naming.modelName nested1,
      Naming.modelName (Name.str nested0 "leaf"),
      Naming.modelName (Name.str nested0 "node"),
      Naming.modelName (Name.str nested1 "nil"),
      Naming.modelName (Name.str nested1 "cons"),
      Naming.modelName nested0Rec, Naming.modelName nested1Rec,
      Naming.iotaName nested0Rec 0, Naming.iotaName nested0Rec 1,
      Name.str (Name.str nested0Model "_impl") "tag",
      Name.str (Name.str nested0Model "_impl") "aux"])
  state := state.check "nested-to-mutual has no old mutual slots"
    (hasNone composedNames #[
      Name.str nested0Model "self", Name.str nested0Model "ctor_0",
      Name.str nested0Model "rec_0", Name.str nested0Model "iota_0_0"])

  IO.println s!"generation flags: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1

end GenerationFlagsTest
