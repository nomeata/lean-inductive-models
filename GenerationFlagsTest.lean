import Modelgen.Driver

open Lean Meta Modelgen

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

def runFixture (path : String) (generation : Modelgen.Cli.Config) : IO Modelgen.Report := do
  let text ← IO.FS.readFile path
  let .ok parsed := Modelgen.parse text (analyse := false)
    | throw <| IO.userError s!"cannot parse {path}"
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<generation-flags-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((_, report), _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (runFilter parsed false generation)) context { env }
  unless report.stmtErrors.isEmpty do
    throw <| IO.userError s!"{path}: generated statements differ: {report.stmtErrors}"
  return report

def generatedNames (report : Modelgen.Report) : Array Name :=
  report.generated.map (·.1)

def hasGeneratedSuffix (report : Modelgen.Report) (suffix : String) : Bool :=
  (generatedNames report).any fun name => (toString name).endsWith suffix

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut state : TestState := {}

  -- Input `Nonempty` is basic, while `Ac` and its generated `.below` family
  -- are ordinary simple declarations.
  let basicOnly ← runFixture "tests/prim_graph_pre.ndjson" { noGeneration with basic := true }
  state := state.check "basic selects input Nonempty"
    ((generatedNames basicOnly).contains `Nonempty)
  state := state.check "basic excludes ordinary Ac"
    (!(generatedNames basicOnly).contains `Ac)
  let simpleOnly ← runFixture "tests/prim_graph_pre.ndjson" { noGeneration with simple := true }
  state := state.check "simple selects ordinary Ac" ((generatedNames simpleOnly).contains `Ac)
  state := state.check "simple excludes input Nonempty"
    (!(generatedNames simpleOnly).contains `Nonempty)

  -- The graph arm splices Nonempty. It is present in both outputs, but only
  -- the basic closure recursively models it.
  let graphSimple ← runFixture "tests/prim_graph.ndjson" { noGeneration with simple := true }
  state := state.check "simple alone leaves spliced Nonempty unmodelled"
    (!(generatedNames graphSimple).contains `Nonempty &&
      graphSimple.spliced.any fun (_, names) => names.contains `Nonempty)
  let graphClosed ← runFixture "tests/prim_graph.ndjson"
    { noGeneration with simple := true, basic := true }
  state := state.check "basic closes a simple model's spliced Nonempty"
    ((generatedNames graphClosed).contains `Nonempty)

  -- Arm C marks its spliced skeleton as `Iso.requires`. Without basic, the
  -- parent model remains valid and is not withdrawn merely because the
  -- skeleton itself has no model.
  let carveSimple ← runFixture "tests/prim_carve.ndjson" { noGeneration with simple := true }
  state := state.check "simple without basic keeps the arm-C parent"
    ((generatedNames carveSimple).contains `Bif)
  state := state.check "simple without basic leaves the required skeleton unmodelled"
    (!(generatedNames carveSimple).contains `Bif._model.skel &&
      carveSimple.spliced.any fun (_, names) => names.contains `Bif._model.skel)

  -- Nested, mutual and simple are separate stages. A later stage cannot fire
  -- when the stage producing its input is disabled.
  let nestedOnly ← runFixture "tests/nested_iota.ndjson" { noGeneration with nested := true }
  state := state.check "nested models the input" ((generatedNames nestedOnly).contains `Tree)
  state := state.check "nested alone does not model its mutual output"
    (!hasGeneratedSuffix nestedOnly "._model.0")

  let nestedMutual ← runFixture "tests/nested_iota.ndjson"
    { noGeneration with nested := true, mutualModels := true }
  state := state.check "mutual models the nested model"
    (hasGeneratedSuffix nestedMutual "._model.0")
  state := state.check "mutual without simple leaves tag and aux unmodelled"
    (!hasGeneratedSuffix nestedMutual "._model.tag" &&
      !hasGeneratedSuffix nestedMutual "._model.aux")

  let nestedSimpleWithoutMutual ← runFixture "tests/nested_iota.ndjson"
    { noGeneration with nested := true, simple := true }
  state := state.check "simple cannot skip the disabled mutual stage"
    (!hasGeneratedSuffix nestedSimpleWithoutMutual "._model.tag" &&
      !hasGeneratedSuffix nestedSimpleWithoutMutual "._model.aux")

  let nestedThroughSimple ← runFixture "tests/nested_iota.ndjson"
    { noGeneration with nested := true, mutualModels := true, simple := true }
  state := state.check "simple models mutual tag output"
    (hasGeneratedSuffix nestedThroughSimple "._model.tag")
  state := state.check "simple models mutual aux output"
    (hasGeneratedSuffix nestedThroughSimple "._model.aux")

  -- A plain mutual input is independently controlled by `mutualModels`.
  let mutualOff ← runFixture "tests/mutual_nonrec.ndjson" { noGeneration with simple := true }
  state := state.check "simple does not model a disabled mutual input"
    (!(generatedNames mutualOff).contains `OA)
  let mutualOnly ← runFixture "tests/mutual_nonrec.ndjson"
    { noGeneration with mutualModels := true }
  state := state.check "mutual models a plain mutual input"
    ((generatedNames mutualOnly).contains `OA)
  state := state.check "plain mutual alone leaves tag and aux unmodelled"
    (!hasGeneratedSuffix mutualOnly "._model.tag" && !hasGeneratedSuffix mutualOnly "._model.aux")
  let mutualSimple ← runFixture "tests/mutual_nonrec.ndjson"
    { noGeneration with mutualModels := true, simple := true }
  state := state.check "simple composes over a plain mutual model"
    (hasGeneratedSuffix mutualSimple "._model.tag" &&
      hasGeneratedSuffix mutualSimple "._model.aux")

  IO.println s!"generation flags: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1
