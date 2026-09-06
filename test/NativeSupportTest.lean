import InductiveModels.Main

/-!
# Native support

A consumer that handles some inductive types itself asks for no models of
them through [`InductiveModels.NativeSupport`]. The predicate is put to every
block before a construction is chosen — input blocks and the blocks a model
introduces alike — so the selector below, "a structure with no indices and no
recursion", must catch the input's `Dep` and `SortFields`, the `PProd'` that
`SortFields`'s model splices, and the index-erasure skeleton the carve arm
splices for `Indexed`. The last one is the sharp case: the carve arm withdraws
a model whose skeleton did not model, and a native skeleton has to count as
closed.
-/

namespace NativeSupportTest

open Lean Meta InductiveModels

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

/-- One member, no indices, no recursion, no nesting, one constructor: what a
checker that supports "structures" natively means by the word. -/
def plain : NativeSupport := fun block =>
  match block with
  | .induct [type] ctors _ =>
    type.numIndices == 0 && !type.isRec && type.numNested == 0 && ctors.length == 1
  | _ => false

def fixture := "test/fixtures/inductive-models/structure_projections.ndjson"

def readFixture (path : String) : IO Export := do
  let text ← IO.FS.readFile path
  let .ok parsed := InductiveModels.parse text
    | throw <| IO.userError s!"cannot parse {path}"
  return parsed

def runExport (parsed : Export) (native : NativeSupport) :
    IO (Array EDecl × InductiveModels.Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<native-support-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (runFilter parsed false {} native)) context { env }
  return result

def generatedNames (report : InductiveModels.Report) : Array Name :=
  report.generated.map (·.1)

def outputNames (decls : Array EDecl) : Array Name :=
  decls.flatMap fun decl => decl.names.toArray

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut state : TestState := {}
  let parsed ← readFixture fixture

  -- The default asks for nothing beyond the basis: the run is the run it was.
  let (_, unclaimed) ← runExport parsed NativeSupport.none
  state := state.check "default: no native row" unclaimed.native.isEmpty
  state := state.check "default: Dep and PProd' are modelled"
    ((generatedNames unclaimed).contains `Dep && (generatedNames unclaimed).contains `PProd')

  -- Plain structures are left to the consumer, wherever they came from.
  let (decls, report) ← runExport parsed plain
  let generated := generatedNames report
  let output := outputNames decls
  for name in [`Dep, `SortFields, `PProd', `Indexed._model._impl.skel,
      `IndexedDep._model._impl.skel] do
    state := state.check s!"plain: {name} is native" (report.native.contains name)
    state := state.check s!"plain: {name} has no model" (!generated.contains name)
    state := state.check s!"plain: {name} is emitted as it stands" (output.contains name)
    state := state.check s!"plain: no {name}._model in the output"
      (!output.contains (Naming.modelName name))
  -- The consumers of what went native still model: `SortFields` spliced
  -- `PProd'`, `Indexed` requires its skeleton.
  for name in [`Indexed, `IndexedDep, `Recursive, `Ix, `Maybe] do
    state := state.check s!"plain: {name} still models" (generated.contains name)
  state := state.check "plain: nothing declined" report.declined.isEmpty
  state := state.check "plain: the basis row is the basis row"
    (report.exempt.map (·.1) == #[`Eq])
  state := state.check "plain: generated islands pass the kernel"
    report.generatedKernelRejected.isNone
  state := state.check "plain: statements literal" report.stmtErrors.isEmpty

  -- Everything native: the output is the input, and the basis is still
  -- reported as the basis.
  let (allDecls, all) ← runExport parsed fun _ => true
  state := state.check "all: nothing generated" all.generated.isEmpty
  state := state.check "all: nothing declined" all.declined.isEmpty
  state := state.check "all: output is the input" (allDecls.size == parsed.decls.size)
  state := state.check "all: the basis row is the basis row" (all.exempt.map (·.1) == #[`Eq])

  -- The library entry, both output paths.
  let discard ← InductiveModels.main ["--no-output", "--quiet", fixture] plain
  state := state.check "main --no-output accepts" (discard == 0)
  let (_, tmp) ← IO.FS.createTempFile
  let stream ← InductiveModels.main ["-o", tmp.toString, "--quiet", fixture] plain
  state := state.check "main -o accepts" (stream == 0)
  let written ← readFixture tmp.toString
  IO.FS.removeFile tmp
  let writtenNames := outputNames written.decls
  state := state.check "main -o: PProd' emitted, Dep and PProd' unmodelled"
    (writtenNames.contains `PProd' && !writtenNames.contains (Naming.modelName `Dep) &&
      !writtenNames.contains (Naming.modelName `PProd'))
  state := state.check "main -o: Indexed modelled"
    (writtenNames.contains (Naming.modelName `Indexed))

  IO.println s!"native support: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1

end NativeSupportTest
