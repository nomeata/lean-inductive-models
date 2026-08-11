import Modelgen.Driver
import Modelgen.Order

/-!
# Focused tests for record-level model ordering

Run from the repository root with `lake exe ordertest [ROOT]`.
-/

open Lean Meta Modelgen

namespace Modelgen.Order.Tests

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def axDecl (name : Name) (type : Expr := .sort (.succ .zero)) : EDecl :=
  .ax name [] type false

def inductiveRecord (names : List Name) : EDecl :=
  .induct (names.map fun name => {
    name, levelParams := [], type := .sort (.succ .zero), all := names, ctors := []
    numParams := 0, numIndices := 0, numNested := 0, isRec := false
    isReflexive := false, isUnsafe := false }) [] []

def metadataRecord : EDecl :=
  .induct [{
    name := `MetaType, levelParams := [], type := .const `TypeDependency []
    all := [`AllDependency], ctors := [`CtorListDependency]
    numParams := 0, numIndices := 0, numNested := 0, isRec := false
    isReflexive := false, isUnsafe := false
  }] [{
    name := `MetaCtor, levelParams := [], type := .const `CtorTypeDependency []
    cidx := 0, numParams := 0, numFields := 0, induct := `InductDependency
    isUnsafe := false
  }] [{
    name := `MetaRec, levelParams := [], type := .const `RecTypeDependency []
    all := [`RecAllDependency], numParams := 0, numIndices := 0
    numMotives := 0, numMinors := 0
    rules := [{
      ctor := `RuleCtorDependency
      nfields := 0
      rhs := .const `RuleRhsDependency []
    }]
    k := false, isUnsafe := false
  }]

def exportOf (decls : Array EDecl) : Export := { metaLine := .null, decls }

def declarationIndex? (x : Export) (name : Name) : Option Nat :=
  x.decls.findIdx? fun declaration => declaration.names.contains name

def before (x : Export) (first second : Name) : Bool :=
  match declarationIndex? x first, declarationIndex? x second with
  | some i, some j => i < j
  | _, _ => false

def familiesBeforeOwners (x : Export) : Bool :=
  Check.discover x |>.all fun family => family.decls.all (· < family.ownerDecl)

def dependenciesForward (x : Export) : Bool := Id.run do
  let mut ownership : Std.HashMap Name Nat := {}
  for i in [0:x.decls.size] do
    for name in x.decls[i]!.names do ownership := ownership.insert name i
  for consumer in [0:x.decls.size] do
    for name in Order.references x.decls[consumer]! do
      if let some provider := ownership[name]? then
        unless provider == consumer || provider < consumer do return false
  return true

def mustReorder (label : String) (x : Export) : IO Export :=
  match Order.reorder x with
  | .ok reordered => return reordered
  | .error error => throw <| IO.userError s!"{label}: unexpected ordering error: {repr error}"

def generatedFixture (path : String) (generation : Modelgen.Cli.Config) : IO Export := do
  let text ← IO.FS.readFile path
  let .ok parsed := Modelgen.parse text (analyse := false)
    | throw <| IO.userError s!"cannot parse {path}"
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<order-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((decls, report), _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (runFilter parsed false generation)) context { env }
  unless report.stmtErrors.isEmpty do
    throw <| IO.userError s!"{path}: generated statements differ: {report.stmtErrors}"
  return { parsed with decls }

def noGeneration : Modelgen.Cli.Config :=
  { nested := false, mutualModels := false, simple := false, basic := false }

def run (root : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut state : TestState := {}

  -- Current simple output can be delayed until a late basis declaration.  The
  -- synthetic two-record form pins the same after-owner move without depending
  -- on any particular primitive construction.
  let simpleOwner := `Simple
  let simpleCarrier := `Simple._model.self
  let simple := exportOf #[inductiveRecord [simpleOwner], axDecl simpleCarrier]
  let simple' ← mustReorder "after-owner simple output" simple
  state := state.check "after-owner simple output reorders"
    (before simple' simpleCarrier simpleOwner && (Check.check simple').isEmpty)

  -- A mutual owner and its mutual model each remain one indivisible record.
  -- Both public families key the same model record to the same owner record.
  let mutualOwner := inductiveRecord [`MA, `MB]
  let mutualModel := inductiveRecord [`MA._model.self, `MB._model.self]
  let mutualExport := exportOf #[mutualOwner, mutualModel]
  let mutual' ← mustReorder "atomic mutual records" mutualExport
  state := state.check "atomic mutual records reorder"
    (mutual'.decls == #[mutualModel, mutualOwner] &&
      (Check.discover mutual').size == 2 && (Check.check mutual').isEmpty)

  -- `Expr.getUsedConstants` omits a projection's `typeName`.  This reference
  -- exists nowhere else, so only an explicit projection walk can order it.
  let projectionUser := axDecl `ProjectionUser (.proj `ProjectionProvider 0 (.bvar 0))
  let projectionProvider := axDecl `ProjectionProvider
  let projection' ← mustReorder "projection typeName dependency"
    (exportOf #[projectionUser, projectionProvider])
  state := state.check "projection typeName dependency"
    (projection'.decls == #[projectionProvider, projectionUser])

  let independent := axDecl `Independent
  let constantUser := axDecl `ConstantUser (.const `ConstantProvider [])
  let constantProvider := axDecl `ConstantProvider
  let stable' ← mustReorder "original-order tie break"
    (exportOf #[independent, constantUser, constantProvider])
  state := state.check "original order breaks ready-node ties"
    (stable'.decls == #[independent, constantProvider, constantUser])

  let metadataReferences := Order.references metadataRecord
  state := state.check "all inductive record reference fields are traversed" <|
    [`TypeDependency, `AllDependency, `CtorListDependency, `CtorTypeDependency,
      `InductDependency, `RecTypeDependency, `RecAllDependency,
      `RuleCtorDependency, `RuleRhsDependency].all metadataReferences.contains

  -- A model that refers to the owner produces owner→model from the ordinary
  -- dependency graph and model→owner from the ordering contract.
  let cyclic := exportOf #[inductiveRecord [`Cycle], axDecl `Cycle._model.self (.const `Cycle [])]
  state := state.check "model-owner backreference is an explicit cycle" <|
    match Order.recordOrder cyclic with
    | .error (.cycle records) => records == #[0, 1]
    | _ => false

  -- Duplicate ownership would make dependency targets ambiguous; reject it
  -- before constructing the graph.
  state := state.check "duplicate record ownership is explicit" <|
    match Order.recordOrder (exportOf #[axDecl `Duplicate, axDecl `Duplicate]) with
    | .error (.duplicateName name 0 1) => name == `Duplicate
    | _ => false

  -- This is the real late-basis shape: simple input `Pre` and simple models of
  -- the mutual model's generated tag/aux declarations are emitted only after
  -- the input's later `PSigma`.  The reorder must repair every discovered
  -- family simultaneously while retaining all ordinary dependencies.
  let late ← generatedFixture s!"{root}/tests/prim_late_basis.ndjson" {}
  let lateFamilies := Check.discover late
  let isLate := fun (family : Check.Family) =>
    family.decls.any (family.ownerDecl < ·)
  state := state.check "late-basis output delays simple input model"
    (lateFamilies.any fun family => family.owner == `Pre && isLate family)
  state := state.check "late-basis output delays a mutual-output model"
    (lateFamilies.any fun family => (`MA._model).isPrefixOf family.owner && isLate family)
  let late' ← mustReorder "late-basis output" late
  state := state.check "late-basis output reorders"
    (familiesBeforeOwners late' && (Check.check late').isEmpty &&
      dependenciesForward late' && late'.decls.size == late.decls.size)

  -- Nested-only generation already emits its family before the owner.  A
  -- stable pass is record-neutral when every dependency is already forward.
  let nested ← generatedFixture s!"{root}/tests/nested_iota.ndjson"
    { noGeneration with nested := true }
  let nested' ← mustReorder "already-before nested output" nested
  state := state.check "already-before nested output is unchanged"
    (nested'.decls == nested.decls && familiesBeforeOwners nested' &&
      dependenciesForward nested')

  IO.println s!"record order: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1

end Modelgen.Order.Tests

def main (args : List String) : IO UInt32 :=
  Modelgen.Order.Tests.run (args.head?.getD ".")
