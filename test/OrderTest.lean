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

def modelDef (name : Name) : EDecl :=
  .defn name [] (.sort (.succ .zero)) (.sort .zero) .opaque "safe" []

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

def declarationType? (x : Export) (name : Name) : Option Expr := do
  let declaration ← x.decls.find? (·.names.contains name)
  match declaration with
  | .ax got _ type _ | .quot got _ type _ => if got == name then some type else none
  | .defn got _ type .. | .thm got _ type .. | .opaq got _ type .. =>
      if got == name then some type else none
  | .induct types constructors recursors =>
      (types.find? (·.name == name)).map (·.type) <|>
      (constructors.find? (·.name == name)).map (·.type) <|>
      (recursors.find? (·.name == name)).map (·.type)

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

def generatedFixtureState (path : String) (generation : Modelgen.Cli.Config) :
    IO (Export × Environment) := do
  let text ← IO.FS.readFile path
  let .ok parsed := Modelgen.parse text (analyse := false)
    | throw <| IO.userError s!"cannot parse {path}"
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<order-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((decls, report), finalState) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (runFilter parsed false generation)) context { env }
  unless report.stmtErrors.isEmpty do
    throw <| IO.userError s!"{path}: generated statements differ: {report.stmtErrors}"
  return ({ parsed with decls }, finalState.env)

def generatedFixture (path : String) (generation : Modelgen.Cli.Config) : IO Export := do
  return (← generatedFixtureState path generation).1

def noGeneration : Modelgen.Cli.Config :=
  { nested := false, mutualModels := false, simple := false, basic := false }

def replayGeneratedIn (base : Environment) (records : Array EDecl) :
    IO (Except String Environment) := do
  let context : Core.Context :=
    { fileName := "<quotient-replay-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (checkGeneratedIn base records)) context { env := base }
  return result

def generatedReplayRejects (base : Environment) (records : Array EDecl) : IO Bool := do
  match ← replayGeneratedIn base records with
  | .error _ => return true
  | .ok _ => return false

def run (root : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut state : TestState := {}

  -- lean4export spells the kernel's one quotient declaration as exactly four
  -- consecutive records.  Replay must validate the bundle before the first
  -- record installs all four constants, or malformed first records and
  -- incomplete/reordered/duplicate bundles become indistinguishable from the
  -- three legitimate covered records.
  -- `importModules #[] {}` already contains Lean's ambient kernel quotient.
  -- Generated support is replayed only when its persistent source-prefix
  -- environment lacks that declaration, which `mkEmptyEnvironment` models.
  let quotientBase ← mkEmptyEnvironment
  let .ok quotientEnv := quotientBase.addDeclCore 0 .quotDecl none true
    | throw <| IO.userError "the kernel rejected its quotient declaration"
  let some quotientRecords := installedQuotRecords? quotientEnv
    | throw <| IO.userError "the kernel did not expose all four quotient records"
  let #[quot, mk, lift, ind] := quotientRecords
    | throw <| IO.userError "the kernel quotient did not have four export records"
  state := state.check "canonical quotient bundle replays exactly once" <|
    match ← replayGeneratedIn quotientBase quotientRecords with
    | .ok checked => installedQuotRecords? checked == some quotientRecords
    | .error _ => false
  let missingRejected ← generatedReplayRejects quotientBase #[quot, mk, lift]
  state := state.check "missing quotient record is rejected" missingRejected
  let reorderedRejected ← generatedReplayRejects quotientBase #[mk, quot, lift, ind]
  state := state.check "reordered quotient bundle is rejected" reorderedRejected
  let interleavedRejected ←
    generatedReplayRejects quotientBase #[quot, mk, axDecl `Between, lift, ind]
  state := state.check "interleaved quotient bundle is rejected" interleavedRejected
  let duplicateRejected ← generatedReplayRejects quotientBase #[quot, mk, lift, ind, ind]
  state := state.check "duplicate quotient record is rejected" duplicateRejected
  let duplicateBundleRejected ←
    generatedReplayRejects quotientBase (quotientRecords ++ quotientRecords)
  state := state.check "duplicate quotient bundle is rejected" duplicateBundleRejected
  let existingBundleRejected ← generatedReplayRejects quotientEnv quotientRecords
  state := state.check "quotient bundle cannot shadow an existing quotient" existingBundleRejected
  let .quot quotName quotParams quotType quotKind := quot
    | throw <| IO.userError "the first quotient record had the wrong constructor"
  let nameRejected ← generatedReplayRejects quotientBase
    #[.quot `NotQuot quotParams quotType quotKind, mk, lift, ind]
  state := state.check "malformed quotient name is rejected" nameRejected
  let levelsRejected ← generatedReplayRejects quotientBase
    #[.quot quotName [`wrong] quotType quotKind, mk, lift, ind]
  state := state.check "mismatched quotient levels are rejected" levelsRejected
  let typeRejected ← generatedReplayRejects quotientBase
    #[.quot quotName quotParams (.sort .zero) quotKind, mk, lift, ind]
  state := state.check "mismatched quotient type is rejected" typeRejected
  let kindRejected ← generatedReplayRejects quotientBase
    #[.quot quotName quotParams quotType (quotKind ++ "-wrong"), mk, lift, ind]
  state := state.check "mismatched quotient kind is rejected" kindRejected

  -- Current simple output can be delayed until a late basis declaration.  The
  -- synthetic two-record form pins the same after-owner move without depending
  -- on any particular primitive construction.
  let simpleOwner := `Simple
  let simpleCarrier := Naming.modelName simpleOwner
  let simple := exportOf #[inductiveRecord [simpleOwner], modelDef simpleCarrier]
  let simple' ← mustReorder "after-owner simple output" simple
  state := state.check "after-owner simple output reorders"
    (before simple' simpleCarrier simpleOwner && (Check.check simple').isEmpty)

  -- A mutual owner remains one indivisible record, while its public model
  -- interface is declaration-local: one definition per member rather than a
  -- second synthetic mutual group. Every interface record must move before
  -- the one atomic owner record.
  let mutualOwner := inductiveRecord [`MA, `MB]
  let mutualModelA := modelDef (Naming.modelName `MA)
  let mutualModelB := modelDef (Naming.modelName `MB)
  let mutualExport := exportOf #[mutualOwner, mutualModelA, mutualModelB]
  let mutual' ← mustReorder "atomic mutual records" mutualExport
  state := state.check "atomic mutual records reorder"
    (mutual'.decls == #[mutualModelA, mutualModelB, mutualOwner] &&
      (Check.discover mutual').size == 1 && (Check.check mutual').isEmpty)

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
  let cyclic := exportOf #[inductiveRecord [`Cycle],
    axDecl (Naming.modelName `Cycle) (.const `Cycle [])]
  state := state.check "model-owner backreference is an explicit cycle" <|
    match Order.recordOrder cyclic with
    | .error (.cycle records declarations) =>
      records == #[0, 1] && declarations == #[#[`Cycle], #[Naming.modelName `Cycle]]
    | _ => false

  -- Duplicate ownership would make dependency targets ambiguous; reject it
  -- before constructing the graph.
  state := state.check "duplicate record ownership is explicit" <|
    match Order.recordOrder (exportOf #[axDecl `Duplicate, axDecl `Duplicate]) with
    | .error (.duplicateName name 0 1) => name == `Duplicate
    | _ => false

  -- This real mutual output has three members, unequal constructor counts,
  -- parameters and levels. Discovery must use each declaration's exact name,
  -- and a stable reorder must retain all ordinary implementation dependencies.
  let generatedMutual ← generatedFixture s!"{root}/test/fixtures/modelgen/mutual_shapes.ndjson"
    { noGeneration with mutualModels := true }
  let generatedMutualFamilies := Check.discover generatedMutual
  state := state.check "generated mutual family has exact member names" <|
    generatedMutualFamilies.any fun family =>
      family.owner == `A && family.decls.all (· < family.ownerDecl) &&
        family.correspondence.typeFormers.any (fun pair =>
          pair.owner == `B && pair.model == Naming.modelName `B) &&
        family.correspondence.constructors.any (fun pair =>
          pair.owner == `C.cf && pair.model == Naming.modelName `C.cf) &&
        family.correspondence.recursors.any (fun pair =>
          pair.owner == `C.rec && pair.model == Naming.modelName `C.rec) &&
        family.correspondence.iotas.any (fun rule =>
          rule.recursor == `C.rec && rule.name == Naming.iotaName `C.rec 2)
  let generatedMutual' ← mustReorder "generated mutual output" generatedMutual
  state := state.check "generated mutual output reorders and checks"
    (familiesBeforeOwners generatedMutual' && (Check.check generatedMutual').isEmpty &&
      dependenciesForward generatedMutual' &&
      generatedMutual'.decls.size == generatedMutual.decls.size)

  -- Nested-only generation already emits its family before the owner.  A
  -- stable pass is record-neutral when every dependency is already forward.
  let nested ← generatedFixture s!"{root}/test/fixtures/modelgen/nested_iota.ndjson"
    { noGeneration with nested := true }
  let nested' ← mustReorder "already-before nested output" nested
  state := state.check "already-before nested output is unchanged"
    (nested'.decls == nested.decls && familiesBeforeOwners nested' &&
      dependenciesForward nested' && (Check.check nested').isEmpty)
  state := state.check "nested recursors and iotas use exact names" <|
    (Check.discover nested').any fun family =>
      family.owner == `Tree &&
        family.correspondence.recursors.any (fun pair =>
          pair.owner == `Tree.rec && pair.model == Naming.modelName `Tree.rec) &&
        family.correspondence.iotas.any (fun rule =>
          rule.recursor == `Tree.rec && rule.name == Naming.iotaName `Tree.rec 1)

  let (simple, simpleEnv) ← generatedFixtureState
    s!"{root}/test/fixtures/modelgen/prim_shapes.ndjson"
    { noGeneration with simple := true }
  let simple' ← mustReorder "simple declaration-local output" simple
  state := state.check "complete simple output checks literally" <|
    (Check.check simple').isEmpty
  state := state.check "replay environment retains source and shared support only" <|
    simpleEnv.constants.contains `Tri &&
      !simpleEnv.constants.contains (Naming.modelName `Tri) &&
      [`Eq, `Nat, `PSigma, `PSigma', `PUnit].all simpleEnv.constants.contains &&
        !simpleEnv.constants.contains `PULiftP
  let svType := declarationType? simple' `Sv
  let svModelType := declarationType? simple' (Naming.modelName `Sv)
  state := state.check "Sv model preserves its literal declared type" <|
    svModelType == svType && svModelType.any (fun type => type.getUsedConstants.contains `SvFam)
  let idxViolations := (Check.check simple').filter fun violation =>
    (`IdxP).isPrefixOf violation.familyOwner
  state := state.check "simple recursors and iotas check literally" <|
    familiesBeforeOwners simple' && dependenciesForward simple' &&
      idxViolations.isEmpty &&
      (Check.discover simple').any (fun family =>
        family.owner == `IdxP &&
          family.correspondence.recursors.any (fun pair =>
            pair.owner == `IdxP.rec && pair.model == Naming.modelName `IdxP.rec) &&
          family.correspondence.iotas.any (fun rule =>
            rule.recursor == `IdxP.rec && rule.name == Naming.iotaName `IdxP.rec 1))

  IO.println s!"record order: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1

end Modelgen.Order.Tests

def main (args : List String) : IO UInt32 :=
  Modelgen.Order.Tests.run (args.head?.getD ".")
