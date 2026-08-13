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

structure FilterRun where
  input : Export
  output : Export
  report : Report
  env : Environment

structure StagedFilterRun extends FilterRun where
  plan : StagedPlan
  planValid : Bool
  malformedPlansRejected : Bool

structure DroppedFilterRun where
  report : Report
  plan : StagedPlan
  planValid : Bool

def cursorAfter (records : Array EDecl) : Writer.Cursor :=
  let writer := records.foldl (fun writer record => (writer.splitDecl record).1) (Writer.fromCursor {})
  writer.cursor

def syntheticCertificate (cursor : Writer.Cursor) (count : Nat) : RawCertificate :=
  let rawCursor : RawArenaCursor :=
    { nextName := cursor.nextName, nextLevel := cursor.nextLevel,
      nextExpr := cursor.nextExpr }
  { cursor := rawCursor
    declarationBytes := count.toUInt64
    declarations := (Array.range count).map fun ordinal =>
      { offset := ordinal.toUInt64, bytes := 1 } }

def syntheticRawSizes (count : Nat) : RawSpoolSizes :=
  { metadata := 0, arena := 0, declarations := count.toUInt64 }

def runFilterState (input : Export) (generation : Modelgen.Cli.Config)
    (checkRecursors : Bool := false) : IO FilterRun := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<order-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((decls, report), finalState) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (runFilter input checkRecursors generation)) context { env }
  unless report.stmtErrors.isEmpty do
    throw <| IO.userError s!"generated statements differ: {report.stmtErrors}"
  return { input, output := { input with decls }, report, env := finalState.env }

def runFilterStagedState (scratch : String) (input : Export)
    (generation : Modelgen.Cli.Config) (checkRecursors : Bool := false) : IO StagedFilterRun :=
  Spool.withWorkspace scratch fun workspace => do
    let stage ← Spool.IslandStage.create workspace (cursorAfter input.decls)
    let env ← importModules #[] {}
    let context : Core.Context :=
      { fileName := "<order-staged-test>", fileMap := default,
        maxHeartbeats := 0, maxRecDepth := 8192 }
    let ((decls, report, plan), finalState) ← Lean.Core.CoreM.toIO
      (Lean.Meta.MetaM.run'
        (runFilterWithIslandSink input checkRecursors generation (.ofStage stage))) context { env }
    let sealed ← stage.finish
    unless sealed.cursor == (← stage.cursor) do
      throw <| IO.userError "sealed staged cursor changed after finish"
    let certificate := syntheticCertificate (cursorAfter input.decls) input.decls.size
    let sourceSizes := syntheticRawSizes input.decls.size
    let planValid := match plan.declarationSpans certificate sourceSizes input.decls.size sealed with
      | .ok spans => spans.size == plan.declarations.size
      | .error _ => false
    let duplicateDeclarations := if plan.declarations.size < 2 then plan.declarations.push (.source 0)
      else plan.declarations.set! 1 plan.declarations[0]!
    let duplicateRejected := if plan.declarations.isEmpty then true else
      match { plan with declarations := duplicateDeclarations }.declarationSpans certificate sourceSizes
          input.decls.size sealed with
      | .ok _ => false
      | .error _ => true
    let badCursor : Writer.Cursor :=
      { sealed.cursor with nextExpr := sealed.cursor.nextExpr + 1 }
    let cursorRejected :=
      match plan.declarationSpans certificate sourceSizes input.decls.size
          { sealed with cursor := badCursor } with
      | .ok _ => false
      | .error _ => true
    let sourceCountRejected :=
      match plan.declarationSpans certificate sourceSizes (input.decls.size + 1) sealed with
      | .ok _ => false
      | .error _ => true
    return {
      input, output := { input with decls }, report, env := finalState.env,
      plan, planValid,
      malformedPlansRejected := duplicateRejected && cursorRejected && sourceCountRejected }

def runFilterDroppedState (scratch : String) (input : Export)
    (generation : Modelgen.Cli.Config) (checkRecursors : Bool := false) : IO DroppedFilterRun :=
  Spool.withWorkspace scratch fun workspace => do
    let stage ← Spool.IslandStage.create workspace (cursorAfter input.decls)
    let env ← importModules #[] {}
    let context : Core.Context :=
      { fileName := "<order-dropped-test>", fileMap := default,
        maxHeartbeats := 0, maxRecDepth := 8192 }
    let ((report, plan), _) ← Lean.Core.CoreM.toIO
      (Lean.Meta.MetaM.run'
        (runFilterStaged input checkRecursors generation (.ofStage stage))) context { env }
    let sealed ← stage.finish
    let certificate := syntheticCertificate (cursorAfter input.decls) input.decls.size
    let planValid := match plan.declarationSpans certificate
        (syntheticRawSizes input.decls.size) input.decls.size sealed with
      | .ok spans => spans.size == plan.declarations.size
      | .error _ => false
    return { report, plan, planValid }

def generatedFixtureState (path : String) (generation : Modelgen.Cli.Config) :
    IO FilterRun := do
  let text ← IO.FS.readFile path
  let .ok parsed := Modelgen.parse text (analyse := false)
    | throw <| IO.userError s!"cannot parse {path}"
  runFilterState parsed generation

def generatedFixture (path : String) (generation : Modelgen.Cli.Config) : IO Export := do
  return (← generatedFixtureState path generation).output

def mapConstructor (input : Export) (target : Name) (f : ECtor → ECtor) : Export :=
  { input with decls := input.decls.map fun declaration => match declaration with
    | .induct types constructors recursors =>
      .induct types (constructors.map fun constructor =>
        if constructor.name == target then f constructor else constructor) recursors
    | other => other }

def ownerDependentRecordIsRejected : IO Bool := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<owner-free-check-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let action : MetaM Bool := do
    let owner := axDecl `ForkOwner
    let dependent := axDecl `ForkOwner._model
      (.forallE `x (.const `ForkOwner []) (.sort (.succ .zero)) .default)
    let rejected ← checkGeneratedIn env #[dependent]
    let some ownerDeclaration := toDeclaration env owner | return false
    let ownerEnv ← match env.addDeclCore 0 ownerDeclaration none true with
      | .ok result => pure result
      | .error _ => return false
    let accepted ← checkGeneratedIn ownerEnv #[dependent]
    let rejectedWithoutOwner := match rejected with | .error _ => true | .ok _ => false
    let acceptedWithOwner := match accepted with | .ok _ => true | .error _ => false
    return rejectedWithoutOwner && acceptedWithOwner
  let (result, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' action) context { env }
  return result

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

/-- The exact-sort proposition-lift support used by the current basis. Kept
separate from the stable Eq/Nat/pair roots so a basis migration changes one
assertion rather than weakening the final-environment census. -/
def currentLiftSupportRoots : Array Name := #[`PUnit]

/-- Names added to the serialized output by one filter run, excluding every
name owned by the input. -/
def emittedNames (run : FilterRun) : Array Name :=
  let inputNames := run.input.decls.flatMap fun declaration => declaration.names.toArray
  run.output.decls.flatMap fun declaration =>
    declaration.names.toArray |>.filter (!inputNames.contains ·)

/-- Emitted records both witnessed as splices and classified as fixed reusable
support. Persistence is a record-level decision: an inductive record rooted at
`Nonempty`, for example, also installs `Nonempty.intro` and `Nonempty.rec`, even
though those two names are not independently support roots. -/
def witnessedFixedSupportRecords (run : FilterRun) : Array EDecl :=
  let witnessed := run.report.spliced.flatMap (·.2)
  run.output.decls.filter (fun declaration =>
      declaration.names.any witnessed.contains &&
        (declaration.names.any persistentSupportRoot ||
          declaration.names.all persistentSupportName ||
          -- One kernel `quotDecl` is four exact export records. Replaying the
          -- witnessed `Quot` record atomically installs the other three, so the
          -- census must classify the complete checked bundle as fixed even
          -- though only its first record independently names a support root.
          (witnessed.contains `Quot && match declaration with
            | .quot name .. => [`Quot, `Quot.mk, `Quot.lift, `Quot.ind].contains name
            | _ => false)))

def witnessedFixedSupportNames (run : FilterRun) : Array Name :=
  (witnessedFixedSupportRecords run).flatMap fun declaration => declaration.names.toArray

structure IsolationCensus where
  generatedOwners : Array Name
  generatedPublicNames : Array Name
  witnessedSplices : Array Name
  fixedSupport : Array Name
  localSplices : Array Name
  retainedEmitted : Array Name
  retainedPublic : Array Name
  retainedUnexpected : Array Name
  missingFixed : Array Name
  deriving Repr

/-- Exact name census for the disposable-environment boundary. The local/fixed
split follows whole serialized records, matching [`installGeneratedSupportIn`]
rather than classifying constructor and recursor names in isolation. -/
def isolationCensus (run : FilterRun) : IsolationCensus :=
  let generatedOwners := run.report.generated.map (·.1)
  let generatedPublicNames := generatedOwners.map Naming.modelName
  let witnessedSplices := run.report.spliced.flatMap (·.2)
  let fixedSupport := witnessedFixedSupportNames run
  let localSplices := witnessedSplices.filter (!fixedSupport.contains ·)
  let retainedEmitted := (emittedNames run).filter run.env.constants.contains
  { generatedOwners, generatedPublicNames, witnessedSplices, fixedSupport, localSplices,
    retainedEmitted,
    retainedPublic := generatedPublicNames.filter run.env.constants.contains,
    retainedUnexpected := retainedEmitted.filter (!fixedSupport.contains ·),
    missingFixed := fixedSupport.filter (!run.env.constants.contains ·) }

/-- Every emitted name retained by the final replay environment is fixed,
witnessed shared support, and every such support name was retained. Public
interfaces and model-local implementation declarations therefore remain in
the output only. -/
def finalEnvironmentIsIsolated (run : FilterRun) : Bool :=
  let census := isolationCensus run
  census.retainedPublic.isEmpty && census.retainedUnexpected.isEmpty &&
    census.missingFixed.isEmpty

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
  -- The quotient's kernel declaration itself depends on exact `Eq` support.
  let empty ← mkEmptyEnvironment
  let .ok quotientBase := empty.addDeclCore 0 eqDecl none true
    | throw <| IO.userError "the kernel rejected exact Eq support"
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

  -- Enabling the nested and mutual branches does not make their fixed support
  -- relevant when the file contains only a simple owner.  In that case the
  -- source remains under ordinary stable dependency ordering.  Once a plain
  -- mutual owner is present, the same support class still hoists atomically.
  let nestedMutualOnly := { noGeneration with nested := true, mutualModels := true }
  let unrelatedSupport := exportOf
    #[inductiveRecord [`UnselectedSimple], axDecl `Eq, axDecl `PUnit]
  state := state.check "support scheduler leaves unrelated records unchanged" <|
    match scheduleSource unrelatedSupport nestedMutualOnly with
    | .ok scheduled => scheduled.decls == unrelatedSupport.decls
    | .error _ => false
  let selectedOwner := inductiveRecord [`SelectedA, `SelectedB]
  let selectedSupport := exportOf #[selectedOwner, axDecl `Eq, axDecl `PUnit]
  state := state.check "support scheduler retains the atomic fixed-support hoist" <|
    match scheduleSource selectedSupport nestedMutualOnly with
    | .ok scheduled => scheduled.decls == #[axDecl `Eq, axDecl `PUnit, selectedOwner]
    | .error _ => false
  let derivedFalse := inductiveRecord [`False]
  let falseBeforeBasis := exportOf #[derivedFalse, selectedOwner, axDecl `Nat, axDecl `Eq]
  state := state.check "fixed basis hoists before derived False" <|
    match scheduleSource falseBeforeBasis { nestedMutualOnly with simple := true } with
    | .ok scheduled =>
        scheduled.decls == #[axDecl `Nat, axDecl `Eq, derivedFalse, selectedOwner]
    | .error _ => false
  let alreadyModeled := exportOf
    #[axDecl (Naming.modelName `SelectedA), selectedOwner, axDecl `Eq, axDecl `PUnit]
  state := state.check "support scheduler leaves an already-modeled export unchanged" <|
    match scheduleSource alreadyModeled nestedMutualOnly with
    | .ok scheduled => scheduled.decls == alreadyModeled.decls
    | .error _ => false

  -- Hoisting a fixed support record hoists its complete predecessor closure,
  -- not merely the named record. Otherwise the persistent replay environment
  -- would receive a support declaration before one of its own dependencies.
  let supportDependency := axDecl `SupportDependency
  let support := axDecl `PSigma' (.const `SupportDependency [])
  let ordinary := axDecl `Ordinary
  let hoisted ← match Order.reorderPrioritizing
      (exportOf #[ordinary, support, supportDependency])
      (fun declaration => declaration.names.contains `PSigma') with
    | .ok result => pure result
    | .error error => throw <| IO.userError s!"support hoist failed: {repr error}"
  state := state.check "shared support hoists with a valid dependency closure" <|
    hoisted.decls == #[supportDependency, support, ordinary] && dependenciesForward hoisted

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

  state := state.check "exact serialized owner reference is rejected owner-free"
    (← ownerDependentRecordIsRejected)

  -- With generation disabled, scheduling has no preferred class. The filter
  -- is byte/order neutral even when the original order is not alphabetical.
  let neutralOwner := inductiveRecord [`NeutralOwner]
  let neutralDependent := axDecl `NeutralDependent (.const `NeutralOwner [])
  let neutralInput := exportOf #[axDecl `NeutralB, neutralOwner,
    neutralDependent, axDecl `NeutralA]
  let neutral ← runFilterState neutralInput noGeneration true
  state := state.check "no-generation preserves exact records and rendering" <|
    neutral.output.decls == neutralInput.decls && neutral.output.render == neutralInput.render &&
      neutral.report.generated.isEmpty && neutral.report.spliced.isEmpty &&
      neutral.report.maxLivePendingModels == 0 && neutral.report.maxLiveIslandRecords == 0 &&
      neutral.env.constants.contains `NeutralOwner &&
      neutral.env.constants.contains `NeutralDependent
  let neutralShadow ← runFilterStagedState s!"{root}/_tmp" neutralInput noGeneration true
  let neutralDropped ← runFilterDroppedState s!"{root}/_tmp" neutralInput noGeneration true
  state := state.check "empty generation skips physical islands in every filter path" <|
    neutralShadow.output.decls == neutralInput.decls && neutralShadow.report == neutral.report &&
      neutralDropped.report == neutral.report && neutralShadow.plan.islands.isEmpty &&
      neutralDropped.plan.islands.isEmpty && neutralShadow.planValid && neutralDropped.planValid &&
      neutralShadow.plan.declarations.size == neutralInput.decls.size &&
      neutralDropped.plan.declarations == neutralShadow.plan.declarations &&
      neutralShadow.env.constants.contains `NeutralOwner &&
      neutralShadow.env.constants.contains `NeutralDependent

  -- This real mutual output has three members, unequal constructor counts,
  -- parameters and levels. Discovery must use each declaration's exact name,
  -- and a stable reorder must retain all ordinary implementation dependencies.
  let generatedMutualRun ← generatedFixtureState
    s!"{root}/test/fixtures/modelgen/mutual_shapes.ndjson"
    { noGeneration with mutualModels := true }
  let generatedMutual := generatedMutualRun.output
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
  state := state.check "plain mutual models are absent from the final replay environment" <|
    finalEnvironmentIsIsolated generatedMutualRun

  -- Nested-only generation already emits its family before the owner.  A
  -- stable pass is record-neutral when every dependency is already forward.
  let nestedRun ← generatedFixtureState s!"{root}/test/fixtures/modelgen/nested_iota.ndjson"
    { noGeneration with nested := true }
  let nested := nestedRun.output
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
  state := state.check "nested-only models are absent from the final replay environment" <|
    finalEnvironmentIsIsolated nestedRun
  let futureModelProbe : EDecl :=
    .ax `CompactFallbackProbe [] (.const (Naming.modelName `Tree) []) false
  let futureModelInput := { nestedRun.input with
    decls := #[futureModelProbe] ++ nestedRun.input.decls }
  let futureModelDropped ← runFilterDroppedState s!"{root}/_tmp" futureModelInput
    { noGeneration with nested := true }
  state := state.check "later generated provider marks compact staging unavailable" <|
    futureModelDropped.plan.unavailable?.isSome

  -- The default pipeline extends the same island through the generated nested
  -- block's mutual model and then through each simple model. None of those
  -- intermediate owners or their interfaces may escape into the source replay
  -- environment, even though all remain in the serialized output.
  let composedRun ← generatedFixtureState
    s!"{root}/test/fixtures/modelgen/nested_iota.ndjson" {}
  let nestedImpl := Name.num `Tree._model._impl 0
  let composedCensus := isolationCensus composedRun
  state := state.check
      s!"nested-mutual-simple composition remains one disposable island: {repr composedCensus}" <|
    composedRun.report.generated.any (·.1 == `Tree) &&
      composedRun.report.generated.any (·.1 == nestedImpl) &&
      (emittedNames composedRun).contains nestedImpl &&
      !composedRun.env.constants.contains nestedImpl &&
      finalEnvironmentIsIsolated composedRun

  let simpleRun ← generatedFixtureState
    s!"{root}/test/fixtures/modelgen/prim_shapes.ndjson"
    { noGeneration with simple := true }
  let simple := simpleRun.output
  let simple' ← mustReorder "simple declaration-local output" simple
  state := state.check "complete simple output checks literally" <|
    (Check.check simple').isEmpty
  state := state.check "replay environment retains source and shared support only" <|
    simpleRun.env.constants.contains `Tri &&
      !simpleRun.env.constants.contains (Naming.modelName `Tri) &&
      [`Eq, `Nat, `PSigma'].all simpleRun.env.constants.contains &&
      !simpleRun.env.constants.contains `PSigma &&
      currentLiftSupportRoots.all simpleRun.env.constants.contains &&
      !simpleRun.env.constants.contains `PULiftP &&
      !simple.decls.any fun declaration =>
        declaration.names.contains `PULiftP ||
          (Order.references declaration).contains `PULiftP
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

  -- Run the legacy full-output oracle, the shadow sink, and the AST-dropping
  -- sink across each generation route. Recursor checking is enabled on the
  -- composed case so its report fields are part of the exact comparison too.
  let stagedMatrix : Array (String × String × Modelgen.Cli.Config × Bool) := #[
    ("nested", "nested_iota.ndjson", { noGeneration with nested := true }, false),
    ("mutual", "mutual_shapes.ndjson", { noGeneration with mutualModels := true }, false),
    ("simple", "prim_shapes.ndjson", { noGeneration with simple := true }, false),
    ("composed", "nested_iota.ndjson", {}, true),
    ("late support", "prim_late_basis.ndjson", {}, false)]
  for (label, fixture, generation, checkRecursors) in stagedMatrix do
    let fixturePath := s!"{root}/test/fixtures/modelgen/{fixture}"
    let text ← IO.FS.readFile fixturePath
    let .ok input := Modelgen.parse text (analyse := false) | do
      state := state.check s!"staged {label} fixture parses" false
      continue
    let legacy ← runFilterState input generation checkRecursors
    let shadow ← runFilterStagedState s!"{root}/_tmp" input generation checkRecursors
    let dropped ← runFilterDroppedState s!"{root}/_tmp" input generation checkRecursors
    state := state.check s!"staged {label} shadow equals legacy" <|
      shadow.output.decls == legacy.output.decls && shadow.report == legacy.report &&
        shadow.plan.checkReport == Check.checkReport shadow.output && shadow.planValid
    state := state.check s!"staged {label} drop equals shadow" <|
      dropped.report == shadow.report && dropped.planValid &&
        dropped.plan.checkReport == shadow.plan.checkReport &&
        dropped.plan.declarations == shadow.plan.declarations &&
        dropped.plan.islands == shadow.plan.islands

  -- A malformed later inductive rejects after earlier owners may already have
  -- committed physical islands. The report/output verdict must still agree;
  -- the deliberately empty returned plan is noncomposable with that tail.
  let lateMalformed := mapConstructor nestedRun.input `PT.node fun constructor =>
    { constructor with type := .sort .zero }
  let malformedLegacy ← runFilterState lateMalformed {}
  let malformedShadow ← runFilterStagedState s!"{root}/_tmp" lateMalformed {}
  let malformedDropped ← runFilterDroppedState s!"{root}/_tmp" lateMalformed {}
  state := state.check "late unreplayable staged verdict equals legacy" <|
    malformedLegacy.report.unreplayable.isSome &&
      malformedShadow.output.decls == malformedLegacy.output.decls &&
      malformedShadow.report == malformedLegacy.report &&
      malformedDropped.report == malformedLegacy.report &&
      malformedShadow.plan.declarations.isEmpty && malformedDropped.plan.declarations.isEmpty &&
      !malformedShadow.planValid && !malformedDropped.planValid

  -- The small alias fixture exercises both a model-local arm-C skeleton and
  -- fixed shared graph support. Every generated declaration that survives in
  -- the replay environment must be explicitly witnessed as spliced and have
  -- a fixed support name; public interfaces and local implementation support
  -- are absent even though they remain in the emitted export.
  let aliasRun ← generatedFixtureState
    s!"{root}/test/fixtures/modelgen/transparent_owner_aliases.ndjson" {}
  let aliasStaged ← runFilterStagedState s!"{root}/_tmp" aliasRun.input {}
  let aliasDropped ← runFilterDroppedState s!"{root}/_tmp" aliasRun.input {}
  let stagedGeneratedRecords := aliasStaged.plan.declarations.foldl (init := 0) fun count locator =>
    match locator with
    | .generated .. => count + 1
    | .source _ => count
  let stagedCommittedRecords := aliasStaged.plan.islands.foldl (init := 0) fun count island =>
    count + island.declarations.size
  state := state.check "staged island sink preserves exact output and report" <|
    aliasStaged.output.decls == aliasRun.output.decls &&
      aliasStaged.report == aliasRun.report &&
      aliasStaged.plan.checkReport == Check.checkReport aliasStaged.output &&
      aliasStaged.plan.declarations.size == aliasStaged.output.decls.size &&
      aliasStaged.planValid && aliasStaged.malformedPlansRejected &&
      stagedCommittedRecords == stagedGeneratedRecords &&
      aliasStaged.plan.islands.all fun island => !island.declarations.isEmpty
  state := state.check "AST-dropping staged path preserves report and compact schedule" <|
    aliasDropped.report == aliasRun.report &&
      aliasDropped.plan.checkReport == aliasStaged.plan.checkReport &&
      aliasDropped.planValid &&
      aliasDropped.plan.declarations == aliasStaged.plan.declarations &&
      aliasDropped.plan.islands == aliasStaged.plan.islands
  let inputNames := aliasRun.input.decls.flatMap fun declaration => declaration.names.toArray
  let generatedNames := aliasRun.output.decls.flatMap fun declaration =>
    declaration.names.toArray |>.filter (!inputNames.contains ·)
  let witnessed := aliasRun.report.spliced.flatMap (·.2)
  let fixedWitnessedNames := aliasRun.output.decls.filter (fun declaration =>
      declaration.names.any witnessed.contains &&
        (declaration.names.any persistentSupportRoot ||
          declaration.names.all persistentSupportName)) |>.flatMap fun declaration =>
            declaration.names.toArray
  let retainedGenerated := generatedNames.filter aliasRun.env.constants.contains
  let localWitnessedNames := witnessed.filter (!fixedWitnessedNames.contains ·)
  let aliasCensus := isolationCensus aliasRun
  state := state.check
      s!"model-local names are disposed after each owner island: {repr aliasCensus}" <|
    aliasRun.report.generated.all (fun entry =>
      !aliasRun.env.constants.contains (Naming.modelName entry.1)) &&
      !aliasRun.env.constants.contains `AliasI._model._impl.skel &&
      generatedNames.contains `AliasI._model._impl.skel &&
      (localWitnessedNames.all fun name =>
        !aliasRun.env.constants.contains name) &&
      retainedGenerated.all fixedWitnessedNames.contains &&
      fixedWitnessedNames.all retainedGenerated.contains
  state := state.check "every witnessed fixed support declaration persists" <|
    !fixedWitnessedNames.isEmpty && fixedWitnessedNames.all aliasRun.env.constants.contains

  -- A W model has the largest fixed splice: the reusable `_wcore` fragment.
  -- The core survives for later source owners, while the public W model and its
  -- per-owner implementation forest remain confined to this island.
  let wRun ← generatedFixtureState s!"{root}/test/fixtures/modelgen/prim_w.ndjson"
    { noGeneration with simple := true }
  let wCensus := isolationCensus wRun
  state := state.check
      s!"W core support persists without retaining its model island: {repr wCensus}" <|
    wRun.report.generated.any (·.1 == `Tree) &&
      wRun.report.spliced.any (fun (_, names) => names.contains wCoreSelf) &&
      wRun.env.constants.contains wCoreSelf &&
      !wRun.env.constants.contains (Naming.modelName `Tree) &&
      finalEnvironmentIsIsolated wRun

  -- Scheduling moves the input's exact PUnit bundle before the owner that
  -- needs it. It is source state, not a generated splice, and remains present
  -- after the owner's generated interface has been discarded.
  let latePUnitRun ← generatedFixtureState
    s!"{root}/test/fixtures/modelgen/tight_prop_field_late.ndjson"
    { noGeneration with simple := true }
  state := state.check "late input PUnit survives scheduled owner-free generation" <|
    latePUnitRun.report.generated.any (·.1 == `PFP) &&
      !latePUnitRun.report.spliced.any (fun (_, names) => names.contains `PUnit) &&
      latePUnitRun.env.constants.contains `PUnit &&
      latePUnitRun.env.constants.contains `PFP &&
      !latePUnitRun.env.constants.contains (Naming.modelName `PFP) &&
      finalEnvironmentIsIsolated latePUnitRun

  IO.println s!"record order: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1

end Modelgen.Order.Tests

def main (args : List String) : IO UInt32 :=
  Modelgen.Order.Tests.run (args.head?.getD ".")
