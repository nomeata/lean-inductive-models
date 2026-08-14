import InductiveModels.Driver
import InductiveModels.Order

set_option maxRecDepth 8192

/--
error: Unknown constant `InductiveModels.Spool.ParseTee.mk`
-/
#guard_msgs in
#check InductiveModels.Spool.ParseTee.mk

/--
error: Unknown constant `InductiveModels.Spool.PlannedSourceReader.mk`
-/
#guard_msgs in
#check InductiveModels.Spool.PlannedSourceReader.mk

/-!
# Focused tests for record-level model ordering

Run from the repository root with `lake exe ordertest [ROOT]`.
-/

open Lean Meta InductiveModels

namespace InductiveModels.Order.Tests

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

/-- Test-only source variant making a prerequisite-first positive case
explicit without changing production source order. -/
def withCompletePrerequisiteBefore (x : Export) (prerequisite owner : Name) : IO Export := do
  let prerequisiteIndices := (Array.range x.decls.size).filter fun index =>
    x.decls[index]!.names.contains prerequisite
  let ownerIndices := (Array.range x.decls.size).filter fun index =>
    x.decls[index]!.names.contains owner
  unless prerequisiteIndices.size == 1 do
    throw <| IO.userError s!"expected one complete {prerequisite} record, got {prerequisiteIndices}"
  unless ownerIndices.size == 1 do
    throw <| IO.userError s!"expected one complete {owner} record, got {ownerIndices}"
  let prerequisiteIndex := prerequisiteIndices[0]!
  let ownerIndex := ownerIndices[0]!
  if prerequisiteIndex < ownerIndex then return x
  let prerequisiteRecord := x.decls[prerequisiteIndex]!
  return { x with decls :=
    x.decls.extract 0 ownerIndex ++ #[prerequisiteRecord] ++
      x.decls.extract ownerIndex prerequisiteIndex ++
      x.decls.extract (prerequisiteIndex + 1) x.decls.size }

/-- No declaration-local model descendant of the complete source block was
emitted for a declined owner. -/
def noModeledBlockDescendants (input output : Export) (owner : Name) : Bool :=
  (input.decls.find? (·.names.contains owner)).any fun sourceBlock =>
    let roots := sourceBlock.names.toArray.map Naming.modelName
    output.decls.all fun declaration => declaration.names.all fun name =>
      roots.all fun root => !root.isPrefixOf name

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

def isExactRecordOrder (outcome : Except Order.Error (Array Nat))
    (expected : Array Nat) : Bool :=
  match outcome with
  | .ok order => order == expected
  | .error _ => false

def kernelAccepts (x : Export) : IO Bool := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<order-kernel-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (typeCheckExport x)) context { env }
  return result matches .ok ()

structure FilterRun where
  input : Export
  output : Export
  report : Report
  env : Environment

structure TracedFilterRun extends FilterRun where
  steps : Array FilterSourceStep

structure DiscardedFilterRun where
  report : Report
  plan : CompactPlan

structure StreamedFilterRun extends DiscardedFilterRun where
  output : Export

structure PlannedCensusFilterRun extends DiscardedFilterRun where
  input : PlannedSourceInput

def runFilterState (input : Export) (generation : InductiveModels.Cli.Config)
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

def runFilterTraceState (input : Export) (generation : InductiveModels.Cli.Config)
    (checkRecursors : Bool := false) : IO TracedFilterRun := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<order-trace-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((decls, report, steps), finalState) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run'
      (runFilterWithSourceTrace input checkRecursors generation)) context { env }
  unless report.stmtErrors.isEmpty do
    throw <| IO.userError s!"traced generated statements differ: {report.stmtErrors}"
  return { input, output := { input with decls }, report, env := finalState.env, steps }

def runFilterDiscardedState (input : Export)
    (generation : InductiveModels.Cli.Config) (checkRecursors : Bool := false) :
    IO DiscardedFilterRun := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<order-discarded-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((report, plan), _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run'
      (runFilterDiscarding input checkRecursors generation)) context { env }
  return { report, plan }

def runFilterStreamedState (input : Export)
    (generation : InductiveModels.Cli.Config) (checkRecursors : Bool := false) :
    IO StreamedFilterRun := do
  let collected ← IO.mkRef (#[] : Array EDecl)
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<order-streamed-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let emit : StreamOutputEmitter := fun event => collected.modify fun declarations =>
    match event with
    | .generatedIsland records => declarations ++ records
    | .source record => declarations.push record
  let ((report, plan), _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run'
      (runFilterStreaming input checkRecursors generation emit)) context { env }
  return { report, plan, output := { input with decls := ← collected.get } }

def runFilterPlannedDiscardedState (scratch : String) (input : Export)
    (generation : InductiveModels.Cli.Config)
    (checkRecursors : Bool := false) : IO DiscardedFilterRun :=
  Spool.withWorkspace scratch fun workspace => do
    let inputFile ← workspace.createFile "planned-input.ndjson"
    discard <| inputFile.append input.render.toUTF8
    discard <| inputFile.finish
    let tee ← Spool.ParseTee.create workspace
    let parsedResult ← IO.FS.withFile inputFile.path .read fun handle =>
      parseHandleWithSink handle tee.sink
        (options := { allowDuplicateNames := true })
    let (parsed, certificate) ← match parsedResult with
      | .ok parsed => pure parsed
      | .error error => throw <| IO.userError s!"planned source parse failed: {error}"
    let sizes ← tee.finish
    let reader ← match ← Spool.PlannedSourceReader.create tee certificate sizes parsed.decls.size with
      | .ok reader => pure reader
      | .error error => throw <| IO.userError s!"planned source reader failed: {error}"
    let env ← importModules #[] {}
    let context : Core.Context :=
      { fileName := "<planned-order-test>", fileMap := default,
        maxHeartbeats := 0, maxRecDepth := 8192 }
    let ((report, plan), _) ← Lean.Core.CoreM.toIO
      (Lean.Meta.MetaM.run'
        (runFilterDiscardingPlanned parsed reader checkRecursors generation)) context { env }
    return { report, plan }

def runFilterPlannedCensusState (scratch : String) (input : Export)
    (generation : InductiveModels.Cli.Config)
    (checkRecursors : Bool := false) : IO PlannedCensusFilterRun :=
  Spool.withWorkspace scratch fun workspace => do
    let inputFile ← workspace.createFile "planned-census-input.ndjson"
    discard <| inputFile.append input.render.toUTF8
    discard <| inputFile.finish
    let tee ← Spool.ParseTee.create workspace
    let parsedResult ← IO.FS.withFile inputFile.path .read fun handle =>
      parsePlannedSourceWithTee handle tee
        (options := { allowDuplicateNames := true })
    let parsed ← match parsedResult with
      | .ok parsed => pure parsed
      | .error error => throw <| IO.userError s!"planned census parse failed: {error}"
    let sizes ← tee.finish
    let reader ← match ← Spool.PlannedSourceReader.create tee parsed.certificate sizes
        parsed.envelope.declarationCount (some parsed.envelope.arena) with
      | .ok reader => pure reader
      | .error error => throw <| IO.userError s!"planned census reader failed: {error}"
    let env ← importModules #[] {}
    let context : Core.Context :=
      { fileName := "<planned-census-order-test>", fileMap := default,
        maxHeartbeats := 0, maxRecDepth := 8192 }
    let ((report, plan), _) ← Lean.Core.CoreM.toIO
      (Lean.Meta.MetaM.run'
        (runFilterDiscardingPlannedCensus parsed reader checkRecursors generation)) context { env }
    return { report, plan, input := parsed }

def preparePlannedCensus (workspace : Spool.Workspace) (input : Export) :
    IO (PlannedSourceInput × Spool.PlannedSourceReader) := do
  let inputFile ← workspace.createFile "planned-provenance-input.ndjson"
  discard <| inputFile.append input.render.toUTF8
  discard <| inputFile.finish
  let tee ← Spool.ParseTee.create workspace
  let parsed ← IO.FS.withFile inputFile.path .read fun handle => do
    match ← parsePlannedSourceWithTee handle tee
        (options := { allowDuplicateNames := true }) with
    | .ok parsed => pure parsed
    | .error error => throw <| IO.userError s!"planned provenance parse failed: {error}"
  let sizes ← tee.finish
  let reader ← match ← Spool.PlannedSourceReader.create tee parsed.certificate sizes
      parsed.envelope.declarationCount (some parsed.envelope.arena) with
    | .ok reader => pure reader
    | .error error => throw <| IO.userError s!"planned provenance reader failed: {error}"
  return (parsed, reader)

def swappedPlannedReaderRejected (scratch : String) (left right : Export) : IO Bool :=
  Spool.withWorkspace scratch fun leftWorkspace => do
    let (leftInput, _) ← preparePlannedCensus leftWorkspace left
    Spool.withWorkspace scratch fun rightWorkspace => do
      let (_, rightReader) ← preparePlannedCensus rightWorkspace right
      let env ← importModules #[] {}
      let context : Core.Context :=
        { fileName := "<planned-provenance-test>", fileMap := default,
          maxHeartbeats := 0, maxRecDepth := 8192 }
      try
        let _ ← Lean.Core.CoreM.toIO
          (Lean.Meta.MetaM.run'
            (runFilterDiscardingPlannedCensus leftInput rightReader false
              { nested := false, mutualModels := false, simple := false, basic := false }))
          context { env }
        return false
      catch error =>
        return (toString error).contains "different raw provenance"

def generatedFixtureState (path : String) (generation : InductiveModels.Cli.Config) :
    IO FilterRun := do
  let text ← IO.FS.readFile path
  let .ok parsed := InductiveModels.parse text
    | throw <| IO.userError s!"cannot parse {path}"
  runFilterState parsed generation

def generatedFixture (path : String) (generation : InductiveModels.Cli.Config) : IO Export := do
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

def noGeneration : InductiveModels.Cli.Config :=
  { nested := false, mutualModels := false, simple := false, basic := false }

def replayGeneratedIn (base : Environment) (records : Array EDecl) :
    IO (Except String Environment) := do
  let context : Core.Context :=
    { fileName := "<quotient-replay-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (checkGeneratedIn base records)) context { env := base }
  return result

def exactInductiveRecord (env : Environment) (names : Array Name) : IO EDecl := do
  let context : Core.Context :=
    { fileName := "<generated-replay-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (record, _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (indEDecl names)) context { env }
  return record

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

def summaryEqual (left right : Order.DeclSummary) : Bool :=
  left.ordinal == right.ordinal && left.introduced == right.introduced &&
    left.referenced == right.referenced &&
    left.owner == right.owner && left.support == right.support &&
    left.modelSlots == right.modelSlots && left.modelBefore == right.modelBefore

def summariesEqual (left right : Array Order.DeclSummary) : Bool :=
  left.size == right.size && (Array.range left.size).all fun i =>
    summaryEqual left[i]! right[i]!

def orderOutcomesEqual (left right : Except Order.Error (Array Nat)) : Bool :=
  match left, right with
  | .ok left, .ok right => left == right
  | .error left, .error right => toString (repr left) == toString (repr right)
  | _, _ => false

def run (root : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut state : TestState := {}

  -- The phase-two census is deliberately checked against the independent
  -- whole-export implementations retained during migration.  The fixture
  -- combines declaration metadata, an inductive owner, duplicate record-name
  -- occurrences and a transparent definition so every frozen table has a
  -- nonempty observation.
  let censusInput := exportOf #[
    modelDef `CensusTransparent,
    metadataRecord,
    axDecl `CensusDuplicate,
    axDecl `CensusDuplicate]
  let census := SourceCensus.ofSource censusInput
  let referenceIndex := Check.SyntaxIndex.ofSource censusInput
  state := state.check "incremental syntax discovery equals whole-export discovery" <|
    Check.discoverWithIndex censusInput census.sourceSyntax ==
      Check.discoverWithIndex censusInput referenceIndex
  state := state.check "incremental transparent normalizer equals whole-export normalizer" <|
    census.sourceSyntax.exactNormalizer.whnf (.const `CensusTransparent []) ==
      referenceIndex.exactNormalizer.whnf (.const `CensusTransparent [])
  state := state.check "incremental global syntax rows equal whole-export rows" <|
    Check.globalExtraRecordsWithIndex census.sourceSyntax censusInput.decls ==
      Check.globalExtraRecordsWithIndex referenceIndex censusInput.decls
  state := state.check "incremental source summaries equal whole-export summaries" <|
    summariesEqual census.summaries (Order.summaries censusInput)
  state := state.check "incremental certificate rows equal whole-export rows" <|
    census.familyCertificateRecords censusInput ==
      Check.compactFamilyCertificateRecordsWithIndex censusInput referenceIndex
        (Check.discoverWithIndex censusInput referenceIndex)
  state := state.check "incremental raw-name callback keeps historical last occurrence" <|
    census.reserved.contains `CensusDuplicate &&
      census.rawOrdinals[`CensusDuplicate]? == some 3
  state := state.check "incremental duplicate diagnostics equal full record ordering" <|
    orderOutcomesEqual (Order.summaryRecordOrder census.summaries)
      (Order.recordOrder censusInput)
  let censusCycle := exportOf #[
    axDecl `CensusCycleA (.const `CensusCycleB []),
    axDecl `CensusCycleB (.const `CensusCycleA [])]
  let cycleCensus := SourceCensus.ofSource censusCycle
  state := state.check "incremental cycle diagnostics equal full record ordering" <|
    orderOutcomesEqual (Order.summaryRecordOrder cycleCensus.summaries)
      (Order.recordOrder censusCycle)
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
  let eqRecord ← exactInductiveRecord quotientBase #[`Eq]
  state := state.check "generated Eq may precede and support a generated quotient bundle" <|
    match ← replayGeneratedIn empty (#[eqRecord] ++ quotientRecords) with
    | .ok checked =>
        checked.constants.contains `Eq && installedQuotRecords? checked == some quotientRecords
    | .error _ => false
  let quotientBeforeEqRejected ←
    generatedReplayRejects empty (quotientRecords ++ #[eqRecord])
  state := state.check "generated quotient cannot precede its generated Eq prerequisite"
    quotientBeforeEqRejected
  state := state.check "record ordering exposes the quotient's hidden Eq prerequisite" <|
    match Order.reorder (exportOf (quotientRecords ++ #[eqRecord])) with
    | .ok reordered => before reordered `Eq `Quot
    | .error _ => false
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

  -- Mutual-block `all` fields are descriptive metadata, not dependencies.
  -- Semantic ownership fields and every expression root remain references.
  let metadataReferences := Order.references metadataRecord
  state := state.check "semantic inductive record references are traversed" <|
    [`TypeDependency, `CtorListDependency, `CtorTypeDependency,
      `InductDependency, `RecTypeDependency, `RuleCtorDependency,
      `RuleRhsDependency].all metadataReferences.contains &&
      !metadataReferences.contains `AllDependency &&
      !metadataReferences.contains `RecAllDependency

  let defMetadata := EDecl.defn `MetadataDef [] (.const `DefType [])
    (.const `DefValue []) .opaque "safe" [`DefAll]
  let theoremMetadata := EDecl.thm `MetadataTheorem [] (.const `TheoremType [])
    (.const `TheoremValue []) [`TheoremAll]
  let opaqueMetadata := EDecl.opaq `MetadataOpaque [] (.const `OpaqueType [])
    (.const `OpaqueValue []) false [`OpaqueAll]
  let defReferences := Order.references defMetadata
  let theoremReferences := Order.references theoremMetadata
  let opaqueReferences := Order.references opaqueMetadata
  state := state.check "definition theorem and opaque all metadata is not a dependency" <|
    [`DefType, `DefValue].all defReferences.contains && !defReferences.contains `DefAll &&
      [`TheoremType, `TheoremValue].all theoremReferences.contains &&
        !theoremReferences.contains `TheoremAll &&
      [`OpaqueType, `OpaqueValue].all opaqueReferences.contains &&
        !opaqueReferences.contains `OpaqueAll

  -- Corpus-shaped opaque declarations may carry the same cyclic mutual-block
  -- metadata even though their exported expressions have at most a one-way
  -- dependency. Both value-retaining and compact ordering must use that real
  -- dependency, and the resulting stream must remain kernel-replayable.
  let groupedAll := [`GroupedA, `GroupedB]
  let groupedA := EDecl.opaq `GroupedA [] (.sort (.succ .zero))
    (.const `GroupedB []) false groupedAll
  let groupedB := EDecl.opaq `GroupedB [] (.sort (.succ .zero))
    (.sort .zero) false groupedAll
  let grouped := exportOf #[groupedA, groupedB]
  state := state.check "mutual metadata does not hide a real opaque dependency" <|
    isExactRecordOrder (Order.recordOrder grouped) #[1, 0] &&
      isExactRecordOrder
        (Order.summaryRecordOrderPrioritizing (Order.summaries grouped)) #[1, 0] &&
      (← kernelAccepts grouped)

  let independentA := EDecl.opaq `IndependentGroupedA [] (.sort (.succ .zero))
    (.sort .zero) false [`IndependentGroupedA, `IndependentGroupedB]
  let independentB := EDecl.opaq `IndependentGroupedB [] (.sort (.succ .zero))
    (.sort .zero) false [`IndependentGroupedA, `IndependentGroupedB]
  let independentGrouped := exportOf #[independentA, independentB]
  state := state.check "mutual metadata alone preserves stable raw order" <|
    isExactRecordOrder (Order.recordOrder independentGrouped) #[0, 1] &&
      isExactRecordOrder
        (Order.summaryRecordOrderPrioritizing (Order.summaries independentGrouped)) #[0, 1] &&
      (← kernelAccepts independentGrouped)

  let expressionCycle := exportOf #[
    EDecl.opaq `ExpressionCycleA [] (.sort (.succ .zero))
      (.const `ExpressionCycleB []) false [`ExpressionCycleA, `ExpressionCycleB],
    EDecl.opaq `ExpressionCycleB [] (.sort (.succ .zero))
      (.const `ExpressionCycleA []) false [`ExpressionCycleA, `ExpressionCycleB]]
  state := state.check "genuine opaque expression cycles remain exact errors" <|
    match Order.recordOrder expressionCycle,
        Order.summaryRecordOrderPrioritizing (Order.summaries expressionCycle) with
    | .error (.cycle records declarations),
        .error (.cycle compactRecords compactDeclarations) =>
      records == #[0, 1] && compactRecords == records &&
        declarations == #[#[`ExpressionCycleA], #[`ExpressionCycleB]] &&
        compactDeclarations == declarations
    | _, _ => false

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

  -- With generation disabled, the filter is byte/order neutral even when the
  -- original order is not alphabetical.
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
  let neutralDiscarded ← runFilterDiscardedState neutralInput noGeneration true
  let neutralStreamed ← runFilterStreamedState neutralInput noGeneration true
  state := state.check "empty generation preserves the compact value plan" <|
      neutralDiscarded.report == neutral.report &&
      neutralDiscarded.plan.declarations.size == neutralInput.decls.size &&
      neutralDiscarded.plan.retainedGeneratedRecords == 0 &&
      neutral.env.constants.contains `NeutralOwner && neutral.env.constants.contains `NeutralDependent
  state := state.check "streaming neutral output retains no declaration payload" <|
    neutralStreamed.output.decls == neutral.output.decls &&
      neutralStreamed.report == neutral.report &&
      neutralStreamed.plan.checkReport == neutralDiscarded.plan.checkReport &&
      neutralStreamed.plan.retainedGeneratedRecords == 0 &&
      neutralStreamed.plan.streamStats.sourceRecords == neutralInput.decls.size &&
      neutralStreamed.plan.streamStats.generatedRecords == 0 &&
      neutralStreamed.plan.streamStats.maxIslandRecords == 0

  -- The declaration-wise filter consumes source records in raw order. Use an
  -- already-valid dependency stream so both retained and planned paths can
  -- pin the identity ordinal mapping.
  let feedConsumer := axDecl `FeedConsumer (.const `FeedProvider [])
  let feedProvider := axDecl `FeedProvider
  let feedInput := exportOf #[feedProvider, feedConsumer]
  let feedRun ← runFilterState feedInput noGeneration
  let feedTrace ← runFilterTraceState feedInput noGeneration
  let feedDiscarded ← runFilterDiscardedState feedInput noGeneration
  let feedPlanned ← runFilterPlannedDiscardedState s!"{root}/_tmp" feedInput noGeneration
  let feedCensus ← runFilterPlannedCensusState s!"{root}/_tmp" feedInput noGeneration
  state := state.check "filter consumes one raw-order source record at a time" <|
    feedRun.output.decls == feedInput.decls &&
      feedRun.report == ({} : Report) &&
      feedRun.env.constants.contains `FeedProvider &&
      feedRun.env.constants.contains `FeedConsumer
  state := state.check "one-record trace preserves output and records logical/raw ordinals" <|
    feedTrace.output.decls == feedRun.output.decls && feedTrace.report == feedRun.report &&
      feedTrace.steps.map (·.sourceOrdinal) == #[0, 1] &&
      feedTrace.steps.map (·.rawOrdinal) == #[0, 1] &&
      feedTrace.steps.map (·.sourceNames) == #[#[`FeedProvider], #[`FeedConsumer]] &&
      feedTrace.steps.all fun step =>
        !step.sourceIsInductive && step.sourceInstalled &&
          step.generated.isEmpty && step.generatedRecords == 0
  state := state.check "planned source spans drive the same frozen raw order" <|
    feedPlanned.report == feedDiscarded.report &&
      feedPlanned.plan.declarations == feedDiscarded.plan.declarations &&
      feedPlanned.plan.checkReport == feedDiscarded.plan.checkReport &&
      feedPlanned.plan.retainedGeneratedRecords ==
        feedDiscarded.plan.retainedGeneratedRecords &&
      feedPlanned.plan.declarations == #[.source 0, .source 1] &&
      feedPlanned.plan.retainedGeneratedRecords == 0
  state := state.check "planned census releases source records and preserves dependency replay" <|
    feedCensus.input.envelope.retainedDeclarations == 0 &&
      feedCensus.input.envelope.declarationCount == feedInput.decls.size &&
      feedCensus.report == feedDiscarded.report &&
      feedCensus.plan.declarations == feedDiscarded.plan.declarations &&
      feedCensus.plan.checkReport == feedDiscarded.plan.checkReport &&
      feedCensus.plan.retainedGeneratedRecords == feedDiscarded.plan.retainedGeneratedRecords
  let alteredFeedInput := exportOf #[
    axDecl `FeedConsumer (.sort .zero),
    axDecl `FeedProvider]
  state := state.check "planned census rejects a same-count same-name reader from another source" <|
    ← swappedPlannedReaderRejected s!"{root}/_tmp" feedInput alteredFeedInput

  -- This real mutual output has three members, unequal constructor counts,
  -- parameters and levels. Discovery must use each declaration's exact name,
  -- and a stable reorder must retain all ordinary implementation dependencies.
  let generatedMutualRun ← generatedFixtureState
    s!"{root}/test/fixtures/inductive-models/mutual_shapes.ndjson"
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
  let nestedRun ← generatedFixtureState s!"{root}/test/fixtures/inductive-models/nested_iota.ndjson"
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
  let nestedDeepRun ← generatedFixtureState
    s!"{root}/test/fixtures/inductive-models/nested_deep.ndjson"
    { noGeneration with nested := true }
  state := state.check "depth-two nested iotas remain on the legacy motive path" <|
    nestedDeepRun.report.generated.any (·.1 == `DTree) &&
      nestedDeepRun.output.decls.any (·.names.contains `DTree.rec_2._model.iota_1)
  state := state.check "nested-only models are absent from the final replay environment" <|
    finalEnvironmentIsIsolated nestedRun
  -- The default pipeline extends the same island through the generated nested
  -- block's mutual model and then through each simple model. None of those
  -- intermediate owners or their interfaces may escape into the source replay
  -- environment, even though all remain in the serialized output.
  let composedRun ← generatedFixtureState
    s!"{root}/test/fixtures/inductive-models/nested_iota.ndjson" {}
  let composedStreamed ← runFilterStreamedState composedRun.input {}
  let nestedImpl := Name.num `Tree._model._impl 0
  let composedCensus := isolationCensus composedRun
  state := state.check
      s!"nested-mutual-simple composition remains one disposable island: {repr composedCensus}" <|
    composedRun.report.generated.any (·.1 == `Tree) &&
      composedRun.report.generated.any (·.1 == nestedImpl) &&
      (emittedNames composedRun).contains nestedImpl &&
      !composedRun.env.constants.contains nestedImpl &&
      finalEnvironmentIsIsolated composedRun
  let composedCheck := Check.check composedStreamed.output
  state := state.check
      s!"composed stream places every recursive model before its generated owner: \
        families={familiesBeforeOwners composedStreamed.output}, \
        compact={repr (composedStreamed.plan.checkReport.violations[0]?)}, \
        full={repr (composedCheck[0]?)}" <|
    composedStreamed.output.decls == composedRun.output.decls &&
      familiesBeforeOwners composedStreamed.output &&
      composedStreamed.plan.checkReport.violations.isEmpty &&
      composedCheck.isEmpty

  let simpleRawRun ← generatedFixtureState
    s!"{root}/test/fixtures/inductive-models/prim_shapes.ndjson"
    { noGeneration with simple := true }
  let simpleInput ← withCompletePrerequisiteBefore simpleRawRun.input `Eq `Tri
  let simpleRun ← runFilterState simpleInput { noGeneration with simple := true }
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

  -- Compare full output, compact discard, and the planned source reader across
  -- each generation route.
  let compactMatrix : Array (String × String × InductiveModels.Cli.Config × Bool) := #[
    ("nested", "nested_iota.ndjson", { noGeneration with nested := true }, false),
    ("mutual", "mutual_shapes.ndjson", { noGeneration with mutualModels := true }, false),
    ("simple", "prim_shapes.ndjson", { noGeneration with simple := true }, false),
    ("recursive indexed", "indexed_fibre_boundary.ndjson",
      { noGeneration with simple := true }, false),
    ("composed", "nested_iota.ndjson", {}, true),
    ("late support", "prim_late_basis.ndjson", {}, false)]
  for (label, fixture, generation, checkRecursors) in compactMatrix do
    let fixturePath := s!"{root}/test/fixtures/inductive-models/{fixture}"
    let text ← IO.FS.readFile fixturePath
    let .ok input := InductiveModels.parse text | do
      state := state.check s!"compact {label} fixture parses" false
      continue
    let legacy ← runFilterState input generation checkRecursors
    let discarded ← runFilterDiscardedState input generation checkRecursors
    let plannedCensus ←
      runFilterPlannedCensusState s!"{root}/_tmp" input generation checkRecursors
    state := state.check s!"compact-discard {label} equals full output" <|
      discarded.report == legacy.report &&
        discarded.plan.checkReport == Check.checkReport legacy.output &&
        discarded.plan.declarations.size == legacy.output.decls.size &&
        discarded.plan.retainedGeneratedRecords == 0
    state := state.check s!"planned-census {label} equals compact full output" <|
      plannedCensus.input.envelope.retainedDeclarations == 0 &&
        plannedCensus.input.envelope.declarationCount == input.decls.size &&
        plannedCensus.report == discarded.report &&
        plannedCensus.plan.checkReport == discarded.plan.checkReport &&
        plannedCensus.plan.declarations == discarded.plan.declarations &&
        plannedCensus.plan.retainedGeneratedRecords == discarded.plan.retainedGeneratedRecords

  let existingDiscarded ← runFilterDiscardedState nestedRun.output
    { noGeneration with nested := true }
  let existingPlanned ← runFilterPlannedCensusState s!"{root}/_tmp" nestedRun.output
    { noGeneration with nested := true }
  state := state.check "planned-census existing model preserves family/check certificates" <|
    existingPlanned.input.envelope.retainedDeclarations == 0 &&
      existingPlanned.report == existingDiscarded.report &&
      existingPlanned.plan.checkReport == existingDiscarded.plan.checkReport &&
      existingPlanned.plan.declarations == existingDiscarded.plan.declarations &&
      existingPlanned.plan.retainedGeneratedRecords ==
        existingDiscarded.plan.retainedGeneratedRecords

  -- A malformed later inductive preserves the completed trace prefix and
  -- returns an empty compact plan.
  let lateMalformed := mapConstructor nestedRun.input `PT.node fun constructor =>
    { constructor with type := .sort .zero }
  let malformedLegacy ← runFilterState lateMalformed {}
  let validTrace ← runFilterTraceState nestedRun.input {}
  let malformedTrace ← runFilterTraceState lateMalformed {}
  let malformedDiscarded ← runFilterDiscardedState lateMalformed {}
  state := state.check "late unreplayable compact verdict equals legacy" <|
    malformedLegacy.report.unreplayable.isSome &&
      malformedDiscarded.report == malformedLegacy.report &&
      malformedDiscarded.plan.declarations.isEmpty &&
      malformedDiscarded.plan.retainedGeneratedRecords == 0
  state := state.check "late unreplayable preserves the completed trace prefix" <|
    malformedTrace.report == malformedLegacy.report &&
      !malformedTrace.steps.isEmpty && malformedTrace.steps.size < validTrace.steps.size &&
      malformedTrace.steps == validTrace.steps.extract 0 malformedTrace.steps.size

  -- The small alias fixture exercises both a model-local arm-C skeleton and
  -- fixed shared graph support. Every generated declaration that survives in
  -- the replay environment must be explicitly witnessed as spliced and have
  -- a fixed support name; public interfaces and local implementation support
  -- are absent even though they remain in the emitted export.
  let aliasRun ← generatedFixtureState
    s!"{root}/test/fixtures/inductive-models/transparent_owner_aliases.ndjson" {}
  let aliasDiscarded ← runFilterDiscardedState aliasRun.input {}
  state := state.check "compact-discard retains no cumulative alias records" <|
    aliasDiscarded.report == aliasRun.report &&
      aliasDiscarded.plan.declarations.size == aliasRun.output.decls.size &&
      aliasDiscarded.plan.checkReport == Check.checkReport aliasRun.output &&
      aliasDiscarded.plan.retainedGeneratedRecords == 0
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
  let wRawRun ← generatedFixtureState s!"{root}/test/fixtures/inductive-models/prim_w.ndjson"
    { noGeneration with simple := true }
  let wInput ← withCompletePrerequisiteBefore wRawRun.input `Eq `Tree
  let wRun ← runFilterState wInput { noGeneration with simple := true }
  let wDiscarded ← runFilterDiscardedState wRun.input
    { noGeneration with simple := true }
  let wCensus := isolationCensus wRun
  state := state.check
      s!"W core support persists without retaining its model island: {repr wCensus}" <|
    wRun.report.generated.any (·.1 == `Tree) &&
      wRun.report.spliced.any (fun (_, names) => names.contains wCoreSelf) &&
      wRun.env.constants.contains wCoreSelf &&
      !wRun.env.constants.contains (Naming.modelName `Tree) &&
      finalEnvironmentIsIsolated wRun
  state := state.check "one-layer W compact discard retains only its value plan" <|
    wDiscarded.report == wRun.report &&
      wDiscarded.plan.declarations.size == wRun.output.decls.size &&
      wDiscarded.plan.checkReport == Check.checkReport wRun.output &&
      wDiscarded.plan.retainedGeneratedRecords == 0

  -- A prerequisite after its owner causes an exact decline and no partial
  -- island. A test-only prerequisite-first variant then pins constructive
  -- island-before-owner emission while every source step remains raw-order.
  let latePUnitRawRun ← generatedFixtureState
    s!"{root}/test/fixtures/inductive-models/tight_prop_field_late.ndjson"
    { noGeneration with simple := true }
  state := state.check "late input PUnit declines without a partial model island" <|
    latePUnitRawRun.report.declined ==
      #[(`PFP, "prim model name taken (PUnit)")] &&
      noModeledBlockDescendants latePUnitRawRun.input latePUnitRawRun.output `PFP
  let latePUnitInput ←
    withCompletePrerequisiteBefore latePUnitRawRun.input `PUnit `PFP
  let latePUnitRun ← runFilterState latePUnitInput
    { noGeneration with simple := true }
  state := state.check "prerequisite-first PUnit supports owner-local generation" <|
    latePUnitRun.report.generated.any (·.1 == `PFP) &&
      !latePUnitRun.report.spliced.any (fun (_, names) => names.contains `PUnit) &&
      latePUnitRun.env.constants.contains `PUnit &&
      latePUnitRun.env.constants.contains `PFP &&
      !latePUnitRun.env.constants.contains (Naming.modelName `PFP) &&
      finalEnvironmentIsIsolated latePUnitRun
  let latePUnitTrace ← runFilterTraceState latePUnitInput
    { noGeneration with simple := true }
  let latePUnitStreamed ← runFilterStreamedState latePUnitInput
    { noGeneration with simple := true }
  let pfpSteps := latePUnitTrace.steps.filter fun step =>
    step.generated.any (·.1 == `PFP)
  let pfpIslandImmediatelyBeforeOwner := match
      declarationIndex? latePUnitRun.input `PFP,
      declarationIndex? latePUnitTrace.output `PFP with
    | some sourceOwner, some outputOwner =>
      let generatedRecords := pfpSteps[0]!.generatedRecords
      outputOwner == sourceOwner + generatedRecords &&
        latePUnitTrace.output.decls.extract 0 sourceOwner ==
          latePUnitRun.input.decls.extract 0 sourceOwner &&
        latePUnitTrace.output.decls.extract (outputOwner + 1)
            latePUnitTrace.output.decls.size ==
          latePUnitRun.input.decls.extract (sourceOwner + 1)
            latePUnitRun.input.decls.size &&
        before latePUnitTrace.output (Naming.modelName `PFP) `PFP
    | _, _ => false
  state := state.check "one raw-order transition emits the island immediately before its owner" <|
    latePUnitTrace.output.decls == latePUnitRun.output.decls &&
      latePUnitTrace.report == latePUnitRun.report &&
      latePUnitTrace.steps.size == latePUnitRun.input.decls.size &&
      latePUnitTrace.steps.map (·.sourceOrdinal) ==
        Array.range latePUnitRun.input.decls.size &&
      latePUnitTrace.steps.map (·.rawOrdinal) ==
        Array.range latePUnitRun.input.decls.size &&
      pfpSteps.size == 1 && pfpSteps[0]!.sourceNames.contains `PFP &&
      pfpSteps[0]!.sourceIsInductive && pfpSteps[0]!.sourceInstalled &&
      pfpSteps[0]!.generatedRecords > 0 &&
      latePUnitTrace.steps.filter (·.generatedRecords > 0) == pfpSteps &&
      pfpIslandImmediatelyBeforeOwner
  state := state.check "stream callback collection equals constructive full output" <|
    latePUnitStreamed.output.decls == latePUnitRun.output.decls &&
      latePUnitStreamed.report == latePUnitRun.report &&
      latePUnitStreamed.plan.retainedGeneratedRecords == 0 &&
      latePUnitStreamed.plan.streamStats.sourceRecords == latePUnitInput.decls.size &&
      latePUnitStreamed.plan.streamStats.generatedRecords ==
        latePUnitRun.output.decls.size - latePUnitInput.decls.size &&
      latePUnitStreamed.plan.streamStats.maxIslandRecords ==
        latePUnitStreamed.report.maxLiveIslandRecords

  IO.println s!"record order: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1

end InductiveModels.Order.Tests

def main (args : List String) : IO UInt32 :=
  InductiveModels.Order.Tests.run (args.head?.getD ".")
