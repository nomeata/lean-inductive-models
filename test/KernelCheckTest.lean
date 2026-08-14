import InductiveModels.Driver

set_option maxRecDepth 8192

/--
error: Unknown identifier `InductiveModels.CompactDirectSealed`
-/
#guard_msgs in
#check InductiveModels.CompactDirectSealed

/-!
# Incremental kernel-check regression tests

These tests pin exact verdicts at behavior-sensitive boundaries and exercise
direct state feeding without passing through an export writer or parser
intermediate.  The existing Order suite remains the broad whole-export oracle.
-/

open Lean Meta InductiveModels

namespace InductiveModels.KernelCheck.Tests

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def sameResult (left right : Except String Unit) : Bool :=
  match left, right with
  | .ok (), .ok () => true
  | .error left, .error right => left == right
  | _, _ => false

def accepted : Except String Unit → Bool
  | .ok () => true
  | .error _ => false

def errorSatisfies (result : Except String Unit) (predicate : String → Bool) : Bool :=
  match result with
  | .error message => predicate message
  | .ok () => false

def reportEquals (result : Except String Check.Report) (expected : Check.Report) : Bool :=
  match result with
  | .ok actual => actual == expected
  | .error _ => false

def exportEquals (result : Except String Export) (expected : Export) : Bool :=
  match result with
  | .ok actual => actual.render == expected.render
  | .error _ => false

def exportOf (decls : Array EDecl) : Export := { metaLine := .null, decls }

def runMeta (action : MetaM (Except String Unit)) : IO (Except String Unit) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<kernel-check-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' action) context { env }
  return result

def runNew (x : Export) : IO (Except String Unit) :=
  runMeta (typeCheckExport x)

def noGeneration : Cli.Config :=
  { nested := false, mutualModels := false, simple := false, basic := false }

def runFilterShadow (x : Export) (generation : Cli.Config)
    (checkRecursors : Bool := false) :
    IO (Array EDecl × Report × Option FilterKernelCheckShadow) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<filter-kernel-check-shadow-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run'
    (runFilterWithKernelCheckShadow x checkRecursors generation)) context { env }
  return result

def runFilterShadowObserved (x : Export) (generation : Cli.Config)
    (checkRecursors : Bool := false) :
    IO ((Array EDecl × Report × Option FilterKernelCheckShadow) × Environment) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<filter-kernel-check-shadow-environment-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (do
    let result ← runFilterWithKernelCheckShadow x checkRecursors generation
    return (result, ← getEnv))) context { env }
  return result

def runFilterOrdinary (x : Export) (generation : Cli.Config)
    (checkRecursors : Bool := false) : IO (Array EDecl × Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<filter-kernel-check-ordinary-oracle-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run'
    (runFilter x checkRecursors generation)) context { env }
  return result

def runFilterDirectObserved (x : Export) (generation : Cli.Config)
    (checkRecursors : Bool := false) :
    IO ((Report × CompactPlan × Option CompactKernelCheckVerdict) × Environment) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<filter-direct-kernel-check-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (do
    let result ← runFilterDirectChecking x checkRecursors generation
    return (result, ← getEnv))) context { env }
  return result

structure PlannedDirectObserved where
  retainedDeclarations : Nat
  inputReport : Except String Check.Report
  materialized : Except String Export
  result : Report × CompactPlan × Option CompactKernelCheckVerdict
  env : Environment

def runFilterDirectPlannedObserved (scratch : String) (x : Export)
    (generation : Cli.Config) (checkRecursors : Bool := false) :
    IO PlannedDirectObserved :=
  Spool.withWorkspace scratch fun workspace => do
    let inputFile ← workspace.createFile "kernel-check-planned-input.ndjson"
    discard <| inputFile.append x.render.toUTF8
    discard <| inputFile.finish
    let tee ← Spool.ParseTee.create workspace
    let planned ← IO.FS.withFile inputFile.path .read fun handle => do
      match ← parsePlannedSourceWithTee handle tee
          (analyse := false) (allowDuplicateNames := true) with
      | .ok input => pure input
      | .error message => throw <| IO.userError message
    let sizes ← tee.finish
    let reader ← match ← Spool.PlannedSourceReader.create tee planned.certificate sizes
        planned.envelope.declarationCount (some planned.envelope.arena) with
      | .ok reader => pure reader
      | .error message => throw <| IO.userError message
    let inputReport ← checkPlannedSource planned reader
    let materialized ← materializePlannedSource planned reader
    let env ← importModules #[] {}
    let context : Core.Context :=
      { fileName := "<filter-direct-planned-kernel-check-test>", fileMap := default,
        maxHeartbeats := 0, maxRecDepth := 8192 }
    let ((result, observed), _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (do
      let result ← runFilterDirectCheckingPlannedCensus
        planned reader checkRecursors generation
      return (result, ← getEnv))) context { env }
    return {
      retainedDeclarations := planned.envelope.retainedDeclarations
      inputReport, materialized, result, env := observed }

def runDiscarding (x : Export) (generation : Cli.Config)
    (checkRecursors : Bool := false) : IO (Report × CompactPlan) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<filter-kernel-check-compact-boundary-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run'
    (runFilterDiscarding x checkRecursors generation)) context { env }
  return result

def readFixture (root file : String) : IO Export := do
  let text ← IO.FS.readFile s!"{root}/test/fixtures/inductive-models/{file}"
  let .ok parsed := InductiveModels.parse text (analyse := false)
    | throw <| IO.userError s!"kernelchecktest: cannot parse {file}"
  return parsed

def shadowAgrees : Option FilterKernelCheckShadow → Bool
  | none => false
  | some shadow =>
    accepted shadow.streamedResult && accepted shadow.batchResult &&
      accepted shadow.result && !shadow.usedFallback &&
      shadow.recordsPushed == shadow.finalRecords

def directAccepted : Option CompactKernelCheckVerdict → Bool
  | none => false
  | some verdict =>
    accepted verdict.result && verdict.fallback?.isNone &&
      verdict.recordsPushed == verdict.scheduledRecords

def sameCompactPlan (left right : CompactPlan) : Bool :=
  left.declarations == right.declarations && left.checkReport == right.checkReport &&
    left.unavailable? == right.unavailable? &&
    left.retainedGeneratedRecords == right.retainedGeneratedRecords

def mapConstructor (input : Export) (target : Name) (f : ECtor → ECtor) : Export :=
  { input with decls := input.decls.map fun declaration => match declaration with
    | .induct types constructors recursors =>
      .induct types (constructors.map fun constructor =>
        if constructor.name == target then f constructor else constructor) recursors
    | other => other }

def runIncremental (records : Array EDecl) : IO (Except String Unit × Nat) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<incremental-kernel-check-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let action : MetaM (Except String Unit × Nat) := do
    let base ← getEnv
    let state ← (KernelCheck.State.create base).pushAll records
    return (state.finish, state.recordsPushed)
  let (result, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' action) context { env }
  return result

def runBound (rows : Array (EDecl × Array Name)) : IO (Except String Unit) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<bound-kernel-check-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let action : MetaM (Except String Unit) := do
    try
      let mut state := KernelCheck.State.create (← getEnv)
      for (record, expectedNames) in rows do
        state ← state.pushBound record expectedNames
      return state.finish
    catch error => return .error (← error.toMessageData.toString)
  let (result, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' action) context { env }
  return result

def metadataFailureInstalls (x : Export) (name : Name) : IO Bool := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<kernel-check-state-compatibility-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let action : MetaM Bool := do
    let result ← typeCheckExport x
    return !accepted result && (← getEnv).constants.contains name
  let (result, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' action) context { env }
  return result

def corruptFirstRecursor (x : Export) : Option Export := do
  let index ← x.decls.findIdx? fun declaration => match declaration with
    | .induct _ _ (_ :: _) => true
    | _ => false
  let .induct types constructors (recursor :: recursors) := x.decls[index]! | none
  let corrupted := .induct types constructors
    ({ recursor with numMinors := recursor.numMinors + 1 } :: recursors)
  return { x with decls := x.decls.set! index corrupted }

def run (root : String) : IO UInt32 := do
  let mut state : TestState := {}

  -- The public batch API keeps its private dependency schedule: source order
  -- is not required to be kernel insertion order.
  let provider : EDecl := .ax `Provider [] (.sort (.succ .zero)) false
  let consumer : EDecl := .ax `Consumer [] (.const `Provider []) false
  let reordered := exportOf #[consumer, provider]
  let reorderedNew ← runNew reordered
  state := state.check "batch replay accepts valid reversed dependencies" <|
    accepted reorderedNew

  let directForward ← runIncremental #[provider, consumer]
  state := state.check "incremental state accepts an already valid schedule" <|
    accepted directForward.1 && directForward.2 == 2
  let directBackward ← runIncremental #[consumer, provider]
  state := state.check "incremental state rejects a backward schedule but counts every push" <|
    !accepted directBackward.1 && directBackward.2 == 2
  let boundForward ← runBound #[(provider, #[`Provider]), (consumer, #[`Consumer])]
  let boundSwapped ← runBound #[(provider, #[`Consumer]), (consumer, #[`Provider])]
  state := state.check "bound pushes reject a swapped equal-count compact schedule" <|
    accepted boundForward && errorSatisfies boundSwapped
      (fun message => message.contains "differ from compact row")

  -- `Kernel.Environment` retains exact private identities even when
  -- `Lean.Environment`'s async lookup normalizes them to the same spelling.
  let publicName : Name := `Collision.foo
  let privateName : Name := (`_private.KernelCheck).mkNum 0 |>.str "Collision" |>.str "foo"
  let collision := exportOf #[
    .ax publicName [] (.sort (.succ .zero)) false,
    .ax privateName [] (.sort (.succ .zero)) false]
  let collisionNew ← runNew collision
  let collisionDirect ← runIncremental collision.decls
  state := state.check "exact kernel state accepts normalized-private collisions" <|
    privateToUserName privateName == publicName && accepted collisionNew &&
      accepted collisionDirect.1 && collisionDirect.2 == 2

  let fixturePath := s!"{root}/test/fixtures/inductive-models/nested_iota.ndjson"
  let fixtureText ← IO.FS.readFile fixturePath
  let .ok fixture := InductiveModels.parse fixtureText (analyse := false)
    | IO.eprintln "kernelchecktest: fixture parse failed"; return 1
  let some malformedMetadata := corruptFirstRecursor fixture
    | IO.eprintln "kernelchecktest: fixture has no recursor"; return 1
  let metadataNew ← runNew malformedMetadata
  state := state.check "malformed regenerated metadata is rejected exactly" <|
    !accepted metadataNew &&
      errorSatisfies metadataNew (fun message => message.contains "recursor numMinors differs")
  let malformedOwner? := malformedMetadata.decls.findSome? fun declaration => match declaration with
    | .induct (type :: _) _ _ => some type.name
    | _ => none
  let malformedStateInstalled ← malformedOwner?.elim (pure false)
    (metadataFailureInstalls malformedMetadata)
  state := state.check "batch metadata rejection preserves its checked Meta environment" <|
    malformedStateInstalled

  -- Kernel insertion failure precedes metadata diagnostics even when the bad
  -- metadata was observed first.  State must keep checking after metadata
  -- observation, while a replay failure makes its final verdict dominant.
  let missing : EDecl := .ax `LateFailure [] (.const `DefinitelyMissing []) false
  let metadataThenReplayFailure :=
    { malformedMetadata with decls := malformedMetadata.decls.push missing }
  let precedenceNew ← runNew metadataThenReplayFailure
  let precedenceDirect ← runIncremental metadataThenReplayFailure.decls
  state := state.check "kernel insertion failure retains precedence over earlier metadata mismatch" <|
    !accepted precedenceNew && sameResult precedenceDirect.1 precedenceNew &&
      errorSatisfies precedenceNew (fun message =>
        message.contains "DefinitelyMissing" && !message.contains "numMinors differs")

  -- The batch preflight occurs before replay, so duplicate exact declaration
  -- data dominates a separate earlier kernel failure exactly as before.
  let duplicatePreflight := exportOf #[missing, provider, provider]
  let duplicateNew ← runNew duplicatePreflight
  let duplicateDirect ← runIncremental duplicatePreflight.decls
  state := state.check "batch duplicate preflight retains precedence over kernel replay" <|
    !accepted duplicateNew && sameResult duplicateDirect.1 duplicateNew &&
      duplicateDirect.2 == 3 &&
      errorSatisfies duplicateNew (fun message =>
        message.contains "duplicate declaration Provider" &&
          !message.contains "DefinitelyMissing")

  let unknownSafety : EDecl :=
    .defn `UnknownSafety [] (.sort (.succ .zero)) (.sort .zero) .opaque "mystery" []
  let unknownDirect ← runIncremental #[unknownSafety]
  state := state.check "incremental preflight rejects unknown definition safety" <|
    unknownDirect.2 == 1 && errorSatisfies unknownDirect.1
      (fun message => message == "unknown definition safety mystery")

  let malformedDuplicate : EDecl :=
    .defn `Provider [] (.sort (.succ .zero)) (.sort .zero) .opaque "mystery" []
  let malformedDuplicateExport := exportOf #[provider, malformedDuplicate]
  let malformedDuplicateBatch ← runNew malformedDuplicateExport
  let malformedDuplicateDirect ← runIncremental malformedDuplicateExport.decls
  state := state.check "malformed safety precedes a duplicate in the same record" <|
    sameResult malformedDuplicateBatch malformedDuplicateDirect.1 &&
      errorSatisfies malformedDuplicateBatch
        (fun message => message == "unknown definition safety mystery")

  let malformedQuotient : EDecl :=
    .quot `Provider [] (.sort (.succ .zero)) "mystery"
  let malformedQuotientExport := exportOf #[provider, malformedQuotient]
  let malformedQuotientBatch ← runNew malformedQuotientExport
  let malformedQuotientDirect ← runIncremental malformedQuotientExport.decls
  state := state.check "malformed quotient kind precedes a duplicate in the same record" <|
    sameResult malformedQuotientBatch malformedQuotientDirect.1 &&
      errorSatisfies malformedQuotientBatch
        (fun message => message == "unknown quotient kind mystery")

  let skippedUnsafe : EDecl :=
    .ax `SkippedUnsafe [] (.const `MissingUnsafeType []) true
  let skippedPartial : EDecl :=
    .defn `SkippedPartial [] (.const `MissingPartialType []) (.const `MissingPartialValue [])
      .opaque "partial" []
  let skippedDirect ← runIncremental #[skippedUnsafe, skippedPartial]
  state := state.check "unsafe and partial declarations retain arena skip behavior" <|
    accepted skippedDirect.1 && skippedDirect.2 == 2

  let emptyInductive : EDecl := .induct [] [] []
  let emptyDirect ← runIncremental #[emptyInductive]
  state := state.check "empty active inductive record is rejected" <|
    emptyDirect.2 == 1 && errorSatisfies emptyDirect.1
      (fun message => message == "empty inductive declaration")

  let cycle := exportOf #[
    .ax `CycleA [] (.const `CycleB []) false,
    .ax `CycleB [] (.const `CycleA []) false]
  let cycleBatch ← runNew cycle
  state := state.check "batch replay rejects a declaration dependency cycle before insertion" <|
    errorSatisfies cycleBatch (fun message =>
      message.contains "cyclic kernel declaration dependencies")

  let duplicateType : EIndType :=
    { name := `DuplicateMember, levelParams := [], type := .sort (.succ .zero)
      all := [`DuplicateMember], ctors := [], numParams := 0, numIndices := 0
      numNested := 0, isRec := false, isReflexive := false, isUnsafe := false }
  let duplicateMembers : EDecl := .induct [duplicateType, duplicateType] [] []
  let duplicateMembersBatch ← runNew (exportOf #[duplicateMembers])
  let duplicateMembersDirect ← runIncremental #[duplicateMembers]
  state := state.check "duplicate names inside one inductive record are preflight errors" <|
    sameResult duplicateMembersBatch duplicateMembersDirect.1 &&
      errorSatisfies duplicateMembersBatch
        (fun message => message == "duplicate declaration DuplicateMember")

  -- The full-output shadow is driven by the same declaration-wise transition
  -- as generation.  These routes deliberately differ in model shape; none is
  -- modeled as a special recursive `Type` form in the checker.
  let routeMatrix : Array (String × String × Cli.Config × Bool) := #[
    ("simple", "prim_shapes.ndjson", { noGeneration with simple := true }, false),
    ("nested", "nested_iota.ndjson", { noGeneration with nested := true }, false),
    ("mutual", "mutual_shapes.ndjson", { noGeneration with mutualModels := true }, false),
    ("indexed", "indexed_fibre_boundary.ndjson",
      { noGeneration with simple := true }, false),
    ("composed", "nested_iota.ndjson", {}, true)]
  for (label, file, generation, checkRecursors) in routeMatrix do
    let input ← readFixture root file
    let (output, report, shadow?) ← runFilterShadow input generation checkRecursors
    state := state.check s!"filter kernel shadow agrees for {label} generation" <|
      shadowAgrees shadow? && shadow?.any (fun shadow => output.size == shadow.finalRecords) &&
        !report.generated.isEmpty

  let declineBase ← readFixture root "nested_iota.ndjson"
  let occupiedTreeModel : EDecl :=
    .ax (Naming.modelName `Tree) [] (.sort (.succ .zero)) false
  let declineInput := { declineBase with decls := declineBase.decls.push occupiedTreeModel }
  let (declineOutput, declineReport, declineShadow?) ← runFilterShadow declineInput {}
  state := state.check "generation declines still feed the exact source stream" <|
    shadowAgrees declineShadow? && !declineReport.declined.isEmpty &&
      declineShadow?.any (fun shadow => declineOutput.size == shadow.finalRecords)

  let privateA : Name := (`_private.FilterKernelShadowA).mkNum 0 |>.str "Collision"
  let privateB : Name := (`_private.FilterKernelShadowB).mkNum 0 |>.str "Collision"
  let privateCollision := exportOf #[
    .ax privateA [] (.sort (.succ .zero)) false,
    .ax privateB [] (.sort (.succ .zero)) false,
    .ax `UsePrivateA [] (.const privateA []) false,
    .ax `UsePrivateB [] (.const privateB []) false]
  let (privateOutput, privateReport, privateShadow?) ←
    runFilterShadow privateCollision noGeneration
  state := state.check "filter kernel shadow consumes normalized-private aliases exactly" <|
    privateToUserName privateA == privateToUserName privateB &&
      privateOutput == privateCollision.decls && privateReport == ({} : Report) &&
      shadowAgrees privateShadow?

  -- The exact/build alias boundary matters only when generation emits records
  -- from a collision-safe construction view. Insert a private-normalized copy
  -- of a real inductive owner and require both generated families to cross the
  -- shadow as exact names. The batch comparison must restore the construction
  -- Meta environment, in which neither disposable carrier remains installed.
  let aliasShapes ← readFixture root "prim_shapes.ndjson"
  let publicOwner : Name := `Sv
  let privateOwner : Name := (`_private.FilterKernelShadowModel).mkNum 0 |>.str "Sv"
  let some ownerOrdinal := aliasShapes.decls.findIdx? (·.names.contains publicOwner)
    | throw <| IO.userError "kernelchecktest: prim_shapes has no Sv owner"
  let privateRoles := aliasShapes.decls[ownerOrdinal]!.names.foldl
    (init := Naming.AliasMap.empty) fun aliases name =>
      aliases.insert name (name.replacePrefix publicOwner privateOwner)
  let privateOwnerRecord := aliasShapes.decls[ownerOrdinal]!.renameAliases privateRoles
  let collidingShapes := { aliasShapes with decls := (
    aliasShapes.decls.extract 0 (ownerOrdinal + 1) ++ #[privateOwnerRecord] ++
      aliasShapes.decls.extract (ownerOrdinal + 1) aliasShapes.decls.size) }
  let collisionGeneration := legacyGenerationConfig true
  let ((collidingOutput, collidingReport, collidingShadow?), collidingEnv) ←
    runFilterShadowObserved collidingShapes collisionGeneration true
  let (ordinaryCollidingOutput, ordinaryCollidingReport) ←
    runFilterOrdinary collidingShapes collisionGeneration true
  let leakedBuildAlias := collidingOutput.any fun declaration =>
    (declaration.names.toArray ++ (Order.references declaration).toArray).any fun name =>
      name.components.any fun component =>
        component.toString.startsWith "_inductive_models_source_alias_"
  state := state.check "generated normalized-private aliases cross the shadow exactly" <|
    shadowAgrees collidingShadow? && collidingOutput == ordinaryCollidingOutput &&
      collidingReport == ordinaryCollidingReport &&
      collidingReport.generated.any (·.1 == publicOwner) &&
      collidingReport.generated.any (·.1 == privateOwner) && !leakedBuildAlias &&
      collidingOutput.any (·.names.contains (Naming.modelName privateOwner)) &&
      !collidingEnv.constants.contains (Naming.modelName publicOwner) &&
      !collidingEnv.constants.contains (Naming.modelName privateOwner)

  let lateMalformed := mapConstructor declineBase `PT.node fun constructor =>
    { constructor with type := .sort .zero }
  let (ordinaryMalformedOutput, ordinaryMalformedReport) ← runFilterOrdinary lateMalformed {}
  let (shadowMalformedOutput, shadowMalformedReport, malformedShadow?) ←
    runFilterShadow lateMalformed {}
  state := state.check "unreplayable source preserves output/report and has no sealed shadow" <|
    ordinaryMalformedReport.unreplayable.isSome && malformedShadow?.isNone &&
      shadowMalformedOutput == ordinaryMalformedOutput &&
      shadowMalformedReport == ordinaryMalformedReport

  -- A source consumer can precede the generated declaration it names.  The
  -- compact planner already marks this future-provider shape unavailable;
  -- direct chronological kernel replay must likewise fall back to the final
  -- reordered batch verdict instead of exposing its early unknown-constant
  -- diagnostic.
  let futureBase ← readFixture root "nested_iota.ndjson"
  let futureProbe : EDecl :=
    .ax `CompactFallbackProbe [] (.const (Naming.modelName `Tree) []) false
  let futureInput := { futureBase with decls := #[futureProbe] ++ futureBase.decls }
  let futureGeneration := { noGeneration with nested := true }
  let (_, _, futureShadow?) ← runFilterShadow futureInput futureGeneration
  let (_, futureCompact) ← runDiscarding futureInput futureGeneration
  let some futureShadow := futureShadow?
    | IO.eprintln "kernelchecktest: future-provider run did not seal"; return 1
  state := state.check "future generated provider preserves the batch diagnostic fallback" <|
    futureShadow.usedFallback && !accepted futureShadow.streamedResult &&
      accepted futureShadow.batchResult && accepted futureShadow.result &&
      futureShadow.recordsPushed == futureShadow.finalRecords &&
      futureCompact.unavailable?.isSome

  -- Direct compact retention seals before ordering/check finalization. Its
  -- public result is value-only, while the post-call Meta environment has
  -- already returned to the exact invocation base (neither source nor model
  -- construction declarations remain visible).
  let ((directSuccessReport, directSuccessPlan, directSuccess?), directSuccessEnv) ←
    runFilterDirectObserved futureBase futureGeneration
  let plannedDirectSuccess ←
    runFilterDirectPlannedObserved s!"{root}/_tmp" futureBase futureGeneration
  let (discardSuccessReport, discardSuccessPlan) ←
    runDiscarding futureBase futureGeneration
  state := state.check "compact direct success equals compact discard after early seal" <|
    directAccepted directSuccess? && directSuccessReport == discardSuccessReport &&
      sameCompactPlan directSuccessPlan discardSuccessPlan &&
      directSuccessPlan.retainedGeneratedRecords == 0 &&
      directSuccess?.any (fun verdict =>
        verdict.scheduledRecords == directSuccessPlan.declarations.size) &&
      !directSuccessEnv.constants.contains `Tree &&
      !directSuccessEnv.constants.contains (Naming.modelName `Tree)
  state := state.check "planned compact direct releases source AST and preserves input oracle" <|
    plannedDirectSuccess.retainedDeclarations == 0 &&
      reportEquals plannedDirectSuccess.inputReport (Check.checkReport futureBase) &&
      exportEquals plannedDirectSuccess.materialized futureBase &&
      plannedDirectSuccess.result.1 == directSuccessReport &&
      sameCompactPlan plannedDirectSuccess.result.2.1 directSuccessPlan &&
      directAccepted plannedDirectSuccess.result.2.2 &&
      !plannedDirectSuccess.env.constants.contains `Tree

  let ((directMalformedReport, directMalformedPlan, directMalformed?),
      directMalformedEnv) ← runFilterDirectObserved lateMalformed {}
  state := state.check "compact direct unreplayable resets Meta before returning none" <|
    directMalformed?.isNone && directMalformedReport == ordinaryMalformedReport &&
      directMalformedReport.unreplayable.isSome &&
      directMalformedPlan.declarations.isEmpty &&
      directMalformedPlan.retainedGeneratedRecords == 0 &&
      !directMalformedEnv.constants.contains `Tree &&
      !directMalformedEnv.constants.contains `PT

  let ((directMetadataReport, directMetadataPlan, directMetadata?),
      directMetadataEnv) ← runFilterDirectObserved malformedMetadata noGeneration
  let some directMetadata := directMetadata?
    | IO.eprintln "kernelchecktest: malformed metadata direct run did not seal"; return 1
  state := state.check "compact direct metadata rejection defers final-order diagnostics" <|
    directMetadataPlan.unavailable?.isNone && directMetadata.fallback?.isSome &&
      errorSatisfies directMetadata.result (fun message =>
        message == "direct kernel rejection requires the final reordered batch diagnostic" &&
          !message.contains "numMinors differs") &&
      directMetadata.recordsPushed == directMetadata.scheduledRecords &&
      directMetadataReport.unreplayable.isNone &&
      !directMetadataEnv.constants.contains `Tree

  let ((directDeclineReport, directDeclinePlan, directDecline?), _) ←
    runFilterDirectObserved declineInput {}
  let (discardDeclineReport, discardDeclinePlan) ← runDiscarding declineInput {}
  state := state.check "compact direct generation decline retains the compact verdict" <|
    directAccepted directDecline? && !directDeclineReport.declined.isEmpty &&
      directDeclineReport == discardDeclineReport &&
      sameCompactPlan directDeclinePlan discardDeclinePlan &&
      directDeclinePlan.retainedGeneratedRecords == 0

  let ((directAliasReport, directAliasPlan, directAlias?), directAliasEnv) ←
    runFilterDirectObserved collidingShapes collisionGeneration true
  let plannedDirectAlias ← runFilterDirectPlannedObserved
    s!"{root}/_tmp" collidingShapes collisionGeneration true
  let (discardAliasReport, discardAliasPlan) ←
    runDiscarding collidingShapes collisionGeneration true
  state := state.check "compact direct generated aliases retain exact bound rows only" <|
    directAccepted directAlias? && directAliasReport == collidingReport &&
      directAliasReport == discardAliasReport &&
      sameCompactPlan directAliasPlan discardAliasPlan &&
      directAliasPlan.retainedGeneratedRecords == 0 &&
      !directAliasEnv.constants.contains publicOwner &&
      !directAliasEnv.constants.contains privateOwner &&
      !directAliasEnv.constants.contains (Naming.modelName privateOwner)
  state := state.check "planned compact direct preserves normalized exact/build aliases" <|
    plannedDirectAlias.retainedDeclarations == 0 &&
      reportEquals plannedDirectAlias.inputReport (Check.checkReport collidingShapes) &&
      exportEquals plannedDirectAlias.materialized collidingShapes &&
      plannedDirectAlias.result.1 == directAliasReport &&
      sameCompactPlan plannedDirectAlias.result.2.1 directAliasPlan &&
      directAccepted plannedDirectAlias.result.2.2 &&
      !plannedDirectAlias.env.constants.contains publicOwner &&
      !plannedDirectAlias.env.constants.contains privateOwner

  let ((directFutureReport, directFuturePlan, directFuture?), directFutureEnv) ←
    runFilterDirectObserved futureInput futureGeneration
  let some directFuture := directFuture?
    | IO.eprintln "kernelchecktest: compact future-provider run did not seal"; return 1
  state := state.check "compact direct late provider returns value-only fallback" <|
    directFuture.fallback? == directFuturePlan.unavailable? &&
      directFuture.fallback?.isSome && !accepted directFuture.result &&
      directFuture.recordsPushed == directFuture.scheduledRecords &&
      directFuture.scheduledRecords == directFuturePlan.declarations.size &&
      directFutureReport.stmtErrors.isEmpty &&
      directFuturePlan.retainedGeneratedRecords == 0 &&
      !directFutureEnv.constants.contains `Tree &&
      !directFutureEnv.constants.contains (Naming.modelName `Tree)

  if state.failed.isEmpty then
    IO.println s!"kernel check: {state.passed}/{state.passed} passed"
    return 0
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  IO.eprintln s!"kernel check: {state.passed}/{state.passed + state.failed.size} passed"
  return 1

end InductiveModels.KernelCheck.Tests

def main (args : List String) : IO UInt32 :=
  InductiveModels.KernelCheck.Tests.run (args.head?.getD ".")
