import InductiveModels.Driver

set_option maxRecDepth 8192

/--
error: Unknown identifier `InductiveModels.CompactDirectSealed`
-/
#guard_msgs in
#check InductiveModels.CompactDirectSealed

/--
error: Unknown identifier `InductiveModels.SharedPrefixSourcePrepared`
-/
#guard_msgs in
#check InductiveModels.SharedPrefixSourcePrepared

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

def observeSharedPrefix (x : Export) (generation : Cli.Config) :
    IO (SharedPrefixSourceObservation × Environment) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<shared-prefix-source-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (do
    let result ← observeSharedPrefixSource x generation
    return (result, ← getEnv))) context { env }
  return result

def runSharedPrefixDirectObserved (x : Export) (generation : Cli.Config)
    (failAfterOwners? : Option Nat := none) :
    IO (((Report × CompactPlan × Option CompactKernelCheckVerdict) ×
      SharedPrefixDirectObservation) × Environment) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<shared-prefix-direct-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (do
    let result ← runFilterDirectCheckingSharedPrefix x generation failAfterOwners?
    return (result, ← getEnv))) context { env }
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

structure PlannedSharedPrefixObserved where
  retainedDeclarations : Nat
  sourceReads : Nat
  result : (Report × CompactPlan × Option CompactKernelCheckVerdict) ×
    SharedPrefixDirectObservation
  env : Environment

def runSharedPrefixPlannedObserved (scratch : String) (x : Export)
    (generation : Cli.Config) (failAfterOwners? : Option Nat := none) :
    IO PlannedSharedPrefixObserved :=
  Spool.withWorkspace scratch fun workspace => do
    let inputFile ← workspace.createFile "kernel-check-shared-planned-input.ndjson"
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
    let env ← importModules #[] {}
    let context : Core.Context :=
      { fileName := "<shared-prefix-planned-kernel-check-test>", fileMap := default,
        maxHeartbeats := 0, maxRecDepth := 8192 }
    let ((result, observed), _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (do
      let result ← runFilterDirectCheckingSharedPrefixPlannedCensus
        planned reader generation failAfterOwners?
      return (result, ← getEnv))) context { env }
    return {
      retainedDeclarations := planned.envelope.retainedDeclarations
      sourceReads := ← reader.readCount
      result
      env := observed }

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

def sameCompactVerdict (left right : Option CompactKernelCheckVerdict) : Bool :=
  match left, right with
  | some left, some right =>
    sameResult left.result right.result && left.recordsPushed == right.recordsPushed &&
      left.scheduledRecords == right.scheduledRecords &&
      left.constructionTransitions == right.constructionTransitions &&
      left.fallback? == right.fallback?
  | none, none => true
  | _, _ => false

def sameDirectResult
    (left right : Report × CompactPlan × Option CompactKernelCheckVerdict) : Bool :=
  left.1 == right.1 && sameCompactPlan left.2.1 right.2.1 &&
    sameCompactVerdict left.2.2 right.2.2

def witnessedSupportCount (output : Array EDecl) (report : Report) : Nat :=
  let spliced := report.spliced.foldl (init := ({} : Std.HashSet Name))
    fun names entry => entry.2.foldl (fun names name => names.insert name) names
  output.countP fun record =>
    record.names.any spliced.contains &&
      (record.names.any persistentSupportRoot || record.names.all persistentSupportName)

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

def runMappedPrefixCollision (prefixLogical prefixBuild logical build : EDecl) :
    IO (Except String Unit) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<mapped-prefix-kernel-check-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let action : MetaM (Except String Unit) := do
    let base ← getEnv
    let .ok (.checked declaration) := KernelCheck.replayDisposition prefixBuild
      | throwError "mapped-prefix fixture is not one checked declaration"
    let sourceEnv ← match base.addDeclCore 0 declaration none true with
      | .ok env => pure env
      | .error exception => throwError (exception.toMessageData {})
    let seeded := KernelCheck.State.createCheckedPrefix sourceEnv
      #[prefixLogical.names.toArray]
    let next ← seeded.pushMappedBound logical build logical.names.toArray
    return next.finish
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

def makeInductiveRecord (name : Name) (isUnsafe : Bool) : IO EDecl := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<shared-prefix-unsafe-inductive-fixture>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let declaration : Declaration := .inductDecl [] 0
    [{ name, type := .sort (.succ .zero),
       ctors := [{ name := Name.str name "mk", type := .const name [] }] }] isUnsafe
  let (result, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (do
    match (← getEnv).addDeclCore 0 declaration none (!isUnsafe) with
    | .error exception =>
      throwError "cannot mint inductive: {← (exception.toMessageData {}).toString}"
    | .ok next =>
      setEnv next
      indEDecl #[name])) context { env }
  return result

def makeUnsafeInductive (name : Name) : IO EDecl :=
  makeInductiveRecord name true

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

  let mappedPrefixProvider : EDecl :=
    .ax `MappedProvider [] (.sort (.succ .zero)) false
  let mappedGeneratedProvider : EDecl :=
    .ax `MappedGeneratedProvider [] (.sort (.succ .zero)) false
  let mappedPrefixCollision ← runMappedPrefixCollision
    provider mappedPrefixProvider provider mappedGeneratedProvider
  state := state.check "adopted source rows retain exact ownership across build images" <|
    errorSatisfies mappedPrefixCollision
      (fun message => message == "duplicate declaration Provider")

  let skippedUnsafe : EDecl :=
    .ax `SkippedUnsafe [] (.const `MissingUnsafeType []) true
  let skippedPartial : EDecl :=
    .defn `SkippedPartial [] (.const `MissingPartialType []) (.const `MissingPartialValue [])
      .opaque "partial" []
  let skippedUnsafeDef : EDecl :=
    .defn `SkippedUnsafeDef [] (.const `MissingUnsafeDefType [])
      (.const `MissingUnsafeDefValue []) .opaque "unsafe" []
  let skippedDirect ← runIncremental #[skippedUnsafe, skippedPartial, skippedUnsafeDef]
  state := state.check "unsafe and partial declarations retain arena skip behavior" <|
    accepted skippedDirect.1 && skippedDirect.2 == 3

  -- Shared-prefix Phase A may retain skipped declarations for construction
  -- visibility, but only while exact kernel roots prove that no checked record
  -- can observe those extra constants.
  let (unsafeProvidersOnly, unsafeProvidersEnv) ← observeSharedPrefix
    (exportOf #[skippedUnsafe, skippedPartial, skippedUnsafeDef]) noGeneration
  state := state.check "shared source prefix retains isolated unsafe and partial providers" <|
    unsafeProvidersOnly.fallback?.isNone && unsafeProvidersOnly.metaOnlyRecords == 3 &&
      unsafeProvidersOnly.ownerSnapshots == 0 &&
      !unsafeProvidersEnv.constants.contains `SkippedUnsafe &&
      !unsafeProvidersEnv.constants.contains `SkippedPartial &&
      !unsafeProvidersEnv.constants.contains `SkippedUnsafeDef
  let unsafeConsumer : EDecl :=
    .ax `SafeUnsafeConsumer [] (.const `SkippedUnsafe []) false
  let partialConsumer : EDecl :=
    .ax `SafePartialConsumer [] (.const `SkippedPartial []) false
  let unsafeDefConsumer : EDecl :=
    .ax `SafeUnsafeDefConsumer [] (.const `SkippedUnsafeDef []) false
  let (unsafeConsumerPrefix, _) ← observeSharedPrefix
    (exportOf #[skippedUnsafe, skippedPartial, skippedUnsafeDef,
      unsafeConsumer, partialConsumer, unsafeDefConsumer]) noGeneration
  state := state.check "safe consumers of construction-only providers force fallback" <|
    unsafeConsumerPrefix.fallback?.any (fun message =>
      message.contains "depends on unchecked construction-only declaration")
  let unsafeProviderInput := exportOf #[skippedUnsafe, skippedPartial, skippedUnsafeDef]
  let ((sharedUnsafeProviders, sharedUnsafeObservation), _) ←
    runSharedPrefixDirectObserved unsafeProviderInput noGeneration
  let (directUnsafeProviders, _) ←
    runFilterDirectObserved unsafeProviderInput noGeneration
  let unsafeConsumerInput := exportOf #[skippedUnsafe, skippedPartial, skippedUnsafeDef,
    unsafeConsumer, partialConsumer, unsafeDefConsumer]
  let ((sharedUnsafeConsumers, sharedUnsafeConsumerObservation), _) ←
    runSharedPrefixDirectObserved unsafeConsumerInput noGeneration
  let (directUnsafeConsumers, _) ←
    runFilterDirectObserved unsafeConsumerInput noGeneration
  state := state.check "shared-prefix direct excludes Meta-only providers from checked roots" <|
    sharedUnsafeObservation.selected &&
      sharedUnsafeObservation.source.metaOnlyRecords == 3 &&
      sharedUnsafeObservation.ownerSnapshotsConsumed == 0 &&
      sharedUnsafeObservation.pendingOwnerSnapshotsAtSeal == 0 &&
      sameDirectResult sharedUnsafeProviders directUnsafeProviders &&
      !sharedUnsafeConsumerObservation.selected &&
      sameDirectResult sharedUnsafeConsumers directUnsafeConsumers

  let unsafeInductive ← makeUnsafeInductive `SkippedUnsafeInductive
  let (unsafeInductiveOnly, _) ← observeSharedPrefix
    (exportOf #[unsafeInductive]) noGeneration
  let unsafeInductiveConsumer : EDecl :=
    .ax `SafeUnsafeInductiveConsumer [] (.const `SkippedUnsafeInductive []) false
  let (unsafeInductiveUsed, _) ← observeSharedPrefix
    (exportOf #[unsafeInductive, unsafeInductiveConsumer]) noGeneration
  state := state.check "unsafe inductive is Meta-only and a safe consumer forces fallback" <|
    unsafeInductiveOnly.fallback?.isNone && unsafeInductiveOnly.metaOnlyRecords == 1 &&
      unsafeInductiveUsed.fallback?.isSome
  let unsafeInductiveInput := exportOf #[unsafeInductive]
  let unsafeInductiveGeneration := { noGeneration with simple := true }
  let ((sharedUnsafeInductive, sharedUnsafeInductiveObservation), _) ←
    runSharedPrefixDirectObserved unsafeInductiveInput unsafeInductiveGeneration
  let (directUnsafeInductive, _) ←
    runFilterDirectObserved unsafeInductiveInput unsafeInductiveGeneration
  unless sharedUnsafeInductiveObservation.selected &&
      sharedUnsafeInductiveObservation.source.metaOnlyRecords == 1 &&
      sharedUnsafeInductiveObservation.source.ownerSnapshots == 1 &&
      sameDirectResult sharedUnsafeInductive directUnsafeInductive do
    IO.eprintln s!"shared unsafe report={repr sharedUnsafeInductive.1}, verdict=\
      {repr sharedUnsafeInductive.2.2}, unavailable={repr sharedUnsafeInductive.2.1.unavailable?}; \
      baseline report={repr directUnsafeInductive.1}, verdict={repr directUnsafeInductive.2.2}, \
      unavailable={repr directUnsafeInductive.2.1.unavailable?}; observation=\
      {repr sharedUnsafeInductiveObservation}"
  state := state.check "generated records remain independent of a Meta-only inductive owner" <|
    sharedUnsafeInductiveObservation.selected &&
      sharedUnsafeInductiveObservation.source.metaOnlyRecords == 1 &&
      sharedUnsafeInductiveObservation.source.ownerSnapshots == 1 &&
      sameDirectResult sharedUnsafeInductive directUnsafeInductive

  let skippedPublic : Name := `SkippedAlias.Collision
  let skippedPrivate : Name :=
    (`_private.SharedPrefixSkippedAlias).mkNum 0 |>.str "SkippedAlias" |>.str "Collision"
  let aliasSkippedProviders := exportOf #[
    .ax skippedPublic [] (.sort (.succ .zero)) false,
    .ax skippedPrivate [] (.sort (.succ .zero)) true]
  let (aliasSkippedOnly, _) ← observeSharedPrefix aliasSkippedProviders noGeneration
  let aliasSkippedConsumer : EDecl :=
    .ax `SafeSkippedAliasConsumer [] (.const skippedPrivate []) false
  let (aliasSkippedUsed, _) ← observeSharedPrefix
    { aliasSkippedProviders with decls := aliasSkippedProviders.decls.push aliasSkippedConsumer }
    noGeneration
  state := state.check "alpha-aliased skipped dependency is audited in exact names" <|
    privateToUserName skippedPrivate == skippedPublic &&
      aliasSkippedOnly.fallback?.isNone && aliasSkippedOnly.metaOnlyRecords == 1 &&
      aliasSkippedUsed.fallback?.any (fun message => message.contains skippedPrivate.toString)

  let quotientSource ← readFixture root "funext_binder.ndjson"
  let (quotientPrefix, _) ← observeSharedPrefix quotientSource noGeneration
  let ((sharedQuotient, sharedQuotientObservation), _) ←
    runSharedPrefixDirectObserved quotientSource noGeneration
  let (directQuotient, _) ← runFilterDirectObserved quotientSource noGeneration
  state := state.check "atomic quotient bundle is checked and never classified Meta-only" <|
    quotientSource.decls.countP (fun declaration => declaration matches .quot ..) == 4 &&
      quotientPrefix.fallback?.isNone && quotientPrefix.metaOnlyRecords == 0 &&
      quotientPrefix.sourceRecords == quotientSource.decls.size &&
      sharedQuotientObservation.selected && sameDirectResult sharedQuotient directQuotient

  -- Phase-A failure text is only an availability reason. The ordinary batch
  -- fallback remains authoritative and therefore retains full-export
  -- preflight precedence over an earlier replay failure.
  let sharedPrecedenceInput := exportOf #[missing, malformedDuplicate]
  let (sharedPrecedence, _) ← observeSharedPrefix sharedPrecedenceInput noGeneration
  let sharedPrecedenceBatch ← runNew sharedPrecedenceInput
  state := state.check "shared-prefix unavailability defers exact failure precedence to batch" <|
    sharedPrecedence.fallback?.isSome &&
      errorSatisfies sharedPrecedenceBatch
        (fun message => message == "unknown definition safety mystery")
  let (sharedUnknownSafety, _) ← observeSharedPrefix
    (exportOf #[unknownSafety]) noGeneration
  state := state.check "shared-prefix classification rejects unknown safety explicitly" <|
    sharedUnknownSafety.fallback? == some "unknown definition safety mystery"

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
  let mut observedSharedSupport := false
  for (label, file, generation, checkRecursors) in routeMatrix do
    let input ← readFixture root file
    let (sourcePrefix, prefixEnv) ← observeSharedPrefix input generation
    let (output, report, shadow?) ← runFilterShadow input generation checkRecursors
    let ((sharedResult, sharedObservation), sharedEnv) ←
      runSharedPrefixDirectObserved input generation
    let (directResult, _) ← runFilterDirectObserved input generation
    let plannedShared ←
      runSharedPrefixPlannedObserved s!"{root}/_tmp" input generation
    let plannedCurrent ←
      runFilterDirectPlannedObserved s!"{root}/_tmp" input generation
    observedSharedSupport := observedSharedSupport ||
      sharedObservation.retainedSupportRecords > 0
    state := state.check s!"filter kernel shadow agrees for {label} generation" <|
      shadowAgrees shadow? && shadow?.any (fun shadow => output.size == shadow.finalRecords) &&
        !report.generated.isEmpty && sourcePrefix.fallback?.isNone &&
        sourcePrefix.sourceRecords == input.decls.size && sourcePrefix.ownerSnapshots > 0 &&
        input.decls.all fun declaration => declaration.names.all fun name =>
          !prefixEnv.constants.contains name
    state := state.check s!"shared-prefix direct agrees for {label} generation" <|
      sharedObservation.selected && sameDirectResult sharedResult directResult &&
        sharedObservation.retainedSupportRecords == witnessedSupportCount output report &&
        sharedObservation.ownerSnapshotsConsumed == sharedObservation.source.ownerSnapshots &&
        sharedObservation.pendingOwnerSnapshotsAtSeal == 0 &&
        sharedObservation.source.ownerSnapshots > 0 &&
        input.decls.all fun declaration => declaration.names.all fun name =>
          !sharedEnv.constants.contains name
    state := state.check s!"planned-census shared prefix agrees for {label} generation" <|
      plannedShared.retainedDeclarations == 0 && plannedShared.result.2.selected &&
        sameDirectResult plannedShared.result.1 sharedResult &&
        sameDirectResult plannedShared.result.1 plannedCurrent.result &&
        plannedShared.result.2.retainedSupportRecords ==
          sharedObservation.retainedSupportRecords &&
        plannedShared.sourceReads ==
          input.decls.size + plannedShared.result.2.source.ownerSnapshots &&
        input.decls.all fun declaration => declaration.names.all fun name =>
          !plannedShared.env.constants.contains name
  state := state.check "shared-prefix retains only witnessed cross-owner support" <|
    observedSharedSupport

  -- A late optimization failure must look like one authoritative direct run,
  -- including the global level-algebra observables that Main snapshots around
  -- its own fallback. Inject after one completed owner, then compare from the
  -- same counter baseline.
  let counterInput ← readFixture root "mutual_shapes.ndjson"
  let counterGeneration := { noGeneration with mutualModels := true }
  let savedLevelCalls ← LevelAlgebra.levelCalls.get
  let savedLevelEscapes ← LevelAlgebra.levelEscapes.get
  LevelAlgebra.levelCalls.set 0
  LevelAlgebra.levelEscapes.set 0
  let ((sharedCounterResult, sharedCounterObservation), _) ←
    runSharedPrefixDirectObserved counterInput counterGeneration (some 1)
  let sharedLevelCalls ← LevelAlgebra.levelCalls.get
  let sharedLevelEscapes ← LevelAlgebra.levelEscapes.get
  LevelAlgebra.levelCalls.set 0
  LevelAlgebra.levelEscapes.set 0
  let (directCounterResult, _) ←
    runFilterDirectObserved counterInput counterGeneration
  let directLevelCalls ← LevelAlgebra.levelCalls.get
  let directLevelEscapes ← LevelAlgebra.levelEscapes.get
  LevelAlgebra.levelCalls.set savedLevelCalls
  LevelAlgebra.levelEscapes.set savedLevelEscapes
  unless !sharedCounterObservation.selected &&
      sharedCounterObservation.fallback?.any (fun message =>
        message.contains "injected shared-prefix failure after owner 1") &&
      sameDirectResult sharedCounterResult directCounterResult &&
      sharedLevelCalls == directLevelCalls &&
      sharedLevelEscapes == directLevelEscapes && directLevelCalls > 0 do
    IO.eprintln s!"shared counter calls={sharedLevelCalls}, escapes={sharedLevelEscapes}; \
      direct calls={directLevelCalls}, escapes={directLevelEscapes}; observation=\
      {repr sharedCounterObservation}"
  state := state.check "late shared-prefix fallback restores level-algebra counters" <|
    !sharedCounterObservation.selected &&
      sharedCounterObservation.fallback?.any (fun message =>
        message.contains "injected shared-prefix failure after owner 1") &&
      sameDirectResult sharedCounterResult directCounterResult &&
      sharedLevelCalls == directLevelCalls &&
      sharedLevelEscapes == directLevelEscapes && directLevelCalls > 0
  let plannedCounter ← runSharedPrefixPlannedObserved
    s!"{root}/_tmp" counterInput counterGeneration (some 1)
  state := state.check "late planned shared-prefix fallback replays without materialization" <|
    plannedCounter.retainedDeclarations == 0 && !plannedCounter.result.2.selected &&
      plannedCounter.result.2.fallback?.any (fun message =>
        message.contains "injected shared-prefix failure after owner 1") &&
      sameDirectResult plannedCounter.result.1 directCounterResult &&
      plannedCounter.sourceReads == counterInput.decls.size * 2 + 1 &&
      counterInput.decls.all fun declaration => declaration.names.all fun name =>
        !plannedCounter.env.constants.contains name

  let declineBase ← readFixture root "nested_iota.ndjson"
  let occupiedTreeModel : EDecl :=
    .ax (Naming.modelName `Tree) [] (.sort (.succ .zero)) false
  let declineInput := { declineBase with decls := declineBase.decls.push occupiedTreeModel }
  let (declineOutput, declineReport, declineShadow?) ← runFilterShadow declineInput {}
  let (declinePrefix, _) ← observeSharedPrefix declineInput {}
  let ((sharedDecline, sharedDeclineObservation), _) ←
    runSharedPrefixDirectObserved declineInput {}
  let plannedSharedDecline ←
    runSharedPrefixPlannedObserved s!"{root}/_tmp" declineInput {}
  let (directDecline, _) ← runFilterDirectObserved declineInput {}
  state := state.check "generation declines still feed the exact source stream" <|
    shadowAgrees declineShadow? && !declineReport.declined.isEmpty &&
      declineShadow?.any (fun shadow => declineOutput.size == shadow.finalRecords) &&
      declinePrefix.fallback?.isNone && declinePrefix.ownerSnapshots > 0 &&
      sharedDeclineObservation.selected && sameDirectResult sharedDecline directDecline &&
      plannedSharedDecline.retainedDeclarations == 0 &&
      plannedSharedDecline.result.2.selected &&
      sameDirectResult plannedSharedDecline.result.1 sharedDecline &&
      plannedSharedDecline.sourceReads == declineInput.decls.size +
        plannedSharedDecline.result.2.source.ownerSnapshots &&
      sharedDeclineObservation.ownerSnapshotsConsumed ==
        sharedDeclineObservation.source.ownerSnapshots &&
      sharedDeclineObservation.pendingOwnerSnapshotsAtSeal == 0

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
  -- of a real inductive owner: the two distinct owner transitions form two
  -- generated islands whose checker aliases must remain globally injective,
  -- while each island's construction aliases still start from the same source
  -- view as the ordinary route. Require both families to cross as exact names.
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
  let (collidingPrefix, _) ← observeSharedPrefix collidingShapes collisionGeneration
  let ((sharedColliding, sharedCollidingObservation), sharedCollidingEnv) ←
    runSharedPrefixDirectObserved collidingShapes collisionGeneration
  let plannedSharedColliding ←
    runSharedPrefixPlannedObserved s!"{root}/_tmp" collidingShapes collisionGeneration
  let (directColliding, _) ←
    runFilterDirectObserved collidingShapes collisionGeneration
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
      collidingPrefix.fallback?.isNone && collidingPrefix.ownerSnapshots > 0 &&
      sharedCollidingObservation.selected &&
      sameDirectResult sharedColliding directColliding &&
      plannedSharedColliding.retainedDeclarations == 0 &&
      plannedSharedColliding.result.2.selected &&
      sameDirectResult plannedSharedColliding.result.1 sharedColliding &&
      plannedSharedColliding.sourceReads == collidingShapes.decls.size +
        plannedSharedColliding.result.2.source.ownerSnapshots &&
      sharedCollidingObservation.ownerSnapshotsConsumed ==
        sharedCollidingObservation.source.ownerSnapshots &&
      sharedCollidingObservation.pendingOwnerSnapshotsAtSeal == 0 &&
      !collidingEnv.constants.contains (Naming.modelName publicOwner) &&
      !collidingEnv.constants.contains (Naming.modelName privateOwner) &&
      !sharedCollidingEnv.constants.contains (Naming.modelName publicOwner) &&
      !sharedCollidingEnv.constants.contains (Naming.modelName privateOwner) &&
      !plannedSharedColliding.env.constants.contains (Naming.modelName publicOwner) &&
      !plannedSharedColliding.env.constants.contains (Naming.modelName privateOwner)

  let lateMalformed := mapConstructor declineBase `PT.node fun constructor =>
    { constructor with type := .sort .zero }
  let (ordinaryMalformedOutput, ordinaryMalformedReport) ← runFilterOrdinary lateMalformed {}
  let (shadowMalformedOutput, shadowMalformedReport, malformedShadow?) ←
    runFilterShadow lateMalformed {}
  let ((sharedMalformed, sharedMalformedObservation), _) ←
    runSharedPrefixDirectObserved lateMalformed {}
  let plannedSharedMalformed ←
    runSharedPrefixPlannedObserved s!"{root}/_tmp" lateMalformed {}
  let (directMalformed, _) ← runFilterDirectObserved lateMalformed {}
  state := state.check "unreplayable source preserves output/report and has no sealed shadow" <|
    ordinaryMalformedReport.unreplayable.isSome && malformedShadow?.isNone &&
      shadowMalformedOutput == ordinaryMalformedOutput &&
      shadowMalformedReport == ordinaryMalformedReport &&
      !sharedMalformedObservation.selected &&
      sameDirectResult sharedMalformed directMalformed &&
      plannedSharedMalformed.retainedDeclarations == 0 &&
      !plannedSharedMalformed.result.2.selected &&
      sameDirectResult plannedSharedMalformed.result.1 directMalformed

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
  let ((sharedFuture, sharedFutureObservation), _) ←
    runSharedPrefixDirectObserved futureInput futureGeneration
  let plannedSharedFuture ←
    runSharedPrefixPlannedObserved s!"{root}/_tmp" futureInput futureGeneration
  let (directFutureBaseline, _) ← runFilterDirectObserved futureInput futureGeneration
  let some futureShadow := futureShadow?
    | IO.eprintln "kernelchecktest: future-provider run did not seal"; return 1
  let futureFallbackOk :=
    futureShadow.usedFallback && !accepted futureShadow.streamedResult &&
      accepted futureShadow.batchResult && accepted futureShadow.result &&
      futureShadow.recordsPushed == futureShadow.finalRecords &&
      futureCompact.unavailable?.isSome && !sharedFutureObservation.selected &&
      sharedFutureObservation.fallback?.isSome &&
      sameDirectResult sharedFuture directFutureBaseline &&
      plannedSharedFuture.retainedDeclarations == 0 &&
      !plannedSharedFuture.result.2.selected &&
      sameDirectResult plannedSharedFuture.result.1 directFutureBaseline &&
      sharedFutureObservation.pendingOwnerSnapshotsAtSeal == 0
  unless futureFallbackOk do
    IO.eprintln s!"shared future verdict={repr sharedFuture.2.2}, \
      unavailable={repr sharedFuture.2.1.unavailable?}; baseline verdict=\
      {repr directFutureBaseline.2.2}, unavailable=\
      {repr directFutureBaseline.2.1.unavailable?}; observation={repr sharedFutureObservation}"
  state := state.check "future generated provider preserves the batch diagnostic fallback" <|
    futureFallbackOk

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

  -- Once the last possible construction owner has completed, independent
  -- source declarations are certified and kernel-checked without rebuilding
  -- the cumulative Meta prefix.  This is a semantic last-use boundary, not a
  -- declaration-shape shortcut: compare the complete output oracle as well as
  -- compact discard and the incremental kernel verdict.
  let exactTail : Array EDecl := (Array.range 4).map fun ordinal =>
    .ax ((`ConstructionCutoffTail).mkNum ordinal) [] (.sort (.succ .zero)) false
  let cutoffInput := { futureBase with decls := futureBase.decls ++ exactTail }
  let ((cutoffReport, cutoffPlan, cutoffVerdict?), cutoffEnv) ←
    runFilterDirectObserved cutoffInput futureGeneration
  let ((sharedCutoff, sharedCutoffObservation), sharedCutoffEnv) ←
    runSharedPrefixDirectObserved cutoffInput futureGeneration
  let plannedCutoff ←
    runFilterDirectPlannedObserved s!"{root}/_tmp" cutoffInput futureGeneration
  let (cutoffDiscardReport, cutoffDiscardPlan) ← runDiscarding cutoffInput futureGeneration
  let (cutoffOutput, cutoffOracleReport) ← runFilterOrdinary cutoffInput futureGeneration
  let cutoffBatch ← runNew { cutoffInput with decls := cutoffOutput }
  state := state.check "compact direct drops construction state before an exact-only tail" <|
    directAccepted cutoffVerdict? && accepted cutoffBatch &&
      cutoffReport == cutoffOracleReport && cutoffReport == cutoffDiscardReport &&
      sameCompactPlan cutoffPlan cutoffDiscardPlan &&
      sharedCutoffObservation.selected &&
      sameDirectResult sharedCutoff (cutoffReport, cutoffPlan, cutoffVerdict?) &&
      sharedCutoffObservation.ownerSnapshotsConsumed ==
        sharedCutoffObservation.source.ownerSnapshots &&
      sharedCutoffObservation.pendingOwnerSnapshotsAtSeal == 0 &&
      cutoffVerdict?.any (fun verdict =>
        verdict.constructionTransitions < cutoffInput.decls.size) &&
      plannedCutoff.retainedDeclarations == 0 &&
      plannedCutoff.result.1 == cutoffReport &&
      sameCompactPlan plannedCutoff.result.2.1 cutoffPlan &&
      plannedCutoff.result.2.2.any (fun verdict =>
        directAccepted (some verdict) &&
          cutoffVerdict?.any fun baseline =>
            verdict.constructionTransitions == baseline.constructionTransitions) &&
      !cutoffEnv.constants.contains `Tree &&
      !sharedCutoffEnv.constants.contains `Tree &&
      exactTail.all fun declaration => declaration.names.all fun name =>
        !cutoffEnv.constants.contains name && !sharedCutoffEnv.constants.contains name

  let simpleTailFixture ← readFixture root "prim_shapes.ndjson"
  let some (simpleTailRecord, simpleTailConstructor) :=
      simpleTailFixture.decls.findSome? fun declaration => match declaration with
        | .induct [type] (constructor :: _) _ =>
          if type.numNested == 0 then some (declaration, constructor.name) else none
        | _ => none
    | IO.eprintln "kernelchecktest: prim_shapes has no simple tail owner"; return 1
  let unreplayableTail := (mapConstructor (exportOf #[simpleTailRecord])
    simpleTailConstructor fun constructor => { constructor with type := .sort .zero }).decls[0]!
  let cutoffMalformed := { cutoffInput with decls := cutoffInput.decls.push unreplayableTail }
  let ((cutoffMalformedReport, cutoffMalformedPlan, cutoffMalformedVerdict?), _) ←
    runFilterDirectObserved cutoffMalformed futureGeneration
  let ((sharedCutoffMalformed, sharedCutoffMalformedObservation),
      sharedCutoffMalformedEnv) ←
    runSharedPrefixDirectObserved cutoffMalformed futureGeneration
  let (_, cutoffMalformedOracleReport) ←
    runFilterOrdinary cutoffMalformed futureGeneration
  unless cutoffMalformedOracleReport.unreplayable.isSome &&
      cutoffMalformedReport.unreplayable.isNone &&
      cutoffMalformedPlan.retainedGeneratedRecords == 0 &&
      cutoffMalformedVerdict?.any (fun verdict =>
        verdict.fallback?.isSome && !accepted verdict.result &&
          verdict.constructionTransitions < cutoffMalformed.decls.size) do
    IO.eprintln s!"cutoff malformed direct={repr cutoffMalformedReport}, \
      oracle={repr cutoffMalformedOracleReport}, verdict={repr cutoffMalformedVerdict?}"
  state := state.check "exact-only tail rejection requests the ordinary replay fallback" <|
    cutoffMalformedOracleReport.unreplayable.isSome &&
      cutoffMalformedReport.unreplayable.isNone &&
      cutoffMalformedPlan.retainedGeneratedRecords == 0 &&
      cutoffMalformedVerdict?.any (fun verdict =>
        verdict.fallback?.isSome && !accepted verdict.result &&
          verdict.constructionTransitions < cutoffMalformed.decls.size) &&
      !sharedCutoffMalformedObservation.selected &&
      sameDirectResult sharedCutoffMalformed
        (cutoffMalformedReport, cutoffMalformedPlan, cutoffMalformedVerdict?) &&
      cutoffMalformed.decls.all fun declaration => declaration.names.all fun name =>
        !sharedCutoffMalformedEnv.constants.contains name

  let noCandidate := exportOf #[provider, consumer]
  let ((noCandidateReport, noCandidatePlan, noCandidateVerdict?), _) ←
    runFilterDirectObserved noCandidate noGeneration
  let ((sharedNoCandidate, sharedNoCandidateObservation), _) ←
    runSharedPrefixDirectObserved noCandidate noGeneration
  let (noCandidateDiscardReport, noCandidateDiscardPlan) ←
    runDiscarding noCandidate noGeneration
  state := state.check "compact direct with no construction candidate releases at transition zero" <|
    directAccepted noCandidateVerdict? && noCandidateReport == noCandidateDiscardReport &&
      sameCompactPlan noCandidatePlan noCandidateDiscardPlan &&
      noCandidateVerdict?.any (·.constructionTransitions == 0) &&
      sharedNoCandidateObservation.selected &&
      sharedNoCandidateObservation.source.ownerSnapshots == 0 &&
      sharedNoCandidateObservation.ownerSnapshotsConsumed == 0 &&
      sharedNoCandidateObservation.pendingOwnerSnapshotsAtSeal == 0 &&
      sameDirectResult sharedNoCandidate
        (noCandidateReport, noCandidatePlan, noCandidateVerdict?)
  state := state.check "planned compact direct releases source AST and preserves input oracle" <|
    plannedDirectSuccess.retainedDeclarations == 0 &&
      reportEquals plannedDirectSuccess.inputReport (Check.checkReport futureBase) &&
      exportEquals plannedDirectSuccess.materialized futureBase &&
      plannedDirectSuccess.result.1 == directSuccessReport &&
      sameCompactPlan plannedDirectSuccess.result.2.1 directSuccessPlan &&
      directAccepted plannedDirectSuccess.result.2.2 &&
      !plannedDirectSuccess.env.constants.contains `Tree

  -- Pin the default input structural check on a genuinely modeled source,
  -- including the historical raw-order diagnostic when a model is moved
  -- behind its owner. This is the CLI's default `--check-input` oracle, not a
  -- vacuous no-family comparison.
  let (modeledDecls, _) ← runFilterOrdinary futureBase futureGeneration
  let modeledInput := { futureBase with decls := modeledDecls }
  let plannedModeled ← runFilterDirectPlannedObserved
    s!"{root}/_tmp" modeledInput noGeneration
  let modeledReport := Check.checkReport modeledInput
  state := state.check "planned default input check equals the nonempty full-source oracle" <|
    modeledReport.familiesChecked > 0 &&
      reportEquals plannedModeled.inputReport modeledReport
  let some modelOrdinal := modeledInput.decls.findIdx? fun declaration =>
      declaration.names.contains (Naming.modelName `Tree)
    | IO.eprintln "kernelchecktest: modeled Tree record is absent"; return 1
  let modelRecord := modeledInput.decls[modelOrdinal]!
  let modelAfterOwner := { modeledInput with decls :=
    (modeledInput.decls.extract 0 modelOrdinal ++
      modeledInput.decls.extract (modelOrdinal + 1) modeledInput.decls.size).push modelRecord }
  let plannedModelAfterOwner ← runFilterDirectPlannedObserved
    s!"{root}/_tmp" modelAfterOwner noGeneration
  let modelAfterOwnerReport := Check.checkReport modelAfterOwner
  state := state.check "planned default input check preserves model-after-owner diagnostics" <|
    modelAfterOwnerReport.violations.any (fun violation =>
      violation matches .modelNotBefore ..) &&
      reportEquals plannedModelAfterOwner.inputReport modelAfterOwnerReport

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
      directDeclinePlan.retainedGeneratedRecords == 0 &&
      directDecline?.any (fun verdict =>
        -- The occupied carrier makes `modelOwner` false, but the owner still
        -- reaches generation and reports `nameTaken`; it must precede cutoff.
        verdict.constructionTransitions > 0 &&
          verdict.constructionTransitions < declineInput.decls.size)

  -- Primitive-basis owners always touch construction state: canonical owners
  -- report an exemption, while malformed metadata records a decline and marks
  -- the basis invalid for every later candidate.  Both cases retain the same
  -- report and compact plan as the ordinary construction path, including a
  -- value-only tail after the final candidate.
  let basisInputBase ← readFixture root "prim_late_basis.ndjson"
  let basisInput := { basisInputBase with decls := basisInputBase.decls ++ exactTail }
  let basisGeneration := legacyGenerationConfig true
  let ((basisReport, basisPlan, basisVerdict?), _) ←
    runFilterDirectObserved basisInput basisGeneration
  let ((sharedBasis, sharedBasisObservation), _) ←
    runSharedPrefixDirectObserved basisInput basisGeneration
  let (basisDiscardReport, basisDiscardPlan) ← runDiscarding basisInput basisGeneration
  let (basisOutput, basisOracleReport) ← runFilterOrdinary basisInput basisGeneration
  let basisBatch ← runNew { basisInput with decls := basisOutput }
  state := state.check "basis exemptions precede the direct construction cutoff" <|
    directAccepted basisVerdict? && accepted basisBatch &&
      basisReport == basisOracleReport && basisReport == basisDiscardReport &&
      sameCompactPlan basisPlan basisDiscardPlan && !basisReport.exempt.isEmpty &&
      sharedBasisObservation.selected &&
      sameDirectResult sharedBasis (basisReport, basisPlan, basisVerdict?) &&
      sharedBasisObservation.ownerSnapshotsConsumed ==
        sharedBasisObservation.source.ownerSnapshots &&
      sharedBasisObservation.pendingOwnerSnapshotsAtSeal == 0 &&
      basisVerdict?.any (fun verdict =>
        verdict.constructionTransitions > 0 &&
          verdict.constructionTransitions < basisInput.decls.size)
  let malformedBasis := mapConstructor basisInput `Eq.refl fun constructor =>
    { constructor with numFields := constructor.numFields + 1 }
  let ((malformedBasisReport, malformedBasisPlan, malformedBasisVerdict?), _) ←
    runFilterDirectObserved malformedBasis basisGeneration
  let ((sharedMalformedBasis, sharedMalformedBasisObservation), _) ←
    runSharedPrefixDirectObserved malformedBasis basisGeneration
  let (malformedBasisDiscardReport, malformedBasisDiscardPlan) ←
    runDiscarding malformedBasis basisGeneration
  let (_, malformedBasisOracleReport) ← runFilterOrdinary malformedBasis basisGeneration
  let malformedBasisOk :=
    malformedBasisReport == malformedBasisOracleReport &&
      malformedBasisReport == malformedBasisDiscardReport &&
      sameCompactPlan malformedBasisPlan malformedBasisDiscardPlan &&
      malformedBasisReport.declined.any (·.1 == `Eq) &&
      malformedBasisReport.generated.isEmpty &&
      !sharedMalformedBasisObservation.selected &&
      sharedMalformedBasisObservation.fallback?.isSome &&
      sameDirectResult sharedMalformedBasis
        (malformedBasisReport, malformedBasisPlan, malformedBasisVerdict?) &&
      sharedMalformedBasisObservation.pendingOwnerSnapshotsAtSeal == 0 &&
      malformedBasisVerdict?.any (fun verdict =>
        verdict.fallback?.isSome && verdict.constructionTransitions > 0 &&
          verdict.constructionTransitions < malformedBasis.decls.size)
  unless malformedBasisOk do
    IO.eprintln s!"shared malformed basis report={repr sharedMalformedBasis.1}, \
      verdict={repr sharedMalformedBasis.2.2}, unavailable=\
      {repr sharedMalformedBasis.2.1.unavailable?}; baseline report=\
      {repr malformedBasisReport}, verdict={repr malformedBasisVerdict?}, unavailable=\
      {repr malformedBasisPlan.unavailable?}; observation=\
      {repr sharedMalformedBasisObservation}"
  state := state.check "invalid basis decline blocks later generation before exact-only tail" <|
    malformedBasisOk

  -- Unlike the metadata-corruption fallback above, these are two genuinely
  -- kernel-valid inductives. The first merely occupies the primitive Eq role
  -- with the wrong family, so Phase B must carry `invalidBasis` and suppress
  -- generation for the later otherwise-eligible owner.
  let noncanonicalEq ← makeInductiveRecord `Eq false
  let afterInvalidBasis ← makeInductiveRecord `AfterInvalidBasis false
  let validInvalidBasisInput := exportOf #[noncanonicalEq, afterInvalidBasis]
  let validInvalidBasisGeneration := { noGeneration with simple := true }
  let ((sharedValidInvalidBasis, validInvalidBasisObservation), _) ←
    runSharedPrefixDirectObserved validInvalidBasisInput validInvalidBasisGeneration
  let (directValidInvalidBasis, _) ←
    runFilterDirectObserved validInvalidBasisInput validInvalidBasisGeneration
  state := state.check "shared-prefix propagates a kernel-valid invalid basis" <|
    validInvalidBasisObservation.selected &&
      validInvalidBasisObservation.ownerSnapshotsConsumed ==
        validInvalidBasisObservation.source.ownerSnapshots &&
      validInvalidBasisObservation.pendingOwnerSnapshotsAtSeal == 0 &&
      sameDirectResult sharedValidInvalidBasis directValidInvalidBasis &&
      sharedValidInvalidBasis.1.declined.any (·.1 == `Eq) &&
      sharedValidInvalidBasis.1.generated.isEmpty

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
