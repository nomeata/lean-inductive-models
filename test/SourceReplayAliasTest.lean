import InductiveModels.Driver

open Lean Meta InductiveModels

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def privateName (module discriminator leaf : String) : Name :=
  Name.str (Name.num (Name.str `_private module) discriminator.toNat!) leaf

def noGeneration : InductiveModels.Cli.Config :=
  { nested := false, mutualModels := false, simple := false, basic := false }

def runExportWith (input : Export) (generation : InductiveModels.Cli.Config)
    (checkRecursors : Bool := false) :
    IO (Array EDecl × Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<source-replay-alias-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (runFilter input checkRecursors generation)) context { env }
  return result

def runExport (input : Export) : IO (Array EDecl × Report) :=
  runExportWith input noGeneration

def runDiscarding (input : Export) (generation : InductiveModels.Cli.Config)
    (checkRecursors : Bool := false) : IO (Report × CompactPlan) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<source-replay-alias-discard-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run'
    (runFilterDiscarding input checkRecursors generation)) context { env }
  return result

def replayNamesVisible (input : Export) (names : Array Name) : IO (Array Bool) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<source-replay-alias-visibility-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (visible, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (do
    discard <| runFilter input false noGeneration
    let replayEnv ← getEnv
    return names.map fun name => (replayEnv.find? name).isSome)) context { env }
  return visible

def kernelChecks (input : Export) : IO Bool := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<source-replay-alias-kernel-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (typeCheckExport input)) context { env }
  return result.isOk

def typeAxiom (name : Name) : EDecl :=
  .ax name [] (.sort (.succ .zero)) false

def useAxiom (name target : Name) : EDecl :=
  .ax name [] (.const target []) false

def collisionInput (first second : Name) : Export :=
  { metaLine := .null
    decls := #[typeAxiom first, typeAxiom second,
      useAxiom `UseFirst first, useAxiom `UseSecond second] }

def aliasesOf (input : Export) : Except String SourceReplayAliases :=
  (SourceCensus.ofSource input).replayAliases

/-- Test-only prerequisite-first source variant; production never reorders
input declarations. -/
def withCompletePrerequisiteBefore (input : Export) (prerequisite owner : Name) : IO Export := do
  let some prerequisiteIndex := input.decls.findIdx? (·.names.contains prerequisite)
    | throw <| IO.userError s!"source has no {prerequisite} prerequisite"
  let some ownerIndex := input.decls.findIdx? (·.names.contains owner)
    | throw <| IO.userError s!"source has no {owner} owner"
  if prerequisiteIndex < ownerIndex then return input
  let prerequisiteRecord := input.decls[prerequisiteIndex]!
  return { input with decls :=
    input.decls.extract 0 ownerIndex ++ #[prerequisiteRecord] ++
      input.decls.extract ownerIndex prerequisiteIndex ++
      input.decls.extract (prerequisiteIndex + 1) input.decls.size }

def emptyInductiveType (name : Name) : EIndType :=
  { name, levelParams := [], type := .sort (.succ .zero), all := [name], ctors := []
    numParams := 0, numIndices := 0, numNested := 0, isRec := false
    isReflexive := false, isUnsafe := false }

def emptyRecursor (name : Name) (all : List Name) : ERec :=
  { name, levelParams := [], type := .sort (.succ .zero), all
    numParams := 0, numIndices := 0, numMotives := all.length, numMinors := 0
    rules := [], k := false, isUnsafe := false }

def declarationConstantNames : EDecl → Array Name
  | .ax name _ type _ => #[name] ++ type.getUsedConstants
  | .defn name _ type value _ _ all | .thm name _ type value all =>
    #[name] ++ all.toArray ++ type.getUsedConstants ++ value.getUsedConstants
  | .opaq name _ type value _ all =>
    #[name] ++ all.toArray ++ type.getUsedConstants ++ value.getUsedConstants
  | .quot name _ type _ => #[name] ++ type.getUsedConstants
  | .induct types constructors recursors =>
    (types.toArray.flatMap fun type =>
      #[type.name] ++ type.all.toArray ++ type.ctors.toArray ++ type.type.getUsedConstants) ++
    (constructors.toArray.flatMap fun constructor =>
      #[constructor.name, constructor.induct] ++ constructor.type.getUsedConstants) ++
    (recursors.toArray.flatMap fun recursor =>
      #[recursor.name] ++ recursor.all.toArray ++ recursor.type.getUsedConstants ++
        recursor.rules.toArray.flatMap fun rule =>
          #[rule.ctor] ++ rule.rhs.getUsedConstants)

def wrappedBox (wrapper : Name) : EDecl :=
  let owner := `AliasWrappedBox
  let ctor := `AliasWrappedBox.mk
  let type : EIndType :=
    { name := owner, levelParams := [], type := .sort (.succ .zero), all := [owner]
      ctors := [ctor], numParams := 0, numIndices := 0, numNested := 0
      isRec := false, isReflexive := false, isUnsafe := false }
  let constructor : ECtor :=
    { name := ctor, levelParams := []
      type := .forallE `value (.const wrapper []) (.const owner []) .default
      cidx := 0, numParams := 0, numFields := 1, induct := owner, isUnsafe := false }
  .induct [type] [constructor] []

def completeWrappedBox (wrapper dependency : Name) : IO EDecl := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<source-replay-alias-owner-builder>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (record, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (do
    let wrapperDecl : EDecl := .defn wrapper [] (.sort (.succ .zero))
      (.const dependency []) (.regular 0) "safe" [wrapper]
    let mut replayEnv ← getEnv
    for source in #[typeAxiom dependency, wrapperDecl] do
      let some declaration := toDeclaration replayEnv source
        | throwError "cannot reconstruct wrapped-box prerequisite"
      replayEnv ← match replayEnv.addDeclCore 0 0 declaration none true with
        | .ok next => pure next
        | .error exception =>
          throwError "wrapped-box prerequisite failed: {← (exception.toMessageData {}).toString}"
    let some declaration := toDeclaration replayEnv (wrappedBox wrapper)
      | throwError "cannot reconstruct wrapped-box owner"
    replayEnv ← match replayEnv.addDeclCore 0 0 declaration none true with
      | .ok next => pure next
      | .error exception =>
        throwError "wrapped-box owner failed: {← (exception.toMessageData {}).toString}"
    setEnv replayEnv
    let records ← toEDecls declaration
    let some record := records.find? (fun record => record matches .induct ..)
      | throwError "wrapped-box owner did not serialize as an inductive record"
    return record)) context { env }
  return record

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut state : TestState := {}
  let privateA := privateName "SourceAliasA" "0" "X"
  let privateB := privateName "SourceAliasB" "0" "X"

  let privateInput := collisionInput privateA privateB
  let .ok privateAliases := aliasesOf privateInput
    | throw <| IO.userError "cannot plan private/private source aliases"
  state := state.check "private/private keeps the earliest raw identity"
    (privateAliases.build? privateA == none && (privateAliases.build? privateB).isSome)
  let (privateOutput, privateReport) ← runExport privateInput
  state := state.check "private/private replay preserves exact source records and report"
    (privateOutput == privateInput.decls && privateReport == {})
  let some privateBuild := privateAliases.build? privateB
    | throw <| IO.userError "second private source name has no replay alias"
  state := state.check "private/private keeps both replay identities Meta-visible"
    ((← replayNamesVisible privateInput #[privateA, privateBuild]) == #[true, true])
  state := state.check "private/private exact output is kernel-valid"
    (← kernelChecks { privateInput with decls := privateOutput })

  let publicInput := collisionInput privateA `X
  let .ok publicAliases := aliasesOf publicInput
    | throw <| IO.userError "cannot plan private/public source aliases"
  state := state.check "public identity wins even when it occurs second"
    ((publicAliases.build? privateA).isSome && publicAliases.build? `X == none)
  let (publicOutput, publicReport) ← runExport publicInput
  state := state.check "private/public replay preserves exact source records and report"
    (publicOutput == publicInput.decls && publicReport == {})
  state := state.check "private/public exact output is kernel-valid"
    (← kernelChecks { publicInput with decls := publicOutput })

  let publicFirstInput := collisionInput `X privateA
  let .ok publicFirstAliases := aliasesOf publicFirstInput
    | throw <| IO.userError "cannot plan public/private source aliases"
  state := state.check "public identity also wins when it occurs first"
    ((publicFirstAliases.build? privateA).isSome && publicFirstAliases.build? `X == none)
  let (publicFirstOutput, publicFirstReport) ← runExport publicFirstInput
  state := state.check "public/private replay preserves both later references"
    (publicFirstOutput == publicFirstInput.decls && publicFirstReport == {} &&
      (← kernelChecks { publicFirstInput with decls := publicFirstOutput }))

  -- The generated-record boundary is the same exhaustive record transform as
  -- source replay, including the otherwise easy-to-miss projection type name.
  let some publicPrivateBuild := publicAliases.build? privateA
    | throw <| IO.userError "private source name has no replay alias"
  let generated : EDecl := .defn `Generated.helper [] (.const privateA [])
    (.proj privateA 0 (.const privateA [])) (.regular 0) "safe" [privateA]
  let replayGenerated := publicAliases.buildRecord generated
  state := state.check "generated records use the replay source identity"
    (match replayGenerated with
      | .defn _ _ (.const typeName _) (.proj projectionName _ (.const valueName _)) _ _ all =>
        typeName == publicPrivateBuild && projectionName == publicPrivateBuild &&
          valueName == publicPrivateBuild && all == [publicPrivateBuild]
      | _ => false)
  state := state.check "every generated-record source alias inverts exactly"
    (publicAliases.exactRecord replayGenerated == generated)
  let unregisteredBuild := Name.str publicPrivateBuild "unregistered"
  let unregisteredExact := Name.str privateA "unregistered"
  let unregisteredRecord : EDecl := .defn unregisteredBuild [] (.const unregisteredBuild [])
    (.proj unregisteredBuild 0 (.const unregisteredBuild [])) (.regular 0) "safe"
    [unregisteredBuild]
  state := state.check "release audit catches every unregistered derived build-name field"
    (publicAliases.exactRecord unregisteredRecord == unregisteredRecord &&
      publicAliases.exactDerivedRecord unregisteredRecord ==
        (.defn unregisteredExact [] (.const unregisteredExact [])
          (.proj unregisteredExact 0 (.const unregisteredExact [])) (.regular 0) "safe"
          [unregisteredExact]))

  -- The moved constant is hidden behind an unchanged transparent definition.
  -- This exercises the construction normalizer's replacement view, not just
  -- the direct expression rewrite above.
  let wrapper := `AliasWrapper
  let wrapperDecl : EDecl := .defn wrapper [] (.sort (.succ .zero))
    (.const privateA []) (.regular 0) "safe" [wrapper]
  let box ← completeWrappedBox wrapper privateA
  let generationInput : Export :=
    { metaLine := .null
      decls := #[typeAxiom privateA, typeAxiom `X, wrapperDecl, box] }
  let .ok generationAliases := aliasesOf generationInput
    | throw <| IO.userError "cannot plan transparent-wrapper source aliases"
  let some generationBuild := generationAliases.build? privateA
    | throw <| IO.userError "transparent-wrapper private name has no replay alias"
  let baseIndex := Check.SyntaxIndex.ofSource generationInput
  let replayWrapper := generationAliases.buildRecord wrapperDecl
  let .ok replayIndex := baseIndex.withReplayRecords #[wrapperDecl] #[replayWrapper]
    | throw <| IO.userError "cannot construct replay syntax replacement"
  state := state.check "transparent normalization unfolds to the replay identity"
    (replayIndex.exactNormalizer.whnf (.const wrapper []) == .const generationBuild [])
  let overrideWrapper : EDecl := .defn wrapper [] (.sort (.succ .zero))
    (.const `X []) (.regular 0) "safe" [wrapper]
  let .ok overrideIndex := baseIndex.withReplayRecords #[wrapperDecl] #[overrideWrapper]
    | throw <| IO.userError "cannot override replay normalization definition"
  state := state.check "replay definition overrides the immutable source normalizer table"
    (overrideIndex.exactNormalizer.whnf (.const wrapper []) == .const `X [])
  let erasedWrapper : EDecl := .ax wrapper [] (.sort (.succ .zero)) false
  let .ok erasedIndex := baseIndex.withReplayRecords #[wrapperDecl] #[erasedWrapper]
    | throw <| IO.userError "cannot erase replay normalization definition"
  state := state.check "replay tombstone hides an immutable source definition"
    (erasedIndex.exactNormalizer.whnf (.const wrapper []) == .const wrapper [])
  let generation := { noGeneration with simple := true }
  let (generationOutput, generationReport) ← runExportWith generationInput generation
  let generationKernelValid ← kernelChecks { generationInput with decls := generationOutput }
  let leakedBuildName := generationOutput.any fun declaration =>
    declaration.names.contains generationBuild ||
      (Order.references declaration).contains generationBuild
  state := state.check "enabled generation through an aliased wrapper succeeds exactly"
    (generationReport.generated.any (·.1 == `AliasWrappedBox) &&
      generationReport.unreplayable.isNone && generationReport.stmtErrors.isEmpty &&
      !leakedBuildName && generationKernelValid)
  -- Preserve the pre-existing collision capability: two exact inductive
  -- blocks whose complete role families normalize alike both model, while the
  -- construction-only source alias namespace remains absent from output.
  let shapesText ← IO.FS.readFile "test/fixtures/inductive-models/prim_shapes.ndjson"
  let .ok shapesRaw := InductiveModels.parse shapesText
    | throw <| IO.userError "cannot parse prim_shapes for atomic alias regression"
  let publicOwner : Name := `Sv
  let privateOwner : Name := (`_private.M).mkNum 0 |>.str "Sv"
  let shapes ← withCompletePrerequisiteBefore shapesRaw `Eq publicOwner
  let some ownerOrdinal := shapes.decls.findIdx? (·.names.contains publicOwner)
    | throw <| IO.userError "prim_shapes has no Sv owner"
  let privateRoles := shapes.decls[ownerOrdinal]!.names.foldl
    (init := Naming.AliasMap.empty) fun aliases name =>
      aliases.insert name (name.replacePrefix publicOwner privateOwner)
  let privateOwnerRecord := shapes.decls[ownerOrdinal]!.renameAliases privateRoles
  let collidingShapes := { shapes with decls := (
    shapes.decls.extract 0 (ownerOrdinal + 1) ++ #[privateOwnerRecord] ++
      shapes.decls.extract (ownerOrdinal + 1) shapes.decls.size) }
  let (collidingOutput, collidingReport) ← runExportWith collidingShapes
    (legacyGenerationConfig true) true
  let collidingExport := { collidingShapes with decls := collidingOutput }
  let collidingKernelValid ← match Order.reorder collidingExport with
    | .error _ => pure false
    | .ok ordered => kernelChecks ordered
  let leakedSourceAliases := collidingOutput.flatMap declarationConstantNames |>.filter
    fun name => name.components.any fun component =>
      component.toString.startsWith "_inductive_models_source_alias_"
  state := state.check "public and private normalized-colliding inductives both model exactly"
    (collidingReport.generated.any (·.1 == publicOwner) &&
      collidingReport.generated.any (·.1 == privateOwner) &&
      collidingReport.stmtErrors.isEmpty && collidingKernelValid &&
      collidingOutput.any (·.names.contains (Naming.modelName privateOwner)) &&
      leakedSourceAliases.isEmpty)
  let (collidingDiscardReport, collidingCompact) ← runDiscarding collidingShapes
    (legacyGenerationConfig true) true
  state := state.check "compact discard preserves the colliding-inductive exact oracle"
    (collidingDiscardReport == collidingReport &&
      collidingCompact.retainedGeneratedRecords == 0 &&
      collidingCompact.checkReport == Check.checkReport collidingExport)

  let some privateMember := privateOwnerRecord.names.find? (· != privateOwner)
    | throw <| IO.userError "private Sv block has no member model slot"
  let reservedPrivateModel := Naming.modelName privateMember
  unless collidingOutput.any (·.names.contains reservedPrivateModel) do
    throw <| IO.userError "private Sv member model slot was not generated"
  let reservedPublicModel := reservedPrivateModel.replacePrefix privateOwner publicOwner
  let reservedShapes := { collidingShapes with decls := (
    collidingShapes.decls.extract 0 (ownerOrdinal + 1) ++
      #[typeAxiom reservedPublicModel, typeAxiom reservedPrivateModel] ++
      collidingShapes.decls.extract (ownerOrdinal + 1) collidingShapes.decls.size) }
  let (reservedOutput, reservedReport) ← runExportWith reservedShapes
    (legacyGenerationConfig true) true
  let reservedLeaks := reservedOutput.flatMap declarationConstantNames |>.filter fun name =>
    name.components.any fun component =>
      component.toString.startsWith "_inductive_models_source_alias_"
  state := state.check "exact reserved private carrier blocks its build descendant"
    (!reservedReport.generated.any (fun (name, _) =>
        name == publicOwner || name == privateOwner) &&
      reservedReport.declined.any (fun (name, reason) =>
        name == privateOwner && reason.contains "model name taken") &&
      (reservedOutput.filter (·.names.contains reservedPrivateModel)).size == 1 &&
      (reservedOutput.filter (·.names.contains reservedPublicModel)).size == 1 &&
      reservedLeaks.isEmpty &&
      !reservedReport.declined.any fun (_, reason) =>
        reason.contains "_inductive_models_source_alias_")

  let atomicInput : Export :=
    { metaLine := .null
      decls := #[.induct
        [{ (emptyInductiveType privateA) with all := [privateA, privateB] },
         { (emptyInductiveType privateB) with all := [privateA, privateB] }] [] []] }
  let (atomicOutput, atomicReport) ← runExport atomicInput
  let .ok atomicAliases := aliasesOf atomicInput
    | throw <| IO.userError "cannot plan atomic inductive aliases"
  let some atomicBuild := atomicAliases.build? privateB
    | throw <| IO.userError "second atomic inductive has no replay alias"
  state := state.check "one atomic inductive collision replays both identities exactly"
    (atomicOutput == atomicInput.decls && atomicReport == {} &&
      (← replayNamesVisible atomicInput #[privateA, atomicBuild]) == #[true, true])

  -- A constructor is an explicit inductDecl input, unlike a recursor. It may
  -- move independently while its owner and kernel-derived recursor stay exact.
  let publicCtor := `SharedCtor
  let privateCtor : Name := (`_private.SourceAliasCtor).mkNum 0 |>.str "SharedCtor"
  let ctorAliases := Naming.AliasMap.empty.insert `AliasWrappedBox.mk privateCtor
  let ctorOwner := box.renameAliases ctorAliases
  let ctorInput : Export :=
    { metaLine := .null
      decls := #[typeAxiom privateA, wrapperDecl, typeAxiom publicCtor, ctorOwner] }
  let (ctorOutput, ctorReport) ← runExportWith ctorInput noGeneration true
  let ctorKernelValid ← match Order.reorder { ctorInput with decls := ctorOutput } with
    | .error _ => pure false
    | .ok ordered => kernelChecks ordered
  state := state.check "constructor-only normalized collision preserves its exact owner"
    (ctorOutput == ctorInput.decls && ctorReport.recMismatch.isEmpty && ctorKernelValid &&
      ctorOutput.any (·.names.contains privateCtor) &&
      !(ctorOutput.flatMap declarationConstantNames).any fun name =>
        name.components.any fun component =>
          component.toString.startsWith "_inductive_models_source_alias_")

  let mutualText ← IO.FS.readFile "test/fixtures/inductive-models/prim_late_basis.ndjson"
  let .ok mutualSource := InductiveModels.parse mutualText
    | throw <| IO.userError "cannot parse mutual alias fixture"
  let some mutualOrdinal := mutualSource.decls.findIdx? (fun declaration =>
    match declaration with
    | .induct types _ _ => types.length > 1 && !types.any (·.numNested > 0)
    | _ => false)
    | throw <| IO.userError "mutual alias fixture has no mutual block"
  let mutualBlock := mutualSource.decls[mutualOrdinal]!
  let privateMutualRoot : Name := (`_private.SourceAliasMutual).mkNum 0
  let mutualAliases := mutualBlock.names.foldl (init := Naming.AliasMap.empty)
    fun aliases name => aliases.insert name (privateMutualRoot ++ name)
  let privateMutualBlock := mutualBlock.renameAliases mutualAliases
  let mutualInput := { mutualSource with decls := (
    mutualSource.decls.extract 0 (mutualOrdinal + 1) ++ #[privateMutualBlock] ++
      mutualSource.decls.extract (mutualOrdinal + 1) mutualSource.decls.size) }
  let (mutualOutput, mutualReport) ← runExportWith mutualInput noGeneration true
  let mutualKernelValid ← match Order.reorder { mutualInput with decls := mutualOutput } with
    | .error _ => pure false
    | .ok ordered => kernelChecks ordered
  let some publicMutualOwner := mutualBlock.names.head?
    | throw <| IO.userError "mutual block has no owner"
  let privateMutualOwner := privateMutualRoot ++ publicMutualOwner
  state := state.check "mutual normalized collision replays every recursor role exactly"
    (mutualOutput == mutualInput.decls && mutualReport.recMismatch.isEmpty &&
      mutualKernelValid && mutualOutput.any (·.names.contains privateMutualOwner))

  -- Longest owner selection is over every member, not only moved members.
  -- Otherwise moving `A` would incorrectly capture the unmoved `A.B.rec`.
  let overlapShort := privateName "SourceAliasOverlap" "0" "OverlapRoot"
  let overlapLong := Name.str overlapShort "B"
  let overlapShortRec := Name.str overlapShort "rec"
  let overlapLongRec := Name.str overlapLong "rec"
  let overlapAll := [overlapShort, overlapLong]
  let overlapBlock : EDecl := .induct
    [{ (emptyInductiveType overlapShort) with all := overlapAll },
     { (emptyInductiveType overlapLong) with all := overlapAll }]
    [] [emptyRecursor overlapShortRec overlapAll, emptyRecursor overlapLongRec overlapAll]
  let overlapInput : Export :=
    { metaLine := .null, decls := #[typeAxiom `OverlapRoot, overlapBlock] }
  let .ok overlapPlanned := aliasesOf overlapInput
    | throw <| IO.userError "cannot plan overlapping owner aliases"
  let overlapRoles := (SourceCensus.ofSource overlapInput).replayRoles
  let .ok overlapAliases := sourceReplayInductiveDerivations overlapRoles overlapPlanned
    | throw <| IO.userError "cannot derive overlapping owner recursor aliases"
  let some overlapShortBuild := overlapAliases.build? overlapShort
    | throw <| IO.userError "short overlapping owner did not move"
  state := state.check "overlapping recursor belongs to the longest exact owner"
    (overlapAliases.build? overlapShortRec ==
        some (overlapShortRec.replacePrefix overlapShort overlapShortBuild) &&
      overlapAliases.build? overlapLong == none &&
      overlapAliases.build? overlapLongRec == none)

  let duplicateInput : Export :=
    { metaLine := .null, decls := #[typeAxiom `ExactDuplicate, typeAxiom `ExactDuplicate] }
  let duplicateRejected ← try
    discard <| runExport duplicateInput
    pure false
  catch error =>
    pure <| (toString error).contains "duplicate source declaration name ExactDuplicate"
  state := state.check "genuine exact duplicates are rejected rather than aliased"
    duplicateRejected
  let atomicDuplicateInput : Export :=
    { metaLine := .null
      decls := #[.induct
        [emptyInductiveType `AtomicDuplicate, emptyInductiveType `AtomicDuplicate] [] []] }
  state := state.check "same-record exact duplicates are rejected by the census"
    (match aliasesOf atomicDuplicateInput with
      | .error message => message.contains "duplicate source declaration name AtomicDuplicate"
      | .ok _ => false)

  -- Occupying salt zero forces the bounded deterministic root search to use
  -- another spelling without changing the chosen class survivor.
  let root0 := Name.str .anonymous "_inductive_models_source_alias_0"
  let root1 := Name.str .anonymous "_inductive_models_source_alias_1"
  let occupied := Name.str root0 "taken"
  let saltedInput := { privateInput with decls := privateInput.decls.push (typeAxiom occupied) }
  let .ok saltedAliases := aliasesOf saltedInput
    | throw <| IO.userError "cannot plan salted source alias"
  state := state.check "reserved source spelling deterministically advances alias salt"
    ((saltedAliases.build? privateB).any fun build =>
      root1.isPrefixOf build)

  IO.println s!"source replay aliases: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1
