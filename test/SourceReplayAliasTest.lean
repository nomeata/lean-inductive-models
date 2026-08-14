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

def runExportWith (input : Export) (generation : InductiveModels.Cli.Config) :
    IO (Array EDecl × Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<source-replay-alias-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (runFilter input false generation)) context { env }
  return result

def runExport (input : Export) : IO (Array EDecl × Report) :=
  runExportWith input noGeneration

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

def emptyInductiveType (name : Name) : EIndType :=
  { name, levelParams := [], type := .sort (.succ .zero), all := [name], ctors := []
    numParams := 0, numIndices := 0, numNested := 0, isRec := false
    isReflexive := false, isUnsafe := false }

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
      replayEnv ← match replayEnv.addDeclCore 0 declaration none true with
        | .ok next => pure next
        | .error exception =>
          throwError "wrapped-box prerequisite failed: {← (exception.toMessageData {}).toString}"
    let some declaration := toDeclaration replayEnv (wrappedBox wrapper)
      | throwError "cannot reconstruct wrapped-box owner"
    replayEnv ← match replayEnv.addDeclCore 0 declaration none true with
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
  let (generationOutput, generationReport) ← runExportWith generationInput
    { noGeneration with simple := true }
  let leakedBuildName := generationOutput.any fun declaration =>
    declaration.names.contains generationBuild ||
      (Order.references declaration).contains generationBuild
  state := state.check "enabled generation through an aliased wrapper succeeds exactly"
    (generationReport.generated.any (·.1 == `AliasWrappedBox) &&
      generationReport.unreplayable.isNone && generationReport.stmtErrors.isEmpty &&
      !leakedBuildName)

  let atomicInput : Export :=
    { metaLine := .null
      decls := #[.induct [emptyInductiveType privateA, emptyInductiveType privateB] [] []] }
  let atomicRejected ← try
    discard <| runExport atomicInput
    pure false
  catch error =>
    pure <| (toString error).contains "collision moves inductive role"
  state := state.check "one atomic inductive collision fails closed before replay" atomicRejected

  let duplicateInput : Export :=
    { metaLine := .null, decls := #[typeAxiom `ExactDuplicate, typeAxiom `ExactDuplicate] }
  let duplicateRejected ← try
    discard <| runExport duplicateInput
    pure false
  catch error =>
    pure <| (toString error).contains "duplicate source declaration name ExactDuplicate"
  state := state.check "genuine exact duplicates are rejected rather than aliased"
    duplicateRejected

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
