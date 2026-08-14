import InductiveModels.Driver

set_option maxRecDepth 8192

/-!
# Kernel-check regression tests

The batch checker is the input-only kernel gate. Generated output is checked
directly at each accepted model-island boundary when `typeCheckOutput` is set.
-/

open Lean Meta InductiveModels

namespace InductiveModels.KernelCheck.Tests

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def accepted : Except String Unit → Bool
  | .ok () => true
  | .error _ => false

def errorSatisfies (result : Except String Unit) (predicate : String → Bool) : Bool :=
  match result with
  | .error message => predicate message
  | .ok () => false

def exportOf (decls : Array EDecl) : Export := { metaLine := .null, decls }

def runMeta (action : MetaM (Except String Unit)) : IO (Except String Unit) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<kernel-check-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' action) context { env }
  return result

def runCheck (x : Export) : IO (Except String Unit) :=
  runMeta (typeCheckExport x)

def metadataFailureInstalls (x : Export) (name : Name) : IO Bool := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<kernel-check-metadata-state-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let action : MetaM Bool := do
    let result ← typeCheckExport x
    return !accepted result && (← getEnv).constants.contains name
  return (← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' action) context { env }).1

def corruptFirstRecursor (x : Export) : Option Export := do
  let index ← x.decls.findIdx? fun declaration => match declaration with
    | .induct _ _ (_ :: _) => true
    | _ => false
  let .induct types constructors (recursor :: recursors) := x.decls[index]! | none
  let corrupted := .induct types constructors
    ({ recursor with numMinors := recursor.numMinors + 1 } :: recursors)
  return { x with decls := x.decls.set! index corrupted }

def corruptGeneratedProof : EDecl → EDecl
  | .thm name levels type _ all =>
    .thm name levels type (.const `DefinitelyMissingGeneratedDependency []) all
  | declaration => declaration

def runFilterWithGeneratedCorruption (x : Export) (typeCheckOutput : Bool) :
    IO (Array EDecl × Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<generated-kernel-flag-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let generation : Cli.Config :=
    { nested := true, mutualModels := false, simple := false, basic := false,
      typeCheckOutput }
  return (← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run'
    (runFilterWithExactBlockTransform x false generation corruptGeneratedProof))
    context { env }).1

def makeUnsafeInductive (name : Name) : IO EDecl := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<unsafe-inductive-kernel-fixture>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let declaration : Declaration := .inductDecl [] 0
    [{ name, type := .sort (.succ .zero),
       ctors := [{ name := Name.str name "mk", type := .const name [] }] }] true
  return (← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (do
    match (← getEnv).addDeclCore 0 declaration none false with
    | .error exception => throwError (exception.toMessageData {})
    | .ok next =>
      setEnv next
      indEDecl #[name])) context { env }).1

def readFixture (root file : String) : IO Export := do
  let text ← IO.FS.readFile s!"{root}/test/fixtures/inductive-models/{file}"
  let .ok parsed := InductiveModels.parse text
    | throw <| IO.userError s!"kernelchecktest: cannot parse {file}"
  return parsed

def run (root : String) : IO UInt32 := do
  let mut state : TestState := {}

  let provider : EDecl := .ax `Provider [] (.sort (.succ .zero)) false
  let consumer : EDecl := .ax `Consumer [] (.const `Provider []) false
  state := state.check "batch replay accepts valid reversed dependencies" <|
    accepted (← runCheck (exportOf #[consumer, provider]))

  let publicName : Name := `Collision.foo
  let privateName : Name := (`_private.KernelCheck).mkNum 0 |>.str "Collision" |>.str "foo"
  state := state.check "exact kernel replay accepts normalized-private collisions" <|
    privateToUserName privateName == publicName && accepted (← runCheck <| exportOf #[
      .ax publicName [] (.sort (.succ .zero)) false,
      .ax privateName [] (.sort (.succ .zero)) false])

  let fixture ← readFixture root "nested_iota.ndjson"
  let generatedCheckOff ← runFilterWithGeneratedCorruption fixture false
  let generatedCheckOn ← runFilterWithGeneratedCorruption fixture true
  state := state.check "generated kernel flag gates only exact emitted island records" <|
    !generatedCheckOff.1.isEmpty && generatedCheckOff.2.outputKernelChecks == 0 &&
      generatedCheckOff.2.outputKernelRejected.isNone &&
      generatedCheckOn.2.outputKernelChecks > 0 &&
      generatedCheckOn.2.outputKernelRejected.any
        (fun message => message.contains "DefinitelyMissingGeneratedDependency")

  let some malformedMetadata := corruptFirstRecursor fixture
    | IO.eprintln "kernelchecktest: fixture has no recursor"; return 1
  let metadataResult ← runCheck malformedMetadata
  state := state.check "malformed regenerated metadata is rejected exactly" <|
    errorSatisfies metadataResult (fun message => message.contains "recursor numMinors differs")
  let malformedOwner? := malformedMetadata.decls.findSome? fun declaration => match declaration with
    | .induct (type :: _) _ _ => some type.name
    | _ => none
  state := state.check "metadata rejection preserves the checked Meta environment" <|
    ← malformedOwner?.elim (pure false) (metadataFailureInstalls malformedMetadata)

  let missing : EDecl := .ax `LateFailure [] (.const `DefinitelyMissing []) false
  let metadataThenReplayFailure :=
    { malformedMetadata with decls := malformedMetadata.decls.push missing }
  state := state.check "kernel insertion failure precedes metadata mismatch" <|
    errorSatisfies (← runCheck metadataThenReplayFailure) fun message =>
      message.contains "DefinitelyMissing" && !message.contains "numMinors differs"

  state := state.check "duplicate preflight precedes kernel replay" <|
    errorSatisfies (← runCheck <| exportOf #[missing, provider, provider]) fun message =>
      message.contains "duplicate declaration Provider" && !message.contains "DefinitelyMissing"

  let unknownSafety : EDecl :=
    .defn `UnknownSafety [] (.sort (.succ .zero)) (.sort .zero) .opaque "mystery" []
  state := state.check "unknown definition safety is rejected" <|
    errorSatisfies (← runCheck <| exportOf #[unknownSafety])
      (fun message => message == "unknown definition safety mystery")
  let malformedDuplicate : EDecl :=
    .defn `Provider [] (.sort (.succ .zero)) (.sort .zero) .opaque "mystery" []
  state := state.check "malformed safety precedes same-record duplicate" <|
    errorSatisfies (← runCheck <| exportOf #[provider, malformedDuplicate])
      (fun message => message == "unknown definition safety mystery")
  let malformedQuotient : EDecl := .quot `Provider [] (.sort (.succ .zero)) "mystery"
  state := state.check "malformed quotient kind precedes same-record duplicate" <|
    errorSatisfies (← runCheck <| exportOf #[provider, malformedQuotient])
      (fun message => message == "unknown quotient kind mystery")

  let skippedUnsafe : EDecl := .ax `SkippedUnsafe [] (.const `MissingUnsafeType []) true
  let skippedPartial : EDecl :=
    .defn `SkippedPartial [] (.const `MissingPartialType []) (.const `MissingPartialValue [])
      .opaque "partial" []
  let skippedUnsafeDef : EDecl :=
    .defn `SkippedUnsafeDef [] (.const `MissingUnsafeDefType [])
      (.const `MissingUnsafeDefValue []) .opaque "unsafe" []
  state := state.check "unsafe and partial declarations retain input skip behavior" <|
    accepted (← runCheck <| exportOf #[skippedUnsafe, skippedPartial, skippedUnsafeDef])
  let unsafeConsumer : EDecl :=
    .ax `SafeUnsafeConsumer [] (.const `SkippedUnsafe []) false
  state := state.check "safe consumers cannot use skipped unsafe input" <|
    errorSatisfies (← runCheck <| exportOf #[skippedUnsafe, unsafeConsumer])
      (fun message => message.contains "unknown constant 'SkippedUnsafe'")

  let unsafeInductive ← makeUnsafeInductive `SkippedUnsafeInductive
  state := state.check "unsafe inductive input is skipped" <|
    accepted (← runCheck <| exportOf #[unsafeInductive])
  let unsafeInductiveConsumer : EDecl :=
    .ax `SafeUnsafeInductiveConsumer [] (.const `SkippedUnsafeInductive []) false
  state := state.check "safe consumers cannot use skipped unsafe inductives" <|
    !accepted (← runCheck <| exportOf #[unsafeInductive, unsafeInductiveConsumer])

  let quotientSource ← readFixture root "funext_binder.ndjson"
  state := state.check "atomic quotient bundle remains input-checkable" <|
    quotientSource.decls.countP (fun declaration => declaration matches .quot ..) == 4 &&
      accepted (← runCheck quotientSource)

  let emptyInductive : EDecl := .induct [] [] []
  state := state.check "empty active inductive record is rejected" <|
    errorSatisfies (← runCheck <| exportOf #[emptyInductive])
      (fun message => message == "empty inductive declaration")

  let cycle := exportOf #[
    .ax `CycleA [] (.const `CycleB []) false,
    .ax `CycleB [] (.const `CycleA []) false]
  state := state.check "input dependency cycle is rejected before insertion" <|
    errorSatisfies (← runCheck cycle)
      (fun message => message.contains "cyclic kernel declaration dependencies")

  let duplicateType : EIndType :=
    { name := `DuplicateMember, levelParams := [], type := .sort (.succ .zero)
      all := [`DuplicateMember], ctors := [], numParams := 0, numIndices := 0
      numNested := 0, isRec := false, isReflexive := false, isUnsafe := false }
  state := state.check "duplicate names inside one inductive record are preflight errors" <|
    errorSatisfies (← runCheck <| exportOf #[.induct [duplicateType, duplicateType] [] []])
      (fun message => message == "duplicate declaration DuplicateMember")

  if state.failed.isEmpty then
    IO.println s!"kernel check: {state.passed}/{state.passed} passed"
    return 0
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  IO.eprintln s!"kernel check: {state.passed}/{state.passed + state.failed.size} passed"
  return 1

end InductiveModels.KernelCheck.Tests

def main (args : List String) : IO UInt32 :=
  InductiveModels.KernelCheck.Tests.run (args.head?.getD ".")
