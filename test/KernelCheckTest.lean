import InductiveModels.Driver

set_option maxRecDepth 8192

/-!
# Incremental kernel-check regression tests

The old whole-export implementation remains temporarily exposed as an oracle
while `KernelCheck.State` is established.  These tests compare exact verdicts
at the behavior-sensitive boundaries, and exercise direct state feeding
without passing through an export writer or parser intermediate.
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

def runLegacy (x : Export) : IO (Except String Unit) :=
  runMeta (typeCheckExportLegacyOracle x)

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
  let reorderedLegacy ← runLegacy reordered
  state := state.check "batch replay accepts valid reversed dependencies" <|
    accepted reorderedNew && sameResult reorderedNew reorderedLegacy

  let directForward ← runIncremental #[provider, consumer]
  state := state.check "incremental state accepts an already valid schedule" <|
    accepted directForward.1 && directForward.2 == 2
  let directBackward ← runIncremental #[consumer, provider]
  state := state.check "incremental state rejects a backward schedule but counts every push" <|
    !accepted directBackward.1 && directBackward.2 == 2

  -- `Kernel.Environment` retains exact private identities even when
  -- `Lean.Environment`'s async lookup normalizes them to the same spelling.
  let publicName : Name := `Collision.foo
  let privateName : Name := (`_private.KernelCheck).mkNum 0 |>.str "Collision" |>.str "foo"
  let collision := exportOf #[
    .ax publicName [] (.sort (.succ .zero)) false,
    .ax privateName [] (.sort (.succ .zero)) false]
  let collisionNew ← runNew collision
  let collisionLegacy ← runLegacy collision
  let collisionDirect ← runIncremental collision.decls
  state := state.check "exact kernel state accepts normalized-private collisions" <|
    privateToUserName privateName == publicName && accepted collisionNew &&
      sameResult collisionNew collisionLegacy && accepted collisionDirect.1 &&
      collisionDirect.2 == 2

  let fixturePath := s!"{root}/test/fixtures/inductive-models/nested_iota.ndjson"
  let fixtureText ← IO.FS.readFile fixturePath
  let .ok fixture := InductiveModels.parse fixtureText (analyse := false)
    | IO.eprintln "kernelchecktest: fixture parse failed"; return 1
  let some malformedMetadata := corruptFirstRecursor fixture
    | IO.eprintln "kernelchecktest: fixture has no recursor"; return 1
  let metadataNew ← runNew malformedMetadata
  let metadataLegacy ← runLegacy malformedMetadata
  state := state.check "malformed regenerated metadata has the legacy exact verdict" <|
    !accepted metadataNew && sameResult metadataNew metadataLegacy &&
      errorSatisfies metadataNew (fun message => message.contains "recursor numMinors differs")

  -- Kernel insertion failure precedes metadata diagnostics even when the bad
  -- metadata was observed first.  State must keep checking after metadata
  -- observation, while a replay failure makes its final verdict dominant.
  let missing : EDecl := .ax `LateFailure [] (.const `DefinitelyMissing []) false
  let metadataThenReplayFailure :=
    { malformedMetadata with decls := malformedMetadata.decls.push missing }
  let precedenceNew ← runNew metadataThenReplayFailure
  let precedenceLegacy ← runLegacy metadataThenReplayFailure
  let precedenceDirect ← runIncremental metadataThenReplayFailure.decls
  state := state.check "kernel insertion failure retains precedence over earlier metadata mismatch" <|
    !accepted precedenceNew && sameResult precedenceNew precedenceLegacy &&
      sameResult precedenceDirect.1 precedenceNew &&
      errorSatisfies precedenceNew (fun message =>
        message.contains "DefinitelyMissing" && !message.contains "numMinors differs")

  -- The batch preflight occurs before replay, so duplicate exact declaration
  -- data dominates a separate earlier kernel failure exactly as before.
  let duplicatePreflight := exportOf #[missing, provider, provider]
  let duplicateNew ← runNew duplicatePreflight
  let duplicateLegacy ← runLegacy duplicatePreflight
  let duplicateDirect ← runIncremental duplicatePreflight.decls
  state := state.check "batch duplicate preflight retains precedence over kernel replay" <|
    !accepted duplicateNew && sameResult duplicateNew duplicateLegacy &&
      sameResult duplicateDirect.1 duplicateNew && duplicateDirect.2 == 3 &&
      errorSatisfies duplicateNew (fun message =>
        message.contains "duplicate declaration Provider" &&
          !message.contains "DefinitelyMissing")

  let unknownSafety : EDecl :=
    .defn `UnknownSafety [] (.sort (.succ .zero)) (.sort .zero) .opaque "mystery" []
  let unknownDirect ← runIncremental #[unknownSafety]
  state := state.check "incremental preflight rejects unknown definition safety" <|
    unknownDirect.2 == 1 && errorSatisfies unknownDirect.1
      (fun message => message == "unknown definition safety mystery")

  if state.failed.isEmpty then
    IO.println s!"kernel check: {state.passed}/{state.passed} passed"
    return 0
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  IO.eprintln s!"kernel check: {state.passed}/{state.passed + state.failed.size} passed"
  return 1

end InductiveModels.KernelCheck.Tests

def main (args : List String) : IO UInt32 :=
  InductiveModels.KernelCheck.Tests.run (args.head?.getD ".")
