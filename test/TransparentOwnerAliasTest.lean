import InductiveModels.Driver
import InductiveModels.Check
import InductiveModels.Order

namespace TransparentOwnerAliasTest

/-!
# Transparent recursive-owner aliases

Definitional reduction may identify a recursive occurrence for routing and
index recovery.  It must not rewrite the public model contract: constructor,
recursor, and iota theorem types retain the exact transparent former exported
by Lean and are checked literally both before and after NDJSON serialization.
-/

open Lean Meta InductiveModels

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def readExport (path : String) : IO Export := do
  let .ok result := parse (← IO.FS.readFile path)
    | throw <| IO.userError s!"cannot parse {path}"
  return result

def runExport (input : Export) : IO (Export × Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<transparent-owner-alias-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((declarations, report), _) ← Core.CoreM.toIO
    (MetaM.run' (runFilter input false {})) context { env }
  let output := { input with decls := declarations }
  let ordered ← match Order.reorder output with
    | .ok result => pure result
    | .error failure =>
      throw <| IO.userError s!"cannot order transparent-owner output: {repr failure}"
  return (ordered, report)

def declarationType? (input : Export) (name : Name) : Option Expr := do
  let declaration ← input.decls.find? (·.names.contains name)
  match declaration with
  | .ax got _ type _ | .quot got _ type _ => if got == name then some type else none
  | .defn got _ type .. | .thm got _ type .. | .opaq got _ type .. =>
      if got == name then some type else none
  | .induct types constructors recursors =>
      (types.find? (·.name == name)).map (·.type) <|>
      (constructors.find? (·.name == name)).map (·.type) <|>
      (recursors.find? (·.name == name)).map (·.type)

partial def containsConst (target : Name) : Expr → Bool
  | .const name _ => name == target
  | .proj _ _ value => containsConst target value
  | .app fn argument => containsConst target fn || containsConst target argument
  | .lam _ type body _ | .forallE _ type body _ =>
      containsConst target type || containsConst target body
  | .letE _ type value body _ =>
      containsConst target type || containsConst target value || containsConst target body
  | .mdata _ body => containsConst target body
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => false

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let raw ← readExport "test/fixtures/inductive-models/transparent_owner_aliases.ndjson"
  let (generated, report) ← runExport raw
  let mut state : TestState := {}

  -- `N` is the first carrier which needs the derived exact-sort lift, so it
  -- pays once for the complete seven-declaration `PSigma'`/`PUnit` support
  -- bundle. `53746e2` made that bundle the sole pair basis and removed the one
  -- ordinary `PSigma` splice, which is the one declaration every first-owner
  -- count lost; `5786e01` refreshed the same figure in the four other suites
  -- and left this one behind. The alias families and their order are unchanged.
  let expected : Array (Name × Nat) :=
    #[(`N, 15), (`AliasI, 8), (`AliasI._model._impl.skel, 6),
      (`AliasP, 16), (`Nonempty, 4), (`AliasC, 6)]
  state := state.check "generation counts pin all alias routes and support closure" <|
    report.generated == expected
  state := state.check "no transparent owner family declines" <|
    #[`AliasI, `AliasI._model._impl.skel, `AliasP, `AliasC].all fun owner =>
      !report.declined.any (·.1 == owner)
  state := state.check "all generated recursor statements match literally" <|
    report.stmtChecked == 18 && report.stmtErrors.isEmpty

  let interfaces : Array (Name × Name × Array Name) := #[
    (`AliasI, `At,
      #[Naming.modelName `AliasI.step, Naming.modelName `AliasI.rec,
        Naming.iotaName `AliasI.rec 1]),
    (`AliasP, `As,
      #[Naming.modelName `AliasP.intro, Naming.modelName `AliasP.rec,
        Naming.iotaName `AliasP.rec 0]),
    (`AliasC, `As,
      #[Naming.modelName `AliasC.step, Naming.modelName `AliasC.rec,
        Naming.iotaName `AliasC.rec 1])]
  for (owner, alias, declarations) in interfaces do
    state := state.check s!"{owner} public constructor/recursor/iota retain {alias}" <|
      declarations.all fun name =>
        (declarationType? generated name).any (containsConst alias)

  let outputCheck := Check.checkReport generated
  let reparsed ← match parse generated.render with
    | .ok result => pure result
    | .error error => throw <| IO.userError s!"cannot parse generated output: {error}"
  let inputCheck := Check.checkReport reparsed
  state := state.check "in-memory output Check covers every generated family" <|
    outputCheck.familiesChecked == 6 && outputCheck.violations.isEmpty
  state := state.check "serialized input Check preserves the exact contract" <|
    inputCheck.familiesChecked == 6 && inputCheck.violations.isEmpty

  IO.println s!"transparent owner aliases: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1

end TransparentOwnerAliasTest
