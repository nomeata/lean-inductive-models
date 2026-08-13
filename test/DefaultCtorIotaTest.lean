import InductiveModels.Driver
import InductiveModels.Order

/-!
# Default-parameter recursor-iota syntax regression

`DefaultCtor.synthetic` mirrors `Lean.SourceInfo.synthetic`: its last source
constructor binder is an `optParam`, while Lean's generated recursor minor
premise exposes the reduced field domain. This test records all three exact
faces at that boundary: the serialized generated theorem, the statement
checker's reconstruction, and the type stored after kernel replay.
-/

open Lean Meta InductiveModels

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def declarationType? (x : Export) (name : Name) : Option (List Name × Expr) :=
  x.decls.findSome? fun declaration => match declaration with
    | .ax got params type _ | .quot got params type _ =>
      if got == name then some (params, type) else none
    | .defn got params type .. | .thm got params type .. | .opaq got params type .. =>
      if got == name then some (params, type) else none
    | .induct types constructors recursors =>
      (types.find? (·.name == name)).map (fun type => (type.levelParams, type.type)) <|>
      (constructors.find? (·.name == name)).map (fun constructor =>
        (constructor.levelParams, constructor.type)) <|>
      (recursors.find? (·.name == name)).map (fun recursor =>
        (recursor.levelParams, recursor.type))

private def firstDifference? (actual expected : Expr) (path : String := "root") : Option String :=
  if actual == expected then none else
  match actual, expected with
  | .forallE an ad ab ai, .forallE en ed eb ei =>
      if an != en then some s!"{path}.forall.name: actual={an}, expected={en}"
      else if ai != ei then some s!"{path}.forall.info: actual={repr ai}, expected={repr ei}"
      else firstDifference? ad ed s!"{path}.forall.domain" <|>
        firstDifference? ab eb s!"{path}.forall.body"
  | .lam an ad ab ai, .lam en ed eb ei =>
      if an != en then some s!"{path}.lam.name: actual={an}, expected={en}"
      else if ai != ei then some s!"{path}.lam.info: actual={repr ai}, expected={repr ei}"
      else firstDifference? ad ed s!"{path}.lam.domain" <|>
        firstDifference? ab eb s!"{path}.lam.body"
  | .app af aa, .app ef ea =>
      firstDifference? af ef s!"{path}.app.fn" <|>
        firstDifference? aa ea s!"{path}.app.arg"
  | .letE an aty av ab aNonDep, .letE en ety ev eb eNonDep =>
      if an != en then some s!"{path}.let.name: actual={an}, expected={en}"
      else if aNonDep != eNonDep then
        some s!"{path}.let.nonDep: actual={aNonDep}, expected={eNonDep}"
      else firstDifference? aty ety s!"{path}.let.type" <|>
        firstDifference? av ev s!"{path}.let.value" <|>
        firstDifference? ab eb s!"{path}.let.body"
  | .proj aType ai av, .proj eType ei ev =>
      if aType != eType || ai != ei then
        some s!"{path}.proj: actual={aType}.{ai}, expected={eType}.{ei}"
      else firstDifference? av ev s!"{path}.proj.value"
  | _, _ => some s!"{path}: actual={repr actual}, expected={repr expected}"

structure Evidence where
  report : Report
  actual : Expr
  expected : Expr
  kernel : Expr
  actualPretty : String
  expectedPretty : String
  kernelPretty : String
  difference : String
  ownerFreeAccepted : Bool

def collectEvidence (path : String) : IO Evidence := do
  let .ok input := InductiveModels.parse (← IO.FS.readFile path) (analyse := false)
    | throw <| IO.userError s!"cannot parse {path}"
  let base ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<default-ctor-iota-test>"
      fileMap := default
      maxHeartbeats := 0
      maxRecDepth := 8192 }
  let action : MetaM Evidence := do
    let (declarations, report) ← runFilter input false
      { nested := false, mutualModels := false, simple := true, basic := false }
    let generated : Export := { input with decls := declarations }
    let ordered ← match Order.reorder generated with
      | .ok ordered => pure ordered
      | .error error => throwError "cannot order generated fixture: {repr error}"
    let iotaName := Naming.iotaName `DefaultCtor.rec 1
    let some (modelParams, actual) := declarationType? ordered iotaName
      | throwError "generated fixture has no {iotaName}"
    let some family := Check.discover ordered |>.find? (·.owner == `DefaultCtor)
      | throwError "generated fixture has no DefaultCtor correspondence"
    let some iota := family.correspondence.iotas.find? (·.name == iotaName)
      | throwError "DefaultCtor correspondence has no second recursor rule"
    let some (ownerParams, ownerType) :=
        Check.iotaProposition? ordered family.ownerDecl iota.recursor iota.ruleIndex
      | throwError "checker could not reconstruct DefaultCtor's second iota proposition"
    let expected := family.correspondence.expectedIotaType ownerParams modelParams ownerType

    -- Replay exactly the source prefix available before the owner, then ask
    -- the production owner-free gate to check only generated records. This
    -- pins that the syntax repair did not merely satisfy the correspondence
    -- checker while weakening the kernel boundary.
    let inputNames := input.decls.foldl (init := ({} : Std.HashSet Name)) fun names declaration =>
      declaration.names.foldl (·.insert ·) names
    let generatedRecords := ordered.decls.filter fun declaration =>
      declaration.names.any fun name => !inputNames.contains name
    let mut sourceBase := base
    for declaration in input.decls do
      unless declaration.names.contains `DefaultCtor do
        if let some replay := toDeclaration sourceBase declaration then
          match sourceBase.addDeclCore 0 replay none false with
          | .ok next => sourceBase := next
          | .error exception =>
            throwError "source-prefix replay rejected {declaration.names}: {
              ← (exception.toMessageData {}).toString}"
    let ownerFreeAccepted := match ← checkGeneratedIn sourceBase generatedRecords with
      | .ok _ => true
      | .error _ => false

    let mut checked := base
    for declaration in ordered.decls do
      if let some replay := toDeclaration checked declaration then
        match checked.addDeclCore 0 replay none false with
        | .ok next => checked := next
        | .error exception =>
          throwError "kernel replay rejected {declaration.names}: {
            ← (exception.toMessageData {}).toString}"
    let some info := checked.find? iotaName
      | throwError "kernel replay did not retain {iotaName}"
    let kernel := info.type
    setEnv checked
    let actualPretty := toString (← ppExpr actual)
    let expectedPretty := toString (← ppExpr expected)
    let kernelPretty := toString (← ppExpr kernel)
    return {
      report, actual, expected, kernel, actualPretty, expectedPretty, kernelPretty
      ownerFreeAccepted
      difference := (firstDifference? actual expected).getD "no structural difference" }
  return (← Core.CoreM.toIO (MetaM.run' action) context { env := base }).1

def containsText (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

def run (root : String) : IO UInt32 := do
  let evidence ← collectEvidence s!"{root}/test/fixtures/lean-inductive-models/default_ctor_iota.ndjson"
  IO.println s!"default ctor actual: {evidence.actualPretty}"
  IO.println s!"default ctor checker expected: {evidence.expectedPretty}"
  IO.println s!"default ctor kernel readback: {evidence.kernelPretty}"
  IO.println s!"default ctor first difference: {evidence.difference}"

  let mut state : TestState := {}
  state := state.check "direct simple route has no statement mismatch"
    evidence.report.stmtErrors.isEmpty
  state := state.check "serialized theorem follows the recursor's reduced field domain"
    (containsText evidence.actualPretty "startPos endPos canonical : Flag" &&
      !containsText evidence.actualPretty "canonical : optParam Flag Flag.false")
  state := state.check "kernel readback exactly equals the serialized theorem type"
    (evidence.actual == evidence.kernel && evidence.actualPretty == evidence.kernelPretty)
  state := state.check "checker reconstruction exactly equals the serialized theorem"
    (evidence.actual == evidence.expected && evidence.difference == "no structural difference")
  state := state.check "generated records pass owner-free kernel replay"
    evidence.ownerFreeAccepted

  IO.println s!"default constructor iota: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1

def main (args : List String) : IO UInt32 :=
  run (args.head?.getD ".")
