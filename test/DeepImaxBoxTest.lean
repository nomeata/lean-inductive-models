import Modelgen.Driver
import Modelgen.Check
import Modelgen.Order

open Lean Meta Modelgen

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def readExport (path : String) : IO Export := do
  let .ok result := parse (← IO.FS.readFile path) (analyse := false)
    | throw <| IO.userError s!"cannot parse {path}"
  return result

def runExport (input : Export) : IO (Export × Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<deep-imax-box-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((declarations, report), _) ← Core.CoreM.toIO
    (MetaM.run' (runFilter input false {})) context { env }
  let output := { input with decls := declarations }
  let ordered ← match Order.reorder output with
    | .ok result => pure result
    | .error failure =>
      throw <| IO.userError s!"cannot order deep-imax output: {repr failure}"
  return (ordered, report)

def declarationValue? (input : Export) (name : Name) : Option Expr := do
  let .defn got _ _ value .. ← input.decls.find? (·.names.contains name) | none
  if got == name then some value else none

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
  | .app function argument => containsConst target function || containsConst target argument
  | .lam _ type body _ | .forallE _ type body _ =>
      containsConst target type || containsConst target body
  | .letE _ type value body _ =>
      containsConst target type || containsConst target value || containsConst target body
  | .mdata _ body => containsConst target body
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => false

def ownerPasses (input : Export) (owner : Name) : Bool :=
  (Check.check input).all (·.familyOwner != owner)

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let raw ← readExport "test/fixtures/modelgen/imax_box.ndjson"
  let (generated, report) ← runExport raw
  let names := generated.decls.flatMap (·.names.toArray)
  let boxModel := Naming.modelName `BoxF
  let boxCtor := Naming.modelName `BoxF.mk
  let boxRec := Naming.modelName `BoxF.rec
  let boxIota := Naming.iotaName `BoxF.rec 0
  let boxProjection := Naming.projectionName `BoxF 0
  let boxProjectionIota := Naming.projectionIotaName `BoxF 0
  let boxEta := Naming.etaName `BoxF
  let indexedModel := Naming.modelName `IBox
  let indexedCtor := Naming.modelName `IBox.mk
  let indexedRec := Naming.modelName `IBox.rec
  let indexedIota := Naming.iotaName `IBox.rec 0
  let indexedProjection := Naming.projectionName `IBox 0
  let indexedProjectionIota := Naming.projectionIotaName `IBox 0
  let skeleton := `IBox._model._impl.skel
  let mut state : TestState := {}

  state := state.check "BoxF and IBox generate without a level decline" <|
    #[`BoxF, `IBox].all fun owner =>
      report.generated.any (·.1 == owner) && !report.declined.any (·.1 == owner)
  state := state.check "BoxF has its complete declaration-local interface" <|
    #[boxModel, boxCtor, boxRec, boxIota, boxProjection, boxProjectionIota,
      boxEta].all names.contains
  state := state.check "indexed BoxF has its complete non-eta interface" <|
    #[indexedModel, indexedCtor, indexedRec, indexedIota, indexedProjection,
      indexedProjectionIota].all names.contains && !names.contains (Naming.etaName `IBox)
  state := state.check "recursive boxing stores and recovers through PSigma" <|
    (declarationValue? generated boxModel).any (containsConst `PSigma) &&
      (declarationValue? generated boxCtor).any (containsConst `PSigma.mk) &&
      (declarationValue? generated boxRec).any (containsConst `PSigma.rec)
  state := state.check "the representation adds no choice axiom dependency" <|
    #[boxModel, boxCtor, boxRec, boxProjection].all fun name =>
      (declarationValue? generated name).all fun value =>
        !containsConst `Classical.choice value && !containsConst `Nonempty value
  state := state.check "BoxF projection iota stays literal and untransported" <|
    (declarationType? generated boxProjectionIota).any fun type =>
      !containsConst ``Eq.rec type
  state := state.check "IBox's erased skeleton models before the parent is retained" <|
    report.generated.any (·.1 == skeleton) && names.contains (Naming.modelName skeleton)
  state := state.check "literal correspondence accepts all affected families" <|
    ownerPasses generated `BoxF && ownerPasses generated `IBox &&
      ownerPasses generated skeleton

  IO.println s!"deep imax box: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  unless state.failed.isEmpty do
    IO.eprintln s!"declined: {report.declined}"
    for violation in Check.check generated do
      if #[`BoxF, `IBox, skeleton].contains violation.familyOwner then
        IO.eprintln s!"check violation: {repr violation}"
  return if state.failed.isEmpty then 0 else 1
