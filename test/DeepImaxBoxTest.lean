import Modelgen.Driver
import Modelgen.Check
import Modelgen.Order
import Lean.Util.CollectAxioms

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

def runExport (input : Export) : IO (Export × Report × Environment) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<deep-imax-box-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((declarations, report), state) ← Core.CoreM.toIO
    (MetaM.run' (runFilter input false {})) context { env }
  let output := { input with decls := declarations }
  let ordered ← match Order.reorder output with
    | .ok result => pure result
    | .error failure =>
      throw <| IO.userError s!"cannot order deep-imax output: {repr failure}"
  return (ordered, report, state.env)

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

def axiomsOf (environment : Environment) (name : Name) : IO (Array Name) := do
  let context : Core.Context :=
    { fileName := "<deep-imax-axioms>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (axioms, _) ← Core.CoreM.toIO (collectAxioms name) context { env := environment }
  return axioms

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let raw ← readExport "test/fixtures/modelgen/imax_box.ndjson"
  let (generated, report, _) ← runExport raw
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

  let wRaw ← readExport "test/fixtures/modelgen/w_imax.ndjson"
  let (wGenerated, wReport, wEnvironment) ← runExport wRaw
  let wNames := wGenerated.decls.flatMap (·.names.toArray)
  let dataModel := Naming.modelName `WData
  let dataCtors := #[Naming.modelName `WData.leaf, Naming.modelName `WData.fork]
  let dataRec := Naming.modelName `WData.rec
  let dataIotas := #[Naming.iotaName `WData.rec 0, Naming.iotaName `WData.rec 1]
  let bindModel := Naming.modelName `WBind
  let bindCtors := #[Naming.modelName `WBind.leaf, Naming.modelName `WBind.lim]
  let bindRec := Naming.modelName `WBind.rec
  let bindIotas := #[Naming.iotaName `WBind.rec 0, Naming.iotaName `WBind.rec 1]
  state := state.check "W data and binder imax shapes generate" <|
    #[`WData, `WBind].all fun owner =>
      wReport.generated.any (·.1 == owner) && !wReport.declined.any (·.1 == owner)
  state := state.check "W imax shapes have constructors, recursors, and both iotas" <|
    (#[dataModel, dataRec, bindModel, bindRec] ++ dataCtors ++ dataIotas ++
      bindCtors ++ bindIotas).all wNames.contains
  state := state.check "W data and binder towers use recursive PSigma boxing" <|
    [`WData._model._impl.wD, `WData._model._impl.wF,
      `WBind._model._impl.wTel, `WBind._model._impl.wF].all fun name =>
        (declarationValue? wGenerated name).any (containsConst `PSigma)
  state := state.check "literal correspondence accepts both W imax families" <|
    ownerPasses wGenerated `WData && ownerPasses wGenerated `WBind
  let dataAxioms ← axiomsOf wEnvironment dataRec
  let bindAxioms ← axiomsOf wEnvironment bindRec
  state := state.check "W recursive boxing preserves the tagged axiom boundary" <|
    #[dataAxioms, bindAxioms].all fun axioms =>
      axioms.contains `propext && axioms.contains `Quot.sound &&
        !axioms.contains `Classical.choice && axioms.size == 2

  -- Recursive-result recognition may unfold a transparent former, but the
  -- model interface may not. `AliasW.lim` is accepted as infinitary because
  -- `As AliasW` is definitionally `AliasW`; its exported spelling remains in
  -- the model constructor and is checked once in memory and once after the
  -- same NDJSON serialization the public CLI uses.
  let aliasRaw ← readExport "test/fixtures/modelgen/w_alias.ndjson"
  let (aliasGenerated, aliasReport, _) ← runExport aliasRaw
  let aliasNames := aliasGenerated.decls.flatMap (·.names.toArray)
  let aliasModel := Naming.modelName `AliasW
  let aliasCtors := #[Naming.modelName `AliasW.leaf, Naming.modelName `AliasW.lim]
  let aliasRec := Naming.modelName `AliasW.rec
  let aliasIotas := #[Naming.iotaName `AliasW.rec 0, Naming.iotaName `AliasW.rec 1]
  state := state.check "transparent W result aliases generate as infinitary children" <|
    aliasReport.generated.any (·.1 == `AliasW) &&
      !aliasReport.declined.any (·.1 == `AliasW)
  state := state.check "transparent W result alias has the complete public interface" <|
    (#[aliasModel, aliasRec] ++ aliasCtors ++ aliasIotas).all aliasNames.contains
  state := state.check "transparent W result spelling remains literal in the model" <|
    (declarationType? aliasGenerated aliasCtors[1]!).any (containsConst `As)
  let outputCheck := Check.checkReport aliasGenerated
  let aliasSerialized ← match parse aliasGenerated.render (analyse := false) with
    | .ok output => pure output
    | .error error => throw <| IO.userError s!"cannot parse serialized W alias output: {error}"
  let inputCheck := Check.checkReport aliasSerialized
  state := state.check "transparent W alias passes output and serialized input Check" <|
    outputCheck.violations.isEmpty && inputCheck.violations.isEmpty &&
      outputCheck.familiesChecked == inputCheck.familiesChecked
  state := state.check "transparent W alias recursor statements remain literal" <|
    aliasReport.stmtChecked > 0 && aliasReport.stmtErrors.isEmpty

  IO.println s!"deep imax box: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  unless state.failed.isEmpty do
    IO.eprintln s!"declined: {report.declined}"
    for violation in Check.check generated do
      if #[`BoxF, `IBox, skeleton].contains violation.familyOwner then
        IO.eprintln s!"check violation: {repr violation}"
  return if state.failed.isEmpty then 0 else 1
