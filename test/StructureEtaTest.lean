import InductiveModels.Driver
import InductiveModels.Check
import InductiveModels.ModelRoles

namespace StructureEtaTest

open Lean Meta InductiveModels

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def generation : Cli.Config :=
  { nested := false, mutualModels := true, simple := true, basic := true }

def readExport (path : String) : IO Export := do
  let .ok x := parse (← IO.FS.readFile path)
    | throw <| IO.userError s!"cannot parse {path}"
  return x

def runExport (input : Export) : IO (Export × Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<structure-eta-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((declarations, report), _) ← Core.CoreM.toIO
    (MetaM.run' (runFilter input false generation)) context { env }
  return ({ input with decls := declarations }, report)

def declarationType? (x : Export) (name : Name) : Option Expr := do
  let declaration ← x.decls.find? (·.names.contains name)
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
  | .proj _ _ struct => containsConst target struct
  | .app fn argument => containsConst target fn || containsConst target argument
  | .lam _ type body _ | .forallE _ type body _ =>
      containsConst target type || containsConst target body
  | .letE _ type value body _ =>
      containsConst target type || containsConst target value || containsConst target body
  | .mdata _ body => containsConst target body
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => false

def replaceDeclarationType (x : Export) (name : Name) (type : Expr) : Export :=
  { x with decls := x.decls.map fun declaration => match declaration with
    | .ax got params _ isUnsafe =>
      if got == name then .ax got params type isUnsafe else declaration
    | .defn got params _ value hints safety all =>
      if got == name then .defn got params type value hints safety all else declaration
    | .thm got params _ value all =>
      if got == name then .thm got params type value all else declaration
    | .opaq got params _ value isUnsafe all =>
      if got == name then .opaq got params type value isUnsafe all else declaration
    | _ => declaration }

def withoutDeclaration (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.filter (!·.names.contains name) }

def insertCollision (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.push (.ax name [] (.sort (.succ .zero)) false) }

def hasTypeViolation (owner declaration : Name) : Check.Violation → Bool
  | .declarationType gotOwner gotDeclaration =>
      gotOwner == owner && gotDeclaration == declaration
  | _ => false

def hasMissingViolation (owner declaration : Name) : Check.Violation → Bool
  | .missingPublic gotOwner gotDeclaration =>
      gotOwner == owner && gotDeclaration == declaration
  | _ => false

def hasExtraEta (owner declaration : Name) : Check.Violation → Bool
  | .extraMetadata gotOwner gotDeclaration .eta =>
      gotOwner == owner && gotDeclaration == declaration
  | _ => false

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut state : TestState := {}

  let focusedRaw ← readExport "test/fixtures/inductive-models/structure_eta.ndjson"
  let (focusedOutput, focusedReport) ← runExport focusedRaw
  let focusedNames := focusedOutput.decls.flatMap (·.names.toArray)
  let focusedOwners :=
    #[`EtaZero, `EtaDependent, `EtaBare, `EtaMutualLeft, `EtaMutualRight,
      `EtaProposition, `EtaIndexed, `EtaRecursive, `EtaTwo]
  let positiveEtas :=
    [`EtaZero, `EtaDependent, `EtaBare, `EtaMutualLeft, `EtaMutualRight].map
      Naming.etaName
  state := state.check "focused kernel-positive shapes get eta" <|
    positiveEtas.all focusedNames.contains
  state := state.check "focused dependent eta uses every intrinsic projection" <|
    (declarationType? focusedOutput (Naming.etaName `EtaDependent)).any fun type =>
      containsConst (Naming.projectionName `EtaDependent 0) type &&
      containsConst (Naming.projectionName `EtaDependent 1) type &&
      containsConst (Naming.projectionName `EtaDependent 2) type &&
      !containsConst `EtaDependent.key type &&
      !containsConst `EtaDependent.payload type &&
      !containsConst `EtaDependent.witness type
  state := state.check "unnamed inductive fields get intrinsic eta projections" <|
    (declarationType? focusedOutput (Naming.etaName `EtaBare)).any fun type =>
      containsConst (Naming.projectionName `EtaBare 0) type &&
      containsConst (Naming.projectionName `EtaBare 1) type
  state := state.check "mutual eta remains per member" <|
    focusedReport.generated.any (·.1 == `EtaMutualLeft) &&
      focusedNames.contains (Naming.etaName `EtaMutualLeft) &&
      focusedNames.contains (Naming.etaName `EtaMutualRight)
  state := state.check "focused source families pass the checker" <|
    Check.check focusedOutput |>.all fun violation =>
      !focusedOwners.contains violation.familyOwner
  for negative in [`EtaProposition, `EtaIndexed, `EtaRecursive, `EtaTwo] do
    state := state.check s!"focused miss {negative} has no eta" <|
      !focusedNames.contains (Naming.etaName negative)

  -- **Where the exported flag and the exported recursor disagree.**
  -- `ProjDead`'s only owner mention is `cst ProjDead N`, which unfolding a
  -- definition discards, so Lean's syntactic `isRec` is `true` of it while the
  -- recursor Lean minted beside it binds no induction hypothesis at all.
  -- Structure-likeness follows the recursor, so the owner is structure-like
  -- and earns η exactly as the `Plain` control does. `ProjDeadDep`'s `child`
  -- is an occurrence that survives reduction, and it earns none.
  -- `test/fixtures/inductive-models/delta_dead_mention.lean` is the source.
  let deadRaw ← readExport "test/fixtures/inductive-models/delta_dead_mention.ndjson"
  let (deadOutput, _) ← runExport deadRaw
  let deadNames := deadOutput.decls.flatMap (·.names.toArray)
  let deadOwners := #[`Plain, `ProjDead, `ProjDeadDep]
  let exportedIsRec := fun (owner : Name) =>
    deadRaw.decls.any fun declaration => match declaration with
      | .induct types _ _ => types.any fun type => type.name == owner && type.isRec
      | _ => false
  state := state.check "the export's own flag calls a dead owner mention recursive" <|
    exportedIsRec `ProjDead && exportedIsRec `ProjDeadDep && !exportedIsRec `Plain
  state := state.check "a dead owner mention is structure-like and gets eta" <|
    deadNames.contains (Naming.etaName `ProjDead) &&
      deadNames.contains (Naming.etaName `Plain)
  state := state.check "an occurrence that survives reduction gets no eta" <|
    !deadNames.contains (Naming.etaName `ProjDeadDep)
  state := state.check "the dead-mention families pass the checker" <|
    Check.check deadOutput |>.all fun violation =>
      !deadOwners.contains violation.familyOwner
  let extraDeadEta := insertCollision deadOutput (Naming.etaName `ProjDeadDep)
  state := state.check "checker rejects eta at an owner that really recurses" <|
    (Check.check extraDeadEta).any (hasExtraEta `ProjDeadDep (Naming.etaName `ProjDeadDep))

  let projectionRaw ← readExport "test/fixtures/inductive-models/structure_projections.ndjson"
  let (projectionOutput, projectionReport) ← runExport projectionRaw
  let depEta := Naming.etaName `Dep
  let depType := declarationType? projectionOutput depEta
  state := state.check "simple structure emits eta" <|
    projectionReport.generated.any (·.1 == `Dep) && depType.isSome
  state := state.check "dependent fields use intrinsic projection models" <|
    depType.any fun type =>
      containsConst (Naming.projectionName `Dep 0) type &&
      containsConst (Naming.projectionName `Dep 1) type &&
      containsConst (Naming.projectionName `Dep 2) type &&
      !containsConst `Dep.key type && !containsConst `Dep.payload type
  state := state.check "checker accepts intrinsic-projection eta" <|
    Check.check projectionOutput |>.all (·.familyOwner != `Dep)
  state := state.check "eta is keyed to its owner without an elimination universe" <|
    (ModelRoles.table projectionOutput)[depEta]?.any fun entry =>
      entry.owner == `Dep && entry.role == .eta

  let missing := Check.check (withoutDeclaration projectionOutput depEta)
  state := state.check "checker rejects missing eta" <|
    missing.any (hasMissingViolation `Dep depEta)
  let malformed := Check.check <|
    replaceDeclarationType projectionOutput depEta (.sort (.succ .zero))
  state := state.check "checker compares eta syntax literally" <|
    malformed.any (hasTypeViolation `Dep depEta)
  let sourceProjectionType := depType.map (mapConstsE fun name =>
    if name == Naming.projectionName `Dep 1 then some `Dep.payload else none)
  let sourceProjectionMutation := sourceProjectionType.map
    (replaceDeclarationType projectionOutput depEta ·) |>.getD projectionOutput
  state := state.check "checker rejects a source projection in eta" <|
    (Check.check sourceProjectionMutation).any (hasTypeViolation `Dep depEta)

  let unitRaw ← readExport "test/fixtures/inductive-models/unitlike.ndjson"
  let (unitOutput, unitReport) ← runExport unitRaw
  let unitEta := Naming.etaName `UnitType
  let fieldEta := Naming.etaName `WithField
  let muEta := Naming.etaName `MU
  let mvEta := Naming.etaName `MV
  let unitNames := unitOutput.decls.flatMap (·.names.toArray)
  state := state.check "zero-field Type gets eta" (unitNames.contains unitEta)
  state := state.check "plain one-constructor inductive gets eta" (unitNames.contains fieldEta)
  state := state.check "nonrecursive mutual members independently get eta" <|
    unitNames.contains muEta && unitNames.contains mvEta &&
      unitReport.generated.any (·.1 == `MU)
  state := state.check "plain inductive uses its intrinsic projection" <|
    (declarationType? unitOutput fieldEta).any fun type =>
      containsConst (Naming.projectionName `WithField 0) type &&
        !containsConst `WithField.rec type
  state := state.check "checker accepts zero, unnamed and mutual eta" <|
    Check.check unitOutput |>.all fun violation =>
      !#[`UnitType, `WithField, `MU, `MV].contains violation.familyOwner

  for negative in [`UnitProp, `Indexed, `Recursive, `TwoCtor, `MR, `MS] do
    state := state.check s!"{negative} has no eta" <|
      !unitNames.contains (Naming.etaName negative)
  let extraProp := insertCollision unitOutput (Naming.etaName `UnitProp)
  state := state.check "Prop one-constructor eta is rejected as extra metadata" <|
    (Check.check extraProp).any
      (hasExtraEta `UnitProp (Naming.etaName `UnitProp))
  let extraIndexed := insertCollision unitOutput (Naming.etaName `Indexed)
  state := state.check "indexed one-constructor eta is rejected as extra metadata" <|
    (Check.check extraIndexed).any
      (hasExtraEta `Indexed (Naming.etaName `Indexed))

  let intrinsicType := declarationType? unitOutput fieldEta
  let sourceRecursorType := intrinsicType.map (mapConstsE fun name =>
    if name == Naming.projectionName `WithField 0 then some `WithField.rec else none)
  let sourceRecursorMutation := sourceRecursorType.map
    (replaceDeclarationType unitOutput fieldEta ·) |>.getD unitOutput
  state := state.check "checker rejects a source selector in eta" <|
    (Check.check sourceRecursorMutation).any (hasTypeViolation `WithField fieldEta)

  let (_, collisionReport) ← runExport (insertCollision unitRaw unitEta)
  state := state.check "an exact eta collision withdraws the model atomically" <|
    !collisionReport.generated.any (·.1 == `UnitType) &&
      collisionReport.declined.any fun (owner, reason) =>
        owner == `UnitType && reason == s!"prim model name taken ({unitEta})"

  IO.println s!"structure eta: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1

end StructureEtaTest
