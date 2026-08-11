import Modelgen.Driver
import Modelgen.Check
import Modelgen.Mono

open Lean Meta Modelgen

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def projectionGeneration : Cli.Config :=
  { nested := false, mutualModels := true, simple := true, basic := true }

def readExport (path : String) : IO Export := do
  let .ok x := parse (← IO.FS.readFile path) (analyse := false)
    | throw <| IO.userError s!"cannot parse {path}"
  return x

def runExport (x : Export) : IO (Array EDecl × Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<projection-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Core.CoreM.toIO
    (MetaM.run' (runFilter x false projectionGeneration)) context { env }
  return result

def outputExport (input : Export) (declarations : Array EDecl) : Export :=
  { input with decls := declarations }

def declarationIndex? (x : Export) (name : Name) : Option Nat :=
  x.decls.findIdx? (·.names.contains name)

def declaration? (x : Export) (name : Name) : Option EDecl :=
  x.decls.find? (·.names.contains name)

def declarationType? (x : Export) (name : Name) : Option Expr := do
  let declaration ← declaration? x name
  match declaration with
  | .ax got _ type _ | .quot got _ type _ => if got == name then some type else none
  | .defn got _ type .. | .thm got _ type .. | .opaq got _ type .. =>
      if got == name then some type else none
  | .induct types constructors recursors =>
      (types.find? (·.name == name)).map (·.type) <|>
      (constructors.find? (·.name == name)).map (·.type) <|>
      (recursors.find? (·.name == name)).map (·.type)

def definitionValue? (x : Export) (name : Name) : Option Expr := do
  let .defn got _ _ value .. ← declaration? x name | none
  if got == name then some value else none

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

partial def containsProjection : Expr → Bool
  | .proj .. => true
  | .app fn argument => containsProjection fn || containsProjection argument
  | .lam _ type body _ | .forallE _ type body _ =>
      containsProjection type || containsProjection body
  | .letE _ type value body _ =>
      containsProjection type || containsProjection value || containsProjection body
  | .mdata _ body => containsProjection body
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => false

def declarationNames : EDecl → Array Name
  | .ax name _ type _ | .quot name _ type _ =>
      #[name] ++ type.getUsedConstants
  | .defn name _ type value _ _ all |
    .thm name _ type value all |
    .opaq name _ type value _ all =>
      #[name] ++ all.toArray ++ type.getUsedConstants ++ value.getUsedConstants
  | .induct types constructors recursors =>
      (types.toArray.flatMap fun type =>
        #[type.name] ++ type.all.toArray ++ type.ctors.toArray ++ type.type.getUsedConstants) ++
      (constructors.toArray.flatMap fun constructor =>
        #[constructor.name, constructor.induct] ++ constructor.type.getUsedConstants) ++
      (recursors.toArray.flatMap fun recursor =>
        #[recursor.name] ++ recursor.all.toArray ++ recursor.type.getUsedConstants ++
          recursor.rules.toArray.flatMap fun rule =>
            #[rule.ctor] ++ rule.rhs.getUsedConstants)

def insertCollision (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.push (.ax name [] (.sort (.succ .zero)) false) }

def withoutDeclaration (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.filter (!·.names.contains name) }

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

/-- Raise only the universe argument of a theorem's outer equality, retaining
the complete binder telescope and all three equality arguments literally. -/
partial def raiseOuterEqLevel? : Expr → Option Expr
  | .forallE name domain body info =>
      return .forallE name domain (← raiseOuterEqLevel? body) info
  | body => do
      let .const ``Eq [level] := body.getAppFn | none
      some (mkAppN (.const ``Eq [.succ level]) body.getAppArgs)

def hasTypeViolation (owner declaration : Name) : Check.Violation → Bool
  | .declarationType gotOwner gotDeclaration =>
      gotOwner == owner && gotDeclaration == declaration
  | _ => false

def hasMissingViolation (owner declaration : Name) : Check.Violation → Bool
  | .missingPublic gotOwner gotDeclaration =>
      gotOwner == owner && gotDeclaration == declaration
  | _ => false

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let raw ← readExport "tests/structure_projections.ndjson"
  let sourceProjections := raw.projectionsFor `Dep
  let (declarations, report) ← runExport raw
  let generated := outputExport raw declarations
  let names := declarations.flatMap (·.names.toArray)
  let keyModel := Naming.projectionName `Dep.key
  let payloadModel := Naming.projectionName `Dep.payload
  let witnessModel := Naming.projectionName `Dep.witness
  let keyRule := Naming.projectionIotaName `Dep.key
  let payloadRule := Naming.projectionIotaName `Dep.payload
  let witnessRule := Naming.projectionIotaName `Dep.witness
  let projectionNames := #[keyModel, payloadModel, witnessModel]
  let projectionRules := #[keyRule, payloadRule, witnessRule]
  let sortFieldProjections := #[`SortFields.carrier, `SortFields.family,
    `SortFields.element, `SortFields.letCarrier].flatMap fun name =>
      #[Naming.projectionName name, Naming.projectionIotaName name]
  let mut state : TestState := {}

  state := state.check "three source projections recovered in field order" <|
    sourceProjections.map (fun projection => (projection.name, projection.fieldIndex)) ==
      #[(`Dep.key, 0), (`Dep.payload, 1), (`Dep.witness, 2)]
  state := state.check "dependent structure generated" <|
    report.generated.any (·.1 == `Dep) && report.stmtErrors.isEmpty
  state := state.check "exact projection definitions and rules emitted" <|
    projectionNames.all names.contains && projectionRules.all names.contains

  let ownerBeforeSources := match declarationIndex? raw `Dep with
    | none => false
    | some owner => sourceProjections.all (owner < ·.declIndex)
  state := state.check "source projections occur after their owner" ownerBeforeSources
  let modelsBeforeOwner := match declarationIndex? generated `Dep with
    | none => false
    | some owner => (projectionNames ++ projectionRules).all fun name =>
        (declarationIndex? generated name).any (· < owner)
  state := state.check "whole-export prepass emits every projection model before owner"
    modelsBeforeOwner

  state := state.check "projection definitions eliminate with the model recursor" <|
    projectionNames.all fun name =>
      (definitionValue? generated name).any fun value =>
        containsConst (Naming.modelName `Dep.rec) value && !containsProjection value
  state := state.check "payload type uses the preceding projection model literally" <|
    (declarationType? generated payloadModel).any fun type =>
      containsConst keyModel type && !containsConst `Dep.key type
  state := state.check "witness type uses both preceding projection models literally" <|
    (declarationType? generated witnessModel).any fun type =>
      containsConst keyModel type && containsConst payloadModel type &&
        !containsConst `Dep.key type && !containsConst `Dep.payload type
  state := state.check "format-only checker accepts generated projection family" <|
    Check.check generated |>.all (·.familyOwner != `Dep)
  state := state.check "projection universe inference covers sorts, functions, lets and dependencies" <|
    sortFieldProjections.all names.contains &&
      (Check.check generated |>.all (·.familyOwner != `SortFields))

  let missingModel := Check.check (withoutDeclaration generated payloadModel)
  state := state.check "checker rejects a missing projection definition" <|
    missingModel.any (hasMissingViolation `Dep.payload payloadModel)
  let missingRule := Check.check (withoutDeclaration generated witnessRule)
  state := state.check "checker rejects a missing projection rule" <|
    missingRule.any (hasMissingViolation `Dep.witness witnessRule)
  let badModelType := Check.check <|
    replaceDeclarationType generated payloadModel (.sort (.succ .zero))
  state := state.check "checker compares projection types syntactically" <|
    badModelType.any (hasTypeViolation `Dep.payload payloadModel)
  let badRuleType := Check.check <|
    replaceDeclarationType generated keyRule (.sort (.succ .zero))
  state := state.check "checker compares projection iota statements syntactically" <|
    badRuleType.any (hasTypeViolation `Dep.key keyRule)
  let raisedEqExport := (declarationType? generated keyRule).bind raiseOuterEqLevel?
    |>.map (replaceDeclarationType generated keyRule ·) |>.getD generated
  let raisedEqViolations := Check.check raisedEqExport
  state := state.check "checker rejects a projection iota with only Eq's universe raised" <|
    raisedEqViolations.any (hasTypeViolation `Dep.key keyRule)
  let (_, raisedEqReplay) ← runExport raisedEqExport
  state := state.check "raised-Eq projection theorem remains kernel-valid" <|
    raisedEqReplay.unreplayable.isNone

  let monoTable := Mono.modelTable generated
  state := state.check "Mono keys projection definitions to the owner record" <|
    (monoTable[payloadModel]?).any fun entry =>
      entry.owner == `Dep && entry.role == .projection
  state := state.check "Mono keys projection rules without an eliminating universe" <|
    (monoTable[payloadRule]?).any fun entry =>
      entry.owner == `Dep && entry.role == .projectionIota

  -- A real collision retry requires both spellings in the flattened export.
  -- Manufacture the second module's block and primitive projections using the
  -- same explicit, whole-name substitution used by serialization.  The
  -- public block remains in place, so the raw private model names normalize
  -- onto declarations already installed for it.  The copied payload
  -- projection deliberately lives outside the copied owner's namespace;
  -- exact aliases must not assume projections are owner descendants.
  let privateDep := (`_private.ProjectionTest).mkNum 0 |>.str "Dep"
  let privatePayload := (`_private.ProjectionTest).mkNum 0 |>.str "payload"
  let sourceNames := raw.decls.flatMap (fun declaration => declaration.names.toArray)
    |>.filter fun name => (`Dep).isPrefixOf name
  let privateAliases := sourceNames.foldl (init := Naming.AliasMap.empty)
    fun aliases name =>
      let exact := if name == `Dep.payload then privatePayload
        else name.replacePrefix `Dep privateDep
      aliases.insert name exact
  let privateRecords := raw.decls.map (·.renameAliases privateAliases)
  let privateRaw := { raw with decls := privateRecords }
  let (privateDecls, privateReport) ← runExport privateRaw
  let privateNames := privateDecls.flatMap (·.names.toArray)
  state := state.check "raw private structure and non-descendant projection model exactly" <|
    privateReport.generated.any (·.1 == privateDep) &&
      privateNames.contains (Naming.projectionName privatePayload) &&
      privateNames.contains (Naming.projectionIotaName privatePayload)
  let leakedAliases := privateDecls.flatMap declarationNames |>.filter fun name =>
    name.components.any (· == `_modelgen_alias)
  state := state.check "projection retry aliases do not leak into serialized records" <|
    leakedAliases.isEmpty

  let (_, collisionReport) ← runExport (insertCollision raw keyModel)
  state := state.check "an exact projection model collision withdraws the owner atomically" <|
    !collisionReport.generated.any (·.1 == `Dep) &&
      collisionReport.declined.any fun (owner, reason) =>
        owner == `Dep && reason == s!"prim model name taken ({keyModel})"
  let (legacyDecls, legacyReport) ← runExport
    (insertCollision raw (Name.str keyModel "self"))
  state := state.check "an old carrier-shaped projection descendant is not a collision" <|
    legacyReport.generated.any (·.1 == `Dep) &&
      legacyDecls.any (·.names.contains payloadModel)

  let mutualRaw ← readExport "tests/mutual_structure_projections.ndjson"
  let mutualSourceProjections := mutualRaw.projections.filter fun projection =>
    projection.owner == `MLeft || projection.owner == `MRight
  let (mutualDecls, mutualReport) ← runExport mutualRaw
  let mutualGenerated := outputExport mutualRaw mutualDecls
  let mutualNames := mutualDecls.flatMap (·.names.toArray)
  let leftProjection := Naming.projectionName `MLeft.value
  let leftRule := Naming.projectionIotaName `MLeft.value
  let rightKeyProjection := Naming.projectionName `MRight.key
  let rightPayloadProjection := Naming.projectionName `MRight.payload
  let rightPayloadRule := Naming.projectionIotaName `MRight.payload
  state := state.check "mutual projection fixture declares PULiftP after its owner" <|
    (declarationIndex? mutualRaw `MLeft).any fun owner =>
      (declarationIndex? mutualRaw `PULiftP).any (owner < ·)
  unless mutualReport.generated.any (·.1 == `MLeft) do
    IO.eprintln s!"mutual projection generation declined: {mutualReport.declined}"
    for error in mutualReport.stmtErrors do
      IO.eprintln s!"mutual projection statement error: {error}"
    for declaration in mutualRaw.decls do
      if let .induct _ _ recursors := declaration then
        for recursor in recursors do
          if recursor.all.contains `MLeft then
            IO.eprintln s!"source recursor {recursor.name}: motives {recursor.all}, rules {recursor.rules.map (·.ctor)}"
  state := state.check "non-recursive mutual members recover all primitive projections" <|
    mutualSourceProjections.map (fun projection => (projection.name, projection.fieldIndex)) ==
      #[(`MLeft.value, 0), (`MRight.key, 0), (`MRight.payload, 1)]
  state := state.check "plain mutual route emits each member's projection interface" <|
    mutualReport.generated.any (·.1 == `MLeft) && mutualReport.stmtErrors.isEmpty &&
      #[leftProjection, leftRule, rightKeyProjection, rightPayloadProjection,
        rightPayloadRule].all mutualNames.contains
  state := state.check "mutual dependent projection type uses its preceding model" <|
    (declarationType? mutualGenerated rightPayloadProjection).any fun type =>
      containsConst rightKeyProjection type && !containsConst `MRight.key type
  state := state.check "mutual projection models precede their modeled block" <|
    (declarationIndex? mutualGenerated `MLeft).any fun owner =>
      #[leftProjection, leftRule, rightKeyProjection, rightPayloadProjection,
        rightPayloadRule].all fun name =>
          (declarationIndex? mutualGenerated name).any (· < owner)
  state := state.check "checker accepts mutual projection interfaces per member" <|
    Check.check mutualGenerated |>.all fun violation =>
      violation.familyOwner != `MLeft && violation.familyOwner != `MRight
  let mutualMono := Mono.modelTable mutualGenerated
  state := state.check "Mono attaches a later member's projection to the mutual owner record" <|
    (mutualMono[rightPayloadProjection]?).any fun entry =>
      entry.owner == `MLeft && entry.role == .projection

  IO.println s!"structure projections: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1
