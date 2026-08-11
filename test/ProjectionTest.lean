import Modelgen.Driver
import Modelgen.Check
import Modelgen.Mono
import Modelgen.Order

set_option maxRecDepth 2048

open Lean Meta Modelgen

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def projectionGeneration : Cli.Config :=
  { nested := true, mutualModels := true, simple := true, basic := true }

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

def intrinsicFieldsFor (x : Export) (owner : Name) : Array Nat :=
  x.decls.findSome? (fun declaration => match declaration with
    | .induct types constructors _ =>
      (types.find? (·.name == owner)).map fun type =>
        x.intrinsicProjectionFieldsFor type constructors
    | _ => none) |>.getD #[]

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

def replaceDefinitionSafety (x : Export) (name : Name) (safety : String) : Export :=
  { x with decls := x.decls.map fun declaration => match declaration with
    | .defn got params type value hints _ all =>
        if got == name then .defn got params type value hints safety all else declaration
    | _ => declaration }

def replaceImplementationWithAxiom (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.map fun declaration => match declaration with
    | .defn got params type _ _ _ _ =>
        if got == name then .ax got params type false else declaration
    | _ => declaration }

def replaceTheoremWithDefinition (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.map fun declaration => match declaration with
    | .thm got params type value all =>
        if got == name then .defn got params type value .opaque "safe" all else declaration
    | _ => declaration }

def replaceConst (type : Expr) (target replacement : Name) : Expr :=
  type.replace fun
    | .const name levels =>
        if name == target then some (.const replacement levels) else none
    | _ => none

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

def hasExtraProjectionViolation (owner declaration : Name) : Check.Violation → Bool
  | .extraProjection gotOwner gotDeclaration =>
      gotOwner == owner && gotDeclaration == declaration
  | _ => false

def hasKindViolation (owner declaration : Name)
    (expected actual : Check.DeclarationKind) : Check.Violation → Bool
  | .declarationKind gotOwner gotDeclaration gotExpected gotActual =>
      gotOwner == owner && gotDeclaration == declaration &&
        gotExpected == expected && gotActual == actual
  | _ => false

def hasSafetyViolation (owner declaration : Name) (actual : String) :
    Check.Violation → Bool
  | .declarationSafety gotOwner gotDeclaration gotActual =>
      gotOwner == owner && gotDeclaration == declaration && gotActual == actual
  | _ => false

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let wrapperRaw ← readExport "test/fixtures/modelgen/structure_projections.ndjson"
  let raw := #[`Dep.key, `Dep.payload, `Dep.witness, `SortFields.carrier,
    `SortFields.family, `SortFields.element, `SortFields.letCarrier,
    `depKey, `depPayload, `depWitness].foldl withoutDeclaration wrapperRaw
  let (declarations, report) ← runExport raw
  let generated := outputExport raw declarations
  let names := declarations.flatMap (·.names.toArray)
  let keyModel := Naming.projectionName `Dep 0
  let payloadModel := Naming.projectionName `Dep 1
  let witnessModel := Naming.projectionName `Dep 2
  let keyRule := Naming.projectionIotaName `Dep 0
  let payloadRule := Naming.projectionIotaName `Dep 1
  let witnessRule := Naming.projectionIotaName `Dep 2
  let projectionNames := #[keyModel, payloadModel, witnessModel]
  let projectionRules := #[keyRule, payloadRule, witnessRule]
  let sortFieldProjections := (Array.range 4).flatMap fun fieldIndex =>
    #[Naming.projectionName `SortFields fieldIndex,
      Naming.projectionIotaName `SortFields fieldIndex]
  let mut state : TestState := {}

  -- A maybe-zero singleton cannot use the ordinary Church carrier: it forgets
  -- which payload constructed it, while an intrinsic projection retains that
  -- payload at positive instantiations.  `PI` uses its exact-sort field as the
  -- carrier; `PF` lifts its exactly proposition-valued field with `PULiftP`.
  let primRaw ← readExport "test/fixtures/modelgen/prim_shapes.ndjson"
  let (primDeclarations, primReport) ← runExport primRaw
  let primGenerated := outputExport primRaw primDeclarations
  let pfProjection := Naming.projectionName `PF 0
  let pfRule := Naming.projectionIotaName `PF 0
  let pfSlots := #[Naming.modelName `PF, Naming.modelName `PF.mk,
    Naming.modelName `PF.rec, Naming.iotaName `PF.rec 0, pfProjection, pfRule]
  let piProjection := Naming.projectionName `PI 0
  let piRule := Naming.projectionIotaName `PI 0
  let piDefinitions := #[Naming.modelName `PI, Naming.modelName `PI.mk,
    Naming.modelName `PI.rec, piProjection]
  let primNames := primDeclarations.flatMap (·.names.toArray)
  state := state.check "proposition-field singleton emits its six exact slots" <|
    primReport.generated.any (·.1 == `PF) &&
      !primReport.declined.any (·.1 == `PF) && pfSlots.all primNames.contains
  state := state.check "proposition-field singleton interface is exact" <|
    (Check.check primGenerated).all (·.familyOwner != `PF)
  state := state.check "proposition-field model uses the existing lift basis" <|
    (definitionValue? primGenerated (Naming.modelName `PF)).any (containsConst `PULiftP) &&
    (definitionValue? primGenerated (Naming.modelName `PF.mk)).any
      (containsConst `PULiftP.up) &&
    (definitionValue? primGenerated (Naming.modelName `PF.rec)).any
      (containsConst `PULiftP.rec) &&
    (definitionValue? primGenerated pfProjection).any (containsConst `PULiftP.rec)
  state := state.check "proposition-field projection iota is literal and uncast" <|
    (declarationType? primGenerated pfRule).any fun type => !containsConst ``Eq.rec type
  state := state.check "variable-sort singleton retains its intrinsic field" <|
    primReport.generated.any (·.1 == `PI) &&
      !primReport.declined.any (·.1 == `PI) &&
      primNames.contains piProjection && primNames.contains piRule
  state := state.check "variable-sort singleton projection is exact" <|
    (Check.check primGenerated).all (·.familyOwner != `PI)
  state := state.check "variable-sort singleton selector avoids its small recursor" <|
    (definitionValue? primGenerated piProjection).any fun value =>
      !containsConst `PI.rec._model value
  state := state.check "exact-sort singleton remains the identity route" <|
    piDefinitions.all fun name => (definitionValue? primGenerated name).any fun value =>
      !containsConst `PULiftP value && !containsConst `PULiftP.up value &&
        !containsConst `PULiftP.rec value

  -- A recursive Type with no base constructor is empty, including when arm C
  -- obtains it as the erasure skeleton of an indexed family.  `NoBase` checks
  -- both layers: the eight-slot skeleton interface (including its two
  -- intrinsic projection pairs) must close before the ten-slot indexed model
  -- is allowed to emit.
  let noBaseRaw ← readExport "test/fixtures/modelgen/prim_carve.ndjson"
  let (noBaseDeclarations, noBaseReport) ← runExport noBaseRaw
  let noBaseGenerated := outputExport noBaseRaw noBaseDeclarations
  let noBaseOrdered ← match Order.reorder noBaseGenerated with
    | .ok output => pure output
    | .error error => throw <| IO.userError s!"cannot order no-base fixture: {repr error}"
  let noBaseSkel := `NoBase._model._impl.skel
  state := state.check "no-base indexed family and its empty skeleton both model" <|
    noBaseReport.generated.contains (`NoBase, 10) &&
      noBaseReport.generated.contains (noBaseSkel, 8) &&
      !noBaseReport.declined.any fun (owner, _) => owner == `NoBase || owner == noBaseSkel
  state := state.check "no-base interfaces satisfy the exact public checker" <|
    (Check.check noBaseOrdered).all fun violation =>
      violation.familyOwner != `NoBase && violation.familyOwner != noBaseSkel
  state := state.check "no-base skeleton uses the exact empty lift carrier" <|
    (definitionValue? noBaseGenerated (Naming.modelName noBaseSkel)).any
      (containsConst `PULiftP)
  state := state.check "no-base recursor eliminates the empty lift" <|
    (definitionValue? noBaseGenerated (Naming.modelName (Name.str noBaseSkel "rec"))).any
      (containsConst `PULiftP.rec)

  -- Arm F's packed equation can change the declared type of a pivot.  Fmid's
  -- recursor transports a function over that pivot, so the target endpoint is
  -- applied to the caller's field literally and the exact syntactic interface
  -- still passes the public checker.
  let fmidRaw ← readExport "test/fixtures/modelgen/prim_idx.ndjson"
  let (fmidDeclarations, fmidReport) ← runExport fmidRaw
  let fmidGenerated := outputExport fmidRaw fmidDeclarations
  let fmidOrdered ← match Order.reorder fmidGenerated with
    | .ok output => pure output
    | .error error => throw <| IO.userError s!"cannot order dependent-pivot fixture: {repr error}"
  state := state.check "dependent arm-F pivot models" <|
    fmidReport.generated.contains (`Fmid, 4) &&
      !fmidReport.declined.any fun (owner, _) => owner == `Fmid
  state := state.check "dependent arm-F pivot satisfies the exact public checker" <|
    (Check.check fmidOrdered).all fun violation => violation.familyOwner != `Fmid
  state := state.check "dependent arm-F recursor performs equality transport" <|
    (definitionValue? fmidGenerated (Naming.modelName `Fmid.rec)).any
      (containsConst ``Eq.rec)

  -- The parameter-dependent proposition field takes the same route.  Its
  -- source owner precedes the input's own lift declaration, so generation has
  -- to wait, use that declaration, and let the stable order pass place the
  -- complete interface back before its owner.
  let pfpRaw ← readExport "test/fixtures/modelgen/tight_prop_field_late.ndjson"
  let (pfpDeclarations, pfpReport) ← runExport pfpRaw
  let pfpGenerated := outputExport pfpRaw pfpDeclarations
  let pfpProjection := Naming.projectionName `PFP 0
  let pfpRule := Naming.projectionIotaName `PFP 0
  let pfpSlots := #[Naming.modelName `PFP, Naming.modelName `PFP.mk,
    Naming.modelName `PFP.rec, Naming.iotaName `PFP.rec 0, pfpProjection, pfpRule]
  let pfpNames := pfpDeclarations.flatMap (·.names.toArray)
  let pfpOrdered ← match Order.reorder pfpGenerated with
    | .ok output => pure output
    | .error error => throw <| IO.userError s!"cannot order late-PULift fixture: {repr error}"
  state := state.check "parameterized proposition-field fixture has a late lift" <|
    (declarationIndex? pfpRaw `PFP).any fun owner =>
      (declarationIndex? pfpRaw `PULiftP).any (owner < ·)
  state := state.check "parameterized proposition field waits for the input lift" <|
    pfpReport.generated.any (·.1 == `PFP) && !pfpReport.declined.any (·.1 == `PFP) &&
      pfpSlots.all pfpNames.contains
  state := state.check "ordered late-lift projection interface is exact" <|
    (Check.check pfpOrdered).all (·.familyOwner != `PFP)

  -- Arm W's recursor iota is propositional.  A later recursive field whose
  -- domain depends on an earlier data field therefore needs the canonical
  -- transport on the rule's right-hand side; the independent first field
  -- remains the literal, uncast rule.
  let wRaw ← readExport "test/fixtures/modelgen/prim_w.ndjson"
  let (wDeclarations, wReport) ← runExport wRaw
  let wGenerated := outputExport wRaw wDeclarations
  let wNames := wDeclarations.flatMap (·.names.toArray)
  let wtyProjection0 := Naming.projectionName `Wty 0
  let wtyProjection1 := Naming.projectionName `Wty 1
  let wtyRule0 := Naming.projectionIotaName `Wty 0
  let wtyRule1 := Naming.projectionIotaName `Wty 1
  state := state.check "dependent recursive singleton emits every intrinsic field" <|
    wReport.generated.any (·.1 == `Wty) && !wReport.declined.any (·.1 == `Wty) &&
      #[wtyProjection0, wtyProjection1, wtyRule0, wtyRule1].all wNames.contains
  state := state.check "dependent recursive singleton projection interface is exact" <|
    (Check.check wGenerated).all fun violation =>
      violation.familyOwner != `Wty || violation matches .modelNotBefore ..
  state := state.check "independent recursive field retains the literal rule" <|
    (declarationType? wGenerated wtyRule0).any fun type => !containsConst ``Eq.rec type
  state := state.check "dependent recursive field has the canonical transport" <|
    (declarationType? wGenerated wtyRule1).any (containsConst ``Eq.rec)
  let corruptedTransport := (declarationType? wGenerated wtyRule1).map fun type =>
    replaceDeclarationType wGenerated wtyRule1 (replaceConst type ``Eq.rec ``Eq.ndrec)
  state := state.check "checker rejects a corrupted dependent projection transport" <|
    corruptedTransport.any fun corrupted =>
      (declarationType? corrupted wtyRule1).any (containsConst ``Eq.ndrec) &&
        (Check.check corrupted).any (hasTypeViolation `Wty wtyRule1)

  let (wrapperDeclarations, wrapperReport) ← runExport wrapperRaw
  let wrapperGenerated := outputExport wrapperRaw wrapperDeclarations
  let wrapperNames := wrapperDeclarations.flatMap (·.names.toArray)
  state := state.check "incidental exported wrappers do not change intrinsic types" <|
    wrapperReport.stmtErrors.isEmpty && projectionNames.all fun name =>
      declarationType? wrapperGenerated name == declarationType? generated name
  state := state.check "incidental wrappers receive no legacy model declarations" <|
    #[`Dep.key._model, `Dep.payload._model, `Dep.witness._model].all fun name =>
      !wrapperNames.contains name

  state := state.check "intrinsic fields need no exported projection wrappers" <|
    #[`Dep.key, `Dep.payload, `Dep.witness].all fun name =>
      (declarationIndex? raw name).isNone
  state := state.check "dependent structure generated" <|
    report.generated.any (·.1 == `Dep) && report.stmtErrors.isEmpty
  state := state.check "exact projection definitions and rules emitted" <|
    projectionNames.all names.contains && projectionRules.all names.contains

  let modelsBeforeOwner := match declarationIndex? generated `Dep with
    | none => false
    | some owner => (projectionNames ++ projectionRules).all fun name =>
        (declarationIndex? generated name).any (· < owner)
  state := state.check "intrinsic projection interface precedes owner"
    modelsBeforeOwner

  state := state.check "projection definitions eliminate with the model recursor" <|
    projectionNames.all fun name =>
      (definitionValue? generated name).any fun value =>
        containsConst (Naming.modelName `Dep.rec) value && !containsProjection value
  state := state.check "payload type uses the preceding projection model literally" <|
    (declarationType? generated payloadModel).any fun type =>
      containsConst keyModel type
  state := state.check "witness type uses both preceding projection models literally" <|
    (declarationType? generated witnessModel).any fun type =>
      containsConst keyModel type && containsConst payloadModel type &&
        !containsConst `Dep.key type && !containsConst `Dep.payload type
  state := state.check "format-only checker accepts generated projection family" <|
    Check.check generated |>.all (·.familyOwner != `Dep)
  state := state.check "projection universe inference covers sorts, functions, lets and dependencies" <|
    sortFieldProjections.all names.contains &&
      (Check.check generated |>.all (·.familyOwner != `SortFields))

  let wcore ← readExport "test/fixtures/modelgen/w_core.ndjson"
  state := state.check "Prop-valued Iff exposes its two proof fields" <|
    intrinsicFieldsFor wcore `Iff == #[0, 1]
  state := state.check "Prop-valued Nonempty cannot expose its data field" <|
    (intrinsicFieldsFor wcore `Nonempty).isEmpty
  let indexedProjections := (Array.range 1).flatMap fun fieldIndex =>
    #[Naming.projectionName `Indexed fieldIndex,
      Naming.projectionIotaName `Indexed fieldIndex]
  let recursiveProjections := (Array.range 2).flatMap fun fieldIndex =>
    #[Naming.projectionName `Recursive fieldIndex,
      Naming.projectionIotaName `Recursive fieldIndex]
  state := state.check "indexed one-constructor fields are intrinsic projections" <|
    intrinsicFieldsFor raw `Indexed == #[0] && indexedProjections.all names.contains &&
      (Check.check generated).all (·.familyOwner != `Indexed)
  state := state.check "recursive one-constructor fields are intrinsic projections" <|
    intrinsicFieldsFor raw `Recursive == #[0, 1] && recursiveProjections.all names.contains &&
      (Check.check generated).all (·.familyOwner != `Recursive)
  state := state.check "Prop dependency and multi-constructor fields are excluded" <|
    (intrinsicFieldsFor raw `PropDependent).isEmpty &&
      (intrinsicFieldsFor raw `Multi).isEmpty &&
      !names.contains (Naming.projectionName `PropDependent 0) &&
      !names.contains (Naming.projectionName `Multi 0)
  let extraIndexed := Naming.projectionName `Indexed 2
  let extraViolations := Check.check (insertCollision generated extraIndexed)
  state := state.check "checker rejects an out-of-range intrinsic projection slot" <|
    extraViolations.any (hasExtraProjectionViolation `Indexed extraIndexed)

  let missingModel := Check.check (withoutDeclaration generated payloadModel)
  state := state.check "checker rejects a missing projection definition" <|
    missingModel.any (hasMissingViolation `Dep payloadModel)
  let missingRule := Check.check (withoutDeclaration generated witnessRule)
  state := state.check "checker rejects a missing projection rule" <|
    missingRule.any (hasMissingViolation `Dep witnessRule)
  let axiomProjection := Check.check <|
    replaceImplementationWithAxiom generated payloadModel
  state := state.check "checker requires a projection implementation definition" <|
    axiomProjection.any
      (hasKindViolation `Dep payloadModel .defn .axiom)
  let unsafeProjection := Check.check <|
    replaceDefinitionSafety generated payloadModel "unsafe"
  state := state.check "checker requires a safe projection implementation" <|
    unsafeProjection.any (hasSafetyViolation `Dep payloadModel "unsafe")
  let definitionRule := Check.check <|
    replaceTheoremWithDefinition generated payloadRule
  state := state.check "checker requires a projection iota theorem" <|
    definitionRule.any
      (hasKindViolation `Dep payloadRule .thm .defn)
  let badModelType := Check.check <|
    replaceDeclarationType generated payloadModel (.sort (.succ .zero))
  state := state.check "checker compares projection types syntactically" <|
    badModelType.any (hasTypeViolation `Dep payloadModel)
  let badRuleType := Check.check <|
    replaceDeclarationType generated keyRule (.sort (.succ .zero))
  state := state.check "checker compares projection iota statements syntactically" <|
    badRuleType.any (hasTypeViolation `Dep keyRule)
  let raisedEqExport := (declarationType? generated keyRule).bind raiseOuterEqLevel?
    |>.map (replaceDeclarationType generated keyRule ·) |>.getD generated
  let raisedEqViolations := Check.check raisedEqExport
  state := state.check "checker rejects a projection iota with only Eq's universe raised" <|
    raisedEqViolations.any (hasTypeViolation `Dep keyRule)
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
  -- Manufacture the second module's block using the same explicit whole-name
  -- substitution used by serialization.
  let privateDep := (`_private.ProjectionTest).mkNum 0 |>.str "Dep"
  let sourceNames := raw.decls.flatMap (fun declaration => declaration.names.toArray)
    |>.filter fun name => (`Dep).isPrefixOf name
  let privateAliases := sourceNames.foldl (init := Naming.AliasMap.empty)
    fun aliases name => aliases.insert name (name.replacePrefix `Dep privateDep)
  let privateRecords := raw.decls.map (·.renameAliases privateAliases)
  let privateRaw := { raw with decls := privateRecords }
  let (privateDecls, privateReport) ← runExport privateRaw
  let privateNames := privateDecls.flatMap (·.names.toArray)
  state := state.check "raw private structure gets intrinsic projection names exactly" <|
    privateReport.generated.any (·.1 == privateDep) &&
      privateNames.contains (Naming.projectionName privateDep 1) &&
      privateNames.contains (Naming.projectionIotaName privateDep 1)
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
    (insertCollision raw `Dep.key._model)
  state := state.check "a legacy wrapper-shaped name is irrelevant" <|
    legacyReport.generated.any (·.1 == `Dep) &&
      legacyDecls.any (·.names.contains payloadModel)

  let mutualWrapperRaw ← readExport "test/fixtures/modelgen/mutual_structure_projections.ndjson"
  let mutualRaw := #[`MLeft.value, `MRight.key, `MRight.payload,
    `leftValue, `rightPayload].foldl withoutDeclaration mutualWrapperRaw
  let (mutualDecls, mutualReport) ← runExport mutualRaw
  let mutualGenerated := outputExport mutualRaw mutualDecls
  let mutualNames := mutualDecls.flatMap (·.names.toArray)
  let leftProjection := Naming.projectionName `MLeft 0
  let leftRule := Naming.projectionIotaName `MLeft 0
  let rightKeyProjection := Naming.projectionName `MRight 0
  let rightPayloadProjection := Naming.projectionName `MRight 1
  let rightPayloadRule := Naming.projectionIotaName `MRight 1
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
  state := state.check "mutual fields need no exported projection wrappers" <|
    #[`MLeft.value, `MRight.key, `MRight.payload].all fun name =>
      (declarationIndex? mutualRaw name).isNone
  state := state.check "plain mutual route emits each member's projection interface" <|
    mutualReport.generated.any (·.1 == `MLeft) && mutualReport.stmtErrors.isEmpty &&
      #[leftProjection, leftRule, rightKeyProjection, rightPayloadProjection,
        rightPayloadRule].all mutualNames.contains
  state := state.check "mutual dependent projection type uses its preceding model" <|
    (declarationType? mutualGenerated rightPayloadProjection).any fun type =>
      containsConst rightKeyProjection type
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
  unless state.failed.isEmpty do
    IO.eprintln s!"projection declines: {report.declined}"
    for error in report.stmtErrors do IO.eprintln s!"projection statement error: {error}"
    for error in wrapperReport.stmtErrors do IO.eprintln s!"wrapper statement error: {error}"
    for error in mutualReport.stmtErrors do IO.eprintln s!"mutual statement error: {error}"
    for name in projectionNames do
      IO.eprintln s!"wrapper type equal {name}: {declarationType? wrapperGenerated name == declarationType? generated name}"
    IO.eprintln s!"Indexed fields: {intrinsicFieldsFor raw `Indexed}"
    IO.eprintln s!"Recursive fields: {intrinsicFieldsFor raw `Recursive}"
    IO.eprintln s!"generated owners: {report.generated}"
    for name in recursiveProjections do
      IO.eprintln s!"recursive slot {name}: {names.contains name}"
    IO.eprintln s!"Iff fields: {intrinsicFieldsFor wcore `Iff}"
    for violation in Check.check generated do
      if #[`Dep, `SortFields, `Indexed, `Recursive].contains violation.familyOwner then
        IO.eprintln s!"projection check violation: {repr violation}"
    for violation in Check.check mutualGenerated do
      if #[`MLeft, `MRight].contains violation.familyOwner then
        IO.eprintln s!"mutual projection check violation: {repr violation}"
    for violation in Check.check wGenerated do
      if violation.familyOwner == `Wty then
        IO.eprintln s!"Wty projection check violation: {repr violation}"
  return if state.failed.isEmpty then 0 else 1
