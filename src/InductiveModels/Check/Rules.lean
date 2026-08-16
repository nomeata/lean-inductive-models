import InductiveModels.Check.Certificates

/-!
# The per-slot structural checks

One check for each public model slot: constant pairs, recursor rules,
unit-like witnesses, K reductions, structure eta, and intrinsic projections.
The small exact type synthesizer used by the projection rule reads only
declaration and local binder types, unfolding transparent export syntax and
nothing else.
-/

open Lean

namespace InductiveModels.Check

def checkPair (table : Correspondence) (declarations : DeclarationTypes)
    (pair : ConstantPair) : Array Violation := Id.run do
  let mut violations : Array Violation := #[]
  let models := declarations.findD pair.model #[]
  if models.isEmpty then
    return #[.missingPublic pair.owner pair.model]
  if models.size != 1 then
    return #[.duplicatePublic pair.owner pair.model models.size]
  let some ownerDecl := (declarations.findD pair.owner #[])[0]?
    | return #[.declarationType pair.owner pair.model]
  let modelDecl := models[0]!
  violations := violations ++ checkImplementationDecl pair.owner modelDecl
  if ownerDecl.levelParams.length != modelDecl.levelParams.length then
    violations := violations.push (.universeArity pair.owner pair.model
      ownerDecl.levelParams.length modelDecl.levelParams.length)
  else
    let expected := table.expectedType
      ownerDecl.levelParams modelDecl.levelParams ownerDecl.type
    unless expected == modelDecl.type do
      violations := violations.push (.declarationType pair.owner pair.model)
  return violations

def checkIota (x : Export) (constructors : Constructors) (family : Family)
    (declarations : DeclarationTypes) (iota : Naming.Iota) : Array Violation := Id.run do
  let models := declarations.findD iota.name #[]
  if models.isEmpty then
    return #[.missingPublic iota.recursor iota.name]
  if models.size != 1 then
    return #[.duplicatePublic iota.recursor iota.name models.size]
  let some (ownerParams, ownerType) :=
      iotaPropositionWith? x constructors family.ownerDecl iota.recursor iota.ruleIndex
    | return #[.declarationType iota.recursor iota.name]
  let model := models[0]!
  let mut violations := checkTheoremDecl iota.recursor model
  if ownerParams.length != model.levelParams.length then
    return violations.push
      (.universeArity iota.recursor iota.name ownerParams.length model.levelParams.length)
  let expected := family.correspondence.expectedIotaType ownerParams model.levelParams ownerType
  if model.type != expected then
    violations := violations.push (.declarationType iota.recursor iota.name)
  return violations

def checkUnitlike (x : Export) (family : Family)
    (declarations : DeclarationTypes) (metadata : Naming.Metadata) : Array Violation := Id.run do
  let models := declarations.findD metadata.name #[]
  if models.isEmpty then return #[.missingPublic metadata.owner metadata.name]
  if models.size != 1 then
    return #[.duplicatePublic metadata.owner metadata.name models.size]
  let some (ownerParams, ownerType) :=
      unitlikeProposition? x family.ownerDecl metadata.owner
    | return #[.declarationType metadata.owner metadata.name]
  let model := models[0]!
  let mut violations : Array Violation := #[]
  if ownerParams.length != model.levelParams.length then
    return violations.push (.universeArity metadata.owner metadata.name
      ownerParams.length model.levelParams.length)
  let expected := family.correspondence.expectedIotaType
    ownerParams model.levelParams ownerType
  if model.type != expected then
    violations := violations.push (.declarationType metadata.owner metadata.name)
  return violations

def checkRuleK (x : Export) (family : Family) (declarations : DeclarationTypes)
    (metadata : Naming.Metadata) : Array Violation := Id.run do
  let models := declarations.findD metadata.name #[]
  if models.isEmpty then return #[.missingPublic metadata.owner metadata.name]
  if models.size != 1 then
    return #[.duplicatePublic metadata.owner metadata.name models.size]
  let some (ownerParams, ownerType) := ruleKProposition? x family.ownerDecl metadata.owner
    | return #[.declarationType metadata.owner metadata.name]
  let model := models[0]!
  let mut violations : Array Violation := #[]
  if ownerParams.length != model.levelParams.length then
    return violations.push (.universeArity metadata.owner metadata.name
      ownerParams.length model.levelParams.length)
  let expected := family.correspondence.expectedIotaType ownerParams model.levelParams ownerType
  if model.type != expected then
    violations := violations.push (.declarationType metadata.owner metadata.name)
  return violations

private partial def instantiateForallsExact (expression : Expr) (arguments : Array Expr)
    (index : Nat := 0) : Option Expr :=
  match arguments[index]? with
  | none => some expression
  | some argument => match expression with
    | .forallE _ _ body _ => instantiateForallsExact (body.instantiate1 argument) arguments (index + 1)
    | _ => none

/-- Check the exact non-Prop structure-eta statement.  Reconstruction is
through the intrinsic projection slots for the owner's fields, in constructor
telescope order; exported projection wrapper declarations are irrelevant. -/
def checkEta (x : Export) (normalizer : ExactNormalizationEnv) (family : Family)
    (declarations : DeclarationTypes) (metadata : Naming.Metadata) : Array Violation := Id.run do
  let models := declarations.findD metadata.name #[]
  if models.isEmpty then return #[.missingPublic metadata.owner metadata.name]
  if models.size != 1 then
    return #[.duplicatePublic metadata.owner metadata.name models.size]
  let model := models[0]!
  let .induct ownerTypes constructors _ := x.decls[family.ownerDecl]!
    | return #[.declarationType metadata.owner metadata.name]
  let some ownerType := ownerTypes.find? (fun type => type.name == metadata.owner)
    | return #[.declarationType metadata.owner metadata.name]
  let [constructorName] := ownerType.ctors
    | return #[.declarationType metadata.owner metadata.name]
  let some constructor := constructors.find? fun candidate =>
      candidate.name == constructorName && candidate.induct == metadata.owner
    | return #[.declarationType metadata.owner metadata.name]
  unless ownerType.isKernelStructureLike constructors &&
      !normalizer.isPropositionFormer ownerType.type do
    return #[.declarationType metadata.owner metadata.name]
  if ownerType.levelParams.length != model.levelParams.length then
    return #[.universeArity metadata.owner metadata.name
      ownerType.levelParams.length model.levelParams.length]
  let some typePair := family.correspondence.typeFormers.find?
      (·.owner == metadata.owner)
    | return #[.declarationType metadata.owner metadata.name]
  let some constructorPair := family.correspondence.constructors.find?
      (·.owner == constructorName)
    | return #[.declarationType metadata.owner metadata.name]
  let levels := model.levelParams.map Level.param
  let mappedOwnerType := family.correspondence.expectedType
    ownerType.levelParams model.levelParams ownerType.type
  let (parameterBinders, ownerResult) : Array OpenBinder × Expr := openForalls
    ((`_check.structureEtaOwner).append metadata.owner) mappedOwnerType
  unless parameterBinders.size == ownerType.numParams && ownerType.numIndices == 0 do
    return #[.declarationType metadata.owner metadata.name]
  let params := parameterBinders.map fun binder => binder.value
  let .sort carrierLevel := normalizer.whnf ownerResult
    | return #[.declarationType metadata.owner metadata.name]
  let carrier := mkAppN (.const typePair.model levels) params
  let selfValue := mkFVar (FVarId.mk
    ((`_check.structureEtaSelf).append metadata.owner))
  let selfBinder : OpenBinder :=
    { name := `x, type := carrier, info := .default, value := selfValue }
  let mappedConstructorType := family.correspondence.expectedType
    constructor.levelParams model.levelParams constructor.type
  let some constructorTail := instantiateForallsExact mappedConstructorType params
    | return #[.declarationType metadata.owner metadata.name]
  let (fieldBinders, _) : Array OpenBinder × Expr := openForalls
    ((`_check.structureEtaFields).append metadata.owner) constructorTail
  unless fieldBinders.size == constructor.numFields do
    return #[.declarationType metadata.owner metadata.name]
  let mut fields : Array Expr := #[]
  for fieldIndex in [0:constructor.numFields] do
    let some projection := family.correspondence.projections.find? fun projection =>
        projection.owner == metadata.owner && projection.fieldIndex == fieldIndex
      | return #[.declarationType metadata.owner metadata.name]
    fields := fields.push <| mkAppN (.const projection.name levels) (params.push selfValue)
  let reconstruction := mkAppN (.const constructorPair.model levels) (params ++ fields)
  let expectedBody := mkAppN (.const ``Eq [carrierLevel])
    #[carrier, selfValue, reconstruction]
  let expected := closeForalls (parameterBinders.push selfBinder) expectedBody
  if model.type != expected then
    return #[.declarationType metadata.owner metadata.name]
  return #[]

abbrev ExactLocals := Array (FVarId × Expr)

private def ExactLocals.typeOf? (locals : ExactLocals) (id : FVarId) : Option Expr :=
  (locals.find? (·.1 == id)).map (·.2)

mutual

/-- A deliberately small, exact type synthesizer for the result of an
exported projection declaration. Declaration and local binder types suffice;
when their head is hidden, it unfolds only transparent definitions in the
export syntax. The projection case follows the exact recovered primitive
projection interface. -/
private partial def inferExactType? (structures : StructureOwners)
    (normalizer : ExactNormalizationEnv)
    (declarations : DeclarationTypes)
    (locals : ExactLocals) : Expr → Option Expr
  | .sort level => some (.sort (.succ level))
  | .fvar id => locals.typeOf? id
  | .const name levels => do
      let declaration ← (declarations.findD name #[])[0]?
      if declaration.levelParams.length != levels.length then none
      return declaration.type.instantiateLevelParams declaration.levelParams levels
  | .app function argument => do
      let functionType := normalizer.whnf
        (← inferExactType? structures normalizer declarations locals function)
      let .forallE _ _ body _ := functionType | none
      return body.instantiate1 argument
  | .lam name domain body info => do
      let value := mkFVar (FVarId.mk ((`_check.exactLam).mkNum locals.size))
      let bodyType ← inferExactType? structures normalizer declarations
        (locals.push (value.fvarId!, domain)) (body.instantiate1 value)
      return .forallE name domain (bodyType.abstract #[value]) info
  | .forallE name domain body info => do
      let domainLevel ← inferExactSortLevel? structures normalizer declarations locals domain
      let value := mkFVar (FVarId.mk ((`_check.exactPi).mkNum locals.size))
      let bodyLevel ← inferExactSortLevel? structures normalizer declarations
        (locals.push (value.fvarId!, domain)) (body.instantiate1 value)
      let _ := name
      let _ := info
      return .sort (Level.imax domainLevel bodyLevel).normalize
  | .letE _ _ value body _ =>
      inferExactType? structures normalizer declarations locals (body.instantiate1 value)
  | .mdata _ body => inferExactType? structures normalizer declarations locals body
  | .proj owner fieldIndex struct => do
      let structType := normalizer.whnf
        (← inferExactType? structures normalizer declarations locals struct)
      let .const structOwner levels := structType.getAppFn | none
      unless structOwner == owner do none
      let (type, constructors) ← structures.find? owner
      let constructorName ← type.ctors.head?
      let constructor ← constructors.find? fun constructor =>
        constructor.name == constructorName && constructor.induct == owner
      unless type.ctors == [constructorName] do none
      unless constructor.levelParams.length == levels.length do none
      let ownerArguments := structType.getAppArgs
      unless ownerArguments.size == type.numParams + type.numIndices do none
      let params := ownerArguments.extract 0 type.numParams
      let mut current := constructor.type.instantiateLevelParams constructor.levelParams levels
      for param in params do
        let .forallE _ _ body _ := normalizer.whnf current | none
        current := body.instantiate1 param
      let ownerIsProp := normalizer.isPropositionFormer type.type
      for earlier in [0:fieldIndex + 1] do
        let .forallE _ fieldType rest _ := normalizer.whnf current | none
        let fieldIsProp :=
          inferExactSortLevel? structures normalizer declarations locals fieldType == some .zero
        if earlier == fieldIndex then
          if ownerIsProp && !fieldIsProp then none else return fieldType
        if ownerIsProp && rest.hasLooseBVars && !fieldIsProp then none
        current := rest.instantiate1 (.proj owner earlier struct)
      none
  | .lit (.natVal _) => some (.const ``Nat [])
  | .lit (.strVal _) => some (.const ``String [])
  | .bvar _ | .mvar _ => none

partial def inferExactSortLevel? (structures : StructureOwners)
    (normalizer : ExactNormalizationEnv)
    (declarations : DeclarationTypes)
    (locals : ExactLocals) (expression : Expr) : Option Level := do
  let .sort level := normalizer.whnf
    (← inferExactType? structures normalizer declarations locals expression) | none
  return level

end

/-- Check one intrinsic projection and its literal constructor rule.

There is no source projection declaration to rewrite.  Both types are
synthesized from the unique constructor telescope.  References to earlier
fields in a dependent result become applications of the corresponding earlier
intrinsic projections. -/
def checkProjection (x : Export) (structures : StructureOwners)
    (normalizer : ExactNormalizationEnv) (family : Family)
    (declarations : DeclarationTypes) (oneLayerCertificate : Phase1OneLayerCertificate)
    (projection : Naming.Projection) : Array Violation := Id.run do
  let projectionModels := declarations.findD projection.name #[]
  if projectionModels.isEmpty then
    return #[.missingPublic projection.owner projection.name]
  if projectionModels.size != 1 then
    return #[.duplicatePublic projection.owner projection.name projectionModels.size]
  let ruleModels := declarations.findD projection.iota #[]
  if ruleModels.isEmpty then return #[.missingPublic projection.owner projection.iota]
  if ruleModels.size != 1 then
    return #[.duplicatePublic projection.owner projection.iota ruleModels.size]
  let .induct _ ownerConstructors _ := x.decls[family.ownerDecl]!
    | return #[.declarationType projection.owner projection.name]
  let some constructor := ownerConstructors.find? (·.induct == projection.owner)
    | return #[.declarationType projection.owner projection.name]
  let some constructorPair := family.correspondence.constructors.find?
      (·.owner == constructor.name)
    | return #[.declarationType projection.owner projection.name]
  let ownerTypes : List EIndType := match x.decls[family.ownerDecl]! with
    | .induct types _ _ => types
    | _ => []
  let some ownerType := ownerTypes.find? (fun (type : EIndType) => type.name == projection.owner)
    | return #[.declarationType projection.owner projection.name]
  let model := projectionModels[0]!
  let ruleModel := ruleModels[0]!
  if let .malformed slot := oneLayerCertificate then
    return #[.declarationType projection.owner slot]
  if ownerType.levelParams.length != model.levelParams.length then
    return #[.universeArity projection.owner projection.name
      ownerType.levelParams.length model.levelParams.length]
  if ownerType.levelParams.length != ruleModel.levelParams.length then
    return #[.universeArity projection.owner projection.iota
      ownerType.levelParams.length ruleModel.levelParams.length]
  let mappedConstructorType := family.correspondence.expectedType
    constructor.levelParams model.levelParams constructor.type
  let (constructorBinders, constructorResult) : Array OpenBinder × Expr := openForalls
    ((`_check.intrinsicProjectionCtor).append projection.name) mappedConstructorType
  -- Kernel insertion β-normalizes a head application in a constructor-local
  -- binder type. Mirror exactly that step for the theorem's outer binders, but
  -- retain written `let`s and named model constants so the public statement
  -- remains literal. The unnormalized binders below still drive the RHS.
  let propositionLiteral := propositionProjectionIotaUsesLiteralField ownerType
  let theoremBinders := if oneLayerCertificate matches .valid || propositionLiteral then
      constructorBinders
    else constructorBinders.map fun binder =>
      { binder with type := normalizer.beta binder.type }
  unless constructorBinders.size == constructor.numParams + constructor.numFields do
    return #[.declarationType projection.owner projection.name]
  let constructorArgs := constructorBinders.map fun (binder : OpenBinder) => binder.value
  let params := constructorArgs.extract 0 constructor.numParams
  let fields := constructorArgs.extract constructor.numParams constructorArgs.size
  let levels := model.levelParams.map Level.param
  let some typePair := family.correspondence.typeFormers.find? (·.owner == projection.owner)
    | return #[.declarationType projection.owner projection.name]
  let mappedOwnerType := family.correspondence.expectedType
    ownerType.levelParams model.levelParams ownerType.type
  let (ownerBinders, _) : Array OpenBinder × Expr := openForalls
    ((`_check.intrinsicProjectionOwner).append projection.name) mappedOwnerType
  let ownerArity := ownerType.numParams + ownerType.numIndices
  unless ownerBinders.size == ownerArity do
    return #[.declarationType projection.owner projection.name]
  let ownerArgs := ownerBinders.map fun (binder : OpenBinder) => binder.value
  let ownerParams := ownerArgs.extract 0 ownerType.numParams
  let some projectionFieldsType := instantiateForallsExact mappedConstructorType ownerParams
    | return #[.declarationType projection.owner projection.name]
  let (projectionFieldBinders, _) : Array OpenBinder × Expr := openForalls
    ((`_check.intrinsicProjectionFields).append projection.name) projectionFieldsType
  let some selectedBinder := projectionFieldBinders[projection.fieldIndex]?
    | return #[.declarationType projection.owner projection.name]
  let selfValue := mkFVar (FVarId.mk
    ((`_check.intrinsicProjectionSelf).append projection.name))
  let selfBinder : OpenBinder :=
    { name := `self, type := mkAppN (.const typePair.model levels) ownerArgs,
      info := .default, value := selfValue }
  let projectionFieldArgs := projectionFieldBinders.map fun (binder : OpenBinder) => binder.value
  let mut projectionResult := selectedBinder.type
  for earlier in [:projection.fieldIndex] do
    let earlierField := projectionFieldArgs[earlier]!
    let earlierProjection := mkAppN
      (.const (Naming.projectionName projection.owner earlier) levels) (ownerArgs.push selfValue)
    projectionResult := projectionResult.replace fun subexpression =>
      if subexpression == earlierField then some earlierProjection else none
  let expectedProjectionType := closeForalls
    (ownerBinders.push selfBinder) projectionResult
  let mut violations := checkImplementationDecl projection.owner model
  violations := violations ++ checkTheoremDecl projection.owner ruleModel
  unless model.type == expectedProjectionType do
    violations := violations.push (.declarationType projection.owner projection.name)

  let major := mkAppN (.const constructorPair.model levels) constructorArgs
  let constructorIndices := constructorResult.getAppArgs.extract constructor.numParams ownerArity
  unless constructorIndices.size == ownerType.numIndices do
    return violations.push (.declarationType projection.owner projection.iota)
  let some alpha := instantiateForallsExact expectedProjectionType
      (params ++ constructorIndices ++ #[major])
    | return violations.push (.declarationType projection.owner projection.iota)
  let lhs := mkAppN (.const projection.name levels) (params ++ constructorIndices ++ #[major])

  let sourceConstructorType := constructor.type
  let (sourceBinders, _) : Array OpenBinder × Expr := openForalls
    ((`_check.intrinsicProjectionSource).append projection.name) sourceConstructorType
  let some sourceField := sourceBinders[constructor.numParams + projection.fieldIndex]?
    | return violations.push (.declarationType projection.owner projection.iota)
  let sourceLocals := sourceBinders.map fun (binder : OpenBinder) =>
    (binder.value.fvarId!, binder.type)
  -- The expected right-hand side is the constructor field binder, on every
  -- route and with no predicate left to select it.  Generation states exactly
  -- this ([`InductiveModels.addProjectionModels`]), and where the field's own
  -- type and the projection's codomain are not the same type — so that only a
  -- transport could bridge them — it declines the owner rather than stating a
  -- rule at all ([`InductiveModels.Decline.projectionCodomain`]).
  let some rhs := fields[projection.fieldIndex]?
    | return violations.push (.declarationType projection.owner projection.iota)
  let some sourceEqLevel :=
      inferExactSortLevel? structures normalizer declarations sourceLocals sourceField.type
    | return violations.push (.declarationType projection.owner projection.iota)
  let eqLevel := renameLevelParamNamesExact
    constructor.levelParams model.levelParams sourceEqLevel
  let expectedBody := mkAppN (.const ``Eq [eqLevel]) #[alpha, lhs, rhs]
  let expected := closeForalls theoremBinders expectedBody
  unless ruleModel.type == expected do
    violations := violations.push (.declarationType projection.owner projection.iota)
  return violations

end InductiveModels.Check
