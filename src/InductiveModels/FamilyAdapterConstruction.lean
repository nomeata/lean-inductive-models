import InductiveModels.FamilyAdapterShadow
import InductiveModels.Simple

/-!
# Generic family-adapter construction primitives

This module is the disabled construction seam behind `FamilyAdapterPlan`.
It reads exact finite telescope dimensions from the plan and installed
declaration metadata.  It does not select a production route or emit a public
declaration.
-/

open Lean Meta

namespace InductiveModels.FamilyAdapter

/-- A keyed construction obligation.  These are semantic failures of an exact
certificate, never eligibility predicates or cardinality limits. -/
inductive ConstructionIssue where
  | incompleteShadow (reason : ShadowReason)
  | invalidPlan (error : PlanError)
  | missingInstalledMemberMap (member : MemberKey) (map : Name)
  | installedMemberMapTypeMismatch (member : MemberKey) (map : Name)
  | missingInstalledRecursor (member : MemberKey) (recursor : Name)
  | shortInstalledRecursorPrefix (member : MemberKey) (recursor : Name)
  | missingInstalledMinor (rule : RuleKey)
  | ambiguousInstalledMinor (rule : RuleKey)
  | malformedInstalledMinor (rule : RuleKey)
  | missingInstalledHypothesis (rule : RuleKey) (occurrence : OccurrenceKey)
  | ambiguousInstalledHypothesis (rule : RuleKey) (occurrence : OccurrenceKey)
  | installedHypothesisMismatch (rule : RuleKey) (occurrence : OccurrenceKey)
      (expected actual : Nat)
  | missingMemberMap (member : MemberKey)
  | missingOccurrenceMap (occurrence : OccurrenceKey)
  | missingContainerMap (occurrence : OccurrenceKey)
  | dependentFieldTransport (constructor : ConstructorKey) (fieldIndex : Nat)
  | indexFibreMismatch (constructor : ConstructorKey)
  deriving Inhabited, BEq, Repr

abbrev ConstructionM := ExceptT ConstructionIssue GenM

structure PrototypeBuild where
  declarations : Array Declaration := #[]
  certificate : Option FamilyAdapterCertificate := none
  minorHypotheses : Array MinorHypothesisCertificate := #[]
  issues : Array ConstructionIssue := #[]
  deriving Inhabited

private def failConstruction (issue : ConstructionIssue) : ConstructionM α :=
  throwThe ConstructionIssue issue

private def liftGen (action : GenM α) : ConstructionM α :=
  ExceptT.lift action

private def generatedType (name : Name) : GenM Expr := do
  let some information := (← getEnv).constants.find? name
    | badShape s!"family-adapter prototype declaration {name} is absent"
  return information.type

private def prototypeName (root owner suffix : Name) : Name :=
  Name.str (root.append owner) suffix.toString

private def ensurePrototypeFresh (name : Name) : GenM Unit := do
  if (← getEnv).constants.contains name then
    badShape s!"family-adapter prototype name {name} is already installed"

private def identityMemberCertificate (plan : FamilyAdapterPlan) (root : Name)
    (member : MemberPlan) : GenM (Array Declaration × MemberCertificate) := do
  let levels := plan.levelParams.map Level.param
  let arity := member.parameterArity + member.indexArity
  let carrierType ← generatedType member.publicCarrier
  let forward := prototypeName root member.key.owner `forward
  let backward := prototypeName root member.key.owner `backward
  let backwardForward := prototypeName root member.key.owner `backwardForward
  let forwardBackward := prototypeName root member.key.owner `forwardBackward
  for name in #[forward, backward, backwardForward, forwardBackward] do
    ensurePrototypeFresh name
  let mapType := fun (source target : Name) =>
    forallBoundedTelescope carrierType (some arity) fun arguments _ =>
      withLocalDeclD `value (mkAppN (.const source levels) arguments) fun value =>
        mkForallFVars (arguments.push value) (mkAppN (.const target levels) arguments)
  let mapDeclaration := fun (name source target : Name) => do
    let type ← mapType source target
    let value ← forallTelescope type fun arguments _ =>
      mkLambdaFVars arguments arguments.back!
    let declaration := Declaration.defnDecl
      { name, levelParams := plan.levelParams, type, value,
        hints := .abbrev, safety := .safe }
    addChecked declaration
    return declaration
  let forwardDeclaration ← mapDeclaration forward member.publicCarrier
    member.implementationCarrier
  let backwardDeclaration ← mapDeclaration backward member.implementationCarrier
    member.publicCarrier
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error message => badShape s!"family-adapter prototype needs Eq ({message})"
  let lawDeclaration := fun (name carrier first second : Name) => do
    let type ← forallBoundedTelescope carrierType (some arity) fun arguments _ =>
      withLocalDeclD `value (mkAppN (.const carrier levels) arguments) fun value => do
        let lhs := mkAppN (.const second levels)
          (arguments.push (mkAppN (.const first levels) (arguments.push value)))
        let alpha := mkAppN (.const carrier levels) arguments
        mkForallFVars (arguments.push value)
          (eqi.mk' (← ilevel alpha) alpha lhs value)
    let value ← forallTelescope type fun arguments result => do
      let #[alpha, lhs, _] := result.getAppArgs
        | badShape s!"family-adapter prototype law {name} is not an equality"
      mkLambdaFVars arguments (eqi.refl' (← ilevel alpha) alpha lhs)
    let declaration := Declaration.thmDecl
      { name, levelParams := plan.levelParams, type, value }
    addChecked declaration
    return declaration
  let backwardForwardDeclaration ← lawDeclaration backwardForward member.publicCarrier
    forward backward
  let forwardBackwardDeclaration ← lawDeclaration forwardBackward member.implementationCarrier
    backward forward
  let certificate : MemberCertificate :=
    { key := member.key
      maps := { forward, backward, backwardForward, forwardBackward } }
  return (#[forwardDeclaration, backwardDeclaration, backwardForwardDeclaration,
    forwardBackwardDeclaration], certificate)

private def memberMapType (plan : FamilyAdapterPlan) (member : MemberPlan)
    (source target : Name) : GenM Expr := do
  let levels := plan.levelParams.map Level.param
  let arity := member.parameterArity + member.indexArity
  let carrierType ← generatedType source
  forallBoundedTelescope carrierType (some arity) fun arguments _ =>
    withLocalDeclD `value (mkAppN (.const source levels) arguments) fun value =>
      mkForallFVars (arguments.push value) (mkAppN (.const target levels) arguments)

private def memberLawType (plan : FamilyAdapterPlan) (member : MemberPlan)
    (carrier first second : Name) : GenM Expr := do
  let levels := plan.levelParams.map Level.param
  let arity := member.parameterArity + member.indexArity
  let carrierType ← generatedType carrier
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error message => badShape s!"family-adapter prototype needs Eq ({message})"
  forallBoundedTelescope carrierType (some arity) fun arguments _ =>
    withLocalDeclD `value (mkAppN (.const carrier levels) arguments) fun value => do
      let lhs := mkAppN (.const second levels)
        (arguments.push (mkAppN (.const first levels) (arguments.push value)))
      let alpha := mkAppN (.const carrier levels) arguments
      mkForallFVars (arguments.push value)
        (eqi.mk' (← ilevel alpha) alpha lhs value)

private def validateMemberMap (member : MemberKey) (name : Name) (expected : Expr) :
    GenM (Option ConstructionIssue) := do
  let some actual := (← getEnv).constants.find? name |>.map (·.type)
    | return some (.missingInstalledMemberMap member name)
  return if actual == expected then none
    else some (.installedMemberMapTypeMismatch member name)

private def validateInstalledEquivalence (plan : FamilyAdapterPlan) (member : MemberPlan)
    (maps : EquivalenceCertificate) : GenM (Array ConstructionIssue) := do
  let expected := #[
    (maps.forward, ← memberMapType plan member member.publicCarrier
      member.implementationCarrier),
    (maps.backward, ← memberMapType plan member member.implementationCarrier
      member.publicCarrier),
    (maps.backwardForward, ← memberLawType plan member member.publicCarrier
      maps.forward maps.backward),
    (maps.forwardBackward, ← memberLawType plan member member.implementationCarrier
      maps.backward maps.forward)]
  return (← expected.filterMapM fun (name, type) => validateMemberMap member.key name type)

/-- Resolve installed member equivalences. Identity boundaries receive fresh,
kernel-checked private aliases; changed simultaneous members reuse the exact
maps and laws already recorded by `Iso.familyImplementation?`. -/
def prototypeMemberCertificates (plan : FamilyAdapterPlan) (iso : Iso) (root : Name) :
    GenM (Array Declaration × Array MemberCertificate × Array ConstructionIssue) := do
  let mut declarations := #[]
  let mut certificates := #[]
  let mut issues := #[]
  for member in plan.members do
    if let some installed := iso.familyImplementation?.bind fun family =>
        family.members.find? (·.owner == member.key.owner) then
      let maps : EquivalenceCertificate :=
        { forward := installed.roll
          backward := installed.unroll
          backwardForward := installed.unrollRoll
          forwardBackward := installed.rollUnroll }
      let certificate : MemberCertificate :=
        { key := member.key
          maps }
      let mapIssues ← validateInstalledEquivalence plan member maps
      if mapIssues.isEmpty then certificates := certificates.push certificate
      else issues := issues ++ mapIssues
    else if member.publicCarrier == member.implementationCarrier then
      let (added, certificate) ← identityMemberCertificate plan root member
      declarations := declarations ++ added
      certificates := certificates.push certificate
    else
      let occurrence := plan.occurrences.find? (·.key.target == member.key)
      match occurrence with
      | some occurrence => issues := issues.push (.missingOccurrenceMap occurrence.key)
      | none => issues := issues.push (.missingMemberMap member.key)
  return (declarations, certificates, issues)

/-- Exact-sort dependent package for an arbitrary finite field telescope. -/
def packedTelescopeType (fields : Array Expr) : GenM Expr :=
  if fields.isEmpty then pure (punitT .zero) else tightTowerTy fields 0

private partial def packTelescopeValueAt (fields values : Array Expr) (fieldIndex : Nat) :
    GenM Expr := do
  if fieldIndex + 1 == fields.size then return values[fieldIndex]!
  let (u, v, alpha, beta) ← tightTowerAt fields fieldIndex
    (values.extract 0 fieldIndex)
  let tail ← packTelescopeValueAt fields values (fieldIndex + 1)
  return psigmaMk u v alpha beta values[fieldIndex]! tail

def packTelescopeValue (fields values : Array Expr) : GenM Expr := do
  unless fields.size == values.size do
    badShape "a family-adapter package has inconsistent finite vectors"
  if fields.isEmpty then pure (punitUnit .zero) else packTelescopeValueAt fields values 0

def unpackTelescopeValue (fields : Array Expr) (value : Expr) : GenM (Array Expr) :=
  if fields.isEmpty then pure #[] else tightTowerProjs fields 0 value

private def certificateFor? (certificates : Array MemberCertificate) (key : MemberKey) :
    Option MemberCertificate :=
  certificates.find? (·.key == key)

private def mapName (certificate : MemberCertificate) (forward : Bool) : Name :=
  if forward then certificate.maps.forward else certificate.maps.backward

private def lawName (certificate : MemberCertificate) (forward : Bool) : Name :=
  if forward then certificate.maps.backwardForward else certificate.maps.forwardBackward

private def containerForOccurrences? (plan : FamilyAdapterPlan)
    (occurrences : Array OccurrenceKey) : Option ContainerMapPlan := do
  let firstKey ← occurrences[0]?
  let first ← plan.containerMaps.find? (·.key == firstKey)
  for occurrence in occurrences do
    let current ← plan.containerMaps.find? (·.key == occurrence)
    unless current.parameterArity == first.parameterArity &&
        current.indexArity == first.indexArity && current.maps == first.maps &&
        current.forwardType == first.forwardType && current.backwardType == first.backwardType &&
        current.backwardForwardType == first.backwardForwardType &&
        current.forwardBackwardType == first.forwardBackwardType do none
  return first

private def applyContainerMap (plan : FamilyAdapterPlan) (container : ContainerMapPlan)
    (forward : Bool) (parameters : Array Expr) (sourceType targetType value : Expr) :
    ConstructionM Expr := do
  unless parameters.size == container.parameterArity do
    failConstruction (.missingContainerMap container.key)
  let name := if forward then container.maps.forward else container.maps.backward
  let recordedType := if forward then container.forwardType else container.backwardType
  let some installed := (← getEnv).constants.find? name |>.map (·.type)
    | failConstruction (.missingContainerMap container.key)
  unless installed == recordedType do failConstruction (.missingContainerMap container.key)
  let mut type ← instantiateForall recordedType parameters
  let mut indices := #[]
  for _ in [:container.indexArity] do
    let .forallE binderName domain body _ := type
      | failConstruction (.missingContainerMap container.key)
    let index ← mkFreshExprMVar domain .natural binderName
    indices := indices.push index
    type := body.instantiate1 index
  let .forallE _ domain _ _ := type
    | failConstruction (.missingContainerMap container.key)
  unless ← isDefEq domain sourceType do
    failConstruction (.missingContainerMap container.key)
  let resolvedIndices ← indices.mapM instantiateMVars
  let mut unresolved := false
  for index in resolvedIndices do unresolved := unresolved || (← hasAssignableMVar index)
  if unresolved then
    failConstruction (.missingContainerMap container.key)
  let application := mkAppN (.const name (plan.levelParams.map Level.param))
    (parameters ++ resolvedIndices ++ #[value])
  unless ← isDefEq (← inferType application) targetType do
    failConstruction (.missingContainerMap container.key)
  return application

private def applyContainerLaw (plan : FamilyAdapterPlan) (container : ContainerMapPlan)
    (forward : Bool) (parameters : Array Expr) (sourceType value : Expr) :
    ConstructionM Expr := do
  unless parameters.size == container.parameterArity do
    failConstruction (.missingContainerMap container.key)
  let name := if forward then container.maps.backwardForward
    else container.maps.forwardBackward
  let recordedType := if forward then container.backwardForwardType
    else container.forwardBackwardType
  let some installed := (← getEnv).constants.find? name |>.map (·.type)
    | failConstruction (.missingContainerMap container.key)
  unless installed == recordedType do failConstruction (.missingContainerMap container.key)
  let mut type ← instantiateForall recordedType parameters
  let mut indices := #[]
  for _ in [:container.indexArity] do
    let .forallE binderName domain body _ := type
      | failConstruction (.missingContainerMap container.key)
    let index ← mkFreshExprMVar domain .natural binderName
    indices := indices.push index
    type := body.instantiate1 index
  let .forallE _ domain _ _ := type
    | failConstruction (.missingContainerMap container.key)
  unless ← isDefEq domain sourceType do
    failConstruction (.missingContainerMap container.key)
  let resolvedIndices ← indices.mapM instantiateMVars
  let mut unresolved := false
  for index in resolvedIndices do unresolved := unresolved || (← hasAssignableMVar index)
  if unresolved then
    failConstruction (.missingContainerMap container.key)
  return mkAppN (.const name (plan.levelParams.map Level.param))
    (parameters ++ resolvedIndices ++ #[value])

private def trimBinderBody? (occurrences : Array OccurrenceKey) :
    Option (Array OccurrenceKey) := do
  let mut result := #[]
  for occurrence in occurrences do
    let some first := occurrence.expressionPath[0]? | none
    unless first == .binderBody do none
    result := result.push
      { occurrence with
        expressionPath := occurrence.expressionPath.extract 1 occurrence.expressionPath.size
        binderDepth := occurrence.binderDepth - 1 }
  return result

private partial def mapFieldValue (plan : FamilyAdapterPlan)
    (certificates : Array MemberCertificate) (parameters : Array Expr) (forward : Bool)
    (constructor : ConstructorKey) (fieldIndex : Nat)
    (occurrences : Array OccurrenceKey) (sourceType targetType value : Expr) :
    ConstructionM Expr := do
  if ← isDefEq sourceType targetType then return value
  if occurrences.isEmpty then
    failConstruction (.dependentFieldTransport constructor fieldIndex)
  let direct := occurrences.find? (·.expressionPath.isEmpty)
  if let some occurrence := direct then
    unless occurrences.size == 1 do failConstruction (.missingContainerMap occurrence)
    let some certificate := certificateFor? certificates occurrence.target
      | failConstruction (.missingOccurrenceMap occurrence)
    let some member := plan.members.find? (·.key == occurrence.target)
      | failConstruction (.missingOccurrenceMap occurrence)
    let expectedSource := if forward then member.publicCarrier else member.implementationCarrier
    let expectedTarget := if forward then member.implementationCarrier else member.publicCarrier
    unless sourceType.getAppFn.constName? == some expectedSource &&
        targetType.getAppFn.constName? == some expectedTarget do
      failConstruction (.missingContainerMap occurrence)
    let levels := plan.levelParams.map Level.param
    return mkAppN (.const (mapName certificate forward) levels)
      (sourceType.getAppArgs.push value)
  if let some container := containerForOccurrences? plan occurrences then
    return ← applyContainerMap plan container forward parameters sourceType targetType value
  let some trimmed := trimBinderBody? occurrences
    | failConstruction (.missingContainerMap occurrences[0]!)
  let .forallE name sourceDomain sourceBody info := sourceType
    | failConstruction (.missingContainerMap occurrences[0]!)
  let .forallE _ targetDomain targetBody _ := targetType
    | failConstruction (.missingContainerMap occurrences[0]!)
  unless ← isDefEq sourceDomain targetDomain do
    failConstruction (.missingContainerMap occurrences[0]!)
  withLocalDecl name info sourceDomain fun argument => do
    let mapped ← mapFieldValue plan certificates parameters forward constructor fieldIndex trimmed
      (sourceBody.instantiate1 argument) (targetBody.instantiate1 argument)
      (mkApp value argument)
    mkLambdaFVars #[argument] mapped

private def applyFunext (funextName : Name) (arguments : Array Expr)
    (left right proof : Expr) : GenM Expr := do
  let mut left := left
  let mut right := right
  let mut proof := proof
  for offset in [:arguments.size] do
    let argument := arguments[arguments.size - 1 - offset]!
    let alpha ← ityp argument
    let u ← ilevel alpha
    let v ← ilevel (← ityp left)
    let beta ← mkLambdaFVars #[argument] (← ityp left)
    let leftLambda := (← mkLambdaFVars #[argument] left).eta
    let rightLambda := (← mkLambdaFVars #[argument] right).eta
    proof := mkAppN (.const funextName [u, v])
      #[alpha, beta, leftLambda, rightLambda, ← mkLambdaFVars #[argument] proof]
    left := leftLambda
    right := rightLambda
  return proof

private partial def fieldRoundTrip (plan : FamilyAdapterPlan)
    (certificates : Array MemberCertificate) (parameters : Array Expr)
    (funextName : Name) (forward : Bool)
    (constructor : ConstructorKey) (fieldIndex : Nat)
    (occurrences : Array OccurrenceKey) (sourceType targetType value : Expr) :
    ConstructionM Expr := do
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error _ => failConstruction (.missingOccurrenceMap occurrences[0]!)
  if ← isDefEq sourceType targetType then
    return eqi.refl' (← ilevel sourceType) sourceType value
  if occurrences.isEmpty then
    failConstruction (.dependentFieldTransport constructor fieldIndex)
  if let some occurrence := occurrences.find? (·.expressionPath.isEmpty) then
    unless occurrences.size == 1 do failConstruction (.missingContainerMap occurrence)
    let some certificate := certificateFor? certificates occurrence.target
      | failConstruction (.missingOccurrenceMap occurrence)
    let levels := plan.levelParams.map Level.param
    return mkAppN (.const (lawName certificate forward) levels)
      (sourceType.getAppArgs.push value)
  if let some container := containerForOccurrences? plan occurrences then
    return ← applyContainerLaw plan container forward parameters sourceType value
  let some trimmed := trimBinderBody? occurrences
    | failConstruction (.missingContainerMap occurrences[0]!)
  let .forallE name domain body info := sourceType
    | failConstruction (.missingContainerMap occurrences[0]!)
  let .forallE _ targetDomain targetBody _ := targetType
    | failConstruction (.missingContainerMap occurrences[0]!)
  unless ← isDefEq domain targetDomain do
    failConstruction (.missingContainerMap occurrences[0]!)
  withLocalDecl name info domain fun argument => do
    let pointwise ← fieldRoundTrip plan certificates parameters funextName forward constructor
      fieldIndex trimmed (body.instantiate1 argument) (targetBody.instantiate1 argument)
      (mkApp value argument)
    let once ← mapFieldValue plan certificates parameters forward constructor fieldIndex occurrences
      sourceType targetType value
    let twice ← mapFieldValue plan certificates parameters (!forward) constructor fieldIndex
      occurrences
      targetType sourceType once
    liftGen <| applyFunext funextName #[argument] (mkApp twice argument)
      (mkApp value argument) pointwise

private def withConstructorTelescopes (plan : FamilyAdapterPlan)
    (constructor : ConstructorPlan)
    (k : MemberPlan → Array Expr → Array Expr → Expr →
      Array Expr → Expr → ConstructionM α) : ConstructionM α := do
  let some owner := plan.members.find? (·.key == constructor.key.owner)
    | failConstruction (.dependentFieldTransport constructor.key 0)
  let publicConstructorType ← liftGen <| generatedType constructor.publicName
  let implementationConstructorType ← liftGen <| generatedType constructor.implementationName
  forallBoundedTelescope publicConstructorType (some owner.parameterArity)
      fun parameters _ => do
    let publicFieldsType ← instantiateForall publicConstructorType parameters
    forallBoundedTelescope publicFieldsType (some constructor.telescope.binders.size)
        fun publicFields publicResult => do
      let implementationFieldsType ←
        instantiateForall implementationConstructorType parameters
      forallBoundedTelescope implementationFieldsType
          (some constructor.telescope.binders.size) fun implementationFields implementationResult =>
        k owner parameters publicFields publicResult implementationFields implementationResult

private def mapFields (plan : FamilyAdapterPlan) (certificates : Array MemberCertificate)
    (constructor : ConstructorPlan) (parameters : Array Expr) (forward : Bool)
    (sourceFields targetFields values : Array Expr) :
    ConstructionM (Array Expr) := do
  unless sourceFields.size == constructor.telescope.binders.size &&
      targetFields.size == sourceFields.size && values.size == sourceFields.size do
    failConstruction (.dependentFieldTransport constructor.key values.size)
  let mut mapped := #[]
  for fieldIndex in [:sourceFields.size] do
    let sourceType ← inferType values[fieldIndex]!
    let targetType := (← inferType targetFields[fieldIndex]!).replaceFVars
      (targetFields.extract 0 fieldIndex) mapped
    let occurrences := constructor.telescope.binders[fieldIndex]!.occurrences
    let value ← mapFieldValue plan certificates parameters forward constructor.key fieldIndex
      occurrences sourceType targetType values[fieldIndex]!
    mapped := mapped.push value
  return mapped

private def packageCongruence (eqi : EqInfo) (fields : Array Expr) (packageType : Expr)
    (before after proofs : Array Expr) : GenM Expr := do
  unless before.size == after.size && proofs.size == before.size do
    badShape "a family-adapter package congruence has inconsistent finite vectors"
  let level ← ilevel packageType
  let mixed := fun (offset : Nat) => (Array.range before.size).map fun index =>
    if index < offset then after[index]! else before[index]!
  let makePackage := fun values => packTelescopeValue fields values
  let base ← makePackage before
  let mut proof := eqi.refl' level packageType base
  for fieldIndex in [:before.size] do
    let alpha ← inferType before[fieldIndex]!
    let alphaLevel ← ilevel alpha
    let atBefore ← makePackage ((mixed fieldIndex).set! fieldIndex before[fieldIndex]!)
    let factor ← transportAlong eqi .zero alphaLevel alpha before[fieldIndex]!
      after[fieldIndex]! proofs[fieldIndex]!
      (eqi.refl' level packageType atBefore) fun value => do
        pure (eqi.mk' level packageType atBefore
          (← makePackage ((mixed fieldIndex).set! fieldIndex value)))
    proof ← transOf eqi level packageType base (← makePackage (mixed fieldIndex))
      (← makePackage (mixed (fieldIndex + 1))) proof factor
  return proof

private def constructorPrototypeNames (root : Name) (constructor : ConstructorPlan) :
    TelescopeCertificate :=
  { constructor := constructor.key
    packSource := prototypeName root constructor.key.constructor `packSource
    packImplementation := prototypeName root constructor.key.constructor `packImplementation
    encode := prototypeName root constructor.key.constructor `encode
    decode := prototypeName root constructor.key.constructor `decode
    decodeEncode := prototypeName root constructor.key.constructor `decodeEncode
    encodeDecode := prototypeName root constructor.key.constructor `encodeDecode
    indexFibre := prototypeName root constructor.key.constructor `indexFibre }

private def packDeclaration (plan : FamilyAdapterPlan) (constructorType : Expr)
    (parameterArity fieldArity : Nat) (name : Name) : GenM Declaration := do
  let type ← forallBoundedTelescope constructorType (some parameterArity)
      fun parameters _ => do
    let fieldsType ← instantiateForall constructorType parameters
    forallBoundedTelescope fieldsType (some fieldArity) fun fields _ => do
      mkForallFVars (parameters ++ fields) (← packedTelescopeType fields)
  let value ← forallBoundedTelescope type (some (parameterArity + fieldArity))
      fun arguments _ => do
    let fields := arguments.extract parameterArity
    mkLambdaFVars arguments (← packTelescopeValue fields fields)
  let declaration := Declaration.defnDecl
    { name, levelParams := plan.levelParams, type, value,
      hints := .abbrev, safety := .safe }
  addChecked declaration
  return declaration

private def codecDeclaration (plan : FamilyAdapterPlan)
    (certificates : Array MemberCertificate) (constructor : ConstructorPlan)
    (name : Name) (forward : Bool) : ConstructionM Declaration := do
  let type ← withConstructorTelescopes plan constructor fun _ parameters publicFields _
      implementationFields _ => do
    let sourceFields := if forward then publicFields else implementationFields
    let targetFields := if forward then implementationFields else publicFields
    let sourcePackage ← liftGen <| packedTelescopeType sourceFields
    let targetPackage ← liftGen <| packedTelescopeType targetFields
    withLocalDeclD `package sourcePackage fun package =>
      mkForallFVars (parameters.push package) targetPackage
  let value ← withConstructorTelescopes plan constructor fun _ parameters publicFields _
      implementationFields _ => do
    let sourceFields := if forward then publicFields else implementationFields
    let targetFields := if forward then implementationFields else publicFields
    let sourcePackage ← liftGen <| packedTelescopeType sourceFields
    withLocalDeclD `package sourcePackage fun package => do
      let sourceValues ← liftGen <| unpackTelescopeValue sourceFields package
      let mapped ← mapFields plan certificates constructor parameters forward sourceFields
        targetFields sourceValues
      mkLambdaFVars (parameters.push package)
        (← liftGen <| packTelescopeValue targetFields mapped)
  let declaration := Declaration.defnDecl
    { name, levelParams := plan.levelParams, type, value,
      hints := .abbrev, safety := .safe }
  liftGen <| addChecked declaration
  return declaration

private def roundTripDeclaration (plan : FamilyAdapterPlan)
    (certificates : Array MemberCertificate) (constructor : ConstructorPlan)
    (names : TelescopeCertificate) (funextName name : Name) (forward : Bool) :
    ConstructionM Declaration := do
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error _ => failConstruction (.dependentFieldTransport constructor.key 0)
  let type ← withConstructorTelescopes plan constructor fun _ parameters publicFields _
      implementationFields _ => do
    let sourceFields := if forward then publicFields else implementationFields
    let sourcePackage ← liftGen <| packedTelescopeType sourceFields
    withLocalDeclD `package sourcePackage fun package => do
      let levels := plan.levelParams.map Level.param
      let first := if forward then names.encode else names.decode
      let second := if forward then names.decode else names.encode
      let lhs := mkAppN (.const second levels)
        (parameters.push (mkAppN (.const first levels) (parameters.push package)))
      mkForallFVars (parameters.push package)
        (eqi.mk' (← ilevel sourcePackage) sourcePackage lhs package)
  let value ← withConstructorTelescopes plan constructor fun _ parameters publicFields _
      implementationFields _ => do
    let sourceFields := if forward then publicFields else implementationFields
    let targetFields := if forward then implementationFields else publicFields
    let sourcePackage ← liftGen <| packedTelescopeType sourceFields
    withLocalDeclD `package sourcePackage fun package => do
      let sourceValues ← liftGen <| unpackTelescopeValue sourceFields package
      let once ← mapFields plan certificates constructor parameters forward sourceFields
        targetFields sourceValues
      let twice ← mapFields plan certificates constructor parameters (!forward) targetFields
        sourceFields once
      let mut proofs := #[]
      for fieldIndex in [:sourceFields.size] do
        let sourceType ← inferType sourceValues[fieldIndex]!
        let targetType := (← inferType targetFields[fieldIndex]!).replaceFVars
          (targetFields.extract 0 fieldIndex) (once.extract 0 fieldIndex)
        let proof ← fieldRoundTrip plan certificates parameters funextName forward
          constructor.key fieldIndex constructor.telescope.binders[fieldIndex]!.occurrences
          sourceType targetType sourceValues[fieldIndex]!
        proofs := proofs.push proof
      let proof ← liftGen <| packageCongruence eqi sourceFields sourcePackage twice
        sourceValues proofs
      mkLambdaFVars (parameters.push package) proof
  let declaration := Declaration.thmDecl
    { name, levelParams := plan.levelParams, type, value }
  liftGen <| addChecked declaration
  return declaration

private def resultIndices (owner : MemberPlan) (result : Expr) : Array Expr :=
  let arguments := result.getAppArgs
  arguments.extract owner.parameterArity
    (min arguments.size (owner.parameterArity + owner.indexArity))

private def withIndexTelescopes (owner : MemberPlan)
    (parameters : Array Expr)
    (k : Array Expr → Array Expr → ConstructionM α) : ConstructionM α := do
  let publicCarrierType ← liftGen <| generatedType owner.publicCarrier
  let implementationCarrierType ← liftGen <| generatedType owner.implementationCarrier
  let publicIndicesType ← instantiateForall publicCarrierType parameters
  forallBoundedTelescope publicIndicesType (some owner.indexArity) fun publicIndices _ => do
    let implementationIndicesType ← instantiateForall implementationCarrierType parameters
    forallBoundedTelescope implementationIndicesType (some owner.indexArity)
      fun implementationIndices _ => k publicIndices implementationIndices

private def indexFibreDeclaration (plan : FamilyAdapterPlan)
    (certificates : Array MemberCertificate) (constructor : ConstructorPlan)
    (name : Name) : ConstructionM Declaration := do
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error _ => failConstruction (.indexFibreMismatch constructor.key)
  let build := fun (makeValue : Bool) =>
    withConstructorTelescopes plan constructor fun owner parameters publicFields publicResult
        implementationFields implementationResult => do
      withIndexTelescopes owner parameters fun publicIndexFields implementationIndexFields => do
        let sourcePackage ← liftGen <| packedTelescopeType publicFields
        withLocalDeclD `package sourcePackage fun package => do
          let sourceValues ← liftGen <| unpackTelescopeValue publicFields package
          let implementationValues ← mapFields plan certificates constructor parameters true
            publicFields implementationFields sourceValues
          let publicResult := publicResult.replaceFVars publicFields sourceValues
          let implementationResult := implementationResult.replaceFVars implementationFields
            implementationValues
          let publicIndices := resultIndices owner publicResult
          let implementationIndices := resultIndices owner implementationResult
          unless publicIndices.size == owner.indexArity &&
              implementationIndices.size == owner.indexArity do
            failConstruction (.indexFibreMismatch constructor.key)
          let publicPacked ← liftGen <|
            packTelescopeValue publicIndexFields publicIndices
          let implementationPacked ← liftGen <|
            packTelescopeValue implementationIndexFields implementationIndices
          let publicType ← inferType publicPacked
          let implementationType ← inferType implementationPacked
          unless ← isDefEq publicType implementationType do
            failConstruction (.indexFibreMismatch constructor.key)
          unless ← isDefEq implementationPacked publicPacked do
            failConstruction (.indexFibreMismatch constructor.key)
          if makeValue then
            mkLambdaFVars (parameters.push package)
              (eqi.refl' (← ilevel publicType) publicType implementationPacked)
          else
            mkForallFVars (parameters.push package)
              (eqi.mk' (← ilevel publicType) publicType implementationPacked publicPacked)
  let type ← build false
  let value ← build true
  let declaration := Declaration.thmDecl
    { name, levelParams := plan.levelParams, type, value }
  liftGen <| addChecked declaration
  return declaration

/-- Build one complete private telescope certificate.  Failure is a keyed
semantic obligation; successful declarations have already passed the kernel.
-/
def buildTelescopePrototype (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate) (root funextName : Name)
    (constructor : ConstructorPlan) : GenM
    (Except ConstructionIssue (Array Declaration × TelescopeCertificate)) := do
  let names := constructorPrototypeNames root constructor
  let action : ConstructionM (Array Declaration × TelescopeCertificate) := do
    for name in #[names.packSource, names.packImplementation, names.encode, names.decode,
        names.decodeEncode, names.encodeDecode, names.indexFibre] do
      liftGen <| ensurePrototypeFresh name
    let some owner := plan.members.find? (·.key == constructor.key.owner)
      | failConstruction (.dependentFieldTransport constructor.key 0)
    let publicConstructorType ← liftGen <| generatedType constructor.publicName
    let implementationConstructorType ← liftGen <| generatedType constructor.implementationName
    let packSource ← liftGen <| packDeclaration plan publicConstructorType
      owner.parameterArity constructor.telescope.binders.size names.packSource
    let packImplementation ← liftGen <| packDeclaration plan implementationConstructorType
      owner.parameterArity constructor.telescope.binders.size names.packImplementation
    let encode ← codecDeclaration plan memberCertificates constructor names.encode true
    let decode ← codecDeclaration plan memberCertificates constructor names.decode false
    let decodeEncode ← roundTripDeclaration plan memberCertificates constructor names
      funextName names.decodeEncode true
    let encodeDecode ← roundTripDeclaration plan memberCertificates constructor names
      funextName names.encodeDecode false
    let indexFibre ← indexFibreDeclaration plan memberCertificates constructor names.indexFibre
    return (#[packSource, packImplementation, encode, decode, decodeEncode,
      encodeDecode, indexFibre], names)
  action.run

private structure InstalledBinder where
  type : Expr
  value : Expr
  deriving Inhabited

private partial def openExactForalls (tag : Name) (expression : Expr) :
    Array InstalledBinder × Expr :=
  let rec loop (expression : Expr) (binders : Array InstalledBinder) :=
    match expression with
    | .forallE _ type body _ =>
      let value := mkFVar (FVarId.mk (tag.mkNum binders.size))
      loop (body.instantiate1 value) (binders.push { type, value })
    | body => (binders, body)
  loop expression #[]

private def eventualBody (tag : Name) (expression : Expr) : Expr :=
  (openExactForalls tag expression).2

private def installedType? (environment : Environment) (name : Name) : Option Expr :=
  environment.constants.find? name |>.map (·.type)

private def constructorFor? (plan : FamilyAdapterPlan) (key : ConstructorKey) :
    Option ConstructorPlan :=
  plan.constructors.find? (·.key == key)

/-- Associate every source occurrence with the literal induction-hypothesis
binder of its installed private minor.  Constructor and recursor names are
looked up by source keys; no array zip or unary/binary shape test is involved.
-/
def deriveInstalledMinorHypotheses (plan : FamilyAdapterPlan) : MetaM
    (Array MinorHypothesisCertificate × Array ConstructionIssue) := do
  let environment ← getEnv
  let mut certificates := #[]
  let mut issues := #[]
  for member in plan.members do
    let some recursorType := installedType? environment member.implementationRecursor | do
      issues := issues.push
        (.missingInstalledRecursor member.key member.implementationRecursor)
      continue
    let (recursorBinders, _) := openExactForalls
      ((`_family_adapter_installed_rec).append member.implementationRecursor) recursorType
    let prefixSize := member.parameterArity + member.recursorMotiveArity +
      member.recursorMinorArity
    if recursorBinders.size < prefixSize then
      issues := issues.push
        (.shortInstalledRecursorPrefix member.key member.implementationRecursor)
      continue
    let motives := recursorBinders.extract member.parameterArity
      (member.parameterArity + member.recursorMotiveArity) |>.map (·.value)
    let minors := recursorBinders.extract
      (member.parameterArity + member.recursorMotiveArity) prefixSize
    for rule in plan.rules do
      unless rule.key.recursorOwner == member.key do continue
      let some constructor := constructorFor? plan rule.key.constructor | do
        issues := issues.push (.missingInstalledMinor rule.key)
        continue
      let matching := minors.mapIdx fun minorIndex minor =>
        let (binders, result) := openExactForalls
          ((`_family_adapter_installed_minor).append rule.key.recursor |>.mkNum minorIndex)
          minor.type
        (minorIndex, binders, result)
      let matching := matching.filter fun (_, _, result) =>
        (result.getAppArgs.back?.bind (·.getAppFn.constName?)) ==
          some constructor.implementationName
      if matching.isEmpty then
        issues := issues.push (.missingInstalledMinor rule.key)
        continue
      if matching.size > 1 then
        issues := issues.push (.ambiguousInstalledMinor rule.key)
        continue
      let (minorIndex, binders, result) := matching[0]!
      let some major := result.getAppArgs.back? | do
        issues := issues.push (.malformedInstalledMinor rule.key)
        continue
      let majorArguments := major.getAppArgs
      let fieldCount := constructor.telescope.binders.size
      if majorArguments.size < fieldCount then
        issues := issues.push (.malformedInstalledMinor rule.key)
        continue
      let fields := majorArguments.extract (majorArguments.size - fieldCount)
        majorArguments.size
      let mut fieldBinders : Array InstalledBinder := #[]
      let mut malformed := false
      for field in fields do
        match binders.find? (·.value == field) with
        | some binder => fieldBinders := fieldBinders.push binder
        | none => malformed := true
      if malformed then
        issues := issues.push (.malformedInstalledMinor rule.key)
        continue
      let mut hypotheses : Array (Nat × InstalledBinder) := #[]
      for binderIndex in [:binders.size] do
        let binder := binders[binderIndex]!
        if fieldBinders.any (·.value == binder.value) then continue
        let body := eventualBody (`_family_adapter_installed_hypothesis) binder.type
        if motives.contains body.getAppFn then
          hypotheses := hypotheses.push (binderIndex, binder)
      for occurrence in rule.occurrences do
        let some field := fields[occurrence.fieldIndex]? | do
          issues := issues.push (.malformedInstalledMinor rule.key)
          continue
        let candidates := hypotheses.filter fun (_, hypothesis) =>
          let body := eventualBody (`_family_adapter_installed_hypothesis_body)
            hypothesis.type
          (body.getAppArgs.back?.map (·.getAppFn == field)).getD false
        if candidates.isEmpty then
          issues := issues.push (.missingInstalledHypothesis rule.key occurrence)
          continue
        if candidates.size > 1 then
          issues := issues.push (.ambiguousInstalledHypothesis rule.key occurrence)
          continue
        let (binderIndex, _) := candidates[0]!
        let actual := hypotheses.findIdx? (·.1 == binderIndex) |>.getD hypotheses.size
        if actual != occurrence.hypothesisIndex then
          issues := issues.push (.installedHypothesisMismatch rule.key occurrence
            occurrence.hypothesisIndex actual)
          continue
        certificates := certificates.push
          { rule := rule.key, occurrence, minorIndex,
            hypothesisIndex := actual, binderIndex }
  return (certificates, issues)

/-- Test/prototype-only whole-plan construction.  Every returned declaration
has been kernel checked in the current incremental environment.  A single
unresolved semantic obligation leaves `certificate? = none`; callers must not
publish any partial boundary. -/
private def buildPlanPrototype (plan : FamilyAdapterPlan) (iso : Iso) (root : Name) :
    GenM PrototypeBuild := do
  let planIssues := plan.validate
  unless planIssues.isEmpty do
    return { issues := planIssues.map .invalidPlan }
  let mut declarations ← ensureExactSortLift {}
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error message => badShape s!"family-adapter prototype needs Eq ({message})"
  let (funextName, funextDeclarations) ← ensureFunext root eqi {}
  declarations := declarations ++ funextDeclarations
  let (memberDeclarations, members, memberIssues) ←
    prototypeMemberCertificates plan iso root
  declarations := declarations ++ memberDeclarations
  let minorResult : Array MinorHypothesisCertificate × Array ConstructionIssue ←
    deriveInstalledMinorHypotheses plan
  let (minorHypotheses, minorIssues) := minorResult
  let mut issues := memberIssues ++ minorIssues
  let mut telescopes := #[]
  if issues.isEmpty then
    for constructor in plan.constructors do
      match ← buildTelescopePrototype plan members root funextName constructor with
      | .ok (added, certificate) =>
        declarations := declarations ++ added
        telescopes := telescopes.push certificate
      | .error issue => issues := issues.push issue
  if !issues.isEmpty then
    return {
      declarations := declarations
      certificate := none
      minorHypotheses := minorHypotheses
      issues := issues
    }
  let mut occurrences := #[]
  for occurrence in plan.occurrences do
    if let some container := plan.containerMaps.find? (·.key == occurrence.key) then
      occurrences := occurrences.push { key := occurrence.key, maps := container.maps }
    else
      let some member := members.find? (·.key == occurrence.key.target)
        | return {
            declarations := declarations
            certificate := none
            minorHypotheses := minorHypotheses
            issues := #[.missingOccurrenceMap occurrence.key]
          }
      occurrences := occurrences.push { key := occurrence.key, maps := member.maps }
  let certificate : FamilyAdapterCertificate :=
    { members := members,
      telescopes := telescopes,
      occurrences := occurrences,
      minorHypotheses := minorHypotheses }
  return {
    declarations := declarations
    certificate := some certificate
    minorHypotheses := minorHypotheses
  }

/-- Construct only from a complete exact-source shadow. This binds prototype
certification to all installed carrier/constructor/recursor/iota comparisons;
a caller cannot accidentally turn a partially covered plan into a certificate. -/
def buildFamilyPrototype (report : ShadowReport) (iso : Iso) (root : Name) :
    GenM PrototypeBuild := do
  unless report.complete do
    return { issues := report.reasons.map .incompleteShadow }
  let some plan := report.plan?
    | return { issues := #[.incompleteShadow .sourceNotInductive] }
  let saved ← getEnv
  match ← ExceptT.lift (buildPlanPrototype plan iso root).run with
  | .error decline =>
    setEnv saved
    declineWith decline
  | .ok built =>
    if built.certificate.isNone then
      setEnv saved
      return { built with declarations := #[] }
    return built

end InductiveModels.FamilyAdapter
