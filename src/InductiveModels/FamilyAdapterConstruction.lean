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

/-- Arity-independent recursor compatibility after packing a complete
dependent constructor telescope and its finite IH telescope into one value.
The generator instantiates this theorem only with exact keyed maps and laws;
it performs no proof search. -/
theorem packedRecursorCompatibility
    {M : Sort uM} {P : Sort uP} {Q : Sort uQ} {R : Sort uR}
    {C : P → Sort v} {H : R → Sort x}
    (forward : P → M) (backward : M → P)
    (backwardForward : ∀ p, backward (forward p) = p)
    (encode : R → Q) (decode : Q → R)
    (decodeEncode : ∀ p, decode (encode p) = p)
    (privateCtor : Q → M) (publicCtor : R → P)
    (forwardCtor : ∀ p, forward (publicCtor p) = privateCtor (encode p))
    (privateIH : ∀ q, H (decode q)) (publicIH : ∀ p, H p)
    (ihAgreement : ∀ q, publicIH (decode q) = privateIH q)
    (minor : ∀ p, H p → C (publicCtor p))
    (core : ∀ q, C (backward q))
    (constructorAgreement : ∀ q,
      publicCtor (decode q) = backward (privateCtor q))
    (coreIota : ∀ q, core (privateCtor q) =
      Eq.mp (congrArg C (constructorAgreement q))
        (minor (decode q) (privateIH q))) :
    let publicRec : ∀ p, C p := fun p =>
      Eq.mp (congrArg C (backwardForward p)) (core (forward p))
    ∀ p, publicRec (publicCtor p) = minor p (publicIH p) := by
  have cancel {a b : P} (h : a = b) (value : C a) :
      Eq.mp (congrArg C h.symm) (Eq.mp (congrArg C h) value) = value := by
    exact Eq.rec (motive := fun b h =>
      Eq.mp (congrArg C h.symm) (Eq.mp (congrArg C h) value) = value) rfl h
  intro publicRec p
  unfold publicRec
  have compat (q : Q) (r : M) (p : R)
      (hp : decode q = p) (hc : r = privateCtor q)
      (hout : backward r = publicCtor p) :
      Eq.mp (congrArg C hout) (core r) = minor p (publicIH p) := by
    let afterCtor : ∀ (r : M), r = privateCtor q →
        ∀ (p : R) (hp : decode q = p)
          (hout : backward r = publicCtor p),
          Eq.mp (congrArg C hout) (core r) = minor p (publicIH p) :=
      fun r hc => Eq.rec (motive := fun r _ =>
          ∀ (p : R) (hp : decode q = p)
            (hout : backward r = publicCtor p),
            Eq.mp (congrArg C hout) (core r) = minor p (publicIH p))
        (fun p hp => Eq.rec (motive := fun p _ =>
            ∀ hout : backward (privateCtor q) = publicCtor p,
              Eq.mp (congrArg C hout) (core (privateCtor q)) =
                minor p (publicIH p))
          (fun hout => by
            let move := fun value : C (backward (privateCtor q)) =>
              Eq.mp (congrArg C hout) value
            let first := congrArg move (coreIota q)
            let privateResult := minor (decode q) (privateIH q)
            let middle : move
                (Eq.mp (congrArg C (constructorAgreement q)) privateResult) =
                privateResult := by
              exact cancel (constructorAgreement q) _
            let last := congrArg (minor (decode q)) (ihAgreement q)
            exact first.trans (middle.trans last.symm))
          hp)
        hc.symm
    exact afterCtor r hc p hp hout
  exact compat (encode p) (forward (publicCtor p)) p
    (decodeEncode p) (forwardCtor p) (backwardForward (publicCtor p))

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
  | dependentMinorTransport (rule : RuleKey) (binderIndex : Nat)
  | missingInstalledIota (rule : RuleKey) (iota : Name)
  | installedIotaTypeMismatch (rule : RuleKey) (iota : Name)
  | missingPublicIotaInput (rule : RuleKey)
  | inconsistentPublicIotaHypothesis (rule : RuleKey) (binderIndex : Nat)
  | recursorResultMismatch (member : MemberKey)
  | malformedRecursorMinor (member : MemberKey) (minorIndex : Nat)
  | dependentRecursorMinorTransport (member : MemberKey) (minorIndex binderIndex : Nat)
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

private def containerKeyAtBody? (original current : OccurrenceKey) : Bool :=
  if original.constructor != current.constructor || original.fieldIndex != current.fieldIndex ||
      original.hypothesisIndex != current.hypothesisIndex || original.target != current.target ||
      original.binderDepth < current.binderDepth then
    false
  else
    let removed := original.binderDepth - current.binderDepth
    removed <= original.expressionPath.size &&
      (original.expressionPath.extract 0 removed).all (· == .binderBody) &&
      original.expressionPath.extract removed original.expressionPath.size == current.expressionPath

private def containerForOccurrences? (plan : FamilyAdapterPlan)
    (occurrences : Array OccurrenceKey) : Option ContainerMapPlan := do
  let firstKey ← occurrences[0]?
  let firstCandidates := plan.containerMaps.filter (containerKeyAtBody? ·.key firstKey)
  unless firstCandidates.size == 1 do none
  let first := firstCandidates[0]!
  for occurrence in occurrences do
    let candidates := plan.containerMaps.filter (containerKeyAtBody? ·.key occurrence)
    unless candidates.size == 1 do none
    let current := candidates[0]!
    unless current.parameterArity == first.parameterArity &&
        current.indexArity == first.indexArity &&
        current.implementationCarrier == first.implementationCarrier &&
        current.maps == first.maps &&
        current.forwardType == first.forwardType && current.backwardType == first.backwardType &&
        current.backwardForwardType == first.backwardForwardType &&
        current.forwardBackwardType == first.forwardBackwardType &&
        current.implementationCarrierType == first.implementationCarrierType do none
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
  if let some trimmed := trimBinderBody? occurrences then
    let .forallE name sourceDomain sourceBody info := sourceType
      | failConstruction (.missingContainerMap occurrences[0]!)
    let .forallE _ targetDomain targetBody _ := targetType
      | failConstruction (.missingContainerMap occurrences[0]!)
    unless ← isDefEq sourceDomain targetDomain do
      failConstruction (.missingContainerMap occurrences[0]!)
    return ← withLocalDecl name info sourceDomain fun argument => do
      let mapped ← mapFieldValue plan certificates parameters forward constructor fieldIndex trimmed
        (sourceBody.instantiate1 argument) (targetBody.instantiate1 argument)
        (mkApp value argument)
      mkLambdaFVars #[argument] mapped
  if let some container := containerForOccurrences? plan occurrences then
    return ← applyContainerMap plan container forward parameters sourceType targetType value
  failConstruction (.missingContainerMap occurrences[0]!)

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
  if let some trimmed := trimBinderBody? occurrences then
    let .forallE name domain body info := sourceType
      | failConstruction (.missingContainerMap occurrences[0]!)
    let .forallE _ targetDomain targetBody _ := targetType
      | failConstruction (.missingContainerMap occurrences[0]!)
    unless ← isDefEq domain targetDomain do
      failConstruction (.missingContainerMap occurrences[0]!)
    return ← withLocalDecl name info domain fun argument => do
      let pointwise ← fieldRoundTrip plan certificates parameters funextName forward constructor
        fieldIndex trimmed (body.instantiate1 argument) (targetBody.instantiate1 argument)
        (mkApp value argument)
      let once ← mapFieldValue plan certificates parameters forward constructor fieldIndex occurrences
        sourceType targetType value
      let twice ← mapFieldValue plan certificates parameters (!forward) constructor fieldIndex
        occurrences targetType sourceType once
      liftGen <| applyFunext funextName #[argument] (mkApp twice argument)
        (mkApp value argument) pointwise
  if let some container := containerForOccurrences? plan occurrences then
    return ← applyContainerLaw plan container forward parameters sourceType value
  failConstruction (.missingContainerMap occurrences[0]!)

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

private def publicConstructorAdapterName (root : Name) (constructor : ConstructorKey) : Name :=
  prototypeName root constructor.constructor `publicConstructor

private def publicRecursorAdapterName (root : Name) (member : MemberKey) : Name :=
  prototypeName root member.owner `publicRecursor

private def publicMinorConstructorAdapterName (root : Name) (member : MemberKey)
    (minorIndex : Nat) : Name :=
  prototypeName root (member.owner.mkNum minorIndex) `publicMinorConstructor

private def publicIotaAdapterName (root : Name) (rule : RuleKey) : Name :=
  prototypeName root (rule.recursor.append rule.constructor.constructor) `publicIota

private def rootParameters (plan : FamilyAdapterPlan) (parameters : Array Expr) : Array Expr :=
  let arity := (plan.members.find? (·.key == plan.root)).map (·.parameterArity) |>.getD 0
  parameters.extract 0 (min arity parameters.size)

private def applyMemberMap? (plan : FamilyAdapterPlan) (member : MemberPlan)
    (certificate : MemberCertificate) (forward : Bool)
    (sourceType targetType value : Expr) : MetaM (Option Expr) := do
  let source := if forward then member.publicCarrier else member.implementationCarrier
  let target := if forward then member.implementationCarrier else member.publicCarrier
  unless sourceType.getAppFn.constName? == some source &&
      targetType.getAppFn.constName? == some target do return none
  let arity := member.parameterArity + member.indexArity
  let arguments := sourceType.getAppArgs
  unless arguments.size == arity && targetType.getAppArgs == arguments do return none
  let name := mapName certificate forward
  let application := mkAppN (.const name (plan.levelParams.map Level.param))
    (arguments.push value)
  unless ← isDefEq (← inferType application) targetType do return none
  return some application

private def applyContainerMap? (plan : FamilyAdapterPlan) (container : ContainerMapPlan)
    (forward : Bool) (parameters : Array Expr) (sourceType targetType value : Expr) :
    MetaM (Option Expr) := do
  unless parameters.size == container.parameterArity do return none
  let name := if forward then container.maps.forward else container.maps.backward
  let recordedType := if forward then container.forwardType else container.backwardType
  let some installed := (← getEnv).constants.find? name |>.map (·.type) | return none
  unless installed == recordedType do return none
  let mut type ← instantiateForall recordedType parameters
  let mut indices := #[]
  for _ in [:container.indexArity] do
    let .forallE binderName domain body _ := type | return none
    let index ← mkFreshExprMVar domain .natural binderName
    indices := indices.push index
    type := body.instantiate1 index
  let .forallE _ domain _ _ := type | return none
  unless ← isDefEq domain sourceType do return none
  let resolvedIndices ← indices.mapM instantiateMVars
  for index in resolvedIndices do if ← hasAssignableMVar index then return none
  let application := mkAppN (.const name (plan.levelParams.map Level.param))
    (parameters ++ resolvedIndices ++ #[value])
  unless ← isDefEq (← inferType application) targetType do return none
  return some application

private def applyContainerMapInfer? (plan : FamilyAdapterPlan)
    (container : ContainerMapPlan) (forward : Bool) (parameters : Array Expr)
    (sourceType value : Expr) : MetaM (Option (Expr × Expr)) := do
  unless parameters.size == container.parameterArity do return none
  let name := if forward then container.maps.forward else container.maps.backward
  let recordedType := if forward then container.forwardType else container.backwardType
  let some installed := (← getEnv).constants.find? name |>.map (·.type) | return none
  unless installed == recordedType do return none
  let mut type ← instantiateForall recordedType parameters
  let mut indices := #[]
  for _ in [:container.indexArity] do
    let .forallE binderName domain body _ := type | return none
    let index ← mkFreshExprMVar domain .natural binderName
    indices := indices.push index
    type := body.instantiate1 index
  let .forallE _ domain _ _ := type | return none
  unless ← isDefEq domain sourceType do return none
  let resolvedIndices ← indices.mapM instantiateMVars
  for index in resolvedIndices do if ← hasAssignableMVar index then return none
  let application := mkAppN (.const name (plan.levelParams.map Level.param))
    (parameters ++ resolvedIndices ++ #[value])
  let targetType ← instantiateMVars (← inferType application)
  if ← hasAssignableMVar targetType then return none
  return some (application, targetType)

private def sameContainerBoundary (left right : ContainerMapPlan) : Bool :=
  left.parameterArity == right.parameterArity && left.indexArity == right.indexArity &&
    left.implementationCarrier == right.implementationCarrier && left.maps == right.maps &&
    left.forwardType == right.forwardType && left.backwardType == right.backwardType &&
    left.backwardForwardType == right.backwardForwardType &&
    left.forwardBackwardType == right.forwardBackwardType

private def mapCarrierValueInfer (plan : FamilyAdapterPlan)
    (certificates : Array MemberCertificate) (parameters : Array Expr)
    (member : MemberPlan) (forward : Bool) (sourceType value : Expr) :
    ConstructionM (Expr × Expr × EquivalenceCertificate) := do
  let parameters := rootParameters plan parameters
  let candidates ← liftGen <| plan.containerMaps.filterMapM fun container => do
    let application? ← applyContainerMapInfer? plan container forward parameters sourceType value
    return application?.map fun (application, targetType) => (container, application, targetType)
  if let some first := candidates[0]? then
    unless candidates.all (sameContainerBoundary first.1 ·.1) do
      failConstruction (.missingMemberMap member.key)
    return (first.2.1, first.2.2, first.1.maps)
  let some certificate := certificateFor? certificates member.key
    | failConstruction (.missingMemberMap member.key)
  let source := if forward then member.publicCarrier else member.implementationCarrier
  if sourceType.getAppFn.constName? != some source then
    return (value, sourceType, certificate.maps)
  let arguments := sourceType.getAppArgs
  let application := mkAppN (.const (mapName certificate forward)
    (plan.levelParams.map Level.param)) (arguments.push value)
  let targetType ← inferType application
  return (application, targetType, certificate.maps)

/-- Map an exact carrier application without classifying its syntax. Direct
members use their keyed family equivalence; specialised mimics are selected by
exact installed map domain/codomain unification. -/
private def mapCarrierValue (plan : FamilyAdapterPlan)
    (certificates : Array MemberCertificate) (parameters : Array Expr)
    (member : MemberPlan) (forward : Bool) (sourceType targetType value : Expr) :
    ConstructionM (Expr × EquivalenceCertificate) := do
  let some memberCertificate := certificateFor? certificates member.key
    | failConstruction (.missingMemberMap member.key)
  if ← isDefEq sourceType targetType then return (value, memberCertificate.maps)
  if let some application ← liftGen <|
      applyMemberMap? plan member memberCertificate forward sourceType targetType value then
    return (application, memberCertificate.maps)
  let parameters := rootParameters plan parameters
  let candidates ← liftGen <| plan.containerMaps.filterMapM fun container => do
    let application? ← applyContainerMap? plan container forward parameters sourceType targetType value
    return application?.map fun application => (container, application)
  let some first := candidates[0]? | failConstruction (.missingMemberMap member.key)
  unless candidates.all (sameContainerBoundary first.1 ·.1) do
    failConstruction (.missingMemberMap member.key)
  return (first.2, first.1.maps)

private def carrierRoundTrip (plan : FamilyAdapterPlan)
    (certificates : Array MemberCertificate) (parameters : Array Expr)
    (member : MemberPlan) (forward : Bool) (sourceType targetType value : Expr) :
    ConstructionM Expr := do
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error _ => failConstruction (.missingMemberMap member.key)
  if ← isDefEq sourceType targetType then
    return eqi.refl' (← ilevel sourceType) sourceType value
  let some memberCertificate := certificateFor? certificates member.key
    | failConstruction (.missingMemberMap member.key)
  if (← liftGen <| applyMemberMap? plan member memberCertificate forward sourceType targetType
      value).isSome then
    let law := lawName memberCertificate forward
    return mkAppN (.const law (plan.levelParams.map Level.param))
      (sourceType.getAppArgs.push value)
  let parameters := rootParameters plan parameters
  let candidates ← liftGen <| plan.containerMaps.filterMapM fun container => do
    let application? ← applyContainerMap? plan container forward parameters sourceType targetType value
    return application?.map fun _ => container
  let some first := candidates[0]? | failConstruction (.missingMemberMap member.key)
  unless candidates.all (sameContainerBoundary first ·) do
    failConstruction (.missingMemberMap member.key)
  applyContainerLaw plan first forward parameters sourceType value

/-- A family member with all of its exact indices packed together with the
carrier value.  Totalising the fibre lets one proof schema handle arbitrary
finite index vectors without an index-arity branch. -/
private structure PackedCarrierBoundary where
  publicType : Expr
  implementationType : Expr
  forward : Expr
  backward : Expr
  backwardForward : Expr
  forwardBackward : Expr

private def packedCarrierBoundary (plan : FamilyAdapterPlan)
    (certificates : Array MemberCertificate) (parameters : Array Expr)
    (member : MemberPlan) : ConstructionM PackedCarrierBoundary := do
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error _ => failConstruction (.missingMemberMap member.key)
  withIndexTelescopes member parameters fun publicIndices implementationIndices => do
    let levels := plan.levelParams.map Level.param
    let publicCarrier := mkAppN (.const member.publicCarrier levels)
      (parameters ++ publicIndices)
    let implementationCarrier := mkAppN (.const member.implementationCarrier levels)
      (parameters ++ implementationIndices)
    withLocalDeclD `publicValue publicCarrier fun publicValue => do
      withLocalDeclD `implementationValue implementationCarrier fun implementationValue => do
        let publicFields := publicIndices.push publicValue
        let implementationFields := implementationIndices.push implementationValue
        let publicType ← liftGen <| packedTelescopeType publicFields
        let implementationType ← liftGen <| packedTelescopeType implementationFields
        let makeMap := fun (forward : Bool) => do
          let sourceType := if forward then publicType else implementationType
          let sourceFields := if forward then publicFields else implementationFields
          let targetFields := if forward then implementationFields else publicFields
          withLocalDeclD `total sourceType fun total => do
            let sourceValues ← liftGen <| unpackTelescopeValue sourceFields total
            let sourceValue := sourceValues.back!
            let indices := sourceValues.pop
            let sourceCarrierType ← liftGen <| inferType sourceValue
            let targetCarrierName := if forward then member.implementationCarrier
              else member.publicCarrier
            let targetCarrierType := mkAppN (.const targetCarrierName levels)
              (parameters ++ indices)
            let (targetValue, _) ← mapCarrierValue plan certificates parameters member forward
              sourceCarrierType targetCarrierType sourceValue
            let target ← liftGen <| packTelescopeValue targetFields (indices.push targetValue)
            liftGen <| mkLambdaFVars #[total] target
        let forward ← makeMap true
        let backward ← makeMap false
        let makeLaw := fun (isForward : Bool) => do
          let sourceType := if isForward then publicType else implementationType
          let sourceFields := if isForward then publicFields else implementationFields
          let targetFields := if isForward then implementationFields else publicFields
          let first := if isForward then forward else backward
          let second := if isForward then backward else forward
          withLocalDeclD `total sourceType fun total => do
            let sourceValues ← liftGen <| unpackTelescopeValue sourceFields total
            let once := mkApp first total
            let onceValues ← liftGen <| unpackTelescopeValue targetFields once
            let twice := mkApp second once
            let twiceValues ← liftGen <| unpackTelescopeValue sourceFields twice
            let mut proofs := #[]
            for index in [:member.indexArity] do
              let type ← liftGen <| inferType sourceValues[index]!
              proofs := proofs.push <| eqi.refl' (← liftGen <| ilevel type) type
                sourceValues[index]!
            let sourceValue := sourceValues.back!
            let targetValue := onceValues.back!
            let sourceCarrierType ← liftGen <| inferType sourceValue
            let targetCarrierType ← liftGen <| inferType targetValue
            let valueProof ← carrierRoundTrip plan certificates parameters member isForward
              sourceCarrierType targetCarrierType sourceValue
            proofs := proofs.push valueProof
            let proof ← liftGen <| packageCongruence eqi sourceFields sourceType twiceValues
              sourceValues proofs
            unless ← liftGen <| isDefEq (← inferType proof)
                (eqi.mk' (← ilevel sourceType) sourceType twice total) do
              failConstruction (.missingMemberMap member.key)
            liftGen <| mkLambdaFVars #[total] proof
        let backwardForward ← makeLaw true
        let forwardBackward ← makeLaw false
        return PackedCarrierBoundary.mk publicType implementationType forward backward
          backwardForward forwardBackward

private def packCarrierTotal (parameters : Array Expr) (member : MemberPlan)
    (isPublic : Bool) (indices : Array Expr) (value : Expr) :
    ConstructionM Expr := do
  unless indices.size == member.indexArity do
    failConstruction (.recursorResultMismatch member.key)
  withIndexTelescopes member parameters fun publicIndices implementationIndices => do
    let fields := (if isPublic then publicIndices else implementationIndices).push value
    liftGen <| packTelescopeValue fields (indices.push value)

private def unpackCarrierTotal (plan : FamilyAdapterPlan) (parameters : Array Expr)
    (member : MemberPlan) (isPublic : Bool) (total : Expr) :
    ConstructionM (Array Expr × Expr) := do
  withIndexTelescopes member parameters fun publicIndices implementationIndices => do
    let fields := if isPublic then publicIndices else implementationIndices
    let carrierName := if isPublic then member.publicCarrier else member.implementationCarrier
    let carrier := mkAppN (.const carrierName (plan.levelParams.map Level.param))
      (parameters ++ fields)
    withLocalDeclD `value carrier fun value => do
      let values ← liftGen <| unpackTelescopeValue (fields.push value) total
      return (values.pop, values.back!)

private structure PackedConstructorBoundary where
  publicFieldsType : Expr
  implementationFieldsType : Expr
  encode : Expr
  decode : Expr
  decodeEncode : Expr
  encodeDecode : Expr
  publicCtor : Expr
  implementationCtor : Expr
  forwardCtor : Expr
  constructorAgreement : Expr

private def packedConstructorBoundary (plan : FamilyAdapterPlan)
    (parameters : Array Expr) (owner : MemberPlan) (ownerBoundary : PackedCarrierBoundary)
    (constructor : ConstructorPlan) (constructorCertificate : PublicConstructorCertificate) :
    ConstructionM PackedConstructorBoundary := do
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error _ => failConstruction (.indexFibreMismatch constructor.key)
  let publicConstructorType ← liftGen <| generatedType constructorCertificate.adapter
  let implementationConstructorType ← liftGen <| generatedType constructor.implementationName
  let publicFieldsTail ← instantiateForall publicConstructorType parameters
  forallBoundedTelescope publicFieldsTail (some constructor.telescope.binders.size)
      fun publicFields publicResult => do
    let implementationFieldsTail ← instantiateForall implementationConstructorType parameters
    forallBoundedTelescope implementationFieldsTail (some constructor.telescope.binders.size)
        fun implementationFields implementationResult => do
      let publicFieldsType ← liftGen <| packedTelescopeType publicFields
      let implementationFieldsType ← liftGen <| packedTelescopeType implementationFields
      let levels := plan.levelParams.map Level.param
      let encode := mkAppN (.const constructorCertificate.telescope.encode levels) parameters
      let decode := mkAppN (.const constructorCertificate.telescope.decode levels) parameters
      let decodeEncode := mkAppN
        (.const constructorCertificate.telescope.decodeEncode levels) parameters
      let encodeDecode := mkAppN
        (.const constructorCertificate.telescope.encodeDecode levels) parameters
      let makeConstructor := fun (isPublic : Bool) => do
        let packageType := if isPublic then publicFieldsType else implementationFieldsType
        let fields := if isPublic then publicFields else implementationFields
        let result := if isPublic then publicResult else implementationResult
        let name := if isPublic then constructorCertificate.adapter
          else constructor.implementationName
        withLocalDeclD `package packageType fun package => do
          let values ← liftGen <| unpackTelescopeValue fields package
          let major := mkAppN (.const name levels) (parameters ++ values)
          let majorType := result.replaceFVars fields values
          unless ← liftGen <| isDefEq (← inferType major) majorType do
            failConstruction (.dependentFieldTransport constructor.key values.size)
          let total ← packCarrierTotal parameters owner isPublic
            (resultIndices owner majorType) major
          liftGen <| mkLambdaFVars #[package] total
      let publicCtor ← makeConstructor true
      let implementationCtor ← makeConstructor false
      let forwardCtor ← withLocalDeclD `package publicFieldsType fun package => do
        let right := mkApp implementationCtor (mkApp encode package)
        let proof := mkApp ownerBoundary.forwardBackward right
        let target ← liftGen <| inferType proof
        let expected := eqi.mk'
          (← liftGen <| ilevel ownerBoundary.implementationType)
          ownerBoundary.implementationType
          (mkApp ownerBoundary.forward (mkApp publicCtor package)) right
        unless ← liftGen <| isDefEq target expected do
          failConstruction (.indexFibreMismatch constructor.key)
        liftGen <| mkLambdaFVars #[package] proof
      let constructorAgreement ← withLocalDeclD `package implementationFieldsType
          fun package => do
        let equality := mkApp encodeDecode package
        let function ← liftGen <| withLocalDeclD `next implementationFieldsType fun next =>
          mkLambdaFVars #[next] (mkApp ownerBoundary.backward (mkApp implementationCtor next))
        let proof ← liftGen <| mkAppM ``congrArg #[function, equality]
        let expectedLeft := mkApp publicCtor (mkApp decode package)
        let expectedRight := mkApp ownerBoundary.backward (mkApp implementationCtor package)
        unless ← liftGen <| isDefEq (← inferType proof)
            (eqi.mk' (← ilevel ownerBoundary.publicType) ownerBoundary.publicType
              expectedLeft expectedRight) do
          failConstruction (.indexFibreMismatch constructor.key)
        liftGen <| mkLambdaFVars #[package] proof
      return PackedConstructorBoundary.mk publicFieldsType implementationFieldsType encode decode
        decodeEncode encodeDecode publicCtor implementationCtor forwardCtor constructorAgreement

/-- Regression seam for the packed constructor inputs consumed by the exact
public-iota proof. -/
def validatePackedConstructorBoundaries (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate)
    (constructorCertificates : Array PublicConstructorCertificate) :
    GenM (Except ConstructionIssue Nat) := do
  let action : ConstructionM Nat := do
    let mut count := 0
    for constructor in plan.constructors do
      let some owner := plan.members.find? (·.key == constructor.key.owner)
        | failConstruction (.missingMemberMap constructor.key.owner)
      let some certificate := constructorCertificates.find? (·.key == constructor.key)
        | failConstruction (.dependentFieldTransport constructor.key 0)
      let _ ← forallBoundedTelescope owner.sourceType (some owner.parameterArity)
          fun parameters _ => do
        let ownerBoundary ← packedCarrierBoundary plan memberCertificates parameters owner
        let boundary ← packedConstructorBoundary plan parameters owner ownerBoundary
          constructor certificate
        for expression in #[boundary.publicFieldsType, boundary.implementationFieldsType,
            boundary.encode, boundary.decode, boundary.decodeEncode, boundary.encodeDecode,
            boundary.publicCtor, boundary.implementationCtor, boundary.forwardCtor,
            boundary.constructorAgreement] do
          liftGen <| check expression
        return ()
      count := count + 1
    return count
  action.run

/-- Exercise totalised member boundaries in the disabled prototype. This is a
source/interpreted regression seam for arbitrary finite index telescopes. -/
def validatePackedCarrierBoundaries (plan : FamilyAdapterPlan)
    (certificates : Array MemberCertificate) : GenM (Except ConstructionIssue Nat) := do
  let action : ConstructionM Nat := do
    let mut count := 0
    for member in plan.members do
      let _ ← forallBoundedTelescope member.sourceType (some member.parameterArity)
          fun parameters _ => do
        let boundary ← packedCarrierBoundary plan certificates parameters member
        for expression in #[boundary.publicType, boundary.implementationType,
            boundary.forward, boundary.backward, boundary.backwardForward,
            boundary.forwardBackward] do
          liftGen <| check expression
        return ()
      count := count + 1
    return count
  action.run

private def publicConstructorDeclaration (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate)
    (telescopeCertificates : Array TelescopeCertificate) (root : Name)
    (constructor : ConstructorPlan) : ConstructionM
    (Declaration × PublicConstructorCertificate) := do
  let some owner := plan.members.find? (·.key == constructor.key.owner)
    | failConstruction (.missingMemberMap constructor.key.owner)
  let some telescope := telescopeCertificates.find? (·.constructor == constructor.key)
    | failConstruction (.dependentFieldTransport constructor.key 0)
  let name := publicConstructorAdapterName root constructor.key
  liftGen <| ensurePrototypeFresh name
  let value ← withConstructorTelescopes plan constructor
    fun _ parameters publicFields publicResult implementationFields _ => do
      let implementationValues ← mapFields plan memberCertificates constructor parameters true
        publicFields implementationFields publicFields
      let privateMajor := mkAppN
        (.const constructor.implementationName (plan.levelParams.map Level.param))
        (parameters ++ implementationValues)
      let privateType ← inferType privateMajor
      let publicType := publicResult.replaceFVars publicFields publicFields
      let (publicMajor, ownerMaps) ← mapCarrierValue plan memberCertificates parameters owner false
        privateType publicType privateMajor
      return (← mkLambdaFVars (parameters ++ publicFields) publicMajor, ownerMaps)
  let declaration := Declaration.defnDecl
    { name, levelParams := plan.levelParams, type := constructor.publicType, value := value.1,
      hints := .abbrev, safety := .safe }
  liftGen <| addChecked declaration
  return (declaration,
    { key := constructor.key, adapter := name, exactType := constructor.publicType,
      implementationConstructor := constructor.implementationName,
      telescope, ownerMaps := value.2 })

private def buildPublicConstructorPrototypesCore (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate)
    (telescopeCertificates : Array TelescopeCertificate) (root : Name) : ConstructionM
    (Array Declaration × Array PublicConstructorCertificate) := do
  let mut declarations := #[]
  let mut certificates := #[]
  for constructor in plan.constructors do
    let (declaration, certificate) ← publicConstructorDeclaration plan memberCertificates
      telescopeCertificates root constructor
    declarations := declarations.push declaration
    certificates := certificates.push certificate
  return (declarations, certificates)

/-- Disabled constructor tranche, transactional independently of the whole
family prototype. -/
def buildPublicConstructorPrototypes (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate)
    (telescopeCertificates : Array TelescopeCertificate) (root : Name) : GenM
    (Except ConstructionIssue (Array Declaration × Array PublicConstructorCertificate)) := do
  let saved ← getEnv
  match ← ExceptT.lift
      (buildPublicConstructorPrototypesCore plan memberCertificates telescopeCertificates root).run with
  | .error decline =>
    setEnv saved
    declineWith decline
  | .ok (.error issue) =>
    setEnv saved
    return .error issue
  | .ok (.ok built) => return .ok built

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
      let mut hypotheses : Array (Nat × Nat × InstalledBinder) := #[]
      for binderIndex in [:binders.size] do
        let binder := binders[binderIndex]!
        if fieldBinders.any (·.value == binder.value) then continue
        let body := eventualBody (`_family_adapter_installed_hypothesis) binder.type
        if let some motiveIndex := motives.findIdx? (· == body.getAppFn) then
          hypotheses := hypotheses.push (binderIndex, motiveIndex, binder)
      for occurrence in rule.occurrences do
        let some field := fields[occurrence.fieldIndex]? | do
          issues := issues.push (.malformedInstalledMinor rule.key)
          continue
        let candidates := hypotheses.filter fun (_, _, hypothesis) =>
          let body := eventualBody (`_family_adapter_installed_hypothesis_body)
            hypothesis.type
          (body.getAppArgs.back?.map (·.getAppFn == field)).getD false
        if candidates.isEmpty then
          issues := issues.push (.missingInstalledHypothesis rule.key occurrence)
          continue
        if candidates.size > 1 then
          issues := issues.push (.ambiguousInstalledHypothesis rule.key occurrence)
          continue
        let (binderIndex, motiveIndex, _) := candidates[0]!
        let actual := hypotheses.findIdx? (fun (index, _, _) => index == binderIndex)
          |>.getD hypotheses.size
        if actual != occurrence.hypothesisIndex then
          issues := issues.push (.installedHypothesisMismatch rule.key occurrence
            occurrence.hypothesisIndex actual)
          continue
        certificates := certificates.push
          { rule := rule.key, occurrence, minorIndex,
            hypothesisIndex := actual, binderIndex, motiveIndex }
  return (certificates, issues)

private def uniqueBinderIndices (certificates : Array MinorHypothesisCertificate) : Array Nat :=
  Id.run do
    let mut result := #[]
    for certificate in certificates do
      unless result.contains certificate.binderIndex do
        result := result.push certificate.binderIndex
    return result

private def installedMinorIndexForRule (plan : FamilyAdapterPlan) (member : MemberPlan)
    (rule : RulePlan) (recursorType : Expr) : Except ConstructionIssue Nat := do
  let prefixSize := member.parameterArity + member.recursorMotiveArity +
    member.recursorMinorArity
  let (recursorBinders, _) := openExactForalls
    ((`_family_adapter_compatibility_rec).append member.implementationRecursor) recursorType
  if recursorBinders.size < prefixSize then
    throw (.shortInstalledRecursorPrefix member.key member.implementationRecursor)
  let minors := recursorBinders.extract
    (member.parameterArity + member.recursorMotiveArity) prefixSize
  let some constructor := constructorFor? plan rule.key.constructor
    | throw (.missingInstalledMinor rule.key)
  let matching := minors.mapIdx fun index minor =>
    let (_, result) := openExactForalls
      ((`_family_adapter_compatibility_minor).append rule.key.recursor |>.mkNum index)
      minor.type
    (index, result)
  let matching := matching.filter fun (_, result) =>
    (result.getAppArgs.back?.bind (·.getAppFn.constName?)) ==
      some constructor.implementationName
  if matching.isEmpty then throw (.missingInstalledMinor rule.key)
  if matching.size > 1 then throw (.ambiguousInstalledMinor rule.key)
  return matching[0]!.1

private partial def withMinorReplacements (eqi : EqInfo) (rule : RuleKey)
    (binders : Array Expr) (indices : Array Nat) (position : Nat)
    (replacements proofs extra : Array Expr)
    (k : Array Expr → Array Expr → Array Expr → GenM (Except ConstructionIssue α)) :
    GenM (Except ConstructionIssue α) := do
  if position == indices.size then return ← k replacements proofs extra
  let binderIndex := indices[position]!
  let some original := binders[binderIndex]?
    | return .error (.malformedInstalledMinor rule)
  let type ← inferType original
  let level ← ilevel type
  withLocalDeclD (Name.mkSimple s!"after_{binderIndex}") type fun replacement =>
    withLocalDeclD (Name.mkSimple s!"equal_{binderIndex}")
        (eqi.mk' level type original replacement) fun proof =>
      withMinorReplacements eqi rule binders indices (position + 1)
        (replacements.push replacement) (proofs.push proof)
        (extra.push replacement |>.push proof) k

private def ruleCompatibilityName (root : Name) (rule : RuleKey) : Name :=
  prototypeName root (rule.recursor.append rule.constructor.constructor) `minorCompatibility

/-- Build one arity-independent congruence theorem for an installed recursor
minor. Each distinct keyed IH binder contributes one `Eq.rec`; source
occurrences sharing that binder contribute only one transport step. -/
private def ruleCompatibilityDeclaration (plan : FamilyAdapterPlan)
    (minorHypotheses : Array MinorHypothesisCertificate) (root : Name)
    (rule : RulePlan) : GenM
    (Except ConstructionIssue (Declaration × RuleCompatibilityCertificate)) := do
  let some member := plan.members.find? (·.key == rule.key.recursorOwner)
    | return .error (.missingInstalledMinor rule.key)
  let environment ← getEnv
  for (iota, expected) in #[(rule.implementationIota, rule.implementationIotaType),
      (rule.publicIota, rule.publicIotaType)] do
    let some actual := environment.constants.find? iota | do
      return .error (.missingInstalledIota rule.key iota)
    unless actual.type == expected do
      return .error (.installedIotaTypeMismatch rule.key iota)
  let some recursorInfo := environment.constants.find? member.implementationRecursor
    | return .error (.missingInstalledRecursor member.key member.implementationRecursor)
  let recursorType := recursorInfo.type
  let minorIndex ← match installedMinorIndexForRule plan member rule recursorType with
    | .ok index => pure index
    | .error issue => return .error issue
  let keyed := minorHypotheses.filter (·.rule == rule.key)
  unless keyed.size == rule.occurrences.size &&
      rule.occurrences.all fun occurrence => keyed.any (·.occurrence == occurrence) do
    return .error (.malformedInstalledMinor rule.key)
  unless keyed.all (·.minorIndex == minorIndex) do
    return .error (.malformedInstalledMinor rule.key)
  let transportedHypotheses := uniqueBinderIndices keyed
  let name := ruleCompatibilityName root rule.key
  ensurePrototypeFresh name
  let eqi ← match EqInfo.check environment with
    | .ok information => pure information
    | .error message => badShape s!"family-adapter rule compatibility needs Eq ({message})"
  let prefixSize := member.parameterArity + member.recursorMotiveArity +
    member.recursorMinorArity
  let built ← forallBoundedTelescope recursorType (some prefixSize) fun recursorPrefix _ => do
    let some minor := recursorPrefix[
        member.parameterArity + member.recursorMotiveArity + minorIndex]?
      | return .error (.missingInstalledMinor rule.key)
    let minorType ← inferType minor
    forallBoundedTelescope minorType (some (numForalls minorType)) fun binders _ =>
      withMinorReplacements eqi rule.key binders transportedHypotheses 0 #[] #[] #[]
        fun replacements proofs extra => do
          let argumentsAt := fun position => Id.run do
            let mut arguments := binders
            for step in [:position] do
              arguments := arguments.set! transportedHypotheses[step]! replacements[step]!
            return arguments
          let left := mkAppN minor (argumentsAt 0)
          let alpha ← inferType left
          let equalityLevel ← ilevel alpha
          let mut accumulator := eqi.refl' equalityLevel alpha left
          let mut current := left
          for position in [:transportedHypotheses.size] do
            let binderIndex := transportedHypotheses[position]!
            let original := binders[binderIndex]!
            let replacement := replacements[position]!
            let proof := proofs[position]!
            let valueType ← inferType original
            let priorOriginals := (transportedHypotheses.extract 0 position).map fun index =>
              binders[index]!
            let expectedValueType := valueType.replaceFVars priorOriginals
              (replacements.extract 0 position)
            unless ← isDefEq valueType expectedValueType do
              return .error (.dependentMinorTransport rule.key binderIndex)
            let valueLevel ← ilevel valueType
            let next := mkAppN minor (argumentsAt (position + 1))
            let some nextType ← (try some <$> inferType next catch _ => pure none)
              | return .error (.dependentMinorTransport rule.key binderIndex)
            unless ← isDefEq alpha nextType do
              return .error (.dependentMinorTransport rule.key binderIndex)
            let factor ← transportAlong eqi .zero valueLevel valueType original replacement proof
              (eqi.refl' equalityLevel alpha current) fun value => do
                let stepped := mkAppN minor ((argumentsAt position).set! binderIndex value)
                let steppedType ← inferType stepped
                unless ← isDefEq alpha steppedType do
                  badShape s!"{rule.key.recursor}'s compatibility motive changes result type"
                return eqi.mk' equalityLevel alpha current stepped
            accumulator ← transOf eqi equalityLevel alpha left current next accumulator factor
            current := next
          let proposition := eqi.mk' equalityLevel alpha left current
          let locals := recursorPrefix ++ binders ++ extra
          return .ok (← mkForallFVars locals proposition, ← mkLambdaFVars locals accumulator)
  match built with
  | .error issue => return .error issue
  | .ok (type, value) =>
    let declaration := Declaration.thmDecl
      { name, levelParams := recursorInfo.levelParams, type, value }
    addChecked declaration
    return .ok (declaration,
      { key := rule.key, minorIndex, transportedHypotheses, compatibility := name,
        implementationIota := rule.implementationIota,
        implementationIotaType := rule.implementationIotaType,
        publicIota := rule.publicIota, publicIotaType := rule.publicIotaType })

private def buildRuleCompatibilityPrototypesCore (plan : FamilyAdapterPlan)
    (minorHypotheses : Array MinorHypothesisCertificate) (root : Name) : GenM
    (Except ConstructionIssue (Array Declaration × Array RuleCompatibilityCertificate)) := do
  let mut declarations := #[]
  let mut certificates := #[]
  for rule in plan.rules do
    match ← ruleCompatibilityDeclaration plan minorHypotheses root rule with
    | .error issue => return .error issue
    | .ok (declaration, certificate) =>
      declarations := declarations.push declaration
      certificates := certificates.push certificate
  return .ok (declarations, certificates)

/-- Disabled-prototype rule tranche. It folds over the exact finite rule array
and rolls the incremental environment back on either a keyed obligation or a
kernel/generator decline, so callers cannot retain a partial rule boundary. -/
def buildRuleCompatibilityPrototypes (plan : FamilyAdapterPlan)
    (minorHypotheses : Array MinorHypothesisCertificate) (root : Name) : GenM
    (Except ConstructionIssue (Array Declaration × Array RuleCompatibilityCertificate)) := do
  let saved ← getEnv
  match ← ExceptT.lift
      (buildRuleCompatibilityPrototypesCore plan minorHypotheses root).run with
  | .error decline =>
    setEnv saved
    declineWith decline
  | .ok (.error issue) =>
    setEnv saved
    return .error issue
  | .ok (.ok built) => return .ok built

/-- Resolve the exact, finite inputs of every public-iota proof. Shared source
occurrences are grouped only when the installed private minor assigns them the
same literal IH binder, motive slot, and checked map boundary. -/
def derivePublicIotaProofSchemas (plan : FamilyAdapterPlan)
    (certificate : FamilyAdapterCertificate) :
    Except ConstructionIssue (Array PublicIotaProofSchema) := do
  let mut schemas := #[]
  for rule in plan.rules do
    let some owner := plan.members.find? (·.key == rule.key.recursorOwner)
      | throw (.missingPublicIotaInput rule.key)
    let some memberCertificate := certificate.members.find? (·.key == owner.key)
      | throw (.missingPublicIotaInput rule.key)
    let some telescope := certificate.telescopes.find? (·.constructor == rule.key.constructor)
      | throw (.missingPublicIotaInput rule.key)
    let some compatibility := certificate.rules.find? (·.key == rule.key)
      | throw (.missingPublicIotaInput rule.key)
    let keyed := certificate.minorHypotheses.filter (·.rule == rule.key)
    unless keyed.size == rule.occurrences.size &&
        rule.occurrences.all fun occurrence => keyed.any (·.occurrence == occurrence) do
      throw (.missingPublicIotaInput rule.key)
    let mut hypotheses := #[]
    for binderIndex in compatibility.transportedHypotheses do
      let grouped := keyed.filter (·.binderIndex == binderIndex)
      let some first := grouped[0]?
        | throw (.inconsistentPublicIotaHypothesis rule.key binderIndex)
      unless first.minorIndex == compatibility.minorIndex && grouped.all fun current =>
          current.minorIndex == first.minorIndex && current.motiveIndex == first.motiveIndex do
        throw (.inconsistentPublicIotaHypothesis rule.key binderIndex)
      let mut occurrenceCertificates : Array OccurrenceCertificate := #[]
      for current in grouped do
        let some occurrence := certificate.occurrences.find? (·.key == current.occurrence)
          | throw (.inconsistentPublicIotaHypothesis rule.key binderIndex)
        occurrenceCertificates := occurrenceCertificates.push occurrence
      let some firstOccurrence := occurrenceCertificates[0]?
        | throw (.inconsistentPublicIotaHypothesis rule.key binderIndex)
      unless occurrenceCertificates.all (·.maps == firstOccurrence.maps) do
        throw (.inconsistentPublicIotaHypothesis rule.key binderIndex)
      hypotheses := hypotheses.push
        { rule := rule.key, minorIndex := first.minorIndex, binderIndex,
          motiveIndex := first.motiveIndex,
          occurrences := grouped.map (·.occurrence), maps := firstOccurrence.maps }
    unless (hypotheses.flatMap (·.occurrences)).size == rule.occurrences.size &&
        keyed.all fun current => hypotheses.any fun step =>
          step.binderIndex == current.binderIndex && step.occurrences.contains current.occurrence do
      throw (.missingPublicIotaInput rule.key)
    schemas := schemas.push
      { key := rule.key, owner := owner.key, constructor := rule.key.constructor,
        ownerMaps := memberCertificate.maps, telescope,
        implementationIota := compatibility.implementationIota,
        minorCompatibility := compatibility.compatibility, hypotheses }
  return schemas

private def minorFieldValues? (constructor : ConstructorPlan)
    (binders : Array Expr) (result : Expr) (adapter? : Option Name := none) :
    Option (Array Expr) := do
  let major ← result.getAppArgs.back?
  unless major.getAppFn.constName? == some constructor.publicName ||
      major.getAppFn.constName? == some constructor.implementationName ||
      adapter?.any (some · == major.getAppFn.constName?) do none
  let arguments := major.getAppArgs
  let count := constructor.telescope.binders.size
  unless arguments.size >= count do none
  let fields := arguments.extract (arguments.size - count) arguments.size
  for field in fields do unless binders.contains field do none
  return fields

private def minorConstructorName? (type : Expr) : Option Name := do
  let (_, result) := openExactForalls `_family_adapter_public_recursor_minor type
  let major ← result.getAppArgs.back?
  major.getAppFn.constName?

private def minorConstructorParts? (type : Expr) :
    Option (Array Expr × Array Expr × Expr) := do
  let (binders, result) := openExactForalls `_family_adapter_minor_constructor type
  let major ← result.getAppArgs.back?
  let values := binders.map (·.value)
  let fields := major.getAppArgs.filter values.contains
  return (values, fields, major)

private def motiveCarrierName? (type : Expr) : Option Name := do
  let (binders, _) := openExactForalls `_family_adapter_recursor_motive type
  let value ← binders.back?
  value.type.getAppFn.constName?

private def recursorMotiveCertificates (member : MemberPlan)
    (publicType privateType : Expr) : Except ConstructionIssue
    (Array PublicRecursorMotiveCertificate) := do
  let (publicBinders, _) := openExactForalls `_family_adapter_public_motives publicType
  let (privateBinders, _) := openExactForalls `_family_adapter_private_motives privateType
  let stop := member.parameterArity + member.recursorMotiveArity
  unless publicBinders.size >= stop && privateBinders.size >= stop do
    throw (.shortInstalledRecursorPrefix member.key member.publicRecursor)
  let mut result := #[]
  for motiveIndex in [:member.recursorMotiveArity] do
    let binderIndex := member.parameterArity + motiveIndex
    let some publicCarrier := motiveCarrierName? publicBinders[binderIndex]!.type
      | throw (.recursorResultMismatch member.key)
    let some implementationCarrier := motiveCarrierName? privateBinders[binderIndex]!.type
      | throw (.recursorResultMismatch member.key)
    result := result.push
      { recursor := member.key, motiveIndex, publicCarrier, implementationCarrier }
  return result

private def uniqueOccurrenceHypothesisIndices (constructor : ConstructorPlan) : Array Nat :=
  Id.run do
    let mut result := #[]
    for binder in constructor.telescope.binders do
      for occurrence in binder.occurrences do
        unless result.contains occurrence.hypothesisIndex do
          result := result.push occurrence.hypothesisIndex
    return result

private def minorConstructorSequence (member : MemberPlan) (isPublic : Bool)
    (recursorType : Expr) : Except ConstructionIssue (Array Name) := do
  let (binders, _) := openExactForalls `_family_adapter_public_recursor_prefix recursorType
  let start := member.parameterArity + member.recursorMotiveArity
  let stop := start + member.recursorMinorArity
  unless binders.size >= stop do
    throw (.shortInstalledRecursorPrefix member.key
      (if isPublic then member.publicRecursor else member.implementationRecursor))
  let mut result := #[]
  for minorIndex in [:member.recursorMinorArity] do
    let some constructor := minorConstructorName? binders[start + minorIndex]!.type
      | throw (.malformedRecursorMinor member.key minorIndex)
    result := result.push constructor
  return result

private def motiveHypothesisValues (motives fields binders : Array Expr) : MetaM (Array Expr) := do
  let mut result := #[]
  for binder in binders do
    unless fields.contains binder do
      let type ← inferType binder
      if motives.contains (eventualBody `_family_adapter_public_minor_hypothesis type).getAppFn then
        result := result.push binder
  return result

private def privateMotiveValue (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate) (parameters : Array Expr)
    (member : MemberPlan) (publicMotive expectedType : Expr) : ConstructionM Expr := do
  forallBoundedTelescope expectedType (some (numForalls expectedType)) fun binders _ => do
    let some privateValue := binders.back? | failConstruction (.missingMemberMap member.key)
    let indices := binders.extract 0 (binders.size - 1)
    let publicMotiveType ← inferType publicMotive
    let publicAfterIndices ← instantiateForall publicMotiveType indices
    let .forallE _ publicType _ _ := publicAfterIndices
      | failConstruction (.missingMemberMap member.key)
    let privateType ← inferType privateValue
    let (publicValue, _) ← mapCarrierValue plan memberCertificates parameters member false
      privateType publicType privateValue
    mkLambdaFVars binders (mkAppN publicMotive (indices.push publicValue))

private def privateMinorValue (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate)
    (telescopeCertificates : Array TelescopeCertificate)
    (constructorCertificates : Array PublicConstructorCertificate)
    (parameters publicMotives privateMotives : Array Expr)
    (member : MemberPlan) (minorIndex : Nat) (constructor : ConstructorPlan)
    (publicMinor expectedType : Expr) : ConstructionM Expr := do
  forallBoundedTelescope expectedType (some (numForalls expectedType))
      fun privateBinders privateResult => do
    let some privateFields := minorFieldValues? constructor privateBinders privateResult
      | failConstruction (.malformedRecursorMinor member.key minorIndex)
    let publicMinorType ← inferType publicMinor
    forallBoundedTelescope publicMinorType (some (numForalls publicMinorType))
        fun publicBinders publicResult => do
      let some constructorAdapter := constructorCertificates.find?
          (·.key == constructor.key)
        | failConstruction (.malformedRecursorMinor member.key minorIndex)
      let some publicFields := minorFieldValues? constructor publicBinders publicResult
          (some constructorAdapter.adapter)
        | failConstruction (.malformedRecursorMinor member.key minorIndex)
      let publicValues ← mapFields plan memberCertificates constructor parameters false
        privateFields publicFields privateFields
      let publicHypotheses ← liftGen <|
        motiveHypothesisValues publicMotives publicFields publicBinders
      let privateHypotheses ← liftGen <|
        motiveHypothesisValues privateMotives privateFields privateBinders
      let expectedHypothesisIndices := uniqueOccurrenceHypothesisIndices constructor
      unless expectedHypothesisIndices == Array.range publicHypotheses.size &&
          privateHypotheses.size == publicHypotheses.size do
        failConstruction (.malformedRecursorMinor member.key minorIndex)
      let mut arguments := #[]
      for binderIndex in [:publicBinders.size] do
        let binder := publicBinders[binderIndex]!
        let value? := if let some fieldIndex := publicFields.findIdx? (· == binder) then
            publicValues[fieldIndex]?
          else if let some hypothesisIndex := publicHypotheses.findIdx? (· == binder) then
            privateHypotheses[hypothesisIndex]?
          else none
        let some value := value?
          | failConstruction (.malformedRecursorMinor member.key minorIndex)
        let expected := (← inferType binder).replaceFVars
          (publicBinders.extract 0 binderIndex) arguments
        unless ← isDefEq (← inferType value) expected do
          failConstruction (.dependentRecursorMinorTransport member.key minorIndex binderIndex)
        arguments := arguments.push value
      let base := mkAppN publicMinor arguments
      let some telescope := telescopeCertificates.find? (·.constructor == constructor.key)
        | failConstruction (.malformedRecursorMinor member.key minorIndex)
      let privatePackageType ← liftGen <| packedTelescopeType privateFields
      let privatePackage ← liftGen <| packTelescopeValue privateFields privateFields
      let levels := plan.levelParams.map Level.param
      let decoded := mkAppN (.const telescope.decode levels) (parameters.push privatePackage)
      let encodedDecoded := mkAppN (.const telescope.encode levels) (parameters.push decoded)
      let roundTrip := mkAppN (.const telescope.encodeDecode levels)
        (parameters.push privatePackage)
      let some owner := plan.members.find? (·.key == constructor.key.owner)
        | failConstruction (.malformedRecursorMinor member.key minorIndex)
      let some ownerIndex := plan.members.findIdx? (·.key == owner.key)
        | failConstruction (.malformedRecursorMinor member.key minorIndex)
      let ownerMotive := publicMotives[ownerIndex]!
      let eqi ← match EqInfo.check (← getEnv) with
        | .ok information => pure information
        | .error _ => failConstruction (.malformedRecursorMinor member.key minorIndex)
      let baseType ← inferType base
      let resultLevel ← ilevel baseType
      let packageLevel ← ilevel privatePackageType
      let transported ← liftGen <| transportAlong eqi resultLevel packageLevel
        privatePackageType encodedDecoded privatePackage roundTrip base fun package => do
          let values ← unpackTelescopeValue privateFields package
          let privateMajor := mkAppN
            (.const constructor.implementationName (plan.levelParams.map Level.param))
            (parameters ++ values)
          let privateMajorType ← inferType privateMajor
          let mapped ← (mapCarrierValueInfer plan memberCertificates parameters owner false
            privateMajorType privateMajor).run
          let (publicMajor, publicMajorType, _) ← match mapped with
            | .ok mapped => pure mapped
            | .error issue => badShape s!"family-adapter recursor minor map failed: {repr issue}"
          let indices := resultIndices owner publicMajorType
          return mkAppN ownerMotive (indices.push publicMajor)
      unless ← isDefEq (← inferType transported) privateResult do
        failConstruction (.dependentRecursorMinorTransport member.key minorIndex
          privateBinders.size)
      let _ := constructorAdapter
      mkLambdaFVars privateBinders transported

/-- A nested recursor can bind minors for specialised mimic constructors that
are not source constructors.  Build their source-specialised constructor
boundary from the two exact minor telescopes: fields are the literal binders
used by the constructor application, and every changed field crosses only an
already checked family/container equivalence. -/
private def specialisedMinorConstructorDeclaration (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate) (parameters : Array Expr)
    (root : Name) (member : MemberPlan) (minorIndex : Nat)
    (publicMinorType privateMinorType : Expr) : ConstructionM
    (Declaration × PublicMinorConstructorCertificate) := do
  forallBoundedTelescope publicMinorType (some (numForalls publicMinorType))
      fun publicBinders publicResult => do
    let some publicMajor := publicResult.getAppArgs.back?
      | failConstruction (.malformedRecursorMinor member.key minorIndex)
    let some publicConstructor := publicMajor.getAppFn.constName?
      | failConstruction (.malformedRecursorMinor member.key minorIndex)
    let publicFields := publicMajor.getAppArgs.filter publicBinders.contains
    forallBoundedTelescope privateMinorType (some (numForalls privateMinorType))
        fun privateBinders privateResult => do
      let some privateMajor := privateResult.getAppArgs.back?
        | failConstruction (.malformedRecursorMinor member.key minorIndex)
      let some implementationConstructor := privateMajor.getAppFn.constName?
        | failConstruction (.malformedRecursorMinor member.key minorIndex)
      let privateFields := privateMajor.getAppArgs.filter privateBinders.contains
      unless publicFields.size == privateFields.size do
        failConstruction (.malformedRecursorMinor member.key minorIndex)
      let name := publicMinorConstructorAdapterName root member.key minorIndex
      liftGen <| ensurePrototypeFresh name
      let publicMajorType ← liftGen <| inferType publicMajor
      let exactType ← liftGen <| mkForallFVars (parameters ++ publicFields) publicMajorType
      let mut privateValues := #[]
      for fieldIndex in [:publicFields.size] do
        let publicValue := publicFields[fieldIndex]!
        let publicType ← liftGen <| inferType publicValue
        let privateType := (← liftGen <| inferType privateFields[fieldIndex]!).replaceFVars
          (privateFields.extract 0 fieldIndex) privateValues
        let (privateValue, _) ← mapCarrierValue plan memberCertificates parameters member true
          publicType privateType publicValue
        privateValues := privateValues.push privateValue
      let privateMajor := privateMajor.replaceFVars privateFields privateValues
      let privateMajorType ← liftGen <| inferType privateMajor
      let (publicValue, _) ← mapCarrierValue plan memberCertificates parameters member false
        privateMajorType publicMajorType privateMajor
      let value ← liftGen <| mkLambdaFVars (parameters ++ publicFields) publicValue
      let declaration := Declaration.defnDecl
        { name, levelParams := plan.levelParams, type := exactType, value,
          hints := .abbrev, safety := .safe }
      liftGen <| addChecked declaration
      return (declaration,
        { recursor := member.key, minorIndex, publicConstructor, implementationConstructor,
          adapter := name, exactType, fieldArity := publicFields.size })

private def rewriteSpecialisedMinorType (plan : FamilyAdapterPlan)
    (member : MemberPlan) (parameters : Array Expr)
    (certificate : PublicMinorConstructorCertificate) (minorType : Expr) : ConstructionM Expr := do
  forallBoundedTelescope minorType (some (numForalls minorType)) fun binders result => do
    let some major := result.getAppArgs.back?
      | failConstruction (.malformedRecursorMinor member.key certificate.minorIndex)
    unless major.getAppFn.constName? == some certificate.publicConstructor do
      failConstruction (.malformedRecursorMinor member.key certificate.minorIndex)
    let fields := major.getAppArgs.filter binders.contains
    unless fields.size == certificate.fieldArity do
      failConstruction (.malformedRecursorMinor member.key certificate.minorIndex)
    let replacement := mkAppN
      (.const certificate.adapter (plan.levelParams.map Level.param)) (parameters ++ fields)
    unless ← isDefEq (← inferType replacement) (← inferType major) do
      failConstruction (.malformedRecursorMinor member.key certificate.minorIndex)
    let arguments := result.getAppArgs
    let rewrittenResult := mkAppN result.getAppFn
      (arguments.extract 0 (arguments.size - 1) |>.push replacement)
    mkForallFVars binders rewrittenResult

/-- Rewrite each specialised constructor only in its exact recursor-minor binder.
The recursor parameters are opened once and threaded directly; no constructor
name search or carrier-occurrence search chooses between minor positions. -/
private def rewriteMinorConstructors (plan : FamilyAdapterPlan) (member : MemberPlan)
    (minorConstructors : Array PublicMinorConstructorCertificate)
    (expression : Expr) : ConstructionM Expr := do
  let prefixSize := member.parameterArity + member.recursorMotiveArity +
    member.recursorMinorArity
  forallBoundedTelescope expression (some prefixSize) fun recursorPrefix tail => do
    let minorStart := member.parameterArity + member.recursorMotiveArity
    let outer := recursorPrefix.extract 0 minorStart
    let parameters := recursorPrefix.extract 0 member.parameterArity
    let originalMinors := recursorPrefix.extract minorStart prefixSize
    let rec rebuild (minorIndex : Nat) (rewrittenMinors : Array Expr) : ConstructionM Expr := do
      if h : minorIndex < originalMinors.size then
        let originalMinor := originalMinors[minorIndex]
        let originalType ← inferType originalMinor
        let currentType := originalType.replaceFVars
          (originalMinors.extract 0 minorIndex) rewrittenMinors
        let rewrittenType ← match minorConstructors.find? (·.minorIndex == minorIndex) with
          | some certificate =>
            rewriteSpecialisedMinorType plan member parameters certificate currentType
          | none => pure currentType
        let declaration ← getFVarLocalDecl originalMinor
        withLocalDecl declaration.userName declaration.binderInfo rewrittenType fun rewrittenMinor =>
          rebuild (minorIndex + 1) (rewrittenMinors.push rewrittenMinor)
      else
        let originalPrefix := outer ++ originalMinors
        let rewrittenPrefix := outer ++ rewrittenMinors
        let rewrittenTail := tail.replaceFVars originalPrefix rewrittenPrefix
        mkForallFVars rewrittenPrefix rewrittenTail
    rebuild 0 #[]

private def buildMinorConstructorAdapters (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate)
    (constructorCertificates : Array PublicConstructorCertificate)
    (root : Name) (member : MemberPlan) (publicType privateType : Expr) : ConstructionM
    (Array Declaration × Array PublicMinorConstructorCertificate) := do
  let prefixSize := member.parameterArity + member.recursorMotiveArity +
    member.recursorMinorArity
  forallBoundedTelescope publicType (some prefixSize) fun publicPrefix _ => do
    let parameters := publicPrefix.extract 0 member.parameterArity
    let publicMotives := publicPrefix.extract member.parameterArity
      (member.parameterArity + member.recursorMotiveArity)
    let publicMinors := publicPrefix.extract
      (member.parameterArity + member.recursorMotiveArity) prefixSize
    let mut privateTail ← instantiateForall privateType parameters
    for motiveIndex in [:member.recursorMotiveArity] do
      let .forallE _ expected rest _ := privateTail
        | failConstruction (.shortInstalledRecursorPrefix member.key member.implementationRecursor)
      let motiveMember := plan.members[motiveIndex]?.getD member
      let motive ← privateMotiveValue plan memberCertificates parameters
        motiveMember publicMotives[motiveIndex]! expected
      privateTail := rest.instantiate1 motive
    let (privateBinders, _) := openExactForalls `_family_adapter_private_minor_types privateTail
    unless privateBinders.size >= member.recursorMinorArity do
      failConstruction (.shortInstalledRecursorPrefix member.key member.implementationRecursor)
    let mut declarations := #[]
    let mut certificates := #[]
    for minorIndex in [:member.recursorMinorArity] do
      let publicMinorType ← liftGen <| inferType publicMinors[minorIndex]!
      let privateMinorType := privateBinders[minorIndex]!.type
      let some publicName := minorConstructorName? publicMinorType
        | failConstruction (.malformedRecursorMinor member.key minorIndex)
      let some privateName := minorConstructorName? privateMinorType
        | failConstruction (.malformedRecursorMinor member.key minorIndex)
      if let some constructor := plan.constructors.find? fun constructor =>
          constructor.publicName == publicName && constructor.implementationName == privateName then
        let some adapter := constructorCertificates.find? (·.key == constructor.key)
          | failConstruction (.malformedRecursorMinor member.key minorIndex)
        certificates := certificates.push
          { recursor := member.key, minorIndex, publicConstructor := publicName,
            implementationConstructor := privateName, adapter := adapter.adapter,
            exactType := adapter.exactType,
            fieldArity := constructor.telescope.binders.size }
      else
        let (declaration, certificate) ← specialisedMinorConstructorDeclaration plan
          memberCertificates parameters root member minorIndex publicMinorType privateMinorType
        declarations := declarations.push declaration
        certificates := certificates.push certificate
    return (declarations, certificates)

private def privateSpecialisedMinorValue (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate)
    (parameters publicMotives privateMotives : Array Expr)
    (member : MemberPlan) (minor : PublicMinorConstructorCertificate)
    (publicMinor expectedType : Expr) : ConstructionM Expr := do
  forallBoundedTelescope expectedType (some (numForalls expectedType))
      fun privateBinders privateResult => do
    let privateValues := privateBinders
    let some privateMajor := privateResult.getAppArgs.back?
      | failConstruction (.malformedRecursorMinor member.key minor.minorIndex)
    let privateFields := privateMajor.getAppArgs.filter privateValues.contains
    let publicMinorType ← liftGen <| inferType publicMinor
    forallBoundedTelescope publicMinorType (some (numForalls publicMinorType))
        fun publicBinders publicResult => do
      let some publicMajor := publicResult.getAppArgs.back?
        | failConstruction (.malformedRecursorMinor member.key minor.minorIndex)
      let publicFields := publicMajor.getAppArgs.filter publicBinders.contains
      unless publicFields.size == privateFields.size do
        failConstruction (.malformedRecursorMinor member.key minor.minorIndex)
      let mut mappedPublic := #[]
      for fieldIndex in [:privateFields.size] do
        let privateValue := privateFields[fieldIndex]!
        let privateType ← liftGen <| inferType privateValue
        let publicType := (← liftGen <| inferType publicFields[fieldIndex]!).replaceFVars
          (publicFields.extract 0 fieldIndex) mappedPublic
        let (publicValue, _) ← mapCarrierValue plan memberCertificates parameters member false
          privateType publicType privateValue
        mappedPublic := mappedPublic.push publicValue
      let publicHypotheses ← liftGen <|
        motiveHypothesisValues publicMotives publicFields publicBinders
      let privateHypotheses ← liftGen <|
        motiveHypothesisValues privateMotives privateFields privateBinders
      unless publicHypotheses.size == privateHypotheses.size do
        failConstruction (.malformedRecursorMinor member.key minor.minorIndex)
      let mut arguments := #[]
      for binderIndex in [:publicBinders.size] do
        let binder := publicBinders[binderIndex]!
        let value? := if let some fieldIndex := publicFields.findIdx? (· == binder) then
            mappedPublic[fieldIndex]?
          else if let some hypothesisIndex := publicHypotheses.findIdx? (· == binder) then
            privateHypotheses[hypothesisIndex]?
          else none
        let some value := value?
          | failConstruction (.malformedRecursorMinor member.key minor.minorIndex)
        let expected := (← liftGen <| inferType binder).replaceFVars
          (publicBinders.extract 0 binderIndex) arguments
        unless ← liftGen <| isDefEq (← inferType value) expected do
          failConstruction (.dependentRecursorMinorTransport member.key minor.minorIndex binderIndex)
        arguments := arguments.push value
      let base := mkAppN publicMinor arguments
      let mut remappedPrivate := #[]
      let mut proofs := #[]
      for fieldIndex in [:privateFields.size] do
        let publicValue := mappedPublic[fieldIndex]!
        let publicType ← liftGen <| inferType publicValue
        let privateType := (← liftGen <| inferType privateFields[fieldIndex]!).replaceFVars
          (privateFields.extract 0 fieldIndex) remappedPrivate
        let (privateValue, _) ← mapCarrierValue plan memberCertificates parameters member true
          publicType privateType publicValue
        remappedPrivate := remappedPrivate.push privateValue
        let originalType ← liftGen <| inferType privateFields[fieldIndex]!
        let proof ← carrierRoundTrip plan memberCertificates parameters member false
          originalType publicType privateFields[fieldIndex]!
        proofs := proofs.push proof
      let privatePackageType ← liftGen <| packedTelescopeType privateFields
      let privatePackage ← liftGen <| packTelescopeValue privateFields privateFields
      let remappedPackage ← liftGen <| packTelescopeValue privateFields remappedPrivate
      let eqi ← match EqInfo.check (← getEnv) with
        | .ok information => pure information
        | .error _ => failConstruction (.malformedRecursorMinor member.key minor.minorIndex)
      let packageProof ← liftGen <| packageCongruence eqi privateFields privatePackageType
        remappedPrivate privateFields proofs
      let some motiveIndex := privateMotives.findIdx? fun motive =>
          privateResult.getAppFn == motive
        | failConstruction (.malformedRecursorMinor member.key minor.minorIndex)
      let ownerMotive := publicMotives[motiveIndex]!
      let baseType ← liftGen <| inferType base
      let resultLevel ← liftGen <| ilevel baseType
      let packageLevel ← liftGen <| ilevel privatePackageType
      let transported ← liftGen <| transportAlong eqi resultLevel packageLevel
        privatePackageType remappedPackage privatePackage packageProof base fun package => do
          let values ← unpackTelescopeValue privateFields package
          let major := privateMajor.replaceFVars privateFields values
          let majorType ← inferType major
          let fallbackOwner := plan.members[motiveIndex]?.getD member
          let mapped ← (mapCarrierValueInfer plan memberCertificates parameters fallbackOwner false
            majorType major).run
          let (publicMajor, publicMajorType, _) ← match mapped with
            | .ok mapped => pure mapped
            | .error issue =>
              badShape s!"family-adapter specialised minor map failed: {repr issue}"
          let motiveArity := numForalls (← inferType ownerMotive)
          let indexArity := motiveArity - 1
          let majorArguments := publicMajorType.getAppArgs
          let indices := majorArguments.extract (majorArguments.size - indexArity)
            majorArguments.size
          return mkAppN ownerMotive (indices.push publicMajor)
      unless ← liftGen <| isDefEq (← inferType transported) privateResult do
        failConstruction (.dependentRecursorMinorTransport member.key minor.minorIndex
          privateBinders.size)
      mkLambdaFVars privateBinders transported

private def publicRecursorDeclaration (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate)
    (telescopeCertificates : Array TelescopeCertificate)
    (constructorCertificates : Array PublicConstructorCertificate)
    (root : Name) (member : MemberPlan) : ConstructionM
    (Array Declaration × PublicRecursorCertificate) := do
  let name := publicRecursorAdapterName root member.key
  liftGen <| ensurePrototypeFresh name
  let some publicRecursorInfo := (← getEnv).constants.find? member.publicRecursor
    | failConstruction (.missingInstalledRecursor member.key member.publicRecursor)
  let some privateRecursorInfo := (← getEnv).constants.find? member.implementationRecursor
    | failConstruction (.missingInstalledRecursor member.key member.implementationRecursor)
  let constructorMapping := constructorCertificates.map fun certificate =>
    let constructor := (plan.constructors.find? (·.key == certificate.key)).get!
    (constructor.publicName, certificate.adapter)
  let publicSourceType := publicRecursorInfo.type
  let privateType := privateRecursorInfo.type
  let (minorDeclarations, minorCertificates) ← buildMinorConstructorAdapters plan
    memberCertificates constructorCertificates root member publicSourceType privateType
  let sourceMappedType := mapConstsE
    (fun name => constructorMapping.find? (·.1 == name) |>.map (·.2)) publicSourceType
  let specialisedMinors := minorCertificates.filter fun certificate =>
    !plan.constructors.any fun constructor =>
      constructor.publicName == certificate.publicConstructor &&
        constructor.implementationName == certificate.implementationConstructor
  let publicType ← rewriteMinorConstructors plan member specialisedMinors sourceMappedType
  let motiveCertificates ← match recursorMotiveCertificates member publicSourceType privateType with
    | .ok certificates => pure certificates
    | .error issue => failConstruction issue
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error _ => failConstruction (.recursorResultMismatch member.key)
  let prefixSize := member.parameterArity + member.recursorMotiveArity +
    member.recursorMinorArity
  let publicMinorNames ← match minorConstructorSequence member true publicSourceType with
    | .ok keys => pure keys
    | .error issue => failConstruction issue
  let privateMinorNames ← match minorConstructorSequence member false privateType with
    | .ok keys => pure keys
    | .error issue => failConstruction issue
  unless minorCertificates.size == member.recursorMinorArity &&
      (Array.range member.recursorMinorArity).all fun minorIndex =>
        (minorCertificates[minorIndex]?).any fun certificate =>
          certificate.minorIndex == minorIndex &&
            publicMinorNames[minorIndex]? == some certificate.publicConstructor &&
            privateMinorNames[minorIndex]? == some certificate.implementationConstructor do
    failConstruction (.malformedRecursorMinor member.key minorCertificates.size)
  let value ← forallBoundedTelescope publicType (some prefixSize)
      fun publicPrefix publicTailType => do
    let parameters := publicPrefix.extract 0 member.parameterArity
    let publicMotives := publicPrefix.extract member.parameterArity
      (member.parameterArity + member.recursorMotiveArity)
    let publicMinors := publicPrefix.extract
      (member.parameterArity + member.recursorMotiveArity) prefixSize
    unless publicMotives.size == motiveCertificates.size &&
        publicMinors.size == minorCertificates.size do
      failConstruction (.shortInstalledRecursorPrefix member.key member.publicRecursor)
    let mut privateTail ← instantiateForall privateType parameters
    let mut privateMotives := #[]
    for motiveIndex in [:motiveCertificates.size] do
      let .forallE _ expected rest _ := privateTail
        | do
          failConstruction (.shortInstalledRecursorPrefix member.key member.implementationRecursor)
      let motiveMember := plan.members[motiveIndex]?.getD member
      let motive ← privateMotiveValue plan memberCertificates parameters
        motiveMember publicMotives[motiveIndex]! expected
      privateMotives := privateMotives.push motive
      privateTail := rest.instantiate1 motive
    let mut privateMinors := #[]
    for minorIndex in [:minorCertificates.size] do
      let .forallE _ expected rest _ := privateTail
        | do
          failConstruction (.shortInstalledRecursorPrefix member.key member.implementationRecursor)
      let certificate := minorCertificates[minorIndex]!
      let minor ← if let some constructor := plan.constructors.find? fun constructor =>
          constructor.publicName == certificate.publicConstructor &&
            constructor.implementationName == certificate.implementationConstructor then
        privateMinorValue plan memberCertificates telescopeCertificates
          constructorCertificates parameters publicMotives privateMotives member minorIndex
          constructor publicMinors[minorIndex]! expected
      else
        privateSpecialisedMinorValue plan memberCertificates parameters publicMotives
          privateMotives member certificate publicMinors[minorIndex]! expected
      privateMinors := privateMinors.push minor
      privateTail := rest.instantiate1 minor
    forallBoundedTelescope publicTailType (some (numForalls publicTailType))
        fun publicTail publicResult => do
      let some publicMajor := publicTail.back?
        | failConstruction (.shortInstalledRecursorPrefix member.key member.publicRecursor)
      let indices := publicTail.extract 0 (publicTail.size - 1)
      let privateMajorTail ← instantiateForall privateTail indices
      let .forallE _ privateMajorType _ _ := privateMajorTail
        | do
          failConstruction (.shortInstalledRecursorPrefix member.key member.implementationRecursor)
      let publicMajorType ← inferType publicMajor
      let (privateMajor, _) ← mapCarrierValue plan memberCertificates parameters member true
        publicMajorType privateMajorType publicMajor
      let privateCall := mkAppN
        (.const member.implementationRecursor
          (privateRecursorInfo.levelParams.map Level.param))
        (parameters ++ privateMotives ++ privateMinors ++ indices ++ #[privateMajor])
      let privateCallType ← inferType privateCall
      let (roundTripMajor, _) ← mapCarrierValue plan memberCertificates parameters member false
        privateMajorType publicMajorType privateMajor
      let roundTrip ← carrierRoundTrip plan memberCertificates parameters member true
        publicMajorType privateMajorType publicMajor
      let some ownerIndex := plan.members.findIdx? (·.key == member.key)
        | failConstruction (.missingMemberMap member.key)
      let publicMotive := publicMotives[ownerIndex]!
      let resultLevel ← ilevel privateCallType
      let majorLevel ← ilevel publicMajorType
      let transported ← liftGen <| transportAlong eqi
        resultLevel majorLevel publicMajorType roundTripMajor publicMajor roundTrip privateCall
        fun value => pure (mkAppN publicMotive (indices.push value))
      unless ← isDefEq (← inferType transported) publicResult do
        failConstruction (.recursorResultMismatch member.key)
      mkLambdaFVars (publicPrefix ++ publicTail) transported
  let declaration := Declaration.defnDecl
    { name, levelParams := publicRecursorInfo.levelParams, type := publicType, value,
      hints := .abbrev, safety := .safe }
  liftGen <| addChecked declaration
  return (minorDeclarations.push declaration,
    { member := member.key, adapter := name, exactType := publicType,
      implementationRecursor := member.implementationRecursor,
      motives := motiveCertificates, minors := minorCertificates,
      rules := member.sourceRules })

private def buildPublicRecursorPrototypesCore (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate)
    (telescopeCertificates : Array TelescopeCertificate)
    (constructorCertificates : Array PublicConstructorCertificate)
    (root : Name) : ConstructionM
    (Array Declaration × Array PublicRecursorCertificate) := do
  let mut declarations := #[]
  let mut certificates := #[]
  for member in plan.members do
    let (memberDeclarations, certificate) ← publicRecursorDeclaration plan memberCertificates
      telescopeCertificates constructorCertificates root member
    declarations := declarations ++ memberDeclarations
    certificates := certificates.push certificate
  return (declarations, certificates)

/-- Disabled exact-public recursor tranche. -/
def buildPublicRecursorPrototypes (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate)
    (telescopeCertificates : Array TelescopeCertificate)
    (constructorCertificates : Array PublicConstructorCertificate) (root : Name) : GenM
    (Except ConstructionIssue (Array Declaration × Array PublicRecursorCertificate)) := do
  let saved ← getEnv
  match ← ExceptT.lift
      (buildPublicRecursorPrototypesCore plan memberCertificates telescopeCertificates
        constructorCertificates root).run with
  | .error decline =>
    setEnv saved
    declineWith decline
  | .ok (.error issue) =>
    setEnv saved
    return .error issue
  | .ok (.ok built) => return .ok built

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
  let mut ruleCertificates := #[]
  if issues.isEmpty then
    match ← buildRuleCompatibilityPrototypes plan minorHypotheses root with
    | .error issue => issues := issues.push issue
    | .ok (added, certificates) =>
      declarations := declarations ++ added
      ruleCertificates := certificates
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
      minorHypotheses := minorHypotheses,
      rules := ruleCertificates }
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
