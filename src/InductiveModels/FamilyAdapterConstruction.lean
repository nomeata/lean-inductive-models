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
    {C : P → Sort v} {HP : R → Sort x} {HI : Q → Sort y}
    (forward : P → M) (backward : M → P)
    (backwardForward : ∀ p, backward (forward p) = p)
    (encode : R → Q) (decode : Q → R)
    (decodeEncode : ∀ p, decode (encode p) = p)
    (privateCtor : Q → M) (publicCtor : R → P)
    (forwardCtor : ∀ p, forward (publicCtor p) = privateCtor (encode p))
    (privateIH : ∀ q, HI q) (publicIH : ∀ p, HP p)
    (decodeIH : ∀ q, HI q → HP (decode q))
    (ihAgreement : ∀ q, publicIH (decode q) = decodeIH q (privateIH q))
    (minor : ∀ p, HP p → C (publicCtor p))
    (core : ∀ q, C (backward q))
    (constructorAgreement : ∀ q,
      publicCtor (decode q) = backward (privateCtor q))
    (coreIota : ∀ q, core (privateCtor q) =
      Eq.mp (congrArg C (constructorAgreement q))
        (minor (decode q) (decodeIH q (privateIH q)))) :
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
            let privateResult := minor (decode q) (decodeIH q (privateIH q))
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

/-- The transported public recursor agrees with its private core at the
backward image of every totalised carrier value. Proof irrelevance identifies
the two exact round-trip paths; no simplifier is involved. -/
theorem packedRecursorAgreement
    {M : Sort uM} {P : Sort uP} {C : P → Sort v}
    (forward : P → M) (backward : M → P)
    (backwardForward : ∀ p, backward (forward p) = p)
    (forwardBackward : ∀ q, forward (backward q) = q)
    (core : ∀ q, C (backward q)) :
    let publicRec : ∀ p, C p := fun p =>
      Eq.mp (congrArg C (backwardForward p)) (core (forward p))
    ∀ q, publicRec (backward q) = core q := by
  intro publicRec q
  unfold publicRec
  have paths : backwardForward (backward q) = congrArg backward (forwardBackward q) :=
    Subsingleton.elim _ _
  rw [paths]
  have move (r : M) (h : r = q) :
      Eq.mp (congrArg C (congrArg backward h)) (core r) = core q := by
    cases h
    rfl
  exact move _ (forwardBackward q)

/-- Forward-oriented form used at a constructor-package encoding boundary.
The result is transported back to the private motive fibre, so it composes
directly with an installed minor hypothesis. -/
theorem packedRecursorForwardAgreement
    {M : Sort uM} {P : Sort uP} {C : P → Sort v}
    (forward : P → M) (backward : M → P)
    (backwardForward : ∀ p, backward (forward p) = p)
    (core : ∀ q, C (backward q)) :
    let publicRec : ∀ p, C p := fun p =>
      Eq.mp (congrArg C (backwardForward p)) (core (forward p))
    ∀ p, core (forward p) =
      Eq.mp (congrArg C (backwardForward p).symm) (publicRec p) := by
  intro publicRec p
  unfold publicRec
  have cancel {a b : P} (h : a = b) (value : C a) :
      Eq.mp (congrArg C h.symm) (Eq.mp (congrArg C h) value) = value := by
    exact Eq.rec (motive := fun b h =>
      Eq.mp (congrArg C h.symm) (Eq.mp (congrArg C h) value) = value) rfl h
  exact (cancel (backwardForward p) _).symm

/-- A keyed construction obligation.  These are semantic failures of an exact
certificate, never eligibility predicates or cardinality limits. -/
inductive PublicRecursorResultBoundary where
  | transportedResult
  | agreementMotive
  deriving Inhabited, BEq, Repr

inductive PublicIotaProofBoundary where
  | hypothesisAgreement (publicBinder implementationBinder : Nat)
  | expectedHypothesisPackage
  | privateHypothesisPackage
  | decodedHypothesisPackage
  | installedRuleRhs
  | privateMinorResult
  | decodedHypothesis (publicBinder implementationBinder : Nat)
  | minorCompatibilityType
  | minorCompatibilityLeft
  | coreTransport
  | finalProof
  deriving Inhabited, BEq, Repr

/-- Test-visible subdivision of the exact recursive-call certificate boundary.
It records which keyed check rejected the call without changing proof search. -/
inductive PublicIotaRecursiveCallBoundary where
  | roleResolution
  | agreementNotInstalled
  | openedHeadMismatch
  | agreementEndpoint
  | dependentResult
  deriving Inhabited, BEq, Repr

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
  | missingPublicIotaRecursiveCall (rule : RuleKey) (publicBinder implementationBinder : Nat)
  | publicIotaRecursiveCallMismatch (rule : RuleKey)
      (publicBinder implementationBinder : Nat) (boundary : PublicIotaRecursiveCallBoundary)
  | publicIotaProofMismatch (rule : RuleKey) (boundary : PublicIotaProofBoundary)
  | recursorResultMismatch (member : MemberKey)
  | publicRecursorResultMismatch (member : MemberKey)
      (boundary : PublicRecursorResultBoundary)
  | publicRecursorAgreementMismatch (member : MemberKey)
      (actual expected : Expr)
  | malformedRecursorMinor (member : MemberKey) (minorIndex : Nat)
  | dependentRecursorMinorTransport (member : MemberKey) (minorIndex binderIndex : Nat)
  | missingMemberMap (member : MemberKey)
  | missingRecursorMotiveBoundary (member : MemberKey)
  | missingExactCarrierCandidate (member : MemberKey)
  | ambiguousExactCarrierCandidate (member : MemberKey)
  | invalidExactCarrierLaw (member : MemberKey)
  | recursorMajorBoundaryMismatch (member : MemberKey)
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

/-- Recursor telescope metadata, deliberately separate from named-family
membership. Specialised container recursors have this shape without becoming
members of the source family. -/
structure RecursorShape where
  key : MemberKey
  parameterArity : Nat
  indexArity : Nat
  motiveArity : Nat
  minorArity : Nat
  sourceRecursor : Name
  implementationRecursor : Name
  publicRecursor : Name
  sourceRules : Array RuleKey := #[]
  deriving Inhabited, BEq, Repr

/-- An exact installed equivalence for the major carrier of one recursor.
Families are closed lambdas over the complete parameter/index telescope; map
and law types are retained verbatim so construction never reselects metadata
by member position or carrier spelling. -/
structure RecursorCarrierBoundary where
  key : MemberKey
  parameterArity : Nat
  indexArity : Nat
  publicFamily : Expr
  implementationFamily : Expr
  boundary : ContainerRecursorBoundaryPlan
  deriving Inhabited, BEq, Repr

structure BuiltContainerRecursor where
  plan : ContainerRecursorPlan
  shape : RecursorShape
  recursor : PublicRecursorCertificate
  certificate : ContainerRecursorCertificate

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

private def memberRecursorShape (member : MemberPlan) : RecursorShape :=
  { key := member.key
    parameterArity := member.parameterArity
    indexArity := member.indexArity
    motiveArity := member.recursorMotiveArity
    minorArity := member.recursorMinorArity
    sourceRecursor := member.sourceRecursor
    implementationRecursor := member.implementationRecursor
    publicRecursor := member.publicRecursor
    sourceRules := member.sourceRules }

private def containerRecursorShape (container : ContainerRecursorPlan) : RecursorShape :=
  let key : MemberKey := { owner := container.key.publicRecursor }
  { key
    parameterArity := container.parameterArity
    indexArity := container.indexArity
    motiveArity := container.motiveArity
    minorArity := container.minorArity
    sourceRecursor := container.key.publicRecursor
    implementationRecursor := container.key.implementationRecursor
    publicRecursor := container.key.publicRecursor }

private def namedCarrierFamily (plan : FamilyAdapterPlan) (member : MemberPlan)
    (carrier : Name) : GenM Expr := do
  let arity := member.parameterArity + member.indexArity
  let carrierType ← generatedType carrier
  forallBoundedTelescope carrierType (some arity) fun arguments _ =>
    mkLambdaFVars arguments
      (mkAppN (.const carrier (plan.levelParams.map Level.param)) arguments)

private def memberRecursorBoundary (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate) (member : MemberPlan) :
    ConstructionM RecursorCarrierBoundary := do
  let some certificate := memberCertificates.find? (·.key == member.key)
    | failConstruction (.missingMemberMap member.key)
  let publicFamily ← liftGen <| namedCarrierFamily plan member member.publicCarrier
  let implementationFamily ←
    liftGen <| namedCarrierFamily plan member member.implementationCarrier
  let forwardType ← liftGen <| memberMapType plan member member.publicCarrier
    member.implementationCarrier
  let backwardType ← liftGen <| memberMapType plan member member.implementationCarrier
    member.publicCarrier
  let backwardForwardType ← liftGen <| memberLawType plan member member.publicCarrier
    certificate.maps.forward certificate.maps.backward
  let forwardBackwardType ← liftGen <| memberLawType plan member
    member.implementationCarrier certificate.maps.backward certificate.maps.forward
  let result : RecursorCarrierBoundary :=
    { key := member.key
      parameterArity := member.parameterArity
      indexArity := member.indexArity
      publicFamily
      implementationFamily
      boundary := .installed certificate.maps forwardType backwardType
        backwardForwardType forwardBackwardType }
  pure result

private def containerRecursorBoundary (container : ContainerRecursorPlan) :
    RecursorCarrierBoundary :=
  { key := { owner := container.key.publicRecursor }
    parameterArity := container.parameterArity
    indexArity := container.indexArity
    publicFamily := container.publicMajorFamily
    implementationFamily := container.implementationMajorFamily
    boundary := container.boundary }

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

private def instantiateRecursorBoundaryIndices (boundary : RecursorCarrierBoundary)
    (parameters : Array Expr) (recordedType sourceType : Expr) : ConstructionM (Array Expr) := do
  unless parameters.size == boundary.parameterArity do
    failConstruction (.recursorMajorBoundaryMismatch boundary.key)
  let mut type ← liftGen <| instantiateForall recordedType parameters
  let mut indices := #[]
  for _ in [:boundary.indexArity] do
    let .forallE binderName domain body _ := type
      | failConstruction (.recursorMajorBoundaryMismatch boundary.key)
    let index ← liftGen <| mkFreshExprMVar domain .natural binderName
    indices := indices.push index
    type := body.instantiate1 index
  let .forallE _ domain _ _ := type
    | failConstruction (.recursorMajorBoundaryMismatch boundary.key)
  unless ← liftGen <| isDefEq domain sourceType do
    failConstruction (.recursorMajorBoundaryMismatch boundary.key)
  let resolved ← liftGen <| indices.mapM instantiateMVars
  for index in resolved do
    if ← liftGen <| hasAssignableMVar index then
      failConstruction (.recursorMajorBoundaryMismatch boundary.key)
  return resolved

private def applyRecursorBoundaryMap (plan : FamilyAdapterPlan)
    (boundary : RecursorCarrierBoundary) (forward : Bool) (parameters : Array Expr)
    (sourceType targetType value : Expr) : ConstructionM Expr := do
  let .installed maps forwardType backwardType _ _ := boundary.boundary
    | failConstruction (.recursorMajorBoundaryMismatch boundary.key)
  let name := if forward then maps.forward else maps.backward
  let recordedType := if forward then forwardType else backwardType
  let some installed := (← getEnv).constants.find? name |>.map (·.type)
    | failConstruction (.missingInstalledMemberMap boundary.key name)
  unless installed == recordedType do
    failConstruction (.installedMemberMapTypeMismatch boundary.key name)
  let indices ← instantiateRecursorBoundaryIndices boundary parameters recordedType sourceType
  let sourceFamily := if forward then boundary.publicFamily else boundary.implementationFamily
  let targetFamily := if forward then boundary.implementationFamily else boundary.publicFamily
  unless ← liftGen <| isDefEq (mkAppN sourceFamily (parameters ++ indices)) sourceType do
    failConstruction (.recursorMajorBoundaryMismatch boundary.key)
  unless ← liftGen <| isDefEq (mkAppN targetFamily (parameters ++ indices)) targetType do
    failConstruction (.recursorMajorBoundaryMismatch boundary.key)
  let application := mkAppN (.const name (plan.levelParams.map Level.param))
    (parameters ++ indices ++ #[value])
  unless ← liftGen <| isDefEq (← inferType application) targetType do
    failConstruction (.recursorMajorBoundaryMismatch boundary.key)
  return application

private def applyRecursorBoundaryLaw (plan : FamilyAdapterPlan)
    (boundary : RecursorCarrierBoundary) (forward : Bool) (parameters : Array Expr)
    (sourceType targetType value : Expr) : ConstructionM Expr := do
  let .installed maps _ _ backwardForwardType forwardBackwardType := boundary.boundary
    | failConstruction (.recursorMajorBoundaryMismatch boundary.key)
  let name := if forward then maps.backwardForward else maps.forwardBackward
  let recordedType := if forward then backwardForwardType else forwardBackwardType
  let some installed := (← getEnv).constants.find? name |>.map (·.type)
    | failConstruction (.missingInstalledMemberMap boundary.key name)
  unless installed == recordedType do
    failConstruction (.installedMemberMapTypeMismatch boundary.key name)
  let indices ← instantiateRecursorBoundaryIndices boundary parameters recordedType sourceType
  let sourceFamily := if forward then boundary.publicFamily else boundary.implementationFamily
  let targetFamily := if forward then boundary.implementationFamily else boundary.publicFamily
  unless ← liftGen <| isDefEq (mkAppN sourceFamily (parameters ++ indices)) sourceType do
    failConstruction (.recursorMajorBoundaryMismatch boundary.key)
  unless ← liftGen <| isDefEq (mkAppN targetFamily (parameters ++ indices)) targetType do
    failConstruction (.recursorMajorBoundaryMismatch boundary.key)
  return mkAppN (.const name (plan.levelParams.map Level.param))
    (parameters ++ indices ++ #[value])

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

private def publicRecursorCallAgreementName (root : Name) (member : MemberKey) : Name :=
  prototypeName root member.owner `publicRecursorCallAgreement

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
    left.sourceRecursor == right.sourceRecursor &&
    left.implementationRecursor == right.implementationRecursor &&
    left.sourceRecursorType == right.sourceRecursorType &&
    left.implementationRecursorType == right.implementationRecursorType &&
    left.recursorRuleKeys == right.recursorRuleKeys &&
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

private structure ExactCarrierCandidate where
  boundary : ContainerRecursorBoundaryPlan
  mapped : Expr
  roundTrip : Expr
  lawLeft : Expr
  lawRight : Expr

private def checkedExactCarrierCandidate (fallback : MemberKey) (sourceType value : Expr)
    (boundary : ContainerRecursorBoundaryPlan) (mapped roundTrip : Expr) :
    ConstructionM ExactCarrierCandidate := do
  let some (lawCarrier, lawLeft, lawRight) ←
      liftGen <| matchEq? (← inferType roundTrip)
    | failConstruction (.invalidExactCarrierLaw fallback)
  unless ← liftGen <| isDefEq lawCarrier sourceType do
    failConstruction (.invalidExactCarrierLaw fallback)
  unless ← liftGen <| isDefEq lawRight value do
    failConstruction (.invalidExactCarrierLaw fallback)
  let result : ExactCarrierCandidate := { boundary, mapped, roundTrip, lawLeft, lawRight }
  pure result

/-- Resolve a live field conversion by exact source/target typing across every
installed member and container boundary. Repeated occurrence metadata for the
same boundary is harmless; distinct successful boundaries are ambiguous. -/
private def exactCarrierCandidateWithoutRecursors (plan : FamilyAdapterPlan)
    (certificates : Array MemberCertificate) (parameters : Array Expr)
    (fallback : RecursorCarrierBoundary) (forward : Bool)
    (sourceType targetType value : Expr) : ConstructionM ExactCarrierCandidate := do
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error _ => failConstruction (.missingMemberMap fallback.key)
  let mut candidates : Array ExactCarrierCandidate := #[]
  if fallback.boundary == .defeq && (← liftGen <| isDefEq sourceType targetType) then
    let sourceLevel ← liftGen <| ilevel sourceType
    let result : ExactCarrierCandidate :=
      { boundary := .defeq
        mapped := value
        roundTrip := eqi.refl' sourceLevel sourceType value
        lawLeft := value
        lawRight := value }
    candidates := candidates.push result
  for member in plan.members do
    if let some certificate := certificateFor? certificates member.key then
      if let some mapped ← liftGen <|
          applyMemberMap? plan member certificate forward sourceType targetType value then
        let law := lawName certificate forward
        let proof := mkAppN (.const law (plan.levelParams.map Level.param))
          (sourceType.getAppArgs.push value)
        let forwardType ← liftGen <| memberMapType plan member member.publicCarrier
          member.implementationCarrier
        let backwardType ← liftGen <| memberMapType plan member
          member.implementationCarrier member.publicCarrier
        let backwardForwardType ← liftGen <| memberLawType plan member
          member.publicCarrier certificate.maps.forward certificate.maps.backward
        let forwardBackwardType ← liftGen <| memberLawType plan member
          member.implementationCarrier certificate.maps.backward certificate.maps.forward
        let candidate ← checkedExactCarrierCandidate fallback.key sourceType value
          (.installed certificate.maps forwardType backwardType backwardForwardType
            forwardBackwardType) mapped proof
        candidates := candidates.push candidate
  let rootParameters := rootParameters plan parameters
  for container in plan.containerMaps do
    if let some mapped ← liftGen <|
        applyContainerMap? plan container forward rootParameters sourceType targetType value then
      let proof ← applyContainerLaw plan container forward rootParameters sourceType value
      let candidate ← checkedExactCarrierCandidate fallback.key sourceType value
        (.installed container.maps container.forwardType container.backwardType
          container.backwardForwardType container.forwardBackwardType) mapped proof
      candidates := candidates.push candidate
  let some first := candidates[0]?
    | failConstruction (.missingExactCarrierCandidate fallback.key)
  for candidate in candidates do
    unless candidate.boundary == first.boundary do
      failConstruction (.ambiguousExactCarrierCandidate fallback.key)
    unless ← liftGen <| isDefEq candidate.mapped first.mapped do
      failConstruction (.ambiguousExactCarrierCandidate fallback.key)
    unless ← liftGen <| isDefEq candidate.lawLeft first.lawLeft do
      failConstruction (.ambiguousExactCarrierCandidate fallback.key)
    unless ← liftGen <| isDefEq candidate.lawRight first.lawRight do
      failConstruction (.ambiguousExactCarrierCandidate fallback.key)
  return first

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

private def fixedCarrierBoundary (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate) (parameters : Array Expr)
    (fallback : MemberPlan) (publicType implementationType : Expr) :
    ConstructionM PackedCarrierBoundary := do
  let makeMap := fun (forward : Bool) => do
    let sourceType := if forward then publicType else implementationType
    let targetType := if forward then implementationType else publicType
    withLocalDeclD `value sourceType fun value => do
      let (mapped, _) ← mapCarrierValue plan memberCertificates parameters fallback forward
        sourceType targetType value
      liftGen <| mkLambdaFVars #[value] mapped
  let forward ← makeMap true
  let backward ← makeMap false
  let makeLaw := fun (isForward : Bool) => do
    let sourceType := if isForward then publicType else implementationType
    let targetType := if isForward then implementationType else publicType
    withLocalDeclD `value sourceType fun value => do
      let proof ← carrierRoundTrip plan memberCertificates parameters fallback isForward
        sourceType targetType value
      liftGen <| mkLambdaFVars #[value] proof
  let backwardForward ← makeLaw true
  let forwardBackward ← makeLaw false
  return PackedCarrierBoundary.mk publicType implementationType forward backward
    backwardForward forwardBackward

private def recursorCarrierAt (plan : FamilyAdapterPlan)
    (boundary : RecursorCarrierBoundary) (parameters : Array Expr)
    (publicType implementationType : Expr) : ConstructionM PackedCarrierBoundary := do
  if boundary.boundary == .defeq then
    unless parameters.size == boundary.parameterArity &&
        !boundary.publicFamily.hasFVar && !boundary.implementationFamily.hasFVar &&
        (← liftGen <| isDefEq boundary.publicFamily boundary.implementationFamily) &&
        (← liftGen <| isDefEq publicType implementationType) do
      failConstruction (.recursorMajorBoundaryMismatch boundary.key)
    let eqi ← match EqInfo.check (← getEnv) with
      | .ok information => pure information
      | .error _ => failConstruction (.recursorMajorBoundaryMismatch boundary.key)
    let forward ← withLocalDeclD `value publicType fun value =>
      liftGen <| mkLambdaFVars #[value] value
    let backward ← withLocalDeclD `value implementationType fun value =>
      liftGen <| mkLambdaFVars #[value] value
    let backwardForward ← withLocalDeclD `value publicType fun value => do
      let proof := eqi.refl' (← liftGen <| ilevel publicType) publicType value
      liftGen <| mkLambdaFVars #[value] proof
    let forwardBackward ← withLocalDeclD `value implementationType fun value => do
      let proof := eqi.refl' (← liftGen <| ilevel implementationType)
        implementationType value
      liftGen <| mkLambdaFVars #[value] proof
    return PackedCarrierBoundary.mk publicType implementationType forward backward
      backwardForward forwardBackward
  let .installed .. := boundary.boundary
    | failConstruction (.recursorMajorBoundaryMismatch boundary.key)
  let makeMap := fun (forward : Bool) => do
    let sourceType := if forward then publicType else implementationType
    let targetType := if forward then implementationType else publicType
    withLocalDeclD `value sourceType fun value => do
      let mapped ← applyRecursorBoundaryMap plan boundary forward parameters
        sourceType targetType value
      liftGen <| mkLambdaFVars #[value] mapped
  let forward ← makeMap true
  let backward ← makeMap false
  let makeLaw := fun (forward : Bool) => do
    let sourceType := if forward then publicType else implementationType
    let targetType := if forward then implementationType else publicType
    withLocalDeclD `value sourceType fun value => do
      let proof ← applyRecursorBoundaryLaw plan boundary forward parameters
        sourceType targetType value
      liftGen <| mkLambdaFVars #[value] proof
  let backwardForward ← makeLaw true
  let forwardBackward ← makeLaw false
  return PackedCarrierBoundary.mk publicType implementationType forward backward
    backwardForward forwardBackward

private def recursorBoundaryParameters? (boundary : RecursorCarrierBoundary)
    (forward : Bool) (sourceType targetType : Expr) : ConstructionM (Option (Array Expr)) := do
  let sourceFamily := if forward then boundary.publicFamily else boundary.implementationFamily
  let targetFamily := if forward then boundary.implementationFamily else boundary.publicFamily
  let totalArity := boundary.parameterArity + boundary.indexArity
  let rec open (position : Nat) (family : Expr) (arguments : Array Expr) : ConstructionM
      (Option (Array Expr)) := do
    if position == totalArity then
      unless ← liftGen <| isDefEq family sourceType do return none
      let resolved ← liftGen <| arguments.mapM instantiateMVars
      for argument in resolved do
        if ← liftGen <| hasAssignableMVar argument then return none
      unless ← liftGen <| isDefEq (mkAppN targetFamily resolved) targetType do return none
      return some (resolved.extract 0 boundary.parameterArity)
    let .lam name domain body _ := family | return none
    let argument ← liftGen <| mkFreshExprMVar domain .natural name
    open (position + 1) (body.instantiate1 argument) (arguments.push argument)
  open 0 sourceFamily #[]

private def exactCarrierCandidate (plan : FamilyAdapterPlan)
    (certificates : Array MemberCertificate) (parameters : Array Expr)
    (fallback : RecursorCarrierBoundary) (forward : Bool)
    (sourceType targetType value : Expr) : ConstructionM ExactCarrierCandidate := do
  let mut candidates : Array ExactCarrierCandidate := #[]
  match ← liftGen <| (exactCarrierCandidateWithoutRecursors plan certificates parameters
      fallback forward sourceType targetType value).run with
  | .ok candidate => candidates := candidates.push candidate
  | .error (.missingExactCarrierCandidate key) =>
    unless key == fallback.key do failConstruction (.missingExactCarrierCandidate key)
  | .error issue => failConstruction issue
  for container in plan.containerRecursors do
    let boundary := containerRecursorBoundary container
    if let some liveParameters ←
        recursorBoundaryParameters? boundary forward sourceType targetType then
      let carrier ← recursorCarrierAt plan boundary liveParameters sourceType targetType
      let mapped := mkApp (if forward then carrier.forward else carrier.backward) value
      let roundTrip := mkApp
        (if forward then carrier.backwardForward else carrier.forwardBackward) value
      let candidate ← checkedExactCarrierCandidate fallback.key sourceType value
        container.boundary mapped roundTrip
      candidates := candidates.push candidate
  let some first := candidates[0]?
    | failConstruction (.missingExactCarrierCandidate fallback.key)
  for candidate in candidates do
    unless candidate.boundary == first.boundary do
      failConstruction (.ambiguousExactCarrierCandidate fallback.key)
    unless ← liftGen <| isDefEq candidate.mapped first.mapped do
      failConstruction (.ambiguousExactCarrierCandidate fallback.key)
    unless ← liftGen <| isDefEq candidate.lawLeft first.lawLeft do
      failConstruction (.ambiguousExactCarrierCandidate fallback.key)
    unless ← liftGen <| isDefEq candidate.lawRight first.lawRight do
      failConstruction (.ambiguousExactCarrierCandidate fallback.key)
  return first

private def recursorAgreementAt (shape : RecursorShape)
    (recursor : PublicRecursorCertificate)
    (rule : RuleKey) (publicBinderIndex implementationBinderIndex : Nat)
    (expectedPublic expectedPrivate : Expr) : ConstructionM Expr := do
  let reducedPrivate ← liftGen <| whnf expectedPrivate
  unless expectedPublic.getAppFn.constName? == some recursor.adapter &&
      reducedPrivate.getAppFn.constName? == some shape.implementationRecursor do
    failConstruction (.publicIotaRecursiveCallMismatch rule publicBinderIndex
      implementationBinderIndex .openedHeadMismatch)
  let publicArguments := expectedPublic.getAppArgs
  let privateArguments := reducedPrivate.getAppArgs
  let prefixSize := shape.parameterArity + shape.motiveArity + shape.minorArity
  unless publicArguments.size > prefixSize && privateArguments.size > prefixSize do
    failConstruction (.publicIotaRecursiveCallMismatch rule publicBinderIndex
      implementationBinderIndex .dependentResult)
  let publicPrefix := publicArguments.extract 0 prefixSize
  let privateTail := privateArguments.extract prefixSize privateArguments.size
  let some agreementInfo := (← getEnv).constants.find? recursor.callAgreement
    | failConstruction (.publicIotaRecursiveCallMismatch rule publicBinderIndex
        implementationBinderIndex .agreementNotInstalled)
  let proof := mkAppN
    (.const recursor.callAgreement (agreementInfo.levelParams.map Level.param))
    (publicPrefix ++ privateTail)
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error _ => failConstruction (.missingMemberMap shape.key)
  let resultType ← liftGen <| inferType expectedPrivate
  unless ← liftGen <| isDefEq (← inferType proof)
      (eqi.mk' (← ilevel resultType) resultType expectedPrivate expectedPublic) do
    failConstruction (.publicIotaRecursiveCallMismatch rule publicBinderIndex
      implementationBinderIndex .agreementEndpoint)
  return proof

private def recursiveCallCertificate (plan : FamilyAdapterPlan)
    (recursors : Array PublicRecursorCertificate)
    (containerRecursors : Array BuiltContainerRecursor) (rule : RuleKey)
    (role : PublicIotaRecursiveCallRole)
    (publicBinderIndex implementationBinderIndex : Nat) : ConstructionM
    (RecursorShape × PublicRecursorCertificate) := do
  let pair? : Option (RecursorShape × PublicRecursorCertificate) :=
    match role.member?, role.container? with
    | some memberKey, none => do
      let member ← plan.members.find? fun member =>
        member.key == memberKey && member.publicRecursor == role.publicRecursor &&
          member.implementationRecursor == role.implementationRecursor
      let recursor ← recursors.find? fun recursor =>
        recursor.member == member.key &&
          recursor.implementationRecursor == role.implementationRecursor
      some (memberRecursorShape member, recursor)
    | none, some key => do
      let built ← containerRecursors.find? fun built =>
        built.plan.key == key && built.plan.key.publicRecursor == role.publicRecursor &&
          built.plan.key.implementationRecursor == role.implementationRecursor &&
          role.containerOccurrences.all built.plan.occurrences.contains
      some (built.shape, built.recursor)
    | _, _ => none
  let some pair := pair?
    | failConstruction (.publicIotaRecursiveCallMismatch rule publicBinderIndex
        implementationBinderIndex .roleResolution)
  return pair

private def recursorForwardAgreementAt (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate)
    (member : MemberPlan) (recursor : PublicRecursorCertificate)
    (rawPublic expectedPrivate expectedPublic : Expr) : ConstructionM Expr := do
  let publicArguments := rawPublic.getAppArgs
  let reducedPrivate ← liftGen <| whnf expectedPrivate
  let privateArguments := reducedPrivate.getAppArgs
  let prefixSize := member.parameterArity + member.recursorMotiveArity +
    member.recursorMinorArity
  unless rawPublic.getAppFn.constName? == some recursor.adapter &&
      reducedPrivate.getAppFn.constName? == some member.implementationRecursor &&
      publicArguments.size > prefixSize && privateArguments.size > prefixSize do
    failConstruction (.recursorResultMismatch recursor.member)
  let publicPrefix := publicArguments.extract 0 prefixSize
  let privatePrefix := privateArguments.extract 0 prefixSize
  let publicTail := publicArguments.extract prefixSize publicArguments.size
  let privateTail := privateArguments.extract prefixSize privateArguments.size
  let publicMajor := publicTail.back!
  let privateMajor := privateTail.back!
  let publicIndices := publicTail.pop
  let privateIndices := privateTail.pop
  let publicMajorType ← liftGen <| inferType publicMajor
  let privateMajorType ← liftGen <| inferType privateMajor
  let parameters := publicPrefix.extract 0 member.parameterArity
  let boundary ← fixedCarrierBoundary plan memberCertificates parameters member
    publicMajorType privateMajorType
  unless ← liftGen <| isDefEq (mkApp boundary.forward publicMajor) privateMajor do
    failConstruction (.recursorResultMismatch recursor.member)
  let some privateRecursorInfo := (← getEnv).constants.find? member.implementationRecursor
    | failConstruction (.missingInstalledRecursor member.key member.implementationRecursor)
  let core ← withLocalDeclD `value boundary.implementationType fun value => do
    let call := mkAppN
      (.const member.implementationRecursor
        (privateRecursorInfo.levelParams.map Level.param))
      (privatePrefix ++ privateIndices ++ #[value])
    liftGen <| mkLambdaFVars #[value] call
  let carrier := publicMajorType.getAppFn.constName?
  let motives := recursor.motives.filter fun motive =>
    some motive.publicCarrier == carrier
  let some motiveCertificate := motives[0]?
    | failConstruction (.recursorResultMismatch recursor.member)
  unless motives.all (·.motiveIndex == motiveCertificate.motiveIndex) do
    failConstruction (.recursorResultMismatch recursor.member)
  let some publicMotive := publicPrefix[
      member.parameterArity + motiveCertificate.motiveIndex]?
    | failConstruction (.recursorResultMismatch recursor.member)
  let motive ← withLocalDeclD `value boundary.publicType fun value =>
    liftGen <| mkLambdaFVars #[value] (mkAppN publicMotive (publicIndices.push value))
  let agreement ← liftGen <| mkAppOptM ``packedRecursorForwardAgreement <|
    #[boundary.implementationType, boundary.publicType, motive,
      boundary.forward, boundary.backward, boundary.backwardForward, core].map some
  let proof := mkApp agreement publicMajor
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error _ => failConstruction (.missingMemberMap member.key)
  let resultType ← liftGen <| inferType expectedPrivate
  unless ← liftGen <| isDefEq (← inferType proof)
      (eqi.mk' (← ilevel resultType) resultType expectedPrivate expectedPublic) do
    failConstruction (.recursorResultMismatch recursor.member)
  return proof

/-- Lift one keyed recursive-result agreement through the exact paired
function telescope of its installed minor hypothesis.  The telescope itself,
not an occurrence depth or arity classifier, determines the finite fold. -/
private partial def recursorHypothesisAgreement (plan : FamilyAdapterPlan)
    (recursors : Array PublicRecursorCertificate) (rule : RuleKey)
    (containerRecursors : Array BuiltContainerRecursor)
    (role? : Option PublicIotaRecursiveCallRole)
    (publicBinderIndex implementationBinderIndex : Nat)
    (expectedPublic expectedPrivate : Expr) : ConstructionM Expr := do
  if ← liftGen <| isDefEq expectedPrivate expectedPublic then
    let type ← liftGen <| inferType expectedPrivate
    let eqi ← match EqInfo.check (← getEnv) with
      | .ok information => pure information
      | .error _ => failConstruction (.missingPublicIotaInput rule)
    return eqi.refl' (← liftGen <| ilevel type) type expectedPrivate
  let direct? : Option Expr ← match role? with
    | none => pure none
    | some role => do
      let (shape, recursor) ← recursiveCallCertificate plan recursors containerRecursors
        rule role publicBinderIndex implementationBinderIndex
      let reducedPrivate ← liftGen <| whnf expectedPrivate
      let publicMatches := expectedPublic.getAppFn.constName? == some recursor.adapter
      let privateMatches :=
        reducedPrivate.getAppFn.constName? == some role.implementationRecursor
      if publicMatches || privateMatches then
        unless publicMatches && privateMatches do
          failConstruction (.publicIotaRecursiveCallMismatch rule publicBinderIndex
            implementationBinderIndex .openedHeadMismatch)
        pure (some (← recursorAgreementAt shape recursor rule publicBinderIndex
          implementationBinderIndex expectedPublic expectedPrivate))
      else pure none
  if let some proof := direct? then return proof
  let publicType ← liftGen <| whnf (← inferType expectedPublic)
  let privateType ← liftGen <| whnf (← inferType expectedPrivate)
  match publicType, privateType with
  | .forallE publicName publicDomain _ publicInfo,
      .forallE _ privateDomain _ _ =>
    unless ← liftGen <| isDefEq publicDomain privateDomain do
      failConstruction (.publicIotaRecursiveCallMismatch rule publicBinderIndex
        implementationBinderIndex .dependentResult)
    withLocalDecl publicName publicInfo publicDomain fun argument => do
      let pointwise ← recursorHypothesisAgreement plan recursors rule containerRecursors
        role? publicBinderIndex implementationBinderIndex
        (mkApp expectedPublic argument).headBeta
        (mkApp expectedPrivate argument).headBeta
      let functionProof ← liftGen <| mkLambdaFVars #[argument] pointwise
      liftGen <| mkAppM ``funext #[functionProof]
  | .forallE .., _ | _, .forallE .. =>
    failConstruction (.publicIotaRecursiveCallMismatch rule publicBinderIndex
      implementationBinderIndex .dependentResult)
  | _, _ =>
    if role?.isSome then
      failConstruction (.publicIotaRecursiveCallMismatch rule publicBinderIndex
        implementationBinderIndex .openedHeadMismatch)
    failConstruction (.missingPublicIotaInput rule)

private partial def withReboundTelescope (fixedOriginal fixedReplacement binders : Array Expr)
    (position : Nat) (rebound : Array Expr)
    (k : Array Expr → ConstructionM α) : ConstructionM α := do
  if position == binders.size then return ← k rebound
  let binder := binders[position]!
  let declaration ← liftGen <| getFVarLocalDecl binder
  let type := declaration.type.replaceFVars
    (fixedOriginal ++ binders.extract 0 position) (fixedReplacement ++ rebound)
  withLocalDecl declaration.userName declaration.binderInfo type fun value =>
    withReboundTelescope fixedOriginal fixedReplacement binders (position + 1)
      (rebound.push value) k

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

private def minorHypothesisBinder? (member : MemberPlan) (recursorType : Expr)
    (constructorName : Name) (fieldCount : Nat) (occurrence : OccurrenceKey) :
    Option (Nat × Nat × Nat × Nat) := do
  let (recursorBinders, _) := openExactForalls
    ((`_family_adapter_exact_hypothesis_rec).append member.key.owner) recursorType
  let prefixSize := member.parameterArity + member.recursorMotiveArity +
    member.recursorMinorArity
  unless recursorBinders.size >= prefixSize do none
  let motives := recursorBinders.extract member.parameterArity
    (member.parameterArity + member.recursorMotiveArity) |>.map (·.value)
  let minors := recursorBinders.extract
    (member.parameterArity + member.recursorMotiveArity) prefixSize
  let matching := minors.mapIdx fun minorIndex minor =>
    let (binders, result) := openExactForalls
      ((`_family_adapter_exact_hypothesis_minor).append member.key.owner |>.mkNum minorIndex)
      minor.type
    (minorIndex, binders, result)
  let matching := matching.filter fun (_, _, result) =>
    (result.getAppArgs.back?.bind (·.getAppFn.constName?)) == some constructorName
  unless matching.size == 1 do none
  let (minorIndex, binders, result) := matching[0]!
  let major ← result.getAppArgs.back?
  let arguments := major.getAppArgs
  unless arguments.size >= fieldCount do none
  let fields := arguments.extract (arguments.size - fieldCount) arguments.size
  let field ← fields[occurrence.fieldIndex]?
  let mut hypotheses : Array (Nat × Nat × InstalledBinder) := #[]
  for binderIndex in [:binders.size] do
    let binder := binders[binderIndex]!
    if fields.contains binder.value then continue
    let body := eventualBody (`_family_adapter_exact_hypothesis) binder.type
    if let some motiveIndex := motives.findIdx? (· == body.getAppFn) then
      hypotheses := hypotheses.push (binderIndex, motiveIndex, binder)
  let candidates := hypotheses.filter fun (_, _, hypothesis) =>
    let body := eventualBody (`_family_adapter_exact_hypothesis_body) hypothesis.type
    (body.getAppArgs.back?.map (·.getAppFn == field)).getD false
  unless candidates.size == 1 do none
  let (binderIndex, motiveIndex, _) := candidates[0]!
  let actual := hypotheses.findIdx? (fun (index, _, _) => index == binderIndex)
    |>.getD hypotheses.size
  unless actual == occurrence.hypothesisIndex do none
  return (minorIndex, binderIndex, motiveIndex, actual)

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
    let some publicRecursorType := installedType? environment member.publicRecursor | do
      issues := issues.push (.missingInstalledRecursor member.key member.publicRecursor)
      continue
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
        let some (publicMinorIndex, publicBinderIndex, publicMotiveIndex,
            publicHypothesisPosition) :=
            minorHypothesisBinder? member publicRecursorType constructor.publicName fieldCount
              occurrence | do
          issues := issues.push (.missingInstalledHypothesis rule.key occurrence)
          continue
        unless publicMinorIndex == minorIndex do
          issues := issues.push (.installedHypothesisMismatch rule.key occurrence
            minorIndex publicMinorIndex)
          continue
        certificates := certificates.push
          { rule := rule.key, occurrence, minorIndex,
            hypothesisIndex := actual, publicBinderIndex, publicMotiveIndex,
            binderIndex, motiveIndex, publicHypothesisPosition,
            implementationHypothesisPosition := actual }
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

private partial def openExactLambdas (tag : Name) (expression : Expr) : Array Expr × Expr :=
  let rec loop (expression : Expr) (binders : Array Expr) :=
    match expression with
    | .lam _ _ body _ =>
      let value := mkFVar (FVarId.mk (tag.mkNum binders.size))
      loop (body.instantiate1 value) (binders.push value)
    | body => (binders, body)
  loop expression #[]

private def exactRhsArgument? (tag : Name) (rhs : Expr) (binderIndex : Nat) : Option Expr :=
  let (_, body) := openExactLambdas tag rhs
  body.getAppArgs[binderIndex]?

private def exactRecursiveCallHead (tag : Name) (value : Expr) : Expr :=
  (openExactLambdas tag value).2.getAppFn

private def publicIotaRecursiveCallRole (plan : FamilyAdapterPlan) (rule : RulePlan)
    (occurrences : Array OccurrenceKey)
    (publicBinderIndex implementationBinderIndex : Nat) :
    Except ConstructionIssue (Option PublicIotaRecursiveCallRole) := do
  let some publicValue := exactRhsArgument?
      ((`_family_adapter_public_iota_rhs).append rule.key.recursor)
      rule.publicRhs publicBinderIndex
    | throw (.publicIotaRecursiveCallMismatch rule.key publicBinderIndex
        implementationBinderIndex .roleResolution)
  let some implementationValue := exactRhsArgument?
      ((`_family_adapter_implementation_iota_rhs).append rule.key.recursor)
      rule.implementationRhs implementationBinderIndex
    | throw (.publicIotaRecursiveCallMismatch rule.key publicBinderIndex
        implementationBinderIndex .roleResolution)
  let publicHead := exactRecursiveCallHead `_family_adapter_public_iota_call publicValue
  let implementationHead := exactRecursiveCallHead
    `_family_adapter_implementation_iota_call implementationValue
  match publicHead.constName?, implementationHead.constName? with
  | some publicRecursor, some implementationRecursor =>
    let memberCandidates := plan.members.filter fun member =>
      member.publicRecursor == publicRecursor &&
        member.implementationRecursor == implementationRecursor
    let containerCandidates := plan.containerRecursors.filter fun container =>
      container.key.publicRecursor == publicRecursor &&
        container.key.implementationRecursor == implementationRecursor &&
        occurrences.all container.occurrences.contains
    unless memberCandidates.size + containerCandidates.size == 1 do
      throw (.publicIotaRecursiveCallMismatch rule.key publicBinderIndex
        implementationBinderIndex .roleResolution)
    return some
      { publicRecursor, implementationRecursor,
        member? := memberCandidates[0]?.map (·.key),
        container? := containerCandidates[0]?.map (·.key),
        containerOccurrences := if containerCandidates.isEmpty then #[] else occurrences }
  | none, none =>
    unless publicHead.isFVar && implementationHead.isFVar do
      throw (.publicIotaRecursiveCallMismatch rule.key publicBinderIndex
        implementationBinderIndex .roleResolution)
    return none
  | _, _ =>
    throw (.publicIotaRecursiveCallMismatch rule.key publicBinderIndex
      implementationBinderIndex .roleResolution)

private def installedIotaBinderRoles (owner : MemberPlan) (rule : RulePlan) :
    Except ConstructionIssue (Array InstalledIotaBinderRole) := do
  let (binders, _) := openExactForalls
    ((`_family_adapter_installed_iota).append rule.key.recursor)
    rule.implementationIotaType
  let prefixSize := owner.parameterArity + owner.recursorMotiveArity +
    owner.recursorMinorArity
  unless binders.size == prefixSize + owner.indexArity + 1 do
    throw (.installedIotaTypeMismatch rule.key rule.implementationIota)
  let mut roles := (Array.range prefixSize).map
    InstalledIotaBinderRole.recursorPrefix
  roles := roles ++ (Array.range owner.indexArity).map
    InstalledIotaBinderRole.resultIndex
  return roles.push .major

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
    let implementationIotaInputs ← installedIotaBinderRoles owner rule
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
          current.minorIndex == first.minorIndex &&
            current.publicBinderIndex == first.publicBinderIndex &&
            current.publicMotiveIndex == first.publicMotiveIndex &&
            current.motiveIndex == first.motiveIndex &&
            current.publicHypothesisPosition == first.publicHypothesisPosition &&
            current.implementationHypothesisPosition ==
              first.implementationHypothesisPosition do
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
      let recursiveCall? ← publicIotaRecursiveCallRole plan rule (grouped.map (·.occurrence))
        first.publicBinderIndex binderIndex
      hypotheses := hypotheses.push
        { rule := rule.key, minorIndex := first.minorIndex,
          publicBinderIndex := first.publicBinderIndex,
          publicMotiveIndex := first.publicMotiveIndex, binderIndex,
          motiveIndex := first.motiveIndex,
          publicHypothesisPosition := first.publicHypothesisPosition,
          implementationHypothesisPosition := first.implementationHypothesisPosition,
          recursiveCall?,
          occurrences := grouped.map (·.occurrence), maps := firstOccurrence.maps }
    unless (hypotheses.flatMap (·.occurrences)).size == rule.occurrences.size &&
        keyed.all fun current => hypotheses.any fun step =>
          step.binderIndex == current.binderIndex && step.occurrences.contains current.occurrence do
      throw (.missingPublicIotaInput rule.key)
    schemas := schemas.push
      { key := rule.key, owner := owner.key, constructor := rule.key.constructor,
        ownerMaps := memberCertificate.maps, telescope,
        implementationIota := compatibility.implementationIota,
        implementationIotaInputs,
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

private def recursorMotiveCertificates (shape : RecursorShape)
    (publicType privateType : Expr) : Except ConstructionIssue
    (Array PublicRecursorMotiveCertificate) := do
  let (publicBinders, _) := openExactForalls `_family_adapter_public_motives publicType
  let (privateBinders, _) := openExactForalls `_family_adapter_private_motives privateType
  let stop := shape.parameterArity + shape.motiveArity
  unless publicBinders.size >= stop && privateBinders.size >= stop do
    throw (.shortInstalledRecursorPrefix shape.key shape.publicRecursor)
  let mut result := #[]
  for motiveIndex in [:shape.motiveArity] do
    let binderIndex := shape.parameterArity + motiveIndex
    let some publicCarrier := motiveCarrierName? publicBinders[binderIndex]!.type
      | throw (.recursorResultMismatch shape.key)
    let some implementationCarrier := motiveCarrierName? privateBinders[binderIndex]!.type
      | throw (.recursorResultMismatch shape.key)
    result := result.push
      { recursor := shape.key, motiveIndex, publicCarrier, implementationCarrier }
  return result

private def uniqueOccurrenceHypothesisIndices (constructor : ConstructorPlan) : Array Nat :=
  Id.run do
    let mut result := #[]
    for binder in constructor.telescope.binders do
      for occurrence in binder.occurrences do
        unless result.contains occurrence.hypothesisIndex do
          result := result.push occurrence.hypothesisIndex
    return result

private def minorConstructorSequence (shape : RecursorShape) (isPublic : Bool)
    (recursorType : Expr) : Except ConstructionIssue (Array Name) := do
  let (binders, _) := openExactForalls `_family_adapter_public_recursor_prefix recursorType
  let start := shape.parameterArity + shape.motiveArity
  let stop := start + shape.minorArity
  unless binders.size >= stop do
    throw (.shortInstalledRecursorPrefix shape.key
      (if isPublic then shape.publicRecursor else shape.implementationRecursor))
  let mut result := #[]
  for minorIndex in [:shape.minorArity] do
    let some constructor := minorConstructorName? binders[start + minorIndex]!.type
      | throw (.malformedRecursorMinor shape.key minorIndex)
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

private def identityLiveMotiveBoundary (key : MemberKey) (publicType privateType : Expr) :
    ConstructionM PackedCarrierBoundary := do
  unless ← liftGen <| isDefEq publicType privateType do
    failConstruction (.missingRecursorMotiveBoundary key)
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error _ => failConstruction (.missingRecursorMotiveBoundary key)
  let forward ← withLocalDeclD `value publicType fun value =>
    liftGen <| mkLambdaFVars #[value] value
  let backward ← withLocalDeclD `value privateType fun value =>
    liftGen <| mkLambdaFVars #[value] value
  let backwardForward ← withLocalDeclD `value publicType fun value => do
    let proof := eqi.refl' (← liftGen <| ilevel publicType) publicType value
    liftGen <| mkLambdaFVars #[value] proof
  let forwardBackward ← withLocalDeclD `value privateType fun value => do
    let proof := eqi.refl' (← liftGen <| ilevel privateType) privateType value
    liftGen <| mkLambdaFVars #[value] proof
  for expression in #[forward, backward, backwardForward, forwardBackward] do
    liftGen <| check expression
  return PackedCarrierBoundary.mk publicType privateType forward backward
    backwardForward forwardBackward

private def exactMotiveBoundary (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate) (parameters : Array Expr)
    (indices : Array Expr) (fallback : RecursorCarrierBoundary)
    (publicType privateType : Expr) : ConstructionM PackedCarrierBoundary := do
  let mut boundaries := #[fallback]
  for member in plan.members do
    if memberCertificates.any (·.key == member.key) then
      let boundary ← memberRecursorBoundary plan memberCertificates member
      unless boundaries.contains boundary do boundaries := boundaries.push boundary
  for container in plan.containerRecursors do
    let boundary := containerRecursorBoundary container
    unless boundaries.contains boundary do boundaries := boundaries.push boundary
  let mut candidates : Array PackedCarrierBoundary := #[]
  let publicFamily ← liftGen <| mkLambdaFVars (parameters ++ indices) publicType
  let privateFamily ← liftGen <| mkLambdaFVars (parameters ++ indices) privateType
  if !publicFamily.hasFVar && !privateFamily.hasFVar &&
      (← liftGen <| isDefEq publicFamily privateFamily) &&
      (← liftGen <| isDefEq publicType privateType) then
    candidates := candidates.push
      (← identityLiveMotiveBoundary fallback.key publicType privateType)
  for boundary in boundaries do
    let attempt ← liftGen <|
      (recursorCarrierAt plan boundary parameters publicType privateType).run
    if let .ok instantiated := attempt then
      candidates := candidates.push instantiated
  let some first := candidates[0]?
    | failConstruction (.missingRecursorMotiveBoundary fallback.key)
  for candidate in candidates do
    for (left, right) in #[(candidate.forward, first.forward),
        (candidate.backward, first.backward),
        (candidate.backwardForward, first.backwardForward),
        (candidate.forwardBackward, first.forwardBackward)] do
      unless ← liftGen <| isDefEq left right do
        failConstruction (.missingRecursorMotiveBoundary fallback.key)
  return first

private def privateMotiveValue (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate) (fallback : RecursorCarrierBoundary)
    (parameters : Array Expr) (shape : RecursorShape) (publicMotive expectedType : Expr) :
    ConstructionM Expr := do
  forallBoundedTelescope expectedType (some (numForalls expectedType)) fun binders _ => do
    let some privateValue := binders.back?
      | failConstruction (.missingRecursorMotiveBoundary shape.key)
    let indices := binders.extract 0 (binders.size - 1)
    let publicMotiveType ← inferType publicMotive
    let publicAfterIndices ← instantiateForall publicMotiveType indices
    let .forallE _ publicType _ _ := publicAfterIndices
      | failConstruction (.missingRecursorMotiveBoundary shape.key)
    let privateType ← inferType privateValue
    let carrier ← exactMotiveBoundary plan memberCertificates parameters indices fallback
      publicType privateType
    let publicValue := mkApp carrier.backward privateValue
    mkLambdaFVars binders (mkAppN publicMotive (indices.push publicValue))

/-- Test/prototype validator for the exact motive boundaries consumed by a
fresh recursor. It replays the same live-fibre selector as construction and
does not assign mimic motives to source members by name or array position. -/
def validatePublicRecursorMotiveBoundaries (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate) (member : MemberPlan)
    (recursor : PublicRecursorCertificate) : GenM (Except ConstructionIssue Nat) := do
  let action : ConstructionM Nat := do
    let privateType ← liftGen <| generatedType member.implementationRecursor
    let fallback ← memberRecursorBoundary plan memberCertificates member
    let shape := memberRecursorShape member
    let stop := member.parameterArity + member.recursorMotiveArity
    forallBoundedTelescope recursor.exactType (some stop) fun publicPrefix _ => do
      let parameters := publicPrefix.extract 0 member.parameterArity
      let publicMotives := publicPrefix.extract member.parameterArity stop
      let mut privateTail ← liftGen <| instantiateForall privateType parameters
      for motiveIndex in [:member.recursorMotiveArity] do
        let .forallE _ expected rest _ := privateTail
          | failConstruction (.shortInstalledRecursorPrefix member.key
              member.implementationRecursor)
        let motive ← privateMotiveValue plan memberCertificates fallback parameters shape
          publicMotives[motiveIndex]! expected
        privateTail := rest.instantiate1 motive
      return member.recursorMotiveArity
  action.run

private def privateMinorValue (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate)
    (telescopeCertificates : Array TelescopeCertificate)
    (constructorCertificates : Array PublicConstructorCertificate)
    (parameters publicMotives privateMotives : Array Expr)
    (shape : RecursorShape) (minorIndex : Nat) (constructor : ConstructorPlan)
    (publicMinor expectedType : Expr) : ConstructionM Expr := do
  forallBoundedTelescope expectedType (some (numForalls expectedType))
      fun privateBinders privateResult => do
    let some privateFields := minorFieldValues? constructor privateBinders privateResult
      | failConstruction (.malformedRecursorMinor shape.key minorIndex)
    let publicMinorType ← inferType publicMinor
    forallBoundedTelescope publicMinorType (some (numForalls publicMinorType))
        fun publicBinders publicResult => do
      let some constructorAdapter := constructorCertificates.find?
          (·.key == constructor.key)
        | failConstruction (.malformedRecursorMinor shape.key minorIndex)
      let some publicFields := minorFieldValues? constructor publicBinders publicResult
          (some constructorAdapter.adapter)
        | failConstruction (.malformedRecursorMinor shape.key minorIndex)
      let publicValues ← mapFields plan memberCertificates constructor parameters false
        privateFields publicFields privateFields
      let publicHypotheses ← liftGen <|
        motiveHypothesisValues publicMotives publicFields publicBinders
      let privateHypotheses ← liftGen <|
        motiveHypothesisValues privateMotives privateFields privateBinders
      let expectedHypothesisIndices := uniqueOccurrenceHypothesisIndices constructor
      unless expectedHypothesisIndices == Array.range publicHypotheses.size &&
          privateHypotheses.size == publicHypotheses.size do
        failConstruction (.malformedRecursorMinor shape.key minorIndex)
      let mut arguments := #[]
      for binderIndex in [:publicBinders.size] do
        let binder := publicBinders[binderIndex]!
        let value? := if let some fieldIndex := publicFields.findIdx? (· == binder) then
            publicValues[fieldIndex]?
          else if let some hypothesisIndex := publicHypotheses.findIdx? (· == binder) then
            privateHypotheses[hypothesisIndex]?
          else none
        let some value := value?
          | failConstruction (.malformedRecursorMinor shape.key minorIndex)
        let expected := (← inferType binder).replaceFVars
          (publicBinders.extract 0 binderIndex) arguments
        unless ← isDefEq (← inferType value) expected do
          failConstruction (.dependentRecursorMinorTransport shape.key minorIndex binderIndex)
        arguments := arguments.push value
      let base := mkAppN publicMinor arguments
      let some telescope := telescopeCertificates.find? (·.constructor == constructor.key)
        | failConstruction (.malformedRecursorMinor shape.key minorIndex)
      unless telescope == constructorAdapter.telescope do
        failConstruction (.malformedRecursorMinor shape.key minorIndex)
      let privatePackageType ← liftGen <| packedTelescopeType privateFields
      let privatePackage ← liftGen <| packTelescopeValue privateFields privateFields
      let some owner := plan.members.find? (·.key == constructor.key.owner)
        | failConstruction (.malformedRecursorMinor shape.key minorIndex)
      let some ownerIndex := plan.members.findIdx? (·.key == owner.key)
        | failConstruction (.malformedRecursorMinor shape.key minorIndex)
      let ownerMotive := publicMotives[ownerIndex]!
      let ownerBoundary ← packedCarrierBoundary plan memberCertificates parameters owner
      let constructorBoundary ← packedConstructorBoundary plan parameters owner ownerBoundary
        constructor constructorAdapter
      let motive ← withLocalDeclD `total ownerBoundary.publicType fun total => do
        let (indices, major) ← unpackCarrierTotal plan parameters owner true total
        liftGen <| mkLambdaFVars #[total] (mkAppN ownerMotive (indices.push major))
      let constructorProof := mkApp constructorBoundary.constructorAgreement privatePackage
      let congruence ← liftGen <| mkAppM ``congrArg #[motive, constructorProof]
      let transported ← liftGen <| mkAppM ``Eq.mp #[congruence, base]
      unless ← isDefEq (← inferType transported) privateResult do
        failConstruction (.dependentRecursorMinorTransport shape.key minorIndex
          privateBinders.size)
      mkLambdaFVars privateBinders transported

/-- A nested recursor can bind minors for specialised mimic constructors that
are not source constructors.  Build their source-specialised constructor
boundary from the two exact minor telescopes: fields are the literal binders
used by the constructor application, and every changed field crosses only an
already checked family/container equivalence. -/
private def mapSpecialisedMajorToPublic (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate) (parameters : Array Expr)
    (fallback : RecursorCarrierBoundary) (publicFields : Array Expr)
    (publicMajor : Expr) (privateFields privateValues : Array Expr)
    (privateMajor : Expr) : ConstructionM (Expr × Expr) := do
  let mut publicValues := #[]
  for fieldIndex in [:privateValues.size] do
    let privateValue := privateValues[fieldIndex]!
    let privateType ← liftGen <| inferType privateValue
    let publicType := (← liftGen <| inferType publicFields[fieldIndex]!).replaceFVars
      (publicFields.extract 0 fieldIndex) publicValues
    let candidate ← exactCarrierCandidate plan memberCertificates parameters fallback false
      privateType publicType privateValue
    publicValues := publicValues.push candidate.mapped
  let targetMajor := publicMajor.replaceFVars publicFields publicValues
  let publicMajorType ← liftGen <| inferType targetMajor
  let privateMajorType ← liftGen <| inferType privateMajor
  let candidate ← exactCarrierCandidate plan memberCertificates parameters fallback false
    privateMajorType publicMajorType privateMajor
  return (candidate.mapped, publicMajorType)

private def specialisedMinorConstructorDeclaration (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate) (parameters : Array Expr)
    (root : Name) (shape : RecursorShape) (boundary : RecursorCarrierBoundary)
    (minorIndex : Nat)
    (publicMinorType privateMinorType : Expr) : ConstructionM
    (Declaration × PublicMinorConstructorCertificate) := do
  forallBoundedTelescope publicMinorType (some (numForalls publicMinorType))
      fun publicBinders publicResult => do
    let some publicMajor := publicResult.getAppArgs.back?
      | failConstruction (.malformedRecursorMinor shape.key minorIndex)
    let some publicConstructor := publicMajor.getAppFn.constName?
      | failConstruction (.malformedRecursorMinor shape.key minorIndex)
    let publicFields := publicMajor.getAppArgs.filter publicBinders.contains
    forallBoundedTelescope privateMinorType (some (numForalls privateMinorType))
        fun privateBinders privateResult => do
      let some privateMajor := privateResult.getAppArgs.back?
        | failConstruction (.malformedRecursorMinor shape.key minorIndex)
      let some implementationConstructor := privateMajor.getAppFn.constName?
        | failConstruction (.malformedRecursorMinor shape.key minorIndex)
      let privateFields := privateMajor.getAppArgs.filter privateBinders.contains
      unless publicFields.size == privateFields.size do
        failConstruction (.malformedRecursorMinor shape.key minorIndex)
      let name := publicMinorConstructorAdapterName root shape.key minorIndex
      liftGen <| ensurePrototypeFresh name
      let publicMajorType ← liftGen <| inferType publicMajor
      let exactType ← liftGen <| mkForallFVars (parameters ++ publicFields) publicMajorType
      let mut privateValues := #[]
      for fieldIndex in [:publicFields.size] do
        let publicValue := publicFields[fieldIndex]!
        let publicType ← liftGen <| inferType publicValue
        let privateType := (← liftGen <| inferType privateFields[fieldIndex]!).replaceFVars
          (privateFields.extract 0 fieldIndex) privateValues
        let candidate ← exactCarrierCandidate plan memberCertificates parameters boundary true
          publicType privateType publicValue
        privateValues := privateValues.push candidate.mapped
      let privateMajor := privateMajor.replaceFVars privateFields privateValues
      let (publicValue, _) ← mapSpecialisedMajorToPublic plan memberCertificates parameters
        boundary publicFields publicMajor privateFields privateValues privateMajor
      let value ← liftGen <| mkLambdaFVars (parameters ++ publicFields) publicValue
      let declaration := Declaration.defnDecl
        { name, levelParams := plan.levelParams, type := exactType, value,
          hints := .abbrev, safety := .safe }
      liftGen <| addChecked declaration
      return (declaration,
        { recursor := shape.key, minorIndex, publicConstructor, implementationConstructor,
          adapter := name, exactType, fieldArity := publicFields.size })

private def rewriteSpecialisedMinorType (plan : FamilyAdapterPlan)
    (shape : RecursorShape) (parameters : Array Expr)
    (certificate : PublicMinorConstructorCertificate) (minorType : Expr) : ConstructionM Expr := do
  forallBoundedTelescope minorType (some (numForalls minorType)) fun binders result => do
    let some major := result.getAppArgs.back?
      | failConstruction (.malformedRecursorMinor shape.key certificate.minorIndex)
    unless major.getAppFn.constName? == some certificate.publicConstructor do
      failConstruction (.malformedRecursorMinor shape.key certificate.minorIndex)
    let fields := major.getAppArgs.filter binders.contains
    unless fields.size == certificate.fieldArity do
      failConstruction (.malformedRecursorMinor shape.key certificate.minorIndex)
    let replacement := mkAppN
      (.const certificate.adapter (plan.levelParams.map Level.param)) (parameters ++ fields)
    unless ← isDefEq (← inferType replacement) (← inferType major) do
      failConstruction (.malformedRecursorMinor shape.key certificate.minorIndex)
    let arguments := result.getAppArgs
    let rewrittenResult := mkAppN result.getAppFn
      (arguments.extract 0 (arguments.size - 1) |>.push replacement)
    mkForallFVars binders rewrittenResult

/-- Rewrite each specialised constructor only in its exact recursor-minor binder.
The recursor parameters are opened once and threaded directly; no constructor
name search or carrier-occurrence search chooses between minor positions. -/
private def rewriteMinorConstructors (plan : FamilyAdapterPlan) (shape : RecursorShape)
    (minorConstructors : Array PublicMinorConstructorCertificate)
    (expression : Expr) : ConstructionM Expr := do
  let prefixSize := shape.parameterArity + shape.motiveArity + shape.minorArity
  forallBoundedTelescope expression (some prefixSize) fun recursorPrefix tail => do
    let minorStart := shape.parameterArity + shape.motiveArity
    let outer := recursorPrefix.extract 0 minorStart
    let parameters := recursorPrefix.extract 0 shape.parameterArity
    let originalMinors := recursorPrefix.extract minorStart prefixSize
    let rec rebuild (minorIndex : Nat) (rewrittenMinors : Array Expr) : ConstructionM Expr := do
      if h : minorIndex < originalMinors.size then
        let originalMinor := originalMinors[minorIndex]
        let originalType ← inferType originalMinor
        let currentType := originalType.replaceFVars
          (originalMinors.extract 0 minorIndex) rewrittenMinors
        let rewrittenType ← match minorConstructors.find? (·.minorIndex == minorIndex) with
          | some certificate =>
            rewriteSpecialisedMinorType plan shape parameters certificate currentType
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
    (root : Name) (shape : RecursorShape) (boundary : RecursorCarrierBoundary)
    (publicType privateType : Expr) : ConstructionM
    (Array Declaration × Array PublicMinorConstructorCertificate) := do
  let prefixSize := shape.parameterArity + shape.motiveArity + shape.minorArity
  forallBoundedTelescope publicType (some prefixSize) fun publicPrefix _ => do
    let parameters := publicPrefix.extract 0 shape.parameterArity
    let publicMotives := publicPrefix.extract shape.parameterArity
      (shape.parameterArity + shape.motiveArity)
    let publicMinors := publicPrefix.extract
      (shape.parameterArity + shape.motiveArity) prefixSize
    let mut privateTail ← instantiateForall privateType parameters
    for motiveIndex in [:shape.motiveArity] do
      let .forallE _ expected rest _ := privateTail
        | failConstruction (.shortInstalledRecursorPrefix shape.key shape.implementationRecursor)
      let motive ← privateMotiveValue plan memberCertificates boundary parameters shape
        publicMotives[motiveIndex]! expected
      privateTail := rest.instantiate1 motive
    let (privateBinders, _) := openExactForalls `_family_adapter_private_minor_types privateTail
    unless privateBinders.size >= shape.minorArity do
      failConstruction (.shortInstalledRecursorPrefix shape.key shape.implementationRecursor)
    let mut declarations := #[]
    let mut certificates := #[]
    for minorIndex in [:shape.minorArity] do
      let publicMinorType ← liftGen <| inferType publicMinors[minorIndex]!
      let privateMinorType := privateBinders[minorIndex]!.type
      let some publicName := minorConstructorName? publicMinorType
        | failConstruction (.malformedRecursorMinor shape.key minorIndex)
      let some privateName := minorConstructorName? privateMinorType
        | failConstruction (.malformedRecursorMinor shape.key minorIndex)
      if let some constructor := plan.constructors.find? fun constructor =>
          constructor.publicName == publicName && constructor.implementationName == privateName then
        let some adapter := constructorCertificates.find? (·.key == constructor.key)
          | failConstruction (.malformedRecursorMinor shape.key minorIndex)
        certificates := certificates.push
          { recursor := shape.key, minorIndex, publicConstructor := publicName,
            implementationConstructor := privateName, adapter := adapter.adapter,
            exactType := adapter.exactType,
            fieldArity := constructor.telescope.binders.size }
      else
        let (declaration, certificate) ← specialisedMinorConstructorDeclaration plan
          memberCertificates parameters root shape boundary minorIndex publicMinorType
          privateMinorType
        declarations := declarations.push declaration
        certificates := certificates.push certificate
    return (declarations, certificates)

private def privateSpecialisedMinorValue (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate)
    (parameters publicMotives privateMotives : Array Expr)
    (shape : RecursorShape) (boundary : RecursorCarrierBoundary)
    (minor : PublicMinorConstructorCertificate)
    (publicMinor expectedType : Expr) : ConstructionM Expr := do
  forallBoundedTelescope expectedType (some (numForalls expectedType))
      fun privateBinders privateResult => do
    let privateValues := privateBinders
    let some privateMajor := privateResult.getAppArgs.back?
      | failConstruction (.malformedRecursorMinor shape.key minor.minorIndex)
    let privateFields := privateMajor.getAppArgs.filter privateValues.contains
    let publicMinorType ← liftGen <| inferType publicMinor
    forallBoundedTelescope publicMinorType (some (numForalls publicMinorType))
        fun publicBinders publicResult => do
      let some publicMajor := publicResult.getAppArgs.back?
        | failConstruction (.malformedRecursorMinor shape.key minor.minorIndex)
      let publicFields := publicMajor.getAppArgs.filter publicBinders.contains
      unless publicFields.size == privateFields.size do
        failConstruction (.malformedRecursorMinor shape.key minor.minorIndex)
      let mut mappedPublic := #[]
      for fieldIndex in [:privateFields.size] do
        let privateValue := privateFields[fieldIndex]!
        let privateType ← liftGen <| inferType privateValue
        let publicType := (← liftGen <| inferType publicFields[fieldIndex]!).replaceFVars
          (publicFields.extract 0 fieldIndex) mappedPublic
        let candidate ← exactCarrierCandidate plan memberCertificates parameters boundary false
          privateType publicType privateValue
        mappedPublic := mappedPublic.push candidate.mapped
      let publicHypotheses ← liftGen <|
        motiveHypothesisValues publicMotives publicFields publicBinders
      let privateHypotheses ← liftGen <|
        motiveHypothesisValues privateMotives privateFields privateBinders
      unless publicHypotheses.size == privateHypotheses.size do
        failConstruction (.malformedRecursorMinor shape.key minor.minorIndex)
      let mut arguments := #[]
      for binderIndex in [:publicBinders.size] do
        let binder := publicBinders[binderIndex]!
        let value? := if let some fieldIndex := publicFields.findIdx? (· == binder) then
            mappedPublic[fieldIndex]?
          else if let some hypothesisIndex := publicHypotheses.findIdx? (· == binder) then
            privateHypotheses[hypothesisIndex]?
          else none
        let some value := value?
          | failConstruction (.malformedRecursorMinor shape.key minor.minorIndex)
        let expected := (← liftGen <| inferType binder).replaceFVars
          (publicBinders.extract 0 binderIndex) arguments
        unless ← liftGen <| isDefEq (← inferType value) expected do
          failConstruction (.dependentRecursorMinorTransport shape.key minor.minorIndex binderIndex)
        arguments := arguments.push value
      let base := mkAppN publicMinor arguments
      let mut remappedPrivate := #[]
      let mut proofs := #[]
      for fieldIndex in [:privateFields.size] do
        let publicValue := mappedPublic[fieldIndex]!
        let publicType ← liftGen <| inferType publicValue
        let privateType := (← liftGen <| inferType privateFields[fieldIndex]!).replaceFVars
          (privateFields.extract 0 fieldIndex) remappedPrivate
        let candidate ← exactCarrierCandidate plan memberCertificates parameters boundary true
          publicType privateType publicValue
        remappedPrivate := remappedPrivate.push candidate.mapped
        let originalType ← liftGen <| inferType privateFields[fieldIndex]!
        let candidate ← exactCarrierCandidate plan memberCertificates parameters boundary false
          originalType publicType privateFields[fieldIndex]!
        unless ← liftGen <| isDefEq candidate.lawLeft remappedPrivate[fieldIndex]! do
          failConstruction (.dependentRecursorMinorTransport shape.key minor.minorIndex fieldIndex)
        proofs := proofs.push candidate.roundTrip
      let privatePackageType ← liftGen <| packedTelescopeType privateFields
      let privatePackage ← liftGen <| packTelescopeValue privateFields privateFields
      let remappedPackage ← liftGen <| packTelescopeValue privateFields remappedPrivate
      let eqi ← match EqInfo.check (← getEnv) with
        | .ok information => pure information
        | .error _ => failConstruction (.malformedRecursorMinor shape.key minor.minorIndex)
      let packageProof ← liftGen <| packageCongruence eqi privateFields privatePackageType
        remappedPrivate privateFields proofs
      let some motiveIndex := privateMotives.findIdx? fun motive =>
          privateResult.getAppFn == motive
        | failConstruction (.malformedRecursorMinor shape.key minor.minorIndex)
      let ownerMotive := publicMotives[motiveIndex]!
      let baseType ← liftGen <| inferType base
      let resultLevel ← liftGen <| ilevel baseType
      let packageLevel ← liftGen <| ilevel privatePackageType
      let transported ← liftGen <| transportAlong eqi resultLevel packageLevel
        privatePackageType remappedPackage privatePackage packageProof base fun package => do
          let values ← unpackTelescopeValue privateFields package
          let major := privateMajor.replaceFVars privateFields values
          let mapped ← (mapSpecialisedMajorToPublic plan memberCertificates parameters
            boundary publicFields publicMajor privateFields values major).run
          let (publicMajor, publicMajorType) ← match mapped with
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
        failConstruction (.dependentRecursorMinorTransport shape.key minor.minorIndex
          privateBinders.size)
      mkLambdaFVars privateBinders transported

private def publicRecursorDeclaration (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate)
    (telescopeCertificates : Array TelescopeCertificate)
    (constructorCertificates : Array PublicConstructorCertificate)
    (root : Name) (shape : RecursorShape) (boundary : RecursorCarrierBoundary)
    (resultMotiveIndex? : Option Nat := none) : ConstructionM
    (Array Declaration × PublicRecursorCertificate) := do
  let name := publicRecursorAdapterName root shape.key
  liftGen <| ensurePrototypeFresh name
  let some publicRecursorInfo := (← getEnv).constants.find? shape.publicRecursor
    | failConstruction (.missingInstalledRecursor shape.key shape.publicRecursor)
  let some privateRecursorInfo := (← getEnv).constants.find? shape.implementationRecursor
    | failConstruction (.missingInstalledRecursor shape.key shape.implementationRecursor)
  let constructorMapping := constructorCertificates.map fun certificate =>
    let constructor := (plan.constructors.find? (·.key == certificate.key)).get!
    (constructor.publicName, certificate.adapter)
  let publicSourceType := publicRecursorInfo.type
  let privateType := privateRecursorInfo.type
  let (minorDeclarations, minorCertificates) ← buildMinorConstructorAdapters plan
    memberCertificates constructorCertificates root shape boundary publicSourceType privateType
  let sourceMappedType := mapConstsE
    (fun name => constructorMapping.find? (·.1 == name) |>.map (·.2)) publicSourceType
  let specialisedMinors := minorCertificates.filter fun certificate =>
    !plan.constructors.any fun constructor =>
      constructor.publicName == certificate.publicConstructor &&
        constructor.implementationName == certificate.implementationConstructor
  let publicType ← rewriteMinorConstructors plan shape specialisedMinors sourceMappedType
  let motiveCertificates ← match recursorMotiveCertificates shape publicSourceType privateType with
    | .ok certificates => pure certificates
    | .error issue => failConstruction issue
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error _ => failConstruction (.recursorResultMismatch shape.key)
  let prefixSize := shape.parameterArity + shape.motiveArity + shape.minorArity
  let resultMotiveIndex := resultMotiveIndex?.getD
    ((plan.members.findIdx? (·.key == shape.key)).getD plan.members.size)
  unless resultMotiveIndex < shape.motiveArity do
    failConstruction (.recursorResultMismatch shape.key)
  let publicMinorNames ← match minorConstructorSequence shape true publicSourceType with
    | .ok keys => pure keys
    | .error issue => failConstruction issue
  let privateMinorNames ← match minorConstructorSequence shape false privateType with
    | .ok keys => pure keys
    | .error issue => failConstruction issue
  unless minorCertificates.size == shape.minorArity &&
      (Array.range shape.minorArity).all fun minorIndex =>
        (minorCertificates[minorIndex]?).any fun certificate =>
          certificate.minorIndex == minorIndex &&
            publicMinorNames[minorIndex]? == some certificate.publicConstructor &&
            privateMinorNames[minorIndex]? == some certificate.implementationConstructor do
    failConstruction (.malformedRecursorMinor shape.key minorCertificates.size)
  let agreementName := publicRecursorCallAgreementName root shape.key
  liftGen <| ensurePrototypeFresh agreementName
  let ((value, agreementValue), agreementType) ←
      forallBoundedTelescope publicType (some prefixSize)
      fun publicPrefix publicTailType => do
    let parameters := publicPrefix.extract 0 shape.parameterArity
    let publicMotives := publicPrefix.extract shape.parameterArity
      (shape.parameterArity + shape.motiveArity)
    let publicMinors := publicPrefix.extract
      (shape.parameterArity + shape.motiveArity) prefixSize
    unless publicMotives.size == motiveCertificates.size &&
        publicMinors.size == minorCertificates.size do
      failConstruction (.shortInstalledRecursorPrefix shape.key shape.publicRecursor)
    let mut privateTail ← instantiateForall privateType parameters
    let mut privateMotives := #[]
    for motiveIndex in [:motiveCertificates.size] do
      let .forallE _ expected rest _ := privateTail
        | do
          failConstruction (.shortInstalledRecursorPrefix shape.key shape.implementationRecursor)
      let motive ← privateMotiveValue plan memberCertificates boundary parameters shape
        publicMotives[motiveIndex]! expected
      privateMotives := privateMotives.push motive
      privateTail := rest.instantiate1 motive
    let mut privateMinors := #[]
    for minorIndex in [:minorCertificates.size] do
      let .forallE _ expected rest _ := privateTail
        | do
          failConstruction (.shortInstalledRecursorPrefix shape.key shape.implementationRecursor)
      let certificate := minorCertificates[minorIndex]!
      let minor ← if let some constructor := plan.constructors.find? fun constructor =>
          constructor.publicName == certificate.publicConstructor &&
            constructor.implementationName == certificate.implementationConstructor then
        privateMinorValue plan memberCertificates telescopeCertificates
          constructorCertificates parameters publicMotives privateMotives shape minorIndex
          constructor publicMinors[minorIndex]! expected
      else
        privateSpecialisedMinorValue plan memberCertificates parameters publicMotives
          privateMotives shape boundary certificate publicMinors[minorIndex]! expected
      privateMinors := privateMinors.push minor
      privateTail := rest.instantiate1 minor
    let privatePrefix := parameters ++ privateMotives ++ privateMinors
    let valueTail ← forallBoundedTelescope publicTailType (some (numForalls publicTailType))
        fun publicTail publicResult => do
      let some publicMajor := publicTail.back?
        | failConstruction (.shortInstalledRecursorPrefix shape.key shape.publicRecursor)
      let indices := publicTail.extract 0 (publicTail.size - 1)
      let privateMajorTail ← instantiateForall privateTail indices
      let .forallE _ privateMajorType _ _ := privateMajorTail
        | do
          failConstruction (.shortInstalledRecursorPrefix shape.key shape.implementationRecursor)
      let publicMajorType ← inferType publicMajor
      let carrier ← recursorCarrierAt plan boundary parameters
        publicMajorType privateMajorType
      let privateMajor := mkApp carrier.forward publicMajor
      let privateCall := mkAppN
        (.const shape.implementationRecursor
          (privateRecursorInfo.levelParams.map Level.param))
        (privatePrefix ++ indices ++ #[privateMajor])
      let publicMotive := publicMotives[resultMotiveIndex]!
      let motive ← withLocalDeclD `value carrier.publicType fun value =>
        liftGen <| mkLambdaFVars #[value]
          (mkAppN publicMotive (indices.push value))
      let roundTrip := mkApp carrier.backwardForward publicMajor
      let congruence ← liftGen <| mkAppM ``congrArg #[motive, roundTrip]
      let transported ← liftGen <| mkAppM ``Eq.mp #[congruence, privateCall]
      unless ← isDefEq (← inferType transported) publicResult do
        failConstruction (.publicRecursorResultMismatch shape.key .transportedResult)
      mkLambdaFVars publicTail transported
    let (agreementTail, agreementTailType) ←
      forallBoundedTelescope privateTail (some (numForalls privateTail))
        fun privateTailArguments _ => do
      let some privateMajor := privateTailArguments.back?
        | failConstruction (.shortInstalledRecursorPrefix shape.key
            shape.implementationRecursor)
      let privateIndices := privateTailArguments.pop
      let privateMajorType ← liftGen <| inferType privateMajor
      let publicMajorType := mkAppN boundary.publicFamily (parameters ++ privateIndices)
      let carrier ← recursorCarrierAt plan boundary parameters publicMajorType privateMajorType
      let publicMajor := mkApp carrier.backward privateMajor
      let privateCall := mkAppN
        (.const shape.implementationRecursor
          (privateRecursorInfo.levelParams.map Level.param))
        (privatePrefix ++ privateIndices ++ #[privateMajor])
      let publicCall := mkAppN (.const name
        (publicRecursorInfo.levelParams.map Level.param))
        (publicPrefix ++ privateIndices ++ #[publicMajor])
      let publicMotive := publicMotives[resultMotiveIndex]!
      let publicCarrierArguments := publicMajorType.getAppArgs
      let publicMotiveType ← liftGen <| whnf (← inferType publicMotive)
      let motiveArity := numForalls publicMotiveType
      unless motiveArity > 0 && publicCarrierArguments.size >= motiveArity - 1 do
        failConstruction (.publicRecursorResultMismatch shape.key .agreementMotive)
      let publicIndices := publicCarrierArguments.extract
        (publicCarrierArguments.size - (motiveArity - 1)) publicCarrierArguments.size
      let motive ← withLocalDeclD `value carrier.publicType fun value =>
        liftGen <| mkLambdaFVars #[value]
          (mkAppN publicMotive (publicIndices.push value))
      let core ← withLocalDeclD `value carrier.implementationType fun value =>
        liftGen <| mkLambdaFVars #[value]
          (mkAppN (.const shape.implementationRecursor
            (privateRecursorInfo.levelParams.map Level.param))
            (privatePrefix ++ privateIndices ++ #[value]))
      let agreement ← liftGen <| mkAppOptM ``packedRecursorAgreement <|
        #[carrier.implementationType, carrier.publicType, motive,
          carrier.forward, carrier.backward, carrier.backwardForward,
          carrier.forwardBackward, core].map some
      let publicToPrivate := mkApp agreement privateMajor
      let proof ← liftGen <| mkAppM ``Eq.symm #[publicToPrivate]
      let resultType ← liftGen <| inferType privateCall
      let expected := eqi.mk' (← liftGen <| ilevel resultType) resultType
        privateCall publicCall
      let value ← liftGen <| mkLambdaFVars privateTailArguments proof
      let type ← liftGen <| mkForallFVars privateTailArguments expected
      return (value, type)
    let value ← liftGen <| mkLambdaFVars publicPrefix valueTail
    let agreementValue ← liftGen <| mkLambdaFVars publicPrefix agreementTail
    let agreementType ← liftGen <| mkForallFVars publicPrefix agreementTailType
    return ((value, agreementValue), agreementType)
  let declaration := Declaration.defnDecl
    { name, levelParams := publicRecursorInfo.levelParams, type := publicType, value,
      hints := .abbrev, safety := .safe }
  liftGen <| addChecked declaration
  let actualAgreementType ← liftGen <| inferType agreementValue
  unless ← liftGen <| withTransparency .all <|
      isDefEq actualAgreementType agreementType do
    failConstruction (.publicRecursorAgreementMismatch shape.key
      actualAgreementType agreementType)
  let agreementDeclaration := Declaration.thmDecl
    { name := agreementName, levelParams := publicRecursorInfo.levelParams,
      type := agreementType, value := agreementValue }
  liftGen <| addChecked agreementDeclaration
  return (minorDeclarations ++ #[declaration, agreementDeclaration],
    { member := shape.key, adapter := name, exactType := publicType,
      implementationRecursor := shape.implementationRecursor,
      callAgreement := agreementName,
      motives := motiveCertificates, minors := minorCertificates,
      rules := shape.sourceRules })

private def buildPublicRecursorPrototypesCore (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate)
    (telescopeCertificates : Array TelescopeCertificate)
    (constructorCertificates : Array PublicConstructorCertificate)
    (root : Name) : ConstructionM
    (Array Declaration × Array PublicRecursorCertificate) := do
  let mut declarations := #[]
  let mut certificates := #[]
  for member in plan.members do
    let shape := memberRecursorShape member
    let boundary ← memberRecursorBoundary plan memberCertificates member
    let (memberDeclarations, certificate) ← publicRecursorDeclaration plan memberCertificates
      telescopeCertificates constructorCertificates root shape boundary
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

private def buildContainerRecursorPrototypesCore (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate)
    (telescopeCertificates : Array TelescopeCertificate)
    (constructorCertificates : Array PublicConstructorCertificate)
    (root : Name) : ConstructionM (Array Declaration × Array BuiltContainerRecursor) := do
  let mut declarations := #[]
  let mut built := #[]
  for container in plan.containerRecursors do
    let shape := containerRecursorShape container
    let boundary := containerRecursorBoundary container
    let (added, recursor) ← publicRecursorDeclaration plan memberCertificates
      telescopeCertificates constructorCertificates root shape boundary
      (some container.resultMotiveIndex)
    let certificate : ContainerRecursorCertificate :=
      { key := container.key, adapter := recursor.adapter, exactType := recursor.exactType,
        callAgreement := recursor.callAgreement, rules := container.rules,
        occurrences := container.occurrences }
    declarations := declarations ++ added
    built := built.push { plan := container, shape, recursor, certificate }
  return (declarations, built)

def buildContainerRecursorPrototypes (plan : FamilyAdapterPlan)
    (memberCertificates : Array MemberCertificate)
    (telescopeCertificates : Array TelescopeCertificate)
    (constructorCertificates : Array PublicConstructorCertificate)
    (root : Name) : GenM
    (Except ConstructionIssue (Array Declaration × Array BuiltContainerRecursor)) := do
  let saved ← getEnv
  match ← ExceptT.lift (buildContainerRecursorPrototypesCore plan memberCertificates
      telescopeCertificates constructorCertificates root).run with
  | .error decline => setEnv saved; declineWith decline
  | .ok (.error issue) => setEnv saved; return .error issue
  | .ok (.ok built) => return .ok built

private def exactMinorArguments (rule : RuleKey) (binders fields hypotheses fieldValues
    hypothesisValues : Array Expr) : ConstructionM (Array Expr) := do
  unless fields.size == fieldValues.size && hypotheses.size == hypothesisValues.size do
    failConstruction (.missingPublicIotaInput rule)
  let mut arguments := #[]
  for binderIndex in [:binders.size] do
    let binder := binders[binderIndex]!
    let value? := if let some fieldIndex := fields.findIdx? (· == binder) then
        fieldValues[fieldIndex]?
      else if let some hypothesisIndex := hypotheses.findIdx? (· == binder) then
        hypothesisValues[hypothesisIndex]?
      else none
    let some value := value? | failConstruction (.missingPublicIotaInput rule)
    let expected := (← liftGen <| inferType binder).replaceFVars
      (binders.extract 0 binderIndex) arguments
    unless ← liftGen <| isDefEq (← inferType value) expected do
      failConstruction (.dependentMinorTransport rule binderIndex)
    arguments := arguments.push value
  return arguments

/-- Read the exact installed RHS application of one literal private minor.
The probe is placed at its keyed prefix position; no constructor spelling or
minor count is used to recover the arguments. -/
private def installedMinorArguments (rule : RulePlan) (owner : MemberPlan)
    (compatibility : RuleCompatibilityCertificate) (privatePrefix : Array Expr)
    (privateMinor privateMinorType : Expr) (privateFields : Array Expr) :
    ConstructionM (Array Expr) := do
  withLocalDeclD `minorProbe privateMinorType fun probe => do
    let probeIndex := owner.parameterArity + owner.recursorMotiveArity +
      compatibility.minorIndex
    let probePrefix := privatePrefix.set! probeIndex probe
    let probed ← liftGen <| whnf (mkAppN rule.implementationRhs
      (probePrefix ++ privateFields))
    unless probed.getAppFn == probe do
      failConstruction (.missingPublicIotaInput rule.key)
    return probed.getAppArgs.map (·.replaceFVars #[probe] #[privateMinor])

private def withPrivateIotaHypotheses (rule : RulePlan) (schema : PublicIotaProofSchema)
    (privateMinorType : Expr) (privateFields privateArguments : Array Expr)
    (k : Array Expr → ConstructionM α) : ConstructionM α := do
  forallBoundedTelescope privateMinorType (some (numForalls privateMinorType))
      fun privateBinders _ => do
    let mut privateMinorFields := #[]
    for field in privateFields do
      let positions := (Array.range privateArguments.size).filter fun position =>
        privateArguments[position]! == field
      let some position := positions[0]?
        | failConstruction (.missingPublicIotaInput rule.key)
      unless positions.size == 1 do
        failConstruction (.missingPublicIotaInput rule.key)
      let some binder := privateBinders[position]?
        | failConstruction (.missingPublicIotaInput rule.key)
      privateMinorFields := privateMinorFields.push binder
    let privateHypotheses := privateBinders.filter fun binder =>
      !privateMinorFields.contains binder
    unless privateHypotheses.size == schema.hypotheses.size &&
        privateArguments.size == privateBinders.size &&
        (Array.range privateHypotheses.size).all fun position =>
          schema.hypotheses.any fun step =>
            step.implementationHypothesisPosition == position &&
              privateBinders[step.binderIndex]? == privateHypotheses[position]? do
      failConstruction (.missingPublicIotaInput rule.key)
    withReboundTelescope privateMinorFields privateFields privateHypotheses 0 #[]
      k

/-- Assemble exact private, decoded-public, and source-public IH packages at
one constructor package.  The only equality produced is the whole public
package equality; it is never projected back into dependent fields. -/
private def packedIotaHypothesisAgreement (plan : FamilyAdapterPlan)
    (recursors : Array PublicRecursorCertificate)
    (containerRecursors : Array BuiltContainerRecursor)
    (rule : RulePlan)
    (schema : PublicIotaProofSchema)
    (publicFields publicMinorFields publicMinorHypotheses decodedFields : Array Expr)
    (theoremRightArguments : Array Expr)
    (privateMinorType : Expr) (privateFields privateArguments : Array Expr) :
    ConstructionM (Expr × Expr × Expr × Expr) := do
  withPrivateIotaHypotheses rule schema privateMinorType privateFields privateArguments
      fun reboundPrivateHypotheses => do
      let eqi ← match EqInfo.check (← getEnv) with
        | .ok information => pure information
        | .error _ => failConstruction (.missingPublicIotaInput rule.key)
      let mut actualValues := #[]
      for position in [:reboundPrivateHypotheses.size] do
        let some step := schema.hypotheses.find?
            (·.implementationHypothesisPosition == position)
          | failConstruction (.missingPublicIotaInput rule.key)
        let some actual := privateArguments[step.binderIndex]?
          | failConstruction (.missingPublicIotaInput rule.key)
        actualValues := actualValues.push actual
      let privatePackage ← liftGen <|
        packTelescopeValue reboundPrivateHypotheses actualValues
      withReboundTelescope publicMinorFields decodedFields publicMinorHypotheses 0 #[]
          fun reboundPublicHypotheses => do
        let mut decodedValues := #[]
        let mut expectedValues := #[]
        let mut proofs := #[]
        for position in [:reboundPublicHypotheses.size] do
          let some step := schema.hypotheses.find?
              (·.publicHypothesisPosition == position)
            | failConstruction (.missingPublicIotaInput rule.key)
          let some actual := privateArguments[step.binderIndex]?
            | failConstruction (.missingPublicIotaInput rule.key)
          let some rawPublic := theoremRightArguments[step.publicBinderIndex]?
            | failConstruction (.missingPublicIotaInput rule.key)
          let expected := rawPublic.replaceFVars publicFields decodedFields
          let proof ← recursorHypothesisAgreement plan recursors rule.key containerRecursors
            step.recursiveCall? step.publicBinderIndex step.binderIndex expected actual
          let type ← liftGen <| inferType actual
          let expectedEquality := eqi.mk' (← liftGen <| ilevel type) type actual expected
          unless ← liftGen <| isDefEq (← inferType proof) expectedEquality do
            failConstruction (.publicIotaProofMismatch rule.key
              (.hypothesisAgreement step.publicBinderIndex step.binderIndex))
          decodedValues := decodedValues.push actual
          expectedValues := expectedValues.push expected
          proofs := proofs.push proof
        let publicPackageType ← liftGen <| packedTelescopeType reboundPublicHypotheses
        let decodedPackage ← liftGen <|
          packTelescopeValue reboundPublicHypotheses decodedValues
        let expectedPackage ← liftGen <|
          packTelescopeValue reboundPublicHypotheses expectedValues
        let proof ← liftGen <| packageCongruence eqi reboundPublicHypotheses
          publicPackageType decodedValues expectedValues proofs
        return (privatePackage, decodedPackage, expectedPackage, proof)

private def installedIotaArguments (rule : RulePlan) (schema : PublicIotaProofSchema)
    (privatePrefix privateIndices : Array Expr) (privateMajor : Expr) :
    ConstructionM (Array Expr) := do
  let mut arguments := #[]
  for role in schema.implementationIotaInputs do
    let value? := match role with
      | .recursorPrefix position => privatePrefix[position]?
      | .resultIndex position => privateIndices[position]?
      | .major => some privateMajor
    let some value := value?
      | failConstruction (.installedIotaTypeMismatch rule.key schema.implementationIota)
    arguments := arguments.push value
  return arguments

private partial def rewriteLeadingRecursiveCall (rule : RuleKey)
    (role : PublicIotaRecursiveCallRole) (adapter : Name)
    (publicBinderIndex implementationBinderIndex : Nat) : Expr → ConstructionM Expr
  | .lam name type body info => do
      let body ← rewriteLeadingRecursiveCall rule role adapter publicBinderIndex
        implementationBinderIndex body
      return .lam name type body info
  | body => do
      let .const source levels := body.getAppFn
        | failConstruction (.publicIotaRecursiveCallMismatch rule publicBinderIndex
            implementationBinderIndex .openedHeadMismatch)
      unless source == role.publicRecursor do
        failConstruction (.publicIotaRecursiveCallMismatch rule publicBinderIndex
          implementationBinderIndex .openedHeadMismatch)
      return mkAppN (.const adapter levels) body.getAppArgs

private partial def rewriteExactRhsArgument (rule : RuleKey) (argumentIndex : Nat)
    (rewrite : Expr → ConstructionM Expr) : Expr → ConstructionM Expr
  | .lam name type body info => do
      let body ← rewriteExactRhsArgument rule argumentIndex rewrite body
      return .lam name type body info
  | body => do
      let arguments := body.getAppArgs
      let some argument := arguments[argumentIndex]?
        | failConstruction (.missingPublicIotaInput rule)
      return mkAppN body.getAppFn (arguments.set! argumentIndex (← rewrite argument))

private def rewritePublicIotaRecursiveCalls (plan : FamilyAdapterPlan)
    (recursors : Array PublicRecursorCertificate)
    (containerRecursors : Array BuiltContainerRecursor)
    (schema : PublicIotaProofSchema) (rhs : Expr) : ConstructionM Expr := do
  let mut result := rhs
  for step in schema.hypotheses do
    if let some role := step.recursiveCall? then
      let (_, recursor) ← recursiveCallCertificate plan recursors containerRecursors
        schema.key role step.publicBinderIndex step.binderIndex
      result ← rewriteExactRhsArgument schema.key step.publicBinderIndex
        (rewriteLeadingRecursiveCall schema.key role recursor.adapter
          step.publicBinderIndex step.binderIndex) result
  return result

private def publicIotaDeclaration (plan : FamilyAdapterPlan)
    (base : FamilyAdapterCertificate)
    (constructors : Array PublicConstructorCertificate)
    (recursors : Array PublicRecursorCertificate)
    (containerRecursors : Array BuiltContainerRecursor) (root : Name)
    (schema : PublicIotaProofSchema) : ConstructionM
    (Declaration × PublicIotaCertificate) := do
  let some rule := plan.rules.find? (·.key == schema.key)
    | failConstruction (.missingPublicIotaInput schema.key)
  let some owner := plan.members.find? (·.key == schema.owner)
    | failConstruction (.missingPublicIotaInput schema.key)
  let some constructor := plan.constructors.find? (·.key == schema.constructor)
    | failConstruction (.missingPublicIotaInput schema.key)
  let some constructorCertificate := constructors.find? (·.key == constructor.key)
    | failConstruction (.missingPublicIotaInput schema.key)
  let some recursorCertificate := recursors.find? (·.member == owner.key)
    | failConstruction (.missingPublicIotaInput schema.key)
  let some compatibility := base.rules.find? (·.key == rule.key)
    | failConstruction (.missingPublicIotaInput schema.key)
  let name := publicIotaAdapterName root rule.key
  liftGen <| ensurePrototypeFresh name
  let constructorMapping := constructors.map fun certificate =>
    let source := (plan.constructors.find? (·.key == certificate.key)).get!.publicName
    (source, certificate.adapter)
  let constructorMappedRhs := mapConstsE (fun source =>
    constructorMapping.find? (·.1 == source) |>.map (·.2)) rule.publicRhs
  let mappedPublicRhs ← rewritePublicIotaRecursiveCalls plan recursors containerRecursors
    schema constructorMappedRhs
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error _ => failConstruction (.missingPublicIotaInput rule.key)
  let some privateRecursorInfo := (← getEnv).constants.find? owner.implementationRecursor
    | failConstruction (.missingInstalledRecursor owner.key owner.implementationRecursor)
  let exactType ← forallBoundedTelescope recursorCertificate.exactType
      (some (owner.parameterArity + owner.recursorMotiveArity + owner.recursorMinorArity))
      fun recursorPrefix _ => do
    let parameters := recursorPrefix.extract 0 owner.parameterArity
    let constructorTail ← instantiateForall constructorCertificate.exactType parameters
    forallBoundedTelescope constructorTail (some constructor.telescope.binders.size)
        fun fields result => do
      let major := mkAppN
        (.const constructorCertificate.adapter (plan.levelParams.map Level.param))
        (parameters ++ fields)
      let majorType := result.replaceFVars fields fields
      let indices := resultIndices owner majorType
      let left := mkAppN
        (.const recursorCertificate.adapter
          (privateRecursorInfo.levelParams.map Level.param))
        (recursorPrefix ++ indices ++ #[major])
      let right ← liftGen <| whnf (mkAppN mappedPublicRhs (recursorPrefix ++ fields))
      let resultType ← liftGen <| inferType left
      unless ← liftGen <| isDefEq (← inferType right) resultType do
        failConstruction (.missingPublicIotaInput rule.key)
      liftGen <| mkForallFVars (recursorPrefix ++ fields)
        (eqi.mk' (← ilevel resultType) resultType left right)
  let value ← forallBoundedTelescope exactType
      (some (owner.parameterArity + owner.recursorMotiveArity + owner.recursorMinorArity))
      fun publicPrefix fieldsTail => do
    let parameters := publicPrefix.extract 0 owner.parameterArity
    let publicMotives := publicPrefix.extract owner.parameterArity
      (owner.parameterArity + owner.recursorMotiveArity)
    let publicMinors := publicPrefix.extract
      (owner.parameterArity + owner.recursorMotiveArity) publicPrefix.size
    let publicMinor := publicMinors[compatibility.minorIndex]!
    let publicMinorType ← liftGen <| inferType publicMinor
    forallBoundedTelescope publicMinorType (some (numForalls publicMinorType))
        fun publicMinorBinders publicMinorResult => do
      let some publicMinorFields := minorFieldValues? constructor publicMinorBinders publicMinorResult
          (some constructorCertificate.adapter)
        | failConstruction (.missingPublicIotaInput rule.key)
      let publicMinorHypotheses ← liftGen <|
        motiveHypothesisValues publicMotives publicMinorFields publicMinorBinders
      unless schema.hypotheses.size == publicMinorHypotheses.size &&
          (Array.range publicMinorHypotheses.size).all fun position =>
            schema.hypotheses.any fun step =>
              step.publicHypothesisPosition == position &&
                publicMinorBinders[step.publicBinderIndex]? ==
                  publicMinorHypotheses[position]? do
        failConstruction (.missingPublicIotaInput rule.key)
      forallBoundedTelescope fieldsTail (some constructor.telescope.binders.size)
          fun publicFields proposition => do
        let some (_, _, theoremRight) ← liftGen <| matchEq? proposition
          | failConstruction (.missingPublicIotaInput rule.key)
        unless theoremRight.getAppFn == publicMinor do
          failConstruction (.missingPublicIotaInput rule.key)
        let theoremRightArguments := theoremRight.getAppArgs
        unless theoremRightArguments.size == publicMinorBinders.size do
          failConstruction (.missingPublicIotaInput rule.key)
        let ownerBoundary ← packedCarrierBoundary plan base.members parameters owner
        let recursorShape := memberRecursorShape owner
        let recursorBoundary ← memberRecursorBoundary plan base.members owner
        let constructorBoundary ← packedConstructorBoundary plan parameters owner ownerBoundary
          constructor constructorCertificate
        let publicPackage ← liftGen <| packTelescopeValue publicFields publicFields
        let mut privateTail ← instantiateForall privateRecursorInfo.type parameters
        let mut privateMotives := #[]
        for motiveIndex in [:recursorCertificate.motives.size] do
          let .forallE _ expected rest _ := privateTail
            | failConstruction (.shortInstalledRecursorPrefix owner.key owner.implementationRecursor)
          let motive ← privateMotiveValue plan base.members recursorBoundary parameters
            recursorShape
            publicMotives[motiveIndex]! expected
          privateMotives := privateMotives.push motive
          privateTail := rest.instantiate1 motive
        let mut privateMinors := #[]
        for minorIndex in [:recursorCertificate.minors.size] do
          let .forallE _ expected rest _ := privateTail
            | failConstruction (.shortInstalledRecursorPrefix owner.key owner.implementationRecursor)
          let minorCertificate := recursorCertificate.minors[minorIndex]!
          let minor ← if let some sourceConstructor := plan.constructors.find? fun current =>
              current.publicName == minorCertificate.publicConstructor &&
                current.implementationName == minorCertificate.implementationConstructor then
            privateMinorValue plan base.members base.telescopes constructors parameters
              publicMotives privateMotives recursorShape minorIndex sourceConstructor
              publicMinors[minorIndex]! expected
          else
            privateSpecialisedMinorValue plan base.members parameters publicMotives privateMotives
              recursorShape recursorBoundary minorCertificate publicMinors[minorIndex]! expected
          privateMinors := privateMinors.push minor
          privateTail := rest.instantiate1 minor
        let privatePrefix := parameters ++ privateMotives ++ privateMinors
        let implementationConstructorType ← liftGen <| generatedType constructor.implementationName
        let implementationFieldsTail ← instantiateForall implementationConstructorType parameters
        forallBoundedTelescope implementationFieldsTail
            (some constructor.telescope.binders.size) fun implementationFields _ => do
          let makePublicHypothesisFamily := withLocalDeclD `package
              constructorBoundary.publicFieldsType
              fun package => do
            let fields ← liftGen <| unpackTelescopeValue publicMinorFields package
            withReboundTelescope publicMinorFields fields publicMinorHypotheses 0 #[] fun hypotheses => do
              let type ← liftGen <| packedTelescopeType hypotheses
              liftGen <| mkLambdaFVars #[package] type
          let publicHypothesisFamily ← makePublicHypothesisFamily
          let publicIH ← withLocalDeclD `package constructorBoundary.publicFieldsType
              fun package => do
            let fields ← liftGen <| unpackTelescopeValue publicMinorFields package
            let values := (Array.range publicMinorHypotheses.size).map fun position =>
              let step := (schema.hypotheses.find?
                (·.publicHypothesisPosition == position)).get!
              theoremRightArguments[step.publicBinderIndex]!.replaceFVars publicFields fields
            withReboundTelescope publicMinorFields fields publicMinorHypotheses 0 #[] fun hypotheses => do
              let packed ← liftGen <| packTelescopeValue hypotheses values
              liftGen <| mkLambdaFVars #[package] packed
          let privateMinor := privateMinors[compatibility.minorIndex]!
          let privateMinorType ← liftGen <| inferType privateMinor
          let implementationHypothesisFamily ← withLocalDeclD `package
              constructorBoundary.implementationFieldsType fun package => do
            let privateFields ← liftGen <|
              unpackTelescopeValue implementationFields package
            let privateArguments ← installedMinorArguments rule owner compatibility
              privatePrefix privateMinor privateMinorType privateFields
            withPrivateIotaHypotheses rule schema privateMinorType privateFields privateArguments
                fun privateHypotheses => do
              let type ← liftGen <| packedTelescopeType privateHypotheses
              liftGen <| mkLambdaFVars #[package] type
          let packageData (package : Expr) :
              ConstructionM (Expr × Expr × Expr × Expr) := do
            let privateFields ← liftGen <|
              unpackTelescopeValue implementationFields package
            let privateArguments ← installedMinorArguments rule owner compatibility
              privatePrefix privateMinor privateMinorType privateFields
            let decodedPackage := mkApp constructorBoundary.decode package
            let decodedFields ← liftGen <|
              unpackTelescopeValue publicMinorFields decodedPackage
            packedIotaHypothesisAgreement plan recursors containerRecursors rule schema
              publicFields publicMinorFields publicMinorHypotheses decodedFields
              theoremRightArguments
              privateMinorType privateFields privateArguments
          let privateIH ← withLocalDeclD `package constructorBoundary.implementationFieldsType
              fun package => do
            let (actualPackage, _, _, _) ← packageData package
            liftGen <| mkLambdaFVars #[package] actualPackage
          let decodeIH ← withLocalDeclD `package
              constructorBoundary.implementationFieldsType fun package => do
            let privateFields ← liftGen <|
              unpackTelescopeValue implementationFields package
            let privateArguments ← installedMinorArguments rule owner compatibility
              privatePrefix privateMinor privateMinorType privateFields
            let privateHypothesisType := mkApp implementationHypothesisFamily package
            withLocalDeclD `privateHypotheses privateHypothesisType
                fun privatePackage => do
              withPrivateIotaHypotheses rule schema privateMinorType privateFields
                  privateArguments fun privateHypotheses => do
                let privateValues ← liftGen <|
                  unpackTelescopeValue privateHypotheses privatePackage
                let decodedPackage := mkApp constructorBoundary.decode package
                let decodedFields ← liftGen <|
                  unpackTelescopeValue publicMinorFields decodedPackage
                withReboundTelescope publicMinorFields decodedFields
                    publicMinorHypotheses 0 #[] fun publicHypotheses => do
                  let mut decodedValues := #[]
                  for position in [:publicHypotheses.size] do
                    let some step := schema.hypotheses.find?
                        (·.publicHypothesisPosition == position)
                      | failConstruction (.missingPublicIotaInput rule.key)
                    let some value := privateValues[step.implementationHypothesisPosition]?
                      | failConstruction (.missingPublicIotaInput rule.key)
                    decodedValues := decodedValues.push value
                  let decoded ← liftGen <|
                    packTelescopeValue publicHypotheses decodedValues
                  liftGen <| mkLambdaFVars #[package, privatePackage] decoded
          let ihAgreement ← withLocalDeclD `package constructorBoundary.implementationFieldsType
              fun package => do
            let (actualPrivate, decodedActual, expectedPublic, packageProof) ←
              packageData package
            let expected := mkApp publicIH (mkApp constructorBoundary.decode package)
            let actualPrivateIH := mkApp privateIH package
            let decodedPrivateIH := mkAppN decodeIH #[package, actualPrivateIH]
            unless ← liftGen <| isDefEq expectedPublic expected do
              failConstruction (.publicIotaProofMismatch rule.key
                .expectedHypothesisPackage)
            unless ← liftGen <| isDefEq actualPrivate actualPrivateIH do
              failConstruction (.publicIotaProofMismatch rule.key
                .privateHypothesisPackage)
            unless ← liftGen <| isDefEq decodedActual decodedPrivateIH do
              failConstruction (.publicIotaProofMismatch rule.key
                .decodedHypothesisPackage)
            let proof ← liftGen <| mkAppM ``Eq.symm #[packageProof]
            liftGen <| mkLambdaFVars #[package] proof
          let minor ← withLocalDeclD `package constructorBoundary.publicFieldsType fun package => do
            let fields ← liftGen <| unpackTelescopeValue publicMinorFields package
            let hypothesisType := mkApp publicHypothesisFamily package
            withLocalDeclD `hypotheses hypothesisType fun hypothesisPackage => do
              let hypothesisValues ← liftGen <|
                unpackTelescopeValue publicMinorHypotheses hypothesisPackage
              let arguments ← exactMinorArguments rule.key publicMinorBinders publicMinorFields
                publicMinorHypotheses fields hypothesisValues
              liftGen <| mkLambdaFVars #[package, hypothesisPackage]
                (mkAppN publicMinor arguments)
          let publicMotive := publicMotives[(plan.members.findIdx? (·.key == owner.key)).getD 0]!
          let motive ← withLocalDeclD `total ownerBoundary.publicType fun total => do
            let (indices, major) ← unpackCarrierTotal plan parameters owner true total
            liftGen <| mkLambdaFVars #[total] (mkAppN publicMotive (indices.push major))
          let core ← withLocalDeclD `total ownerBoundary.implementationType fun total => do
            let (indices, major) ← unpackCarrierTotal plan parameters owner false total
            let call := mkAppN
              (.const owner.implementationRecursor
                (privateRecursorInfo.levelParams.map Level.param))
              (privatePrefix ++ indices ++ #[major])
            liftGen <| mkLambdaFVars #[total] call
          let coreIota ← withLocalDeclD `package constructorBoundary.implementationFieldsType
              fun package => do
            let privateFields ← liftGen <| unpackTelescopeValue implementationFields package
            let privateMajor := mkAppN
              (.const constructor.implementationName (plan.levelParams.map Level.param))
              (parameters ++ privateFields)
            let privateMajorType ← liftGen <| inferType privateMajor
            let privateIndices := resultIndices owner privateMajorType
            let implementationLeft := mkAppN
              (.const owner.implementationRecursor
                (privateRecursorInfo.levelParams.map Level.param))
              (privatePrefix ++ privateIndices ++ #[privateMajor])
            let privateArguments ← installedMinorArguments rule owner compatibility
              privatePrefix privateMinor privateMinorType privateFields
            let actualImplementationRight ← liftGen <|
              whnf (mkAppN rule.implementationRhs (privatePrefix ++ privateFields))
            let implementationRight := mkAppN privateMinor privateArguments
            let resultType ← liftGen <| inferType implementationLeft
            unless ← liftGen <| isDefEq actualImplementationRight implementationRight do
              failConstruction (.publicIotaProofMismatch rule.key .installedRuleRhs)
            unless ← liftGen <| isDefEq (← inferType implementationRight) resultType do
              failConstruction (.publicIotaProofMismatch rule.key .privateMinorResult)
            let installedArguments ← installedIotaArguments rule schema privatePrefix
              privateIndices privateMajor
            let some implementationIotaInfo :=
                (← getEnv).constants.find? schema.implementationIota
              | failConstruction (.missingInstalledIota rule.key schema.implementationIota)
            let installedApplication := mkAppN
              (.const schema.implementationIota
                (implementationIotaInfo.levelParams.map Level.param))
              installedArguments
            unless ← liftGen <| isDefEq installedApplication implementationLeft do
              failConstruction (.installedIotaTypeMismatch rule.key
                schema.implementationIota)
            let installedRight ← liftGen <| whnf installedApplication
            unless ← liftGen <| isDefEq installedRight implementationRight do
              failConstruction (.installedIotaTypeMismatch rule.key
                schema.implementationIota)
            let iotaProof := eqi.refl' (← liftGen <| ilevel resultType) resultType
              implementationLeft
            let decodedPackage := mkApp constructorBoundary.decode package
            let decodedFields ← liftGen <|
              unpackTelescopeValue publicMinorFields decodedPackage
            let decodedPrivateIH := mkAppN decodeIH #[package, mkApp privateIH package]
            let replacementValues ← withReboundTelescope publicMinorFields decodedFields
                publicMinorHypotheses 0 #[] fun hypotheses =>
              liftGen <| unpackTelescopeValue hypotheses decodedPrivateIH
            let mut extra := #[]
            for step in schema.hypotheses do
              let expectedPrivate := privateArguments[step.binderIndex]!
              let some expectedPublic := replacementValues[step.publicHypothesisPosition]?
                | failConstruction (.missingPublicIotaInput rule.key)
              unless ← liftGen <| isDefEq expectedPrivate expectedPublic do
                failConstruction (.publicIotaProofMismatch rule.key
                  (.decodedHypothesis step.publicBinderIndex step.binderIndex))
              let expectedType ← liftGen <| inferType expectedPrivate
              let proof := eqi.refl' (← liftGen <| ilevel expectedType)
                expectedType expectedPrivate
              extra := extra.push expectedPublic |>.push proof
            let compatibilityProof := mkAppN
              (.const schema.minorCompatibility
                (((← getEnv).constants.find! schema.minorCompatibility).levelParams.map Level.param))
              (privatePrefix ++ privateArguments ++ extra)
            let some (_, compatibilityLeft, compatibilityRight) ←
                liftGen <| matchEq? (← inferType compatibilityProof)
              | failConstruction (.publicIotaProofMismatch rule.key
                  .minorCompatibilityType)
            unless ← liftGen <| isDefEq compatibilityLeft implementationRight do
              failConstruction (.publicIotaProofMismatch rule.key
                .minorCompatibilityLeft)
            let chained ← liftGen <| transOf eqi (← ilevel resultType) resultType
              implementationLeft implementationRight
              compatibilityRight
              iotaProof compatibilityProof
            let expected := mkAppN minor
              #[decodedPackage, decodedPrivateIH]
            let constructorProof := mkApp constructorBoundary.constructorAgreement package
            let congruence ← liftGen <| mkAppM ``congrArg #[motive, constructorProof]
            let transported ← liftGen <| mkAppM ``Eq.mp #[congruence, expected]
            let desired := eqi.mk' (← liftGen <| ilevel resultType) resultType
              implementationLeft transported
            unless ← liftGen <| isDefEq (← inferType chained) desired do
              failConstruction (.publicIotaProofMismatch rule.key .coreTransport)
            liftGen <| mkLambdaFVars #[package] chained
          let proof ← liftGen <| mkAppOptM ``packedRecursorCompatibility <|
            #[ownerBoundary.implementationType, ownerBoundary.publicType,
              constructorBoundary.implementationFieldsType,
              constructorBoundary.publicFieldsType, motive, publicHypothesisFamily,
              implementationHypothesisFamily,
              ownerBoundary.forward, ownerBoundary.backward, ownerBoundary.backwardForward,
              constructorBoundary.encode, constructorBoundary.decode,
              constructorBoundary.decodeEncode, constructorBoundary.implementationCtor,
              constructorBoundary.publicCtor, constructorBoundary.forwardCtor,
              privateIH, publicIH, decodeIH, ihAgreement, minor, core,
              constructorBoundary.constructorAgreement, coreIota].map some
          let applied := mkApp proof publicPackage
          unless ← liftGen <| isDefEq (← inferType applied) proposition do
            failConstruction (.publicIotaProofMismatch rule.key .finalProof)
          liftGen <| mkLambdaFVars (publicPrefix ++ publicFields) applied
  let declaration := Declaration.thmDecl
    { name, levelParams := privateRecursorInfo.levelParams, type := exactType, value }
  liftGen <| addChecked declaration
  return (declaration,
    { key := rule.key, adapter := name, exactType,
      implementationIota := schema.implementationIota,
      constructorAdapter := constructorCertificate.adapter,
      recursorAdapter := recursorCertificate.adapter,
      minorCompatibility := schema.minorCompatibility, schema })

private def buildPublicIotaPrototypesCore (plan : FamilyAdapterPlan)
    (base : FamilyAdapterCertificate)
    (constructors : Array PublicConstructorCertificate)
    (recursors : Array PublicRecursorCertificate)
    (containerRecursors : Array BuiltContainerRecursor) (root : Name) : ConstructionM
    (Array Declaration × Array PublicIotaCertificate) := do
  let schemas ← match derivePublicIotaProofSchemas plan base with
    | .ok schemas => pure schemas
    | .error issue => failConstruction issue
  let mut declarations := #[]
  let mut certificates := #[]
  for schema in schemas do
    let (declaration, certificate) ←
      publicIotaDeclaration plan base constructors recursors containerRecursors root schema
    declarations := declarations.push declaration
    certificates := certificates.push certificate
  return (declarations, certificates)

/-- Disabled exact-public iota tranche. Any keyed, generator, or kernel
failure restores the environment so no partial rule family survives. -/
def buildPublicIotaPrototypes (plan : FamilyAdapterPlan)
    (base : FamilyAdapterCertificate)
    (constructors : Array PublicConstructorCertificate)
    (recursors : Array PublicRecursorCertificate)
    (containerRecursors : Array BuiltContainerRecursor) (root : Name) : GenM
    (Except ConstructionIssue (Array Declaration × Array PublicIotaCertificate)) := do
  let saved ← getEnv
  match ← ExceptT.lift
      (buildPublicIotaPrototypesCore plan base constructors recursors containerRecursors root).run with
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
