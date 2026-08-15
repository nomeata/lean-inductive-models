import InductiveModels.Driver
import InductiveModels.FamilyAdapterConstruction
import family_adapter_generated

open Lean Meta InductiveModels InductiveModels.FamilyAdapter

namespace FamilyAdapterRejectedBoundaries

inductive Index where
  | here

def erasedResultIndex {alpha : Sort u} (_ : alpha) : Index :=
  Index.here

/--
error: (kernel) invalid return type for 'FamilyAdapterRejectedBoundaries.MovingResult.mk'
-/
#guard_msgs in
inductive MovingResult : Index -> Type where
  | mk (child : MovingResult Index.here) :
      MovingResult (erasedResultIndex child)

axiom Witness {alpha : Type u} (_ : alpha) : Type u

/--
error: (kernel) arg #2 of 'FamilyAdapterRejectedBoundaries.LaterDependency.mk' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
inductive LaterDependency : Index -> Type where
  | mk (child : LaterDependency Index.here) (evidence : Witness child) :
      LaterDependency Index.here

end FamilyAdapterRejectedBoundaries

namespace FamilyAdapterConstructionTest

def identityIso (source : EDecl) : Iso :=
  match source with
  | .induct types constructors recursors =>
    let types := types.toArray
    let constructors := constructors.toArray
    let recursors := recursors.toArray
    let all := types.map (·.name)
    let recursorNames := (Array.range types.size).map fun index =>
      (recursors.find? (·.name == exportRecName all index) |>.map (·.name)).getD .anonymous
    let iotas := (Array.range types.size).flatMap fun index =>
      let recursorName := recursorNames[index]!
      (recursors.find? (·.name == recursorName) |>.map (·.rules.toArray) |>.getD #[]).map
        fun rule => (index, rule.ctor, recursorName)
    { decls := #[]
      levelParams := types[0]?.map (·.levelParams) |>.getD []
      members := all
      selfNames := all
      numAll := all.size
      ctors := constructors.map fun constructor => (constructor.name, constructor.name)
      recs := recursorNames
      iotas
      spliced := #[] }
  | _ => default

structure ChangedContainerBoundary where
  implementationCarrier : Name
  sourceRecursor : Name
  implementationRecursor : Name
  forward : Name
  backward : Name
  backwardForward : Name
  forwardBackward : Name

structure ChangedBoundary where
  publicOwner : Name
  privateOwner : Name
  forward : Name
  backward : Name
  backwardForward : Name
  forwardBackward : Name
  container? : Option ChangedContainerBoundary := none

def changedIso (source : EDecl) (boundary : ChangedBoundary) : MetaM Iso := do
  let publicIso := identityIso source
  let publicConstructor := Name.str boundary.publicOwner "mk"
  let privateConstructor := Name.str boundary.privateOwner "mk"
  let publicRecursor := Name.str boundary.publicOwner "rec"
  let privateRecursor := Name.str boundary.privateOwner "rec"
  let member : IsoFamilyMember :=
    { owner := boundary.publicOwner
      changed := true
      publicSelf := boundary.publicOwner
      privateSelf := boundary.privateOwner
      privateRecursor
      privateConstructors := #[(publicConstructor, privateConstructor)]
      privateIotas := #[(publicRecursor, publicConstructor, privateRecursor)]
      privateRules := #[(publicRecursor, publicConstructor, privateRecursor)]
      roll := boundary.forward
      unroll := boundary.backward
      unrollRoll := boundary.backwardForward
      rollUnroll := boundary.forwardBackward }
  let containerImplementations ← match boundary.container? with
    | none => pure #[]
    | some container =>
      let typeOf := fun name => do
        let some information := (← getEnv).constants.find? name
          | throwError "changed container map {name} is not installed"
        return information.type
      let recursorRules := fun name => do
        let some (.recInfo recursor) := (← getEnv).constants.find? name
          | throwError "changed container recursor {name} is not installed"
        return recursor.rules.toArray.map (·.ctor)
      let sourceRuleKeys ← recursorRules container.sourceRecursor
      let implementationRuleKeys ← recursorRules container.implementationRecursor
      unless sourceRuleKeys.all implementationRuleKeys.contains &&
          implementationRuleKeys.all sourceRuleKeys.contains do
        throwError "changed container recursors have different rule keys"
      pure #[{
        parameterArity := 0
        indexArity := 0
        implementationCarrier := container.implementationCarrier
        sourceRecursor := container.sourceRecursor
        implementationRecursor := container.implementationRecursor
        sourceRecursorType := (← typeOf container.sourceRecursor)
        implementationRecursorType := (← typeOf container.implementationRecursor)
        recursorRuleKeys := sourceRuleKeys.map fun key => (key, key)
        forward := container.forward
        backward := container.backward
        backwardForward := container.backwardForward
        forwardBackward := container.forwardBackward
        forwardType := (← typeOf container.forward)
        backwardType := (← typeOf container.backward)
        backwardForwardType := (← typeOf container.backwardForward)
        forwardBackwardType := (← typeOf container.forwardBackward)
        implementationCarrierType := (← typeOf container.implementationCarrier) }]
  return { publicIso with
    familyImplementation? := some
      { root := boundary.publicOwner, support := #[], members := #[member] }
    containerImplementations }

def changedDirect : ChangedBoundary :=
  { publicOwner := `FamilyAdapterGenerated.GeneratedChangedDirectPublic
    privateOwner := `FamilyAdapterGenerated.GeneratedChangedDirectPrivate
    forward := `FamilyAdapterGenerated.generatedChangedDirectRoll
    backward := `FamilyAdapterGenerated.generatedChangedDirectUnroll
    backwardForward := `FamilyAdapterGenerated.generatedChangedDirectUnrollRoll
    forwardBackward := `FamilyAdapterGenerated.generatedChangedDirectRollUnroll }

def changedIndexed : ChangedBoundary :=
  { publicOwner := `FamilyAdapterGenerated.GeneratedChangedIndexedPublic
    privateOwner := `FamilyAdapterGenerated.GeneratedChangedIndexedPrivate
    forward := `FamilyAdapterGenerated.generatedChangedIndexedRoll
    backward := `FamilyAdapterGenerated.generatedChangedIndexedUnroll
    backwardForward := `FamilyAdapterGenerated.generatedChangedIndexedUnrollRoll
    forwardBackward := `FamilyAdapterGenerated.generatedChangedIndexedRollUnroll }

def changedFunction : ChangedBoundary :=
  { publicOwner := `FamilyAdapterGenerated.GeneratedChangedFunctionPublic
    privateOwner := `FamilyAdapterGenerated.GeneratedChangedFunctionPrivate
    forward := `FamilyAdapterGenerated.generatedChangedFunctionRoll
    backward := `FamilyAdapterGenerated.generatedChangedFunctionUnroll
    backwardForward := `FamilyAdapterGenerated.generatedChangedFunctionUnrollRoll
    forwardBackward := `FamilyAdapterGenerated.generatedChangedFunctionRollUnroll }

def changedNested : ChangedBoundary :=
  { publicOwner := `FamilyAdapterGenerated.GeneratedChangedNestedPublic
    privateOwner := `FamilyAdapterGenerated.GeneratedChangedNestedPrivate
    forward := `FamilyAdapterGenerated.generatedChangedNestedRoll
    backward := `FamilyAdapterGenerated.generatedChangedNestedUnroll
    backwardForward := `FamilyAdapterGenerated.generatedChangedNestedUnrollRoll
    forwardBackward := `FamilyAdapterGenerated.generatedChangedNestedRollUnroll
    container? := some
      { implementationCarrier := `FamilyAdapterGenerated.GeneratedList
        sourceRecursor := `FamilyAdapterGenerated.GeneratedChangedNestedPublic.rec_1
        implementationRecursor := `FamilyAdapterGenerated.GeneratedChangedNestedPrivate.rec_1
        forward := `FamilyAdapterGenerated.generatedChangedNestedContainerForward
        backward := `FamilyAdapterGenerated.generatedChangedNestedContainerBackward
        backwardForward :=
          `FamilyAdapterGenerated.generatedChangedNestedContainerBackwardForward
        forwardBackward :=
          `FamilyAdapterGenerated.generatedChangedNestedContainerForwardBackward } }

def directSamples : Array Name :=
  #[`FamilyAdapterGenerated.GeneratedUniverse,
    `FamilyAdapterGenerated.GeneratedDirect0,
    `FamilyAdapterGenerated.GeneratedDirect1,
    `FamilyAdapterGenerated.GeneratedDirect2,
    `FamilyAdapterGenerated.GeneratedDirect3,
    `FamilyAdapterGenerated.GeneratedDirect5,
    `FamilyAdapterGenerated.GeneratedDirect8]

def dependentSamples : Array Name :=
  #[`FamilyAdapterGenerated.GeneratedDependent0,
    `FamilyAdapterGenerated.GeneratedDependent1,
    `FamilyAdapterGenerated.GeneratedDependent2,
    `FamilyAdapterGenerated.GeneratedDependent3,
    `FamilyAdapterGenerated.GeneratedDependent5,
    `FamilyAdapterGenerated.GeneratedDependent8]

def infinitarySamples : Array Name :=
  #[`FamilyAdapterGenerated.GeneratedInfinitary0,
    `FamilyAdapterGenerated.GeneratedInfinitary1,
    `FamilyAdapterGenerated.GeneratedInfinitary2,
    `FamilyAdapterGenerated.GeneratedInfinitary3,
    `FamilyAdapterGenerated.GeneratedInfinitary5,
    `FamilyAdapterGenerated.GeneratedInfinitary8]

def indexedSamples : Array Name :=
  #[`FamilyAdapterGenerated.GeneratedIndexed1x0,
    `FamilyAdapterGenerated.GeneratedIndexed1x1,
    `FamilyAdapterGenerated.GeneratedIndexed1x3,
    `FamilyAdapterGenerated.GeneratedIndexed1x8,
    `FamilyAdapterGenerated.GeneratedIndexed2x0,
    `FamilyAdapterGenerated.GeneratedIndexed2x2,
    `FamilyAdapterGenerated.GeneratedIndexed2x5,
    `FamilyAdapterGenerated.GeneratedIndexed3x0,
    `FamilyAdapterGenerated.GeneratedIndexed3x3,
    `FamilyAdapterGenerated.GeneratedIndexed3x8]

def constructorSamples : Array Name :=
  #[`FamilyAdapterGenerated.GeneratedConstructors1x8,
    `FamilyAdapterGenerated.GeneratedConstructors2x8,
    `FamilyAdapterGenerated.GeneratedConstructors3x8,
    `FamilyAdapterGenerated.GeneratedConstructors5x8]

def mutualSamples : Array (Array Name) :=
  #[#[`FamilyAdapterGenerated.GeneratedMutual1x8_0],
    #[`FamilyAdapterGenerated.GeneratedMutual2x8_0,
      `FamilyAdapterGenerated.GeneratedMutual2x8_1],
    #[`FamilyAdapterGenerated.GeneratedMutual3x8_0,
      `FamilyAdapterGenerated.GeneratedMutual3x8_1,
      `FamilyAdapterGenerated.GeneratedMutual3x8_2],
    #[`FamilyAdapterGenerated.GeneratedMutual5x8_0,
      `FamilyAdapterGenerated.GeneratedMutual5x8_1,
      `FamilyAdapterGenerated.GeneratedMutual5x8_2,
      `FamilyAdapterGenerated.GeneratedMutual5x8_3,
      `FamilyAdapterGenerated.GeneratedMutual5x8_4]]

def completeSamples : Array (Array Name) :=
  (directSamples ++ dependentSamples ++ infinitarySamples ++ indexedSamples ++
    constructorSamples).map (#[·]) ++ mutualSamples

def nestedSamples : Array Name :=
  #[`FamilyAdapterGenerated.GeneratedShared,
    `FamilyAdapterGenerated.GeneratedMixed,
    `FamilyAdapterGenerated.GeneratedRepeatedSpecialisation,
    `FamilyAdapterGenerated.GeneratedNested1,
    `FamilyAdapterGenerated.GeneratedNested2,
    `FamilyAdapterGenerated.GeneratedNested3,
    `FamilyAdapterGenerated.GeneratedNested5,
    `FamilyAdapterGenerated.GeneratedNested8]

def uniqueBinderIndices (values : Array Nat) : Array Nat := Id.run do
  let mut result := #[]
  for value in values do unless result.contains value do result := result.push value
  return result

partial def containsConstant (target : Name) : Expr → Bool
  | .const name _ => name == target
  | .proj _ _ value => containsConstant target value
  | .app function argument =>
      containsConstant target function || containsConstant target argument
  | .lam _ type body _ | .forallE _ type body _ =>
      containsConstant target type || containsConstant target body
  | .letE _ type value body _ =>
      containsConstant target type || containsConstant target value ||
        containsConstant target body
  | .mdata _ body => containsConstant target body
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => false

def compatibilityUsesTransport (environment : Environment)
    (certificate : RuleCompatibilityCertificate) : Bool :=
  if certificate.transportedHypotheses.isEmpty then true
  else match environment.constants.find? certificate.compatibility with
    | some (.thmInfo information) => containsConstant ``Eq.rec information.value
    | _ => false

def compatibilityHasLevels (environment : Environment)
    (certificate : RuleCompatibilityCertificate) : Bool :=
  (environment.constants.find? certificate.compatibility).any fun information =>
    !information.levelParams.isEmpty

def compatibilityName (root : Name) (rule : RuleKey) : Name :=
  Name.str (root.append (rule.recursor.append rule.constructor.constructor))
    "minorCompatibility"

def iotaSchemasComplete (plan : FamilyAdapterPlan)
    (certificate : FamilyAdapterCertificate) : Bool :=
  match FamilyAdapter.derivePublicIotaProofSchemas plan certificate with
  | .error _ => false
  | .ok schemas => schemas.size == plan.rules.size && plan.rules.all fun rule =>
    (schemas.find? (·.key == rule.key)).any fun schema =>
      let keyed := certificate.minorHypotheses.filter (·.rule == rule.key)
      let compatibility := certificate.rules.find? (·.key == rule.key)
      schema.owner == rule.key.recursorOwner && schema.constructor == rule.key.constructor &&
        schema.implementationIota == rule.implementationIota &&
        schema.telescope.constructor == rule.key.constructor &&
        (plan.members.find? (·.key == rule.key.recursorOwner)).any fun member =>
          schema.implementationIotaInputs == rule.implementationEvidence.application &&
          compatibility.any fun compatibility =>
            schema.minorCompatibility == compatibility.compatibility &&
              schema.hypotheses.map (·.binderIndex) == compatibility.transportedHypotheses &&
              schema.hypotheses.all fun step =>
                !step.occurrences.isEmpty && step.rule == rule.key &&
                  step.minorIndex == compatibility.minorIndex &&
                  (plan.members.find? (·.key == rule.key.recursorOwner)).any fun member =>
                    step.motiveIndex < member.recursorMotiveArity &&
                      step.occurrences.all fun occurrence =>
                        keyed.any fun hypothesis => hypothesis.occurrence == occurrence &&
                          hypothesis.publicBinderIndex == step.publicBinderIndex &&
                          hypothesis.publicMotiveIndex == step.publicMotiveIndex &&
                          hypothesis.binderIndex == step.binderIndex &&
                          hypothesis.motiveIndex == step.motiveIndex &&
                          hypothesis.publicHypothesisPosition ==
                            step.publicHypothesisPosition &&
                          hypothesis.implementationHypothesisPosition ==
                            step.implementationHypothesisPosition &&
                          step.recursiveCall?.all fun role =>
                            !role.publicRecursor.isAnonymous &&
                              !role.implementationRecursor.isAnonymous &&
                              role.containerOccurrences.all step.occurrences.contains &&
                              role.container?.all fun key =>
                                plan.containerRecursors.any (·.key == key)

def ruleCertificatesComplete (plan : FamilyAdapterPlan)
    (certificate : FamilyAdapterCertificate) (environment : Environment) : Bool :=
  iotaSchemasComplete plan certificate && certificate.rules.size == plan.rules.size &&
    plan.rules.all fun rule =>
    let expectedBinders := uniqueBinderIndices <|
      (certificate.minorHypotheses.filter (·.rule == rule.key)).map (·.binderIndex)
    (certificate.rules.find? (·.key == rule.key)).any fun compatibility =>
      compatibility.transportedHypotheses == expectedBinders &&
        compatibility.implementationIota == rule.implementationIota &&
        compatibility.implementationIotaType == rule.implementationIotaType &&
        compatibility.publicIota == rule.publicIota &&
        compatibility.publicIotaType == rule.publicIotaType &&
        environment.constants.contains compatibility.compatibility &&
        compatibilityUsesTransport environment compatibility

/-- Test-only first-failure expansion of `ruleCertificatesComplete`.  Keeping
this separate from the Boolean inventory check makes an installed-family
regression identify the exact certificate conjunct without changing any
construction proof. -/
def ruleCertificateDiagnostic (plan : FamilyAdapterPlan)
    (certificate : FamilyAdapterCertificate) (environment : Environment) : Option String :=
    Id.run do
  let some schemas :=
      (FamilyAdapter.derivePublicIotaProofSchemas plan certificate).toOption
    | return some "iota schema derivation"
  if schemas.size != plan.rules.size then
    return some s!"iota schema cardinality: {schemas.size}/{plan.rules.size}"
  for rule in plan.rules do
    let some schema := schemas.find? (·.key == rule.key)
      | return some s!"{repr rule.key}: missing iota schema"
    if schema.owner != rule.key.recursorOwner then
      return some s!"{repr rule.key}: schema owner"
    if schema.constructor != rule.key.constructor then
      return some s!"{repr rule.key}: schema constructor"
    if schema.implementationIota != rule.implementationIota then
      return some s!"{repr rule.key}: schema implementation iota"
    if schema.telescope.constructor != rule.key.constructor then
      return some s!"{repr rule.key}: schema telescope"
    let some member := plan.members.find? (·.key == rule.key.recursorOwner)
      | return some s!"{repr rule.key}: missing schema member"
    if schema.implementationIotaInputs != rule.implementationEvidence.application then
      return some s!"{repr rule.key}: installed iota input roles"
    let some compatibility := certificate.rules.find? (·.key == rule.key)
      | return some s!"{repr rule.key}: missing compatibility certificate"
    if schema.minorCompatibility != compatibility.compatibility then
      return some s!"{repr rule.key}: schema minor compatibility"
    if schema.hypotheses.map (·.binderIndex) != compatibility.transportedHypotheses then
      return some s!"{repr rule.key}: schema transported hypotheses"
    let keyed := certificate.minorHypotheses.filter (·.rule == rule.key)
    for step in schema.hypotheses do
      if step.occurrences.isEmpty then
        return some s!"{repr rule.key}: empty hypothesis occurrence group"
      if step.rule != rule.key then
        return some s!"{repr rule.key}: hypothesis rule"
      if step.minorIndex != compatibility.minorIndex then
        return some s!"{repr rule.key}: hypothesis minor index"
      if step.motiveIndex >= member.recursorMotiveArity then
        return some s!"{repr rule.key}: hypothesis motive index"
      for occurrence in step.occurrences do
        unless keyed.any fun hypothesis => hypothesis.occurrence == occurrence &&
            hypothesis.publicBinderIndex == step.publicBinderIndex &&
            hypothesis.publicMotiveIndex == step.publicMotiveIndex &&
            hypothesis.binderIndex == step.binderIndex &&
            hypothesis.motiveIndex == step.motiveIndex &&
            hypothesis.publicHypothesisPosition == step.publicHypothesisPosition &&
            hypothesis.implementationHypothesisPosition ==
              step.implementationHypothesisPosition do
          return some s!"{repr rule.key}: keyed hypothesis association"
      if let some role := step.recursiveCall? then
        if role.publicRecursor.isAnonymous then
          return some s!"{repr rule.key}: anonymous public recursive call"
        if role.implementationRecursor.isAnonymous then
          return some s!"{repr rule.key}: anonymous implementation recursive call"
        unless role.containerOccurrences.all step.occurrences.contains do
          return some s!"{repr rule.key}: recursive-call occurrences"
        if let some key := role.container? then
          unless plan.containerRecursors.any (·.key == key) do
            return some s!"{repr rule.key}: recursive-call container key"
  if certificate.rules.size != plan.rules.size then
    return some s!"rule certificate cardinality: {certificate.rules.size}/{plan.rules.size}"
  for rule in plan.rules do
    let some compatibility := certificate.rules.find? (·.key == rule.key)
      | return some s!"{repr rule.key}: missing rule certificate"
    let expectedBinders := uniqueBinderIndices <|
      (certificate.minorHypotheses.filter (·.rule == rule.key)).map (·.binderIndex)
    if compatibility.transportedHypotheses != expectedBinders then
      return some s!"{repr rule.key}: rule transported hypotheses"
    if compatibility.implementationIota != rule.implementationIota then
      return some s!"{repr rule.key}: rule implementation iota"
    if compatibility.implementationIotaType != rule.implementationIotaType then
      return some s!"{repr rule.key}: rule implementation iota type"
    if compatibility.publicIota != rule.publicIota then
      return some s!"{repr rule.key}: rule public iota"
    if compatibility.publicIotaType != rule.publicIotaType then
      return some s!"{repr rule.key}: rule public iota type"
    unless environment.constants.contains compatibility.compatibility do
      return some s!"{repr rule.key}: compatibility not installed"
    unless compatibilityUsesTransport environment compatibility do
      return some s!"{repr rule.key}: compatibility transport"
  return none

def publicConstructorsComplete (plan : FamilyAdapterPlan)
    (certificate : FamilyAdapterCertificate) (root : Name) : MetaM Bool := do
  match ← (FamilyAdapter.buildPublicConstructorPrototypes plan certificate.members
      certificate.telescopes root).run with
  | .error _ => return false
  | .ok (.error _) => return false
  | .ok (.ok (declarations, constructors)) =>
    let environment ← getEnv
    return declarations.size == plan.constructors.size &&
      constructors.size == plan.constructors.size && plan.constructors.all fun constructor =>
        (constructors.find? (·.key == constructor.key)).any fun adapter =>
          adapter.exactType == constructor.publicType &&
            adapter.implementationConstructor == constructor.implementationName &&
            adapter.telescope.constructor == constructor.key &&
            (environment.constants.find? adapter.adapter).any (·.type == constructor.publicType)

partial def forallBinderTypes : Expr → Array Expr
  | .forallE _ domain body _ => #[domain] ++ forallBinderTypes body
  | _ => #[]

partial def minorResultMajorName? : Expr → Option Name
  | .forallE _ _ body _ => minorResultMajorName? body
  | result => result.getAppArgs.back? >>= (·.getAppFn.constName?)

def recursorUsesRecordedMinorAdapters (member : MemberPlan)
    (adapter : PublicRecursorCertificate) : Bool :=
  let binderTypes := forallBinderTypes adapter.exactType
  let minorStart := member.parameterArity + member.recursorMotiveArity
  adapter.minors.all fun minor =>
    (binderTypes[minorStart + minor.minorIndex]?).any fun binderType =>
      minorResultMajorName? binderType == some minor.adapter

inductive PublicPrototypeDiagnostic where
  | complete
  | prerequisite (detail : String)
  | shadowIssues (issues : Array ConstructionIssue)
  | recursorDecline (detail : String)
  | recursorIssue (issue : ConstructionIssue)
  | recursorInvalid (detail : String)
  | iotaDecline (detail : String)
  | iotaIssue (issue : ConstructionIssue)
  | iotaInvalid
  deriving Repr

def PublicPrototypeDiagnostic.isComplete : PublicPrototypeDiagnostic → Bool
  | .complete => true
  | _ => false

/-- Test-only value diagnostic. It preserves the exact keyed construction
issue and whether it arose while building recursors or iotas. -/
def publicPrototypeDiagnostic (plan : FamilyAdapterPlan)
    (certificate : FamilyAdapterCertificate) (root : Name) :
    MetaM PublicPrototypeDiagnostic := do
  let packedCarrier ←
    (FamilyAdapter.validatePackedCarrierBoundaries plan certificate.members).run
  let packedCount ← match packedCarrier with
    | .error decline => return .prerequisite decline.label
    | .ok (.error issue) => return .prerequisite (toString (repr issue))
    | .ok (.ok count) => pure count
  unless packedCount == plan.members.size do
    return .prerequisite "incomplete packed carrier validation"
  let constructorsBuilt ← (FamilyAdapter.buildPublicConstructorPrototypes plan certificate.members
    certificate.telescopes (Name.str root "constructors")).run
  let constructors ← match constructorsBuilt with
    | .error decline => return .prerequisite decline.label
    | .ok (.error issue) => return .prerequisite (toString (repr issue))
    | .ok (.ok (_, constructors)) => pure constructors
  let packedConstructors ←
    (FamilyAdapter.validatePackedConstructorBoundaries plan certificate.members constructors).run
  let packedConstructorCount ← match packedConstructors with
    | .error decline => return .prerequisite decline.label
    | .ok (.error issue) => return .prerequisite (toString (repr issue))
    | .ok (.ok count) => pure count
  unless packedConstructorCount == plan.constructors.size do
    return .prerequisite "incomplete packed constructor validation"
  match ← (FamilyAdapter.buildPublicRecursorPrototypes plan certificate.members
      certificate.telescopes constructors root).run with
  | .error decline => return .recursorDecline decline.label
  | .ok (.error issue) => return .recursorIssue issue
  | .ok (.ok (declarations, recursors)) =>
    let environment ← getEnv
    unless declarations.size >= plan.members.size do
      return .recursorInvalid "ordinary declaration cardinality"
    unless recursors.size == plan.members.size do
      return .recursorInvalid "ordinary certificate cardinality"
    for member in plan.members do
      let some adapter := recursors.find? (·.member == member.key)
        | return .recursorInvalid s!"{member.key.owner}: missing certificate"
      unless adapter.implementationRecursor == member.implementationRecursor do
        return .recursorInvalid s!"{member.key.owner}: implementation recursor"
      unless !adapter.callAgreement.isAnonymous &&
          environment.constants.contains adapter.callAgreement do
        return .recursorInvalid s!"{member.key.owner}: call agreement"
      unless adapter.motives.size == member.recursorMotiveArity do
        return .recursorInvalid s!"{member.key.owner}: motive cardinality"
      unless adapter.motives.all (·.recursor == member.key) do
        return .recursorInvalid s!"{member.key.owner}: motive keys"
      let motiveValidation ←
        (FamilyAdapter.validatePublicRecursorMotiveBoundaries plan certificate.members
          member adapter).run
      match motiveValidation with
      | .error decline =>
        return .recursorInvalid s!"{member.key.owner}: motive decline {decline.label}"
      | .ok (.error issue) =>
        return .recursorInvalid s!"{member.key.owner}: motive boundary {repr issue}"
      | .ok (.ok count) => unless count == member.recursorMotiveArity do
          return .recursorInvalid s!"{member.key.owner}: motive boundary cardinality"
      unless adapter.minors.size == member.recursorMinorArity do
        return .recursorInvalid s!"{member.key.owner}: minor cardinality"
      unless adapter.minors.all fun minor =>
          minor.recursor == member.key &&
            (environment.constants.find? minor.adapter).any (·.type == minor.exactType) do
        return .recursorInvalid s!"{member.key.owner}: minor declarations"
      unless recursorUsesRecordedMinorAdapters member adapter do
        return .recursorInvalid s!"{member.key.owner}: minor substitutions"
      unless adapter.rules == member.sourceRules do
        return .recursorInvalid s!"{member.key.owner}: rule keys"
      unless (environment.constants.find? adapter.adapter).any
          (·.type == adapter.exactType) do
        return .recursorInvalid s!"{member.key.owner}: exact adapter type"
    let containerBuilt ← (FamilyAdapter.buildContainerRecursorPrototypes plan
      certificate.members certificate.telescopes constructors
      (Name.str root "containerRecursors")).run
    let containerRecursors ← match containerBuilt with
      | .error decline => return .recursorDecline decline.label
      | .ok (.error issue) => return .recursorIssue issue
      | .ok (.ok (_, built)) => pure built
    let containerEnvironment ← getEnv
    unless containerRecursors.size == plan.containerRecursors.size do
      return .recursorInvalid "container certificate cardinality"
    for container in plan.containerRecursors do
      let some built := containerRecursors.find? (·.plan.key == container.key)
        | return .recursorInvalid s!"{container.key.publicRecursor}: missing container certificate"
      unless built.certificate.rules == container.rules do
        return .recursorInvalid s!"{container.key.publicRecursor}: container rule keys"
      unless built.certificate.occurrences == container.occurrences do
        return .recursorInvalid s!"{container.key.publicRecursor}: container occurrences"
      unless built.certificate.callRoles == container.callRoles do
        return .recursorInvalid s!"{container.key.publicRecursor}: container call roles"
      unless containerEnvironment.constants.contains built.certificate.callAgreement do
        return .recursorInvalid s!"{container.key.publicRecursor}: container call agreement"
    match ← (FamilyAdapter.buildPublicIotaPrototypes plan certificate constructors recursors
        containerRecursors (Name.str root "iotas")).run with
    | .error decline => return .iotaDecline decline.label
    | .ok (.error issue) => return .iotaIssue issue
    | .ok (.ok (iotaDeclarations, iotas)) =>
      let environment ← getEnv
      if iotaDeclarations.size == plan.rules.size && iotas.size == plan.rules.size &&
        plan.rules.all fun rule => (iotas.find? (·.key == rule.key)).any fun iota =>
          iota.schema.key == rule.key && iota.implementationIota == rule.implementationIota &&
            iota.minorCompatibility == iota.schema.minorCompatibility &&
            (environment.constants.find? iota.adapter).any (·.type == iota.exactType) then
        return .complete
      return .iotaInvalid

def publicRecursorsComplete (plan : FamilyAdapterPlan)
    (certificate : FamilyAdapterCertificate) (root : Name) : MetaM Bool := do
  return (← publicPrototypeDiagnostic plan certificate root).isComplete

def repeatedSpecialisedMinorsComplete (plan : FamilyAdapterPlan)
    (certificate : FamilyAdapterCertificate) (root : Name) : MetaM Bool := do
  let constructorsBuilt ← (FamilyAdapter.buildPublicConstructorPrototypes plan certificate.members
    certificate.telescopes (Name.str root "constructors")).run
  let .ok (.ok (_, constructors)) := constructorsBuilt | return false
  let recursorsBuilt ← (FamilyAdapter.buildPublicRecursorPrototypes plan certificate.members
    certificate.telescopes constructors root).run
  let .ok (.ok (_, recursors)) := recursorsBuilt | return false
  return recursors.any fun recursor =>
    recursor.motives.any (fun motive => !plan.members.any fun member =>
      member.publicCarrier == motive.publicCarrier &&
        member.implementationCarrier == motive.implementationCarrier) &&
    recursor.minors.any fun first => recursor.minors.any fun second =>
      first.minorIndex != second.minorIndex &&
        first.publicConstructor == second.publicConstructor &&
        first.exactType != second.exactType && first.adapter != second.adapter &&
        (plan.members.find? (·.key == recursor.member)).any fun member =>
          recursorUsesRecordedMinorAdapters member recursor

structure Result where
  complete : Nat := 0
  publicConstructors : Nat := 0
  publicRecursors : Nat := 0
  identityNested : Nat := 0
  nestedPublicConstructors : Nat := 0
  nestedPublicRecursors : Nat := 0
  identityCallAgreements : Nat := 0
  invalidIdentityContainerPlans : Nat := 0
  changed : Nat := 0
  changedPublicConstructors : Nat := 0
  changedPublicRecursors : Nat := 0
  installedFamily : Nat := 0
  installedPublicConstructors : Nat := 0
  installedPublicRecursors : Nat := 0
  closedContainers : Nat := 0
  invalidMaps : Nat := 0
  invalidIotas : Nat := 0
  lateInvalidIotas : Nat := 0
  invalidContainerMaps : Nat := 0
  invalidContainerRecursors : Nat := 0
  wrongTargetMaps : Nat := 0
  sharedHypothesis : Nat := 0
  directNestedRule : Nat := 0
  repeatedSpecialisations : Nat := 0
  universeLevels : Nat := 0
  recursorRuleEvidence : Bool := false
  theoremRuleEvidence : Bool := false
  exceptionRollback : Bool := false
  failures : Array String := #[]

def implementationEvidenceConsistent (rule : RulePlan)
    (representation : InstalledRuleRepresentation) : Bool :=
  rule.implementationEvidence.representation == representation &&
    rule.implementationEvidence.declarationType == rule.implementationIotaType &&
    rule.implementationEvidence.semanticRhs == rule.implementationRhs

def runSamples : MetaM Result := do
  let mut result : Result := {}
  let (metadataRestored, kernelRestored) ←
    FamilyAdapter.validatePrototypeExceptionRollback `_family_adapter_transaction_test
  if metadataRestored && kernelRestored then
    result := { result with exceptionRollback := true }
  else
    result := { result with failures := result.failures.push
      "prototype transaction leaked a declaration after an exception" }
  for owners in completeSamples do
    let owner := owners[0]!
    let source ← indEDecl owners
    let iso := identityIso source
    let report ← FamilyAdapter.deriveShadowPlan source iso
    let some plan := report.plan? | do
      result := { result with failures := result.failures.push s!"{owner}: no exact plan" }
      continue
    let built ← (FamilyAdapter.buildFamilyPrototype report iso
      ((`_family_adapter_construction_test).append owner)).run
    match built with
    | .error decline =>
      result := { result with failures := result.failures.push s!"{owner}: {decline.label}" }
    | .ok built =>
      match built.certificate with
      | none =>
        result := { result with failures := result.failures.push s!"{owner}: {repr built.issues}" }
      | some certificate =>
        if plan.rules.any fun rule =>
            implementationEvidenceConsistent rule .recursorRule then
          result := { result with recursorRuleEvidence := true }
        let expectedHypotheses := plan.rules.foldl
          (fun count rule => count + rule.occurrences.size) 0
        let environment ← getEnv
        let declarationsInstalled := built.declarations.all fun declaration =>
          declaration.getNames.all (fun name => environment.constants.contains name)
        let constructorsComplete ← publicConstructorsComplete plan certificate
          ((`_family_adapter_public_constructor_test).append owner)
        if constructorsComplete then
          result := { result with publicConstructors := result.publicConstructors + 1 }
        let recursorsComplete ← publicRecursorsComplete plan certificate
          ((`_family_adapter_public_recursor_test).append owner)
        if recursorsComplete then
          result := { result with publicRecursors := result.publicRecursors + 1 }
        else
          let failures := result.failures.push
            s!"{owner}: exact public recursor prototype did not close"
          result := { result with failures }
        if certificate.telescopes.size == plan.constructors.size &&
            certificate.minorHypotheses.size == expectedHypotheses && declarationsInstalled &&
            ruleCertificatesComplete plan certificate environment then
          result := { result with complete := result.complete + 1 }
          if owner == `FamilyAdapterGenerated.GeneratedUniverse &&
              certificate.rules.all (compatibilityHasLevels environment) then
            result := { result with universeLevels := result.universeLevels + 1 }
        else
          let failures := result.failures.push s!"{owner}: incomplete kernel certificate"
          result := { result with failures }
  for owner in nestedSamples do
    let source ← indEDecl #[owner]
    let iso := identityIso source
    let report ← FamilyAdapter.deriveShadowPlan source iso
    if report.plan?.isNone then
      result := { result with failures := result.failures.push s!"{owner}: no exact plan" }
      continue
    let built ← (FamilyAdapter.buildFamilyPrototype report iso
      ((`_family_adapter_construction_test).append owner)).run
    match built with
    | .error decline =>
      result := { result with failures := result.failures.push s!"{owner}: {decline.label}" }
    | .ok built =>
      let environment ← getEnv
      let rulesComplete := report.plan?.any fun plan => built.certificate.any fun certificate =>
        ruleCertificatesComplete plan certificate environment
      let constructorsComplete ← match report.plan?, built.certificate with
        | some plan, some certificate => do
          publicConstructorsComplete plan certificate
            ((`_family_adapter_nested_public_constructor_test).append owner)
        | _, _ => pure false
      if constructorsComplete then
        result := { result with
          nestedPublicConstructors := result.nestedPublicConstructors + 1 }
      let recursorsComplete ← match report.plan?, built.certificate with
        | some plan, some certificate => do
          publicRecursorsComplete plan certificate
            ((`_family_adapter_nested_public_recursor_test).append owner)
        | _, _ => pure false
      if recursorsComplete then
        result := { result with nestedPublicRecursors := result.nestedPublicRecursors + 1 }
      let identityCalls := match report.plan?, built.certificate with
        | some plan, some certificate =>
          match FamilyAdapter.derivePublicIotaProofSchemas plan certificate with
          | .error _ => false
          | .ok schemas =>
            let roles := schemas.flatMap fun schema =>
              schema.hypotheses.filterMap (·.recursiveCall?)
            let exactRolePositions := schemas.all fun schema =>
              schema.hypotheses.all fun step => step.recursiveCall?.all fun role =>
                role.containerCall?.all fun call =>
                  call.rule == step.rule &&
                    call.hypothesisIndex == step.occurrences[0]!.hypothesisIndex &&
                    call.publicBinderIndex == step.publicBinderIndex &&
                    call.implementationBinderIndex == step.binderIndex &&
                    call.occurrences == step.occurrences
            let canonicalRoles := roles.filter fun role => role.container?.any fun key =>
              plan.containerRecursors.any fun container =>
                container.key == key && container.boundary == .defeq
            exactRolePositions && !canonicalRoles.isEmpty &&
              roles.all fun role =>
                let members := plan.members.filter fun member =>
                  member.publicRecursor == role.publicRecursor &&
                    member.implementationRecursor == role.implementationRecursor
                let containers := plan.containerRecursors.filter fun container =>
                  container.key.publicRecursor == role.publicRecursor &&
                    container.key.implementationRecursor == role.implementationRecursor &&
                    role.containerOccurrences.all container.occurrences.contains
                members.size + containers.size == 1
        | _, _ => false
      if recursorsComplete && identityCalls then
        result := { result with identityCallAgreements :=
          result.identityCallAgreements + 1 }
      if owner == `FamilyAdapterGenerated.GeneratedShared then
        if let some plan := report.plan? then
          if let some canonical := plan.containerRecursors.find? (·.boundary == .defeq) then
            let corrupted : FamilyAdapterPlan := { plan with
              containerRecursors := plan.containerRecursors.map fun container =>
                if container.key == canonical.key then
                  { container with implementationMajorFamily := .sort .zero }
                else container }
            let corruptedDiagnostic ← match built.certificate with
              | some certificate => do
                let diagnostic ← publicPrototypeDiagnostic corrupted certificate
                  (`_family_adapter_invalid_identity_container)
                pure diagnostic
              | none => do
                pure (PublicPrototypeDiagnostic.shadowIssues built.issues)
            let ambiguous : FamilyAdapterPlan := { plan with
              containerRecursors := plan.containerRecursors.push canonical }
            if !corruptedDiagnostic.isComplete && !ambiguous.validate.isEmpty then
              result := { result with invalidIdentityContainerPlans :=
                result.invalidIdentityContainerPlans + 1 }
      if owner == `FamilyAdapterGenerated.GeneratedRepeatedSpecialisation then
        let repeated ← match report.plan?, built.certificate with
          | some plan, some certificate =>
            repeatedSpecialisedMinorsComplete plan certificate
              `_family_adapter_repeated_specialisation_test
          | _, _ => pure false
        if repeated then
          result := { result with
            repeatedSpecialisations := result.repeatedSpecialisations + 1 }
      if built.certificate.isSome && built.issues.isEmpty && rulesComplete then
        result := { result with identityNested := result.identityNested + 1 }
        if owner == `FamilyAdapterGenerated.GeneratedShared then
          let shares := report.plan?.any fun plan => built.certificate.any fun certificate =>
            plan.rules.any fun rule =>
              let binders := uniqueBinderIndices <|
                (certificate.minorHypotheses.filter (·.rule == rule.key)).map (·.binderIndex)
              rule.occurrences.size >= 2 && binders.size < rule.occurrences.size
          if shares then
            result := { result with sharedHypothesis := result.sharedHypothesis + 1 }
        if owner == `FamilyAdapterGenerated.GeneratedMixed then
          let mixed := report.plan?.any fun plan => plan.rules.any fun rule =>
            rule.occurrences.any (·.expressionPath.isEmpty) &&
              rule.occurrences.any (fun occurrence => !occurrence.expressionPath.isEmpty)
          if mixed then result := { result with directNestedRule := result.directNestedRule + 1 }
      else
        let diagnostic ← match report.plan?, built.certificate with
          | some plan, some certificate =>
            publicPrototypeDiagnostic plan certificate
              ((`_family_adapter_nested_diagnostic).append owner)
          | _, _ => pure (.shadowIssues built.issues)
        let failures := result.failures.push
          s!"{owner}: definitionally equal nested field did not close: {repr diagnostic}"
        result := { result with failures }
  for boundary in #[changedDirect, changedFunction, changedIndexed, changedNested] do
    let source ← indEDecl #[boundary.publicOwner]
    let iso ← changedIso source boundary
    let report ← FamilyAdapter.deriveShadowPlan source iso
    if report.plan?.isNone then
      let failures := result.failures.push
        s!"{boundary.publicOwner}: no changed exact plan: {repr report.reasons}"
      result := { result with failures }
      continue
    let built ← (FamilyAdapter.buildFamilyPrototype report iso
      ((`_family_adapter_construction_test_changed).append boundary.publicOwner)).run
    match built with
    | .error decline =>
      let failures := result.failures.push s!"{boundary.publicOwner}: {decline.label}"
      result := { result with failures }
    | .ok built =>
      let constructorsComplete ← match report.plan?, built.certificate with
        | some plan, some certificate => do
          publicConstructorsComplete plan certificate
            ((`_family_adapter_changed_public_constructor_test).append boundary.publicOwner)
        | _, _ => pure false
      if constructorsComplete then
        result := { result with
          changedPublicConstructors := result.changedPublicConstructors + 1 }
      let recursorDiagnostic ← match report.plan?, built.certificate with
        | some plan, some certificate => do
          publicPrototypeDiagnostic plan certificate
            ((`_family_adapter_changed_public_recursor_test).append boundary.publicOwner)
        | _, none => pure (.shadowIssues built.issues)
        | none, _ => pure (.shadowIssues (report.reasons.map .incompleteShadow))
      if recursorDiagnostic.isComplete then
        result := { result with changedPublicRecursors := result.changedPublicRecursors + 1 }
      else
        let failures := result.failures.push
          s!"{boundary.publicOwner}: public prototype diagnostic: {repr recursorDiagnostic}"
        result := { result with failures }
      if boundary.publicOwner == changedNested.publicOwner then
        let keyedPlan := report.plan?.any fun plan => plan.containerMaps.any fun container =>
          container.key.target.owner == boundary.publicOwner &&
            container.maps.forward ==
              `FamilyAdapterGenerated.generatedChangedNestedContainerForward
        let bidirectionalClosedEndpoint := report.plan?.any fun plan =>
          plan.containerRecursors.any fun recursor =>
            recursor.key.publicRecursor ==
                `FamilyAdapterGenerated.GeneratedChangedNestedPublic.rec_1 &&
              match recursor.boundary with
              | .defeq => false
              | .installed evidence =>
                (plan.containerMaps.find? fun map =>
                    map.sourceRecursor == recursor.key.publicRecursor &&
                      map.implementationRecursor == recursor.key.implementationRecursor).any
                    fun map => evidence.forward.exactType == map.forwardType &&
                      evidence.backward.exactType == map.backwardType &&
                      evidence.backwardForward.exactType == map.backwardForwardType &&
                      evidence.forwardBackward.exactType == map.forwardBackwardType &&
                      evidence.maps == map.maps &&
                      #[evidence.forward, evidence.backward, evidence.backwardForward,
                          evidence.forwardBackward].all (·.binders == #[.value])
        let keyedCertificate := built.certificate.any fun certificate =>
          certificate.occurrences.any fun occurrence =>
            occurrence.key.target.owner == boundary.publicOwner &&
              occurrence.maps.forward ==
                `FamilyAdapterGenerated.generatedChangedNestedContainerForward
        let environment ← getEnv
        let rulesComplete := report.plan?.any fun plan => built.certificate.any fun certificate =>
          ruleCertificatesComplete plan certificate environment
        if built.issues.isEmpty && keyedPlan && bidirectionalClosedEndpoint &&
            recursorDiagnostic.isComplete && keyedCertificate && rulesComplete then
          result := { result with changed := result.changed + 1 }
          result := { result with closedContainers := result.closedContainers + 1 }
        else
          let failures := result.failures.push
            s!"{boundary.publicOwner}: changed nested map did not close generically: {
              repr built.issues}"
          result := { result with failures }
      else
        let environment ← getEnv
        let rulesComplete := report.plan?.any fun plan => built.certificate.any fun certificate =>
          ruleCertificatesComplete plan certificate environment
        if built.certificate.isSome && built.issues.isEmpty && rulesComplete then
          result := { result with changed := result.changed + 1 }
        else
          let failures := result.failures.push
            s!"{boundary.publicOwner}: changed boundary did not close: {repr built.issues}"
          result := { result with failures }
  let invalidBoundary := { changedDirect with forward := .anonymous }
  let invalidSource ← indEDecl #[invalidBoundary.publicOwner]
  let invalidIso ← changedIso invalidSource invalidBoundary
  let invalidReport ← FamilyAdapter.deriveShadowPlan invalidSource invalidIso
  let invalidBuilt ← (FamilyAdapter.buildFamilyPrototype invalidReport invalidIso
    `_family_adapter_construction_test_invalid_map).run
  match invalidBuilt with
  | .error decline =>
    let failures := result.failures.push s!"invalid member map: {decline.label}"
    result := { result with failures }
  | .ok built =>
    let keyedMapGap := built.issues.any fun
      | .missingInstalledMemberMap member map =>
          member.owner == invalidBoundary.publicOwner && map.isAnonymous
      | _ => false
    if built.certificate.isNone && keyedMapGap && built.declarations.isEmpty then
      result := { result with invalidMaps := result.invalidMaps + 1 }
    else
      let failures := result.failures.push
        s!"invalid member map was not rejected: {repr built.issues}"
      result := { result with failures }
  let validIotaIso ← changedIso invalidSource changedDirect
  let validIotaReport ← FamilyAdapter.deriveShadowPlan invalidSource validIotaIso
  let invalidIotaReport := { validIotaReport with plan? := validIotaReport.plan?.map fun plan =>
    { plan with rules := plan.rules.mapIdx fun index rule =>
        if index == 0 then { rule with publicIotaType := .sort .zero } else rule } }
  let invalidIotaBuilt ← (FamilyAdapter.buildFamilyPrototype invalidIotaReport validIotaIso
    `_family_adapter_construction_test_invalid_iota).run
  match invalidIotaBuilt with
  | .error decline =>
    let failures := result.failures.push s!"invalid iota metadata: {decline.label}"
    result := { result with failures }
  | .ok built =>
    let keyedIotaGap := built.issues.any fun
      | .installedIotaTypeMismatch rule name =>
          rule.recursorOwner.owner == changedDirect.publicOwner && !name.isAnonymous
      | _ => false
    if built.certificate.isNone && keyedIotaGap && built.declarations.isEmpty then
      result := { result with invalidIotas := result.invalidIotas + 1 }
    else
      let failures := result.failures.push
        s!"invalid iota metadata was not rejected atomically: {repr built.issues}"
      result := { result with failures }
  let lateIotaOwner := `FamilyAdapterGenerated.GeneratedConstructors5x8
  let lateIotaSource ← indEDecl #[lateIotaOwner]
  let lateIotaIso := identityIso lateIotaSource
  let lateIotaReport ← FamilyAdapter.deriveShadowPlan lateIotaSource lateIotaIso
  let lateRuleIndex := lateIotaReport.plan?.map (·.rules.size - 1) |>.getD 0
  let lateRuleKey? := lateIotaReport.plan?.bind (·.rules[lateRuleIndex]?) |>.map (·.key)
  let malformedLateIotaReport := { lateIotaReport with
    plan? := lateIotaReport.plan?.map fun plan =>
      { plan with rules := plan.rules.mapIdx fun index rule =>
          if index == lateRuleIndex then { rule with publicIotaType := .sort .zero } else rule } }
  let lateIotaRoot := `_family_adapter_construction_test_late_invalid_iota
  let malformedLateIotaBuilt ← (FamilyAdapter.buildFamilyPrototype malformedLateIotaReport
    lateIotaIso lateIotaRoot).run
  match malformedLateIotaBuilt with
  | .error decline =>
    let failures := result.failures.push s!"late invalid iota metadata: {decline.label}"
    result := { result with failures }
  | .ok built =>
    let environment ← getEnv
    let noRuleDeclarationLeaked := lateIotaReport.plan?.map (fun plan =>
      plan.rules.all fun rule =>
        !environment.constants.contains (compatibilityName lateIotaRoot rule.key)) |>.getD false
    let keyedIotaGap := built.issues.any fun
      | .installedIotaTypeMismatch rule _ =>
          rule.recursorOwner.owner == lateIotaOwner && lateRuleKey? == some rule
      | _ => false
    if built.certificate.isNone && keyedIotaGap && built.declarations.isEmpty &&
        noRuleDeclarationLeaked then
      result := { result with lateInvalidIotas := result.lateInvalidIotas + 1 }
    else
      let failures := result.failures.push
        s!"late invalid iota metadata retained a partial rule tranche: {repr built.issues}"
      result := { result with failures }
  let invalidContainerSource ← indEDecl #[changedNested.publicOwner]
  let validContainerIso ← changedIso invalidContainerSource changedNested
  let validContainer := validContainerIso.containerImplementations[0]!
  let invalidContainer := { validContainer with forward := validContainer.backward }
  let invalidContainerIso :=
    { validContainerIso with containerImplementations := #[invalidContainer] }
  let invalidContainerReport ←
    FamilyAdapter.deriveShadowPlan invalidContainerSource invalidContainerIso
  let invalidContainerBuilt ← (FamilyAdapter.buildFamilyPrototype invalidContainerReport
    invalidContainerIso `_family_adapter_construction_test_invalid_container_map).run
  match invalidContainerBuilt with
  | .error decline =>
    let failures := result.failures.push s!"invalid container map: {decline.label}"
    result := { result with failures }
  | .ok built =>
    let exactMismatch := invalidContainerReport.reasons.any fun
      | .installedContainerMapTypeMismatch occurrence name =>
          occurrence.target.owner == changedNested.publicOwner &&
            name == validContainer.backward
      | _ => false
    if exactMismatch && invalidContainerReport.coverage.containerMaps.isEmpty &&
        built.certificate.isNone && built.declarations.isEmpty then
      result := { result with invalidContainerMaps := result.invalidContainerMaps + 1 }
    else
      let failures := result.failures.push
        s!"invalid container metadata was not rejected atomically: shadow={
          repr invalidContainerReport.reasons}, construction={repr built.issues}"
      result := { result with failures }
  let invalidContainerRecursor :=
    { validContainer with
      implementationRecursor := validContainer.sourceRecursor
      implementationRecursorType := validContainer.sourceRecursorType
      recursorRuleKeys := validContainer.recursorRuleKeys.map fun (source, _) =>
        (source, source) }
  let invalidContainerRecursorIso :=
    { validContainerIso with containerImplementations := #[invalidContainerRecursor] }
  let invalidContainerRecursorReport ←
    FamilyAdapter.deriveShadowPlan invalidContainerSource invalidContainerRecursorIso
  let invalidContainerRecursorBuilt ←
    (FamilyAdapter.buildFamilyPrototype invalidContainerRecursorReport
      invalidContainerRecursorIso
      `_family_adapter_construction_test_invalid_container_recursor).run
  match invalidContainerRecursorBuilt with
  | .error decline =>
    let failures := result.failures.push s!"invalid container recursor: {decline.label}"
    result := { result with failures }
  | .ok built =>
    let exactMismatch := invalidContainerRecursorReport.reasons.any fun
      | .invalidContainerRecursorAssociation occurrence =>
          occurrence.target.owner == changedNested.publicOwner
      | _ => false
    if exactMismatch && invalidContainerRecursorReport.coverage.containerMaps.isEmpty &&
        built.certificate.isNone && built.declarations.isEmpty then
      result := { result with
        invalidContainerRecursors := result.invalidContainerRecursors + 1 }
    else
      let failures := result.failures.push
        s!"invalid container recursor association was not rejected atomically: shadow={
          repr invalidContainerRecursorReport.reasons}, construction={repr built.issues}"
      result := { result with failures }
  let wrongTargetName :=
    `FamilyAdapterGenerated.generatedChangedNestedContainerWrongTarget
  let wrongTargetType := (← getEnv).constants.find! wrongTargetName |>.type
  let wrongTargetContainer :=
    { validContainer with forward := wrongTargetName, forwardType := wrongTargetType }
  let wrongTargetIso :=
    { validContainerIso with containerImplementations := #[wrongTargetContainer] }
  let wrongTargetReport ← FamilyAdapter.deriveShadowPlan invalidContainerSource wrongTargetIso
  let wrongTargetBuilt ← (FamilyAdapter.buildFamilyPrototype wrongTargetReport wrongTargetIso
    `_family_adapter_construction_test_wrong_container_target).run
  match wrongTargetBuilt with
  | .error decline =>
    let failures := result.failures.push s!"wrong container target: {decline.label}"
    result := { result with failures }
  | .ok built =>
    let keyedMissing := wrongTargetReport.reasons.any fun
      | .missingContainerMap occurrence =>
          occurrence.target.owner == changedNested.publicOwner
      | _ => false
    if keyedMissing && wrongTargetReport.coverage.containerMaps.isEmpty &&
        built.certificate.isNone && built.declarations.isEmpty then
      result := { result with wrongTargetMaps := result.wrongTargetMaps + 1 }
    else
      let failures := result.failures.push
        s!"wrong container target entered the plan: shadow={repr wrongTargetReport.reasons}, \
          construction={repr built.issues}"
      result := { result with failures }
  let installedOwners := #[`FamilyAdapterGenerated.GeneratedLayerA,
    `FamilyAdapterGenerated.GeneratedLayerB]
  let installedSource ← indEDecl installedOwners
  match ← (mutualOneLayerIso installedSource {}).run with
  | .error decline =>
    let failures := result.failures.push s!"installed changed family: {decline.label}"
    result := { result with failures }
  | .ok installedIso =>
    let installedReport ← FamilyAdapter.deriveShadowPlan installedSource installedIso
    if installedReport.plan?.any fun plan => plan.rules.any fun rule =>
        implementationEvidenceConsistent rule .equalityTheorem then
      result := { result with theoremRuleEvidence := true }
    let firstInstalledRule? := installedReport.plan?.bind (·.rules[0]?) |>.map (·.key)
    let rejectsFirstPublicRule := fun (report : ShadowReport) =>
      firstInstalledRule?.any fun expected =>
        report.reasons.any (fun
          | .installedRuleMismatch actual .publicModel => actual == expected
          | _ => false) && !report.coverage.rules.contains expected
    let (iotaOwner, iotaConstructor, _) := installedIso.iotas[0]!
    let wrongKindIotas := installedIso.iotas.set! 0
      (iotaOwner, iotaConstructor, installedIso.selfNames[0]!)
    let wrongKindIso := { installedIso with iotas := wrongKindIotas }
    let wrongRecursors := installedIso.recs.set! 0 installedIso.recs[1]!
    let wrongRecursorIso := { installedIso with recs := wrongRecursors }
    let (sourceConstructor, _) := installedIso.ctors[0]!
    let wrongConstructors := installedIso.ctors.set! 0
      (sourceConstructor, installedIso.ctors[1]!.2)
    let wrongConstructorIso := { installedIso with ctors := wrongConstructors }
    let wrongKindReport ← FamilyAdapter.deriveShadowPlan installedSource wrongKindIso
    let wrongRecursorReport ← FamilyAdapter.deriveShadowPlan installedSource wrongRecursorIso
    let wrongConstructorReport ←
      FamilyAdapter.deriveShadowPlan installedSource wrongConstructorIso
    unless rejectsFirstPublicRule wrongKindReport &&
        rejectsFirstPublicRule wrongRecursorReport &&
        rejectsFirstPublicRule wrongConstructorReport do
      let failures := result.failures.push
        "installed rule theorem kind/recursor/constructor corruption was not rejected keyedly"
      result := { result with failures }
    let installedBuilt ← (FamilyAdapter.buildFamilyPrototype installedReport installedIso
      `_family_adapter_construction_test_installed_family).run
    match installedBuilt with
    | .error decline =>
      let failures := result.failures.push s!"installed family prototype: {decline.label}"
      result := { result with failures }
    | .ok built =>
      let environment ← getEnv
      let rulesComplete := installedReport.plan?.any fun plan =>
        built.certificate.any fun certificate =>
          ruleCertificatesComplete plan certificate environment
      let ruleDiagnostic := match installedReport.plan?, built.certificate with
        | some plan, some certificate =>
          ruleCertificateDiagnostic plan certificate environment
        | none, _ => some "missing installed plan"
        | _, none => some "missing installed construction certificate"
      let constructorsComplete ← match installedReport.plan?, built.certificate with
        | some plan, some certificate => do
          publicConstructorsComplete plan certificate
            `_family_adapter_installed_public_constructor_test
        | _, _ => pure false
      if constructorsComplete then
        result := { result with
          installedPublicConstructors := result.installedPublicConstructors + 1 }
      let recursorDiagnostic ← match installedReport.plan?, built.certificate with
        | some plan, some certificate => do
          publicPrototypeDiagnostic plan certificate
            `_family_adapter_installed_public_recursor_test
        | none, _ => pure (.prerequisite "missing installed plan")
        | _, none => pure (.prerequisite "missing installed construction certificate")
      if recursorDiagnostic.isComplete then
        result := { result with
          installedPublicRecursors := result.installedPublicRecursors + 1 }
      if installedIso.familyImplementation?.isSome && built.certificate.isSome &&
          built.issues.isEmpty && rulesComplete then
        result := { result with installedFamily := result.installedFamily + 1 }
      else
        let failures := result.failures.push
          s!"installed family did not close: shadow={repr installedReport.reasons}, \
            construction={repr built.issues}, baseCertificate={repr ruleDiagnostic}, \
            publicPrototype={repr recursorDiagnostic}"
        result := { result with failures }
  return result

def runMain : IO UInt32 := do
  initSearchPath (← findSysroot)
  let environment ← importModules
    #[`InductiveModels.FamilyAdapterConstruction, `family_adapter_generated] {}
  let context : Core.Context :=
    { fileName := "<family-adapter-construction-test>", fileMap := default,
      options := {}, maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, state) ← Core.CoreM.toIO (MetaM.run' runSamples) context { env := environment }
  if result.failures.isEmpty && result.complete == completeSamples.size &&
      result.publicConstructors == completeSamples.size &&
      result.publicRecursors == completeSamples.size &&
      result.identityNested == nestedSamples.size &&
      result.nestedPublicConstructors == nestedSamples.size && result.changed == 4 &&
      result.nestedPublicRecursors == nestedSamples.size &&
      result.identityCallAgreements == nestedSamples.size &&
      result.invalidIdentityContainerPlans == 1 &&
      result.changedPublicConstructors == 4 &&
      result.changedPublicRecursors == 4 &&
      result.closedContainers == 1 && result.invalidMaps == 1 && result.invalidContainerMaps == 1 &&
      result.invalidContainerRecursors == 1 &&
      result.invalidIotas == 1 && result.lateInvalidIotas == 1 && result.wrongTargetMaps == 1 &&
      result.sharedHypothesis == 1 && result.directNestedRule == 1 &&
      result.repeatedSpecialisations == 1 &&
      result.universeLevels == 1 &&
      result.installedFamily == 1 && result.installedPublicConstructors == 1 &&
      result.installedPublicRecursors == 1 &&
      result.recursorRuleEvidence && result.theoremRuleEvidence &&
      result.exceptionRollback &&
      state.messages.toArray.isEmpty then
    IO.println s!"family adapter construction: {result.complete} complete finite plans, \
      {result.identityNested} definitional nested plans, {result.changed} changed plans, \
      one installed family, {result.closedContainers} keyed container map, \
      validated member/container map and recursion metadata"
    return 0
  for failure in result.failures do IO.eprintln failure
  for message in state.messages.toArray do IO.eprintln (← message.toString)
  IO.eprintln s!"family adapter construction: complete={result.complete}, \
    publicConstructors={result.publicConstructors}, \
    publicRecursors={result.publicRecursors}, \
    identityNested={result.identityNested}, \
    nestedPublicConstructors={result.nestedPublicConstructors}, changed={result.changed}, \
    nestedPublicRecursors={result.nestedPublicRecursors}, \
    identityCallAgreements={result.identityCallAgreements}, \
    invalidIdentityContainerPlans={result.invalidIdentityContainerPlans}, \
    changedPublicConstructors={result.changedPublicConstructors}, \
    changedPublicRecursors={result.changedPublicRecursors}, \
    installedFamily={result.installedFamily}, \
    installedPublicConstructors={result.installedPublicConstructors}, \
    installedPublicRecursors={result.installedPublicRecursors}, \
    closedContainers={result.closedContainers}, \
    invalidMaps={result.invalidMaps}, invalidIotas={result.invalidIotas}, \
    lateInvalidIotas={result.lateInvalidIotas}, \
    invalidContainerMaps={result.invalidContainerMaps}, \
    invalidContainerRecursors={result.invalidContainerRecursors}, \
    wrongTargetMaps={result.wrongTargetMaps}, sharedHypothesis={result.sharedHypothesis}, \
    directNestedRule={result.directNestedRule}, \
    repeatedSpecialisations={result.repeatedSpecialisations}, \
    universeLevels={result.universeLevels}, \
    recursorRuleEvidence={result.recursorRuleEvidence}, \
    theoremRuleEvidence={result.theoremRuleEvidence}, \
    exceptionRollback={result.exceptionRollback}"
  return 1

end FamilyAdapterConstructionTest

def main : IO UInt32 := FamilyAdapterConstructionTest.runMain
