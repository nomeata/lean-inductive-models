import InductiveModels.FamilyAdapterPlan
import family_adapter_generated

open Lean InductiveModels
open InductiveModels.FamilyAdapter

private def numbered (stem : String) (index : Nat) : Name :=
  Name.mkSimple s!"{stem}{index}"

private def memberKey (index : Nat) : MemberKey :=
  { owner := numbered "FamilyAdapterPlanTest.member" index }

private def constructorKey (constructorsPerMember ownerIndex constructorIndex : Nat) :
    ConstructorKey :=
  { owner := memberKey ownerIndex
    constructor := numbered "FamilyAdapterPlanTest.constructor"
      (ownerIndex * constructorsPerMember + constructorIndex) }

private def sourceRecursor (ownerIndex : Nat) : Name :=
  numbered "FamilyAdapterPlanTest.sourceRecursor" ownerIndex

private def ruleKey (constructorsPerMember recursorOwner constructorOwner constructorIndex : Nat) :
    RuleKey :=
  { recursorOwner := memberKey recursorOwner
    recursor := sourceRecursor recursorOwner
    constructor := constructorKey constructorsPerMember constructorOwner constructorIndex }

private def sorts (count : Nat) : Array Expr :=
  Array.replicate count (.sort .zero)

/-- Build a structurally valid plan from independent finite dimensions.  This
is test data, not an eligibility predicate: callers may supply any positive
member count and arbitrary nonnegative values for every other dimension. -/
private def makePlan (memberCount constructorsPerMember parameterArity indexArity
    fieldCount occurrencesPerField : Nat) : FamilyAdapterPlan := Id.run do
  let mut constructors : Array ConstructorPlan := #[]
  let mut occurrences : Array OccurrencePlan := #[]
  let mut rules : Array RulePlan := #[]

  for ownerIndex in [:memberCount] do
    for constructorIndex in [:constructorsPerMember] do
      let ordinal := ownerIndex * constructorsPerMember + constructorIndex
      let key := constructorKey constructorsPerMember ownerIndex constructorIndex
      let mut binders : Array TelescopeBinderPlan := #[]
      for fieldIndex in [:fieldCount] do
        let mut fieldOccurrences : Array OccurrenceKey := #[]
        for occurrenceIndex in [:occurrencesPerField] do
          let targetIndex :=
            (ownerIndex + fieldIndex + occurrenceIndex + 1) % memberCount
          let occurrenceKey : OccurrenceKey :=
            { constructor := key
              fieldIndex
              expressionPath := Array.replicate (occurrenceIndex + 1) .appArgument
              binderDepth := occurrenceIndex
              hypothesisIndex := fieldIndex * occurrencesPerField + occurrenceIndex
              target := memberKey targetIndex }
          fieldOccurrences := fieldOccurrences.push occurrenceKey
          occurrences := occurrences.push
            { key := occurrenceKey
              sourceType := .sort .zero
              implementationType := .sort .zero }
        binders := binders.push
          { fieldIndex
            info := .default
            sourceType := .sort .zero
            implementationType := .sort .zero
            occurrences := fieldOccurrences }

      let telescope : TelescopePlan :=
        { constructor := key
          parameters := sorts parameterArity
          binders
          sourceResultIndices := sorts indexArity
          implementationResultIndices := sorts indexArity
          sourcePackedType := .sort .zero
          implementationPackedType := .sort .zero }
      constructors := constructors.push
        { key
          sourceName := numbered "FamilyAdapterPlanTest.sourceConstructor" ordinal
          implementationName := numbered "FamilyAdapterPlanTest.implConstructor" ordinal
          publicName := numbered "FamilyAdapterPlanTest.publicConstructor" ordinal
          sourceType := .sort .zero
          implementationType := .sort .zero
          publicType := .sort .zero
          telescope }

  -- A mutual source recursor has one rule for every constructor in the whole
  -- family, not merely the constructors owned by its motive's member.
  for recursorOwner in [:memberCount] do
    for constructorOwner in [:memberCount] do
      for constructorIndex in [:constructorsPerMember] do
        let constructorOrdinal :=
          constructorOwner * constructorsPerMember + constructorIndex
        let key := constructorKey constructorsPerMember constructorOwner constructorIndex
        let ruleOrdinal :=
          recursorOwner * memberCount * constructorsPerMember + constructorOrdinal
        rules := rules.push
          { key := ruleKey constructorsPerMember recursorOwner constructorOwner constructorIndex
            ruleIndex := constructorOrdinal
            exactRhs := .sort .zero
            publicRhs := .sort .zero
            implementationRhs := .sort .zero
            implementationIota := numbered "FamilyAdapterPlanTest.implIota" ruleOrdinal
            publicIota := numbered "FamilyAdapterPlanTest.publicIota" ruleOrdinal
            implementationIotaType := .sort .zero
            publicIotaType := .sort .zero
            occurrences := (occurrences.filter (·.key.constructor == key)).map (·.key) }

  let members := (Array.range memberCount).map (fun ownerIndex =>
    { key := memberKey ownerIndex
      component := { anchor := memberKey 0 }
      role := .source
      parameterArity
      indexArity
      sourceType := .sort .zero
      implementationCarrier := numbered "FamilyAdapterPlanTest.implCarrier" ownerIndex
      publicCarrier := numbered "FamilyAdapterPlanTest.publicCarrier" ownerIndex
      representation := .layer
      constructors := (Array.range constructorsPerMember).map
        (constructorKey constructorsPerMember ownerIndex)
      sourceRules := (Array.range memberCount).flatMap fun constructorOwner =>
        (Array.range constructorsPerMember).map
          (ruleKey constructorsPerMember ownerIndex constructorOwner)
      recursorMotiveArity := memberCount
      recursorMinorArity := memberCount * constructorsPerMember
      sourceRecursor := sourceRecursor ownerIndex
      implementationRecursor := numbered "FamilyAdapterPlanTest.implRecursor" ownerIndex
      publicRecursor := numbered "FamilyAdapterPlanTest.publicRecursor" ownerIndex })
  let containerMaps := occurrences.mapIdx fun index occurrence =>
    { key := occurrence.key
      parameterArity
      indexArity
      implementationCarrier := numbered "FamilyAdapterPlanTest.containerCarrier" index
      sourceRecursor := numbered "FamilyAdapterPlanTest.containerSourceRecursor" index
      implementationRecursor := numbered "FamilyAdapterPlanTest.containerImplRecursor" index
      sourceRecursorType := .sort .zero
      implementationRecursorType := .sort .zero
      recursorRuleKeys :=
        #[(numbered "FamilyAdapterPlanTest.containerSourceRule" index,
           numbered "FamilyAdapterPlanTest.containerImplRule" index)]
      maps :=
        { forward := numbered "FamilyAdapterPlanTest.containerForward" index
          backward := numbered "FamilyAdapterPlanTest.containerBackward" index
          backwardForward := numbered "FamilyAdapterPlanTest.containerBackwardForward" index
          forwardBackward := numbered "FamilyAdapterPlanTest.containerForwardBackward" index }
      forwardType := .sort .zero
      backwardType := .sort .zero
      backwardForwardType := .sort .zero
      forwardBackwardType := .sort .zero
      implementationCarrierType := .sort .zero }
  let containerRecursors := containerMaps.map fun container =>
    let key : ContainerRecursorKey :=
      { publicRecursor := container.sourceRecursor
        implementationRecursor := container.implementationRecursor }
    { key
      parameterArity := container.parameterArity
      indexArity := container.indexArity
      publicType := container.sourceRecursorType
      implementationType := container.implementationRecursorType
      publicMajorFamily := .sort .zero
      implementationMajorFamily := .sort .zero
      rules := container.recursorRuleKeys.map fun (publicConstructor,
          implementationConstructor) =>
        { recursor := key, publicConstructor, implementationConstructor }
      occurrences := #[container.key]
      maps := container.maps }
  return { root := memberKey 0
           levelParams := []
           components :=
             #[{ key := { anchor := memberKey 0 }
                 members := (Array.range memberCount).map memberKey }]
           members
           constructors
           rules
           occurrences
           containerMaps
           containerRecursors }

private def sampledCounts : Array Nat := #[0, 1, 2, 3, 5, 8]

/-- Split an otherwise valid source family into a source component and a
mimic-only component.  A mimic SCC need not contain a source member. -/
private def withMimicComponent (plan : FamilyAdapterPlan) : FamilyAdapterPlan :=
  let sourceComponent : ComponentKey := { anchor := plan.members[0]!.key }
  let mimicComponent : ComponentKey := { anchor := plan.members[1]!.key }
  let members := plan.members.mapIdx fun index member =>
    if index == 0 then
      { member with component := sourceComponent, role := .source }
    else
      { member with component := mimicComponent, role := .mimic }
  { plan with
    components :=
      #[{ key := sourceComponent, members := #[plan.members[0]!.key] },
        { key := mimicComponent
          members := (plan.members.extract 1 plan.members.size).map (·.key)
          dependencies := #[sourceComponent] }]
    members }

private def reportErrors (label : String) (errors : Array PlanError) : IO Bool := do
  if errors.isEmpty then
    return true
  IO.eprintln s!"{label}: expected a valid generic plan, got {repr errors}"
  return false

private def checkDimensionSamples : IO Bool := do
  let mut ok := true
  -- Vary each dimension independently across former boundaries.  The builder
  -- itself is not bounded by this regression sample.
  for count in sampledCounts do
    ok := (← reportErrors s!"constructors={count}"
      (makePlan 3 count 2 3 4 3).validate) && ok
    ok := (← reportErrors s!"parameters={count}"
      (makePlan 3 2 count 3 4 3).validate) && ok
    ok := (← reportErrors s!"indices={count}"
      (makePlan 3 2 2 count 4 3).validate) && ok
    ok := (← reportErrors s!"fields={count}"
      (makePlan 3 2 2 3 count 3).validate) && ok
    ok := (← reportErrors s!"occurrences-per-field={count}"
      (makePlan 3 2 2 3 4 count).validate) && ok
  for count in sampledCounts.drop 1 do
    ok := (← reportErrors s!"members={count}"
      (makePlan count 2 2 3 4 3).validate) && ok
  return ok

private def expectError (label : String) (errors : Array PlanError)
    (predicate : PlanError → Bool) : IO Bool := do
  if errors.any predicate then return true
  IO.eprintln s!"{label}: expected error absent from {repr errors}"
  return false

private def checkMalformedPlans : IO Bool := do
  let plan := makePlan 3 2 1 2 3 2
  let duplicate := { plan with members := plan.members.push plan.members[0]! }
  let duplicateOk ← expectError "duplicate source identities" duplicate.validate fun
    | .duplicateMember _ => true
    | _ => false

  let parameterMismatch :=
    { plan with constructors := plan.constructors.mapIdx fun index
        (constructorPlan : ConstructorPlan) =>
        if index == 0 then
          let telescope := { constructorPlan.telescope with parameters := #[] }
          { constructorPlan with telescope }
        else constructorPlan }
  let parameterOk ← expectError "constructor parameter arity" parameterMismatch.validate fun
    | .constructorParameterArityMismatch _ _ _ => true
    | _ => false

  let indexMismatch :=
    { plan with constructors := plan.constructors.mapIdx fun index
        (constructorPlan : ConstructorPlan) =>
        if index == 0 then
          let telescope :=
            { constructorPlan.telescope with sourceResultIndices := #[] }
          { constructorPlan with telescope }
        else constructorPlan }
  let indexOk ← expectError "constructor index arity" indexMismatch.validate fun
    | .constructorIndexArityMismatch _ _ _ _ => true
    | _ => false

  let ruleSequenceMismatch :=
    { plan with rules := plan.rules.mapIdx fun index (rulePlan : RulePlan) =>
        if index == 0 then
          let occurrences := rulePlan.occurrences.extract 1 rulePlan.occurrences.size
          { rulePlan with occurrences }
        else rulePlan }
  let sequenceOk ← expectError "exact rule occurrence sequence"
    ruleSequenceMismatch.validate fun
    | .ruleOccurrenceSequenceMismatch _ => true
    | _ => false

  let missingRule := { plan with rules := plan.rules.extract 1 plan.rules.size }
  let ruleCoverageOk ← expectError "exact source recursor rule coverage"
    missingRule.validate fun
    | .memberRuleMismatch _ _ => true
    | _ => false

  let missingComponents := { plan with components := #[] }
  let componentOk ← expectError "SCC member coverage" missingComponents.validate fun
    | .memberComponentMultiplicity _ _ => true
    | _ => false

  let duplicateContainer :=
    { plan with containerMaps := plan.containerMaps.push plan.containerMaps[0]! }
  let duplicateContainerOk ← expectError "duplicate keyed container map"
    duplicateContainer.validate fun
    | .duplicateContainerMap _ => true
    | _ => false

  let firstContainer := plan.containerMaps[0]!
  let unknownContainerKey :=
    { firstContainer.key with fieldIndex := firstContainer.key.fieldIndex + 1000 }
  let unknownContainer :=
    { plan with containerMaps := #[{ firstContainer with key := unknownContainerKey }] }
  let unknownContainerOk ← expectError "unknown keyed container-map occurrence"
    unknownContainer.validate fun
    | .unknownContainerMapOccurrence key => key == unknownContainerKey
    | _ => false
  return duplicateOk && parameterOk && indexOk && sequenceOk && ruleCoverageOk && componentOk &&
    duplicateContainerOk && unknownContainerOk

def main : IO UInt32 := do
  let samplesOk ← checkDimensionSamples
  -- One deliberately non-default point guards against treating the fixture
  -- sample itself as an implementation limit.
  let wideOk ← reportErrors "wide arbitrary finite plan"
    (makePlan 7 9 6 4 5 11).validate
  let mimicOk ← reportErrors "mimic-only multi-component plan"
    (withMimicComponent (makePlan 5 3 2 3 4 5)).validate
  let malformedOk ← checkMalformedPlans
  return if samplesOk && wideOk && mimicOk && malformedOk then 0 else 1
