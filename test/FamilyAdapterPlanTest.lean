import InductiveModels.FamilyAdapterPlan

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

private def equivalence (index : Nat) : EquivalenceCertificate :=
  { forward := numbered "FamilyAdapterPlanTest.forward" index
    backward := numbered "FamilyAdapterPlanTest.backward" index
    backwardForward := numbered "FamilyAdapterPlanTest.backwardForward" index
    forwardBackward := numbered "FamilyAdapterPlanTest.forwardBackward" index }

private def sourceRecursor (ownerIndex : Nat) : Name :=
  numbered "FamilyAdapterPlanTest.sourceRecursor" ownerIndex

private def ruleKey (constructorsPerMember ownerIndex constructorIndex : Nat) : RuleKey :=
  { recursorOwner := memberKey ownerIndex
    recursor := sourceRecursor ownerIndex
    constructor := constructorKey constructorsPerMember ownerIndex constructorIndex }

private def sorts (count : Nat) : Array Expr :=
  Array.replicate count (.sort .zero)

/-- Build a structurally valid plan from independent finite dimensions.  This
is test data, not an eligibility predicate: callers may supply any positive
member count and arbitrary nonnegative values for every other dimension. -/
private def makePlan (memberCount constructorsPerMember parameterArity indexArity
    fieldCount occurrencesPerField : Nat) : FamilyAdapterPlan := Id.run do
  let mut constructors : Array ConstructorPlan := #[]
  let mut occurrences : Array OccurrenceCertificate := #[]
  let mut rules : Array RulePlan := #[]

  for ownerIndex in [:memberCount] do
    for constructorIndex in [:constructorsPerMember] do
      let ordinal := ownerIndex * constructorsPerMember + constructorIndex
      let key := constructorKey constructorsPerMember ownerIndex constructorIndex
      let mut constructorOccurrences : Array OccurrenceKey := #[]
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
          constructorOccurrences := constructorOccurrences.push occurrenceKey
          occurrences := occurrences.push
            { key := occurrenceKey
              sourceType := .sort .zero
              implementationType := .sort .zero
              maps := equivalence
                (ordinal * fieldCount * occurrencesPerField +
                  fieldIndex * occurrencesPerField + occurrenceIndex) }
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
      let certificate : TelescopeCertificate :=
        { constructor := key
          packSource := numbered "FamilyAdapterPlanTest.packSource" ordinal
          packImplementation := numbered "FamilyAdapterPlanTest.packImplementation" ordinal
          encode := numbered "FamilyAdapterPlanTest.encode" ordinal
          decode := numbered "FamilyAdapterPlanTest.decode" ordinal
          decodeEncode := numbered "FamilyAdapterPlanTest.decodeEncode" ordinal
          encodeDecode := numbered "FamilyAdapterPlanTest.encodeDecode" ordinal }
      constructors := constructors.push
        { key
          sourceName := numbered "FamilyAdapterPlanTest.sourceConstructor" ordinal
          implementationName := numbered "FamilyAdapterPlanTest.implConstructor" ordinal
          publicName := numbered "FamilyAdapterPlanTest.publicConstructor" ordinal
          sourceType := .sort .zero
          implementationType := .sort .zero
          publicType := .sort .zero
          telescope
          certificate }
      rules := rules.push
        { key := ruleKey constructorsPerMember ownerIndex constructorIndex
          ruleIndex := ordinal
          exactRhs := .sort .zero
          implementationIota := numbered "FamilyAdapterPlanTest.implIota" ordinal
          publicIota := numbered "FamilyAdapterPlanTest.publicIota" ordinal
          occurrences := constructorOccurrences }

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
      rules := (Array.range constructorsPerMember).map
        (ruleKey constructorsPerMember ownerIndex)
      sourceRecursor := sourceRecursor ownerIndex
      implementationRecursor := numbered "FamilyAdapterPlanTest.implRecursor" ownerIndex
      publicRecursor := numbered "FamilyAdapterPlanTest.publicRecursor" ownerIndex
      equivalence := equivalence ownerIndex })
  return { root := memberKey 0
           levelParams := []
           components :=
             #[{ key := { anchor := memberKey 0 }
                 members := (Array.range memberCount).map memberKey }]
           members
           constructors
           rules
           occurrences }

private def sampledCounts : Array Nat := #[0, 1, 2, 3, 5, 8]

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

private def checkMalformedPlan : IO Bool := do
  let plan := makePlan 3 2 1 2 3 2
  let duplicate := { plan with members := plan.members.push plan.members[0]! }
  if duplicate.validate.any fun error =>
      match error with
      | .duplicateMember _ => true
      | _ => false then
    return true
  IO.eprintln "duplicate source identities were not rejected"
  return false

def main : IO UInt32 := do
  let samplesOk ← checkDimensionSamples
  -- One deliberately non-default point guards against treating the fixture
  -- sample itself as an implementation limit.
  let wideOk ← reportErrors "wide arbitrary finite plan"
    (makePlan 7 9 6 4 5 11).validate
  let malformedOk ← checkMalformedPlan
  return if samplesOk && wideOk && malformedOk then 0 else 1
