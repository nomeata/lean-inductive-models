import InductiveModels.Model

/-!
# Generic private/public family-adapter plans

This module is deliberately inert.  It describes the source-derived plan and
the declaration-backed certificate for a future adapter around an already
kernel-checked private [`InductiveModels.Iso`], but no generator or checker
imports it yet.

The keys below carry source identities instead of array positions.  Arrays are
used only as finite ordered collections; none of the structures imposes a
bound on members, constructors, indices, fields, or recursive occurrences.
-/

open Lean

namespace InductiveModels

namespace FamilyAdapter

/-- One member of the expanded family seen by the private implementation.
`source` members receive public correspondence slots.  `mimic` members are
the specialised container members introduced by nested compilation. -/
inductive MemberRole where
  | source
  | mimic
  deriving Inhabited, BEq, Repr

/-- Stable identity of a family member. -/
structure MemberKey where
  owner : Name
  deriving Inhabited, BEq, Repr

/-- Stable identity of one strongly connected component.  The anchor is a
source member identity chosen by the plan builder, not an array offset. -/
structure ComponentKey where
  anchor : MemberKey
  deriving Inhabited, BEq, Repr

/-- One component of the recursive dependency graph.  Both its membership and
its outgoing condensation edges are arbitrary finite keyed collections. -/
structure ComponentPlan where
  key : ComponentKey
  members : Array MemberKey
  dependencies : Array ComponentKey := #[]
  deriving Inhabited, BEq, Repr

/-- Stable identity of one constructor.  Including the owner prevents equal
last components in different mutual members from aliasing. -/
structure ConstructorKey where
  owner : MemberKey
  constructor : Name
  deriving Inhabited, BEq, Repr

/-- Stable identity of one exported recursor rule. -/
structure RuleKey where
  recursorOwner : MemberKey
  recursor : Name
  constructor : ConstructorKey
  deriving Inhabited, BEq, Repr

/-- A path to an occurrence inside an exact field type.  This is an expression
path, not a taxonomy of recursive shapes; a direct occurrence has an empty
path, while aliases, binders, and nested container arguments retain their
literal path. -/
inductive ExprPathStep where
  | appFunction
  | appArgument
  | binderDomain
  | binderBody
  | letType
  | letValue
  | letBody
  | metadataBody
  | projectionBody
  deriving Inhabited, BEq, Repr

/-- Source-derived identity of one recursive occurrence and its corresponding
minor hypothesis.  Several occurrences may belong to one field, and one
constructor may contain arbitrarily many fields and hypotheses. -/
structure OccurrenceKey where
  constructor : ConstructorKey
  fieldIndex : Nat
  expressionPath : Array ExprPathStep := #[]
  binderDepth : Nat := 0
  hypothesisIndex : Nat
  target : MemberKey
  deriving Inhabited, BEq, Repr

/-- A declaration-backed equivalence.  The future checker derives all four
types from the exact source plan; names alone do not authorize a contract. -/
structure EquivalenceCertificate where
  forward : Name
  backward : Name
  backwardForward : Name
  forwardBackward : Name
  deriving Inhabited, BEq, Repr

/-- Whether a public member is definitionally the private carrier or exposes a
constructor layer.  This is a result recorded by a complete plan, not an
eligibility classifier. -/
inductive MemberRepresentation where
  | identity
  | layer
  deriving Inhabited, BEq, Repr

/-- One member of the generic adapter plan.  Member-specific index arities are
kept explicitly; mutual members need not be classified as indexed or
unindexed as a block. -/
structure MemberPlan where
  key : MemberKey
  component : ComponentKey
  role : MemberRole
  parameterArity : Nat
  indexArity : Nat
  sourceType : Expr
  implementationCarrier : Name
  publicCarrier : Name
  representation : MemberRepresentation
  constructors : Array ConstructorKey
  rules : Array RuleKey
  sourceRecursor : Name
  implementationRecursor : Name
  publicRecursor : Name
  equivalence : EquivalenceCertificate
  deriving Inhabited, BEq, Repr

/-- One exact constructor binder in the public/private telescope walk. -/
structure TelescopeBinderPlan where
  fieldIndex : Nat
  info : BinderInfo
  sourceType : Expr
  implementationType : Expr
  occurrences : Array OccurrenceKey := #[]
  deriving Inhabited, BEq, Repr

/-- Source and implementation views of one constructor telescope.  Result
indices are arrays rather than special unary fields. -/
structure TelescopePlan where
  constructor : ConstructorKey
  parameters : Array Expr := #[]
  binders : Array TelescopeBinderPlan
  sourceResultIndices : Array Expr := #[]
  implementationResultIndices : Array Expr := #[]
  sourcePackedType : Expr
  implementationPackedType : Expr
  deriving Inhabited, BEq, Repr

/-- Declaration-backed maps and laws for a whole dependent telescope package.
Moving the package as one value allows later binder types to be transported
without one proof template per field count. -/
structure TelescopeCertificate where
  constructor : ConstructorKey
  packSource : Name
  packImplementation : Name
  encode : Name
  decode : Name
  decodeEncode : Name
  encodeDecode : Name
  deriving Inhabited, BEq, Repr

/-- One constructor in the public/private family boundary. -/
structure ConstructorPlan where
  key : ConstructorKey
  sourceName : Name
  implementationName : Name
  publicName : Name
  sourceType : Expr
  implementationType : Expr
  publicType : Expr
  telescope : TelescopePlan
  certificate : TelescopeCertificate
  deriving Inhabited, BEq, Repr

/-- Maps for one recursive occurrence.  For a direct family edge these are the
target member's maps.  For a nested edge they may be the generated
`G(P) <-> G(M)` maps, composed later with the existing mimic pack/unpack laws. -/
structure OccurrenceCertificate where
  key : OccurrenceKey
  sourceType : Expr
  implementationType : Expr
  maps : EquivalenceCertificate
  deriving Inhabited, BEq, Repr

/-- One exact public rule and its private proof oracle.  Occurrences are keyed
to minor hypotheses rather than accepted by a count comparison. -/
structure RulePlan where
  key : RuleKey
  ruleIndex : Nat
  exactRhs : Expr
  implementationIota : Name
  publicIota : Name
  occurrences : Array OccurrenceKey := #[]
  deriving Inhabited, BEq, Repr

/-- Complete finite plan for a single private/public family boundary. -/
structure FamilyAdapterPlan where
  root : MemberKey
  levelParams : List Name
  components : Array ComponentPlan
  members : Array MemberPlan
  constructors : Array ConstructorPlan
  rules : Array RulePlan
  occurrences : Array OccurrenceCertificate
  support : Array Name := #[]
  deriving Inhabited, BEq, Repr

/-- Structural errors in an inert plan.  Semantic validation remains the
future generator/checker's job against exact source and installed metadata. -/
inductive PlanError where
  | emptyFamily
  | duplicateMember (key : MemberKey)
  | missingRoot (key : MemberKey)
  | duplicateComponent (key : ComponentKey)
  | emptyComponent (key : ComponentKey)
  | componentAnchorMismatch (key : ComponentKey)
  | unknownComponentMember (component : ComponentKey) (member : MemberKey)
  | unknownComponentDependency (component dependency : ComponentKey)
  | memberComponentMultiplicity (member : MemberKey) (count : Nat)
  | memberComponentMismatch (member : MemberKey) (expected actual : ComponentKey)
  | duplicateConstructor (key : ConstructorKey)
  | unknownConstructorOwner (key : ConstructorKey)
  | memberConstructorMismatch (member : MemberKey) (constructor : ConstructorKey)
  | duplicateRule (key : RuleKey)
  | memberRuleMismatch (member : MemberKey) (rule : RuleKey)
  | unknownRuleOwner (key : RuleKey)
  | unknownRuleConstructor (key : RuleKey)
  | duplicateOccurrence (key : OccurrenceKey)
  | unknownOccurrenceConstructor (key : OccurrenceKey)
  | unknownOccurrenceTarget (key : OccurrenceKey)
  | occurrenceFieldOutOfBounds (key : OccurrenceKey) (fields : Nat)
  | occurrenceTelescopeMultiplicity (key : OccurrenceKey) (count : Nat)
  | telescopeConstructorMismatch (expected actual : ConstructorKey)
  | telescopeFieldOrder (constructor : ConstructorKey) (expected actual : Nat)
  | telescopeOccurrenceMismatch (key : OccurrenceKey)
  | ruleOccurrenceMismatch (key : OccurrenceKey)
  deriving Inhabited, BEq, Repr

private def duplicateKey? [BEq α] [Inhabited α] (values : Array α) : Option α := Id.run do
  for i in [:values.size] do
    for j in [i + 1:values.size] do
      if values[i]! == values[j]! then return some values[i]!
  return none

private def countKey [BEq α] (values : Array α) (key : α) : Nat :=
  values.foldl (fun count value => if value == key then count + 1 else count) 0

private def memberExists (plan : FamilyAdapterPlan) (key : MemberKey) : Bool :=
  plan.members.any (·.key == key)

private def constructorExists (plan : FamilyAdapterPlan) (key : ConstructorKey) : Bool :=
  plan.constructors.any (·.key == key)

private def componentExists (plan : FamilyAdapterPlan) (key : ComponentKey) : Bool :=
  plan.components.any (·.key == key)

private def ruleExists (plan : FamilyAdapterPlan) (key : RuleKey) : Bool :=
  plan.rules.any (·.key == key)

private def telescopeFor? (plan : FamilyAdapterPlan)
    (key : ConstructorKey) : Option TelescopePlan :=
  plan.constructors.find? (·.key == key) |>.map (·.telescope)

private def telescopeOccurrences (telescope : TelescopePlan) : Array OccurrenceKey :=
  telescope.binders.flatMap (·.occurrences)

/-- Check only representation-independent key and coverage invariants.  There
is intentionally no arity, constructor-count, index-count, recursion-shape,
or source-route predicate here. -/
def FamilyAdapterPlan.validate (plan : FamilyAdapterPlan) : Array PlanError := Id.run do
  let mut errors := #[]
  if plan.members.isEmpty then errors := errors.push .emptyFamily
  if let some key := duplicateKey? (plan.members.map (·.key)) then
    errors := errors.push (.duplicateMember key)
  unless memberExists plan plan.root do errors := errors.push (.missingRoot plan.root)

  if let some key := duplicateKey? (plan.components.map (·.key)) then
    errors := errors.push (.duplicateComponent key)
  for component in plan.components do
    if component.members.isEmpty then errors := errors.push (.emptyComponent component.key)
    unless component.members.contains component.key.anchor do
      errors := errors.push (.componentAnchorMismatch component.key)
    if let some member := duplicateKey? component.members then
      errors := errors.push (.memberComponentMultiplicity member 2)
    for member in component.members do
      unless memberExists plan member do
        errors := errors.push (.unknownComponentMember component.key member)
    for dependency in component.dependencies do
      unless componentExists plan dependency do
        errors := errors.push (.unknownComponentDependency component.key dependency)
  for member in plan.members do
    let containers := plan.components.filter (·.members.contains member.key)
    unless containers.size == 1 do
      errors := errors.push (.memberComponentMultiplicity member.key containers.size)
    if let some component := containers[0]? then
      unless member.component == component.key do
        errors := errors.push
          (.memberComponentMismatch member.key component.key member.component)

  if let some key := duplicateKey? (plan.constructors.map (·.key)) then
    errors := errors.push (.duplicateConstructor key)
  for constructor in plan.constructors do
    unless memberExists plan constructor.key.owner do
      errors := errors.push (.unknownConstructorOwner constructor.key)
    unless constructor.telescope.constructor == constructor.key do
      errors := errors.push
        (.telescopeConstructorMismatch constructor.key constructor.telescope.constructor)
    unless constructor.certificate.constructor == constructor.key do
      errors := errors.push
        (.telescopeConstructorMismatch constructor.key constructor.certificate.constructor)
    if let some owner := plan.members.find? (·.key == constructor.key.owner) then
      unless owner.constructors.contains constructor.key do
        errors := errors.push (.memberConstructorMismatch owner.key constructor.key)
    for fieldOffset in [:constructor.telescope.binders.size] do
      let field := constructor.telescope.binders[fieldOffset]!
      unless field.fieldIndex == fieldOffset do
        errors := errors.push
          (.telescopeFieldOrder constructor.key fieldOffset field.fieldIndex)
      for key in field.occurrences do
        unless key.constructor == constructor.key && key.fieldIndex == field.fieldIndex do
          errors := errors.push (.telescopeOccurrenceMismatch key)

  for member in plan.members do
    if let some constructor := duplicateKey? member.constructors then
      errors := errors.push (.memberConstructorMismatch member.key constructor)
    for constructor in member.constructors do
      unless constructor.owner == member.key && constructorExists plan constructor do
        errors := errors.push (.memberConstructorMismatch member.key constructor)
    if let some rule := duplicateKey? member.rules then
      errors := errors.push (.memberRuleMismatch member.key rule)
    for rule in member.rules do
      unless rule.recursorOwner == member.key && rule.recursor == member.sourceRecursor &&
          ruleExists plan rule do
        errors := errors.push (.memberRuleMismatch member.key rule)

  if let some key := duplicateKey? (plan.rules.map (·.key)) then
    errors := errors.push (.duplicateRule key)
  for rule in plan.rules do
    unless memberExists plan rule.key.recursorOwner do
      errors := errors.push (.unknownRuleOwner rule.key)
    unless constructorExists plan rule.key.constructor do
      errors := errors.push (.unknownRuleConstructor rule.key)
    if let some owner := plan.members.find? (·.key == rule.key.recursorOwner) then
      unless owner.rules.contains rule.key do
        errors := errors.push (.memberRuleMismatch owner.key rule.key)
    for key in rule.occurrences do
      unless key.constructor == rule.key.constructor do
        errors := errors.push (.ruleOccurrenceMismatch key)

  if let some key := duplicateKey? (plan.occurrences.map (·.key)) then
    errors := errors.push (.duplicateOccurrence key)
  for occurrence in plan.occurrences do
    let key := occurrence.key
    unless constructorExists plan key.constructor do
      errors := errors.push (.unknownOccurrenceConstructor key)
    unless memberExists plan key.target do
      errors := errors.push (.unknownOccurrenceTarget key)
    if let some telescope := telescopeFor? plan key.constructor then
      if key.fieldIndex >= telescope.binders.size then
        errors := errors.push (.occurrenceFieldOutOfBounds key telescope.binders.size)
      let count := countKey (telescopeOccurrences telescope) key
      -- Exact key coverage, not an occurrence-count cap: every distinct source
      -- occurrence occupies one and only one slot in its literal telescope.
      unless count == 1 do
        errors := errors.push (.occurrenceTelescopeMultiplicity key count)
    unless plan.rules.any (·.occurrences.contains key) do
      errors := errors.push (.ruleOccurrenceMismatch key)

  for constructor in plan.constructors do
    for key in telescopeOccurrences constructor.telescope do
      unless plan.occurrences.any (·.key == key) do
        errors := errors.push (.telescopeOccurrenceMismatch key)
  for rule in plan.rules do
    for key in rule.occurrences do
      unless plan.occurrences.any (·.key == key) do
        errors := errors.push (.ruleOccurrenceMismatch key)
  return errors

end FamilyAdapter

end InductiveModels
