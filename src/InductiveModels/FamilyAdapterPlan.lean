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
  role : MemberRole
  parameterArity : Nat
  indexArity : Nat
  sourceType : Expr
  implementationCarrier : Name
  publicCarrier : Name
  representation : MemberRepresentation
  constructors : Array ConstructorKey
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
  | duplicateConstructor (key : ConstructorKey)
  | unknownConstructorOwner (key : ConstructorKey)
  | memberConstructorMismatch (member : MemberKey) (constructor : ConstructorKey)
  | duplicateRule (key : RuleKey)
  | unknownRuleOwner (key : RuleKey)
  | unknownRuleConstructor (key : RuleKey)
  | duplicateOccurrence (key : OccurrenceKey)
  | unknownOccurrenceConstructor (key : OccurrenceKey)
  | unknownOccurrenceTarget (key : OccurrenceKey)
  | occurrenceFieldOutOfBounds (key : OccurrenceKey) (fields : Nat)
  | telescopeConstructorMismatch (expected actual : ConstructorKey)
  | telescopeFieldOrder (constructor : ConstructorKey) (expected actual : Nat)
  | telescopeOccurrenceMismatch (key : OccurrenceKey)
  | ruleOccurrenceMismatch (key : OccurrenceKey)
  deriving Inhabited, BEq, Repr

private def duplicateKey? [BEq α] (values : Array α) : Option α := Id.run do
  for i in [:values.size] do
    for j in [i + 1:values.size] do
      if values[i]! == values[j]! then return some values[i]!
  return none

private def memberExists (plan : FamilyAdapterPlan) (key : MemberKey) : Bool :=
  plan.members.any (·.key == key)

private def constructorExists (plan : FamilyAdapterPlan) (key : ConstructorKey) : Bool :=
  plan.constructors.any (·.key == key)

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
    for fieldOffset in [:constructor.telescope.binders.size] do
      let field := constructor.telescope.binders[fieldOffset]!
      unless field.fieldIndex == fieldOffset do
        errors := errors.push
          (.telescopeFieldOrder constructor.key fieldOffset field.fieldIndex)

  for member in plan.members do
    for constructor in member.constructors do
      unless constructor.owner == member.key && constructorExists plan constructor do
        errors := errors.push (.memberConstructorMismatch member.key constructor)

  if let some key := duplicateKey? (plan.rules.map (·.key)) then
    errors := errors.push (.duplicateRule key)
  for rule in plan.rules do
    unless memberExists plan rule.key.recursorOwner do
      errors := errors.push (.unknownRuleOwner rule.key)
    unless constructorExists plan rule.key.constructor do
      errors := errors.push (.unknownRuleConstructor rule.key)

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
      unless (telescopeOccurrences telescope).contains key do
        errors := errors.push (.telescopeOccurrenceMismatch key)
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
