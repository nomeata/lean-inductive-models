import InductiveModels.Model

/-!
# Generic private/public family-adapter plans

This module describes the source-derived plan and declaration-backed
certificate for a future adapter around an already kernel-checked private
[`InductiveModels.Iso`]. `FamilyAdapterShadow` derives and validates plans, but
no production route selects or emits from them yet.

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

/-- Stable identity of one strongly connected component.  The anchor is an
arbitrary source or mimic family member chosen by the plan builder, not an
array offset. -/
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
  /-- Exact rule-key sequence read from this member's source `ERec`. -/
  sourceRules : Array RuleKey
  /-- Exact motive/minor prefix arities read from the source `ERec`.  These
  locate the corresponding binders in an installed private recursor without
  assuming a singleton or non-mutual layout. -/
  recursorMotiveArity : Nat
  recursorMinorArity : Nat
  sourceRecursor : Name
  implementationRecursor : Name
  publicRecursor : Name
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
  /-- Equality of the complete dependent result-index vectors after encoding.
  The vector is packed once, rather than split into an arity-specific list of
  equations. -/
  indexFibre : Name
  deriving Inhabited, BEq, Repr

/-- One occurrence's exact slot in an installed private minor telescope.
Several source occurrences in the same field may intentionally name the same
hypothesis; `binderIndex` remains the literal minor-binder position. -/
structure MinorHypothesisCertificate where
  rule : RuleKey
  occurrence : OccurrenceKey
  minorIndex : Nat
  hypothesisIndex : Nat
  /-- Literal binder position in the exact public/source minor telescope. -/
  publicBinderIndex : Nat
  /-- Literal public/source motive slot used by that binder. -/
  publicMotiveIndex : Nat
  /-- Literal binder position in the exact installed private minor telescope. -/
  binderIndex : Nat
  /-- Literal motive binder used at this installed IH position.  This is read
  from the exact private minor type; it is not inferred from the source member
  order because specialised mimic motives need not have a source member key. -/
  motiveIndex : Nat
  /-- Position in the public minor's filtered dependent IH package. -/
  publicHypothesisPosition : Nat
  /-- Position in the implementation minor's filtered dependent IH package. -/
  implementationHypothesisPosition : Nat
  deriving Inhabited, BEq, Repr

/-- Kernel-checked congruence of one exact installed recursor minor across its
keyed induction-hypothesis binders. `transportedHypotheses` is the deduplicated
literal binder sequence: several source occurrences may intentionally share
one IH. The installed iota names anchor the congruence to both sides of the
already shadow-validated private/public rule contract. -/
structure RuleCompatibilityCertificate where
  key : RuleKey
  minorIndex : Nat
  transportedHypotheses : Array Nat
  compatibility : Name
  implementationIota : Name
  implementationIotaType : Expr
  publicIota : Name
  publicIotaType : Expr
  deriving Inhabited, BEq, Repr

/-- A fresh constructor with the exact public constructor type, implemented by
encoding its complete source telescope, applying the checked private
constructor, and decoding the owning family member. -/
structure PublicConstructorCertificate where
  key : ConstructorKey
  adapter : Name
  exactType : Expr
  implementationConstructor : Name
  telescope : TelescopeCertificate
  ownerMaps : EquivalenceCertificate
  deriving Inhabited, BEq, Repr

/-- One exact minor constructor in an installed recursor telescope.  Nested
recursors also bind minors for specialised mimic members, so this key is the
literal recursor owner/index/name association rather than a source-constructor
key.  `adapter` has the source-specialised constructor type used by the public
recursor wrapper. -/
structure PublicMinorConstructorCertificate where
  recursor : MemberKey
  minorIndex : Nat
  publicConstructor : Name
  implementationConstructor : Name
  adapter : Name
  exactType : Expr
  fieldArity : Nat
  deriving Inhabited, BEq, Repr

/-- One literal motive slot in an installed recursor telescope.  Mimic motives
need not correspond to a source `MemberKey`, so the exact public/private
carrier heads are retained under the recursor/index key. -/
structure PublicRecursorMotiveCertificate where
  recursor : MemberKey
  motiveIndex : Nat
  publicCarrier : Name
  implementationCarrier : Name
  deriving Inhabited, BEq, Repr

/-- A fresh recursor with the exact public recursor type. `motives` and
`rules` are the literal keyed sequences consumed while wrapping the installed
private recursor; neither sequence is inferred from a cardinality. -/
structure PublicRecursorCertificate where
  member : MemberKey
  adapter : Name
  exactType : Expr
  implementationRecursor : Name
  /-- Kernel-checked equality between one exact fresh recursor call at the
  backward image of a private major and the installed private call under the
  paired finite prefix. -/
  callAgreement : Name
  motives : Array PublicRecursorMotiveCertificate
  minors : Array PublicMinorConstructorCertificate
  rules : Array RuleKey
  deriving Inhabited, BEq, Repr

/-- Exact paired recursor call at one installed IH slot.  The enclosing rule
supplies the owner while both literal recursor names are retained independently;
neither side is inferred from an array position or a spelling classifier. -/
structure PublicIotaRecursiveCallRole where
  publicRecursor : Name
  implementationRecursor : Name
  /-- Direct family member when the exact name pair names one.  Specialised
  mimic calls deliberately remain keyed by their independent name pair. -/
  member? : Option MemberKey
  deriving Inhabited, BEq, Repr

/-- One distinct installed IH binder in the deterministic public-iota proof.
Several source occurrences may share the binder, but its motive slot and map
boundary are literal installed metadata. -/
structure PublicIotaHypothesisStep where
  rule : RuleKey
  minorIndex : Nat
  publicBinderIndex : Nat
  publicMotiveIndex : Nat
  binderIndex : Nat
  motiveIndex : Nat
  publicHypothesisPosition : Nat
  implementationHypothesisPosition : Nat
  recursiveCall? : Option PublicIotaRecursiveCallRole
  occurrences : Array OccurrenceKey
  maps : EquivalenceCertificate
  deriving Inhabited, BEq, Repr

/-- One literal argument position of the installed recursor application whose
rule metadata supplies an iota step.  The vector is derived from the exact
installed constant telescope; no constructor field count is substituted for
these roles. -/
inductive InstalledIotaBinderRole where
  | recursorPrefix (position : Nat)
  | resultIndex (position : Nat)
  | major
  deriving Inhabited, BEq, Repr

/-- Exact inputs to one public-iota proof chain.  The constructor-major
roundtrip, private iota, dependent telescope roundtrip, grouped IH agreements,
and minor congruence are composed in this mathematical order.  The arrays are
source/installed-derived finite sequences, never supported-arity cases. -/
structure PublicIotaProofSchema where
  key : RuleKey
  owner : MemberKey
  constructor : ConstructorKey
  ownerMaps : EquivalenceCertificate
  telescope : TelescopeCertificate
  implementationIota : Name
  implementationIotaInputs : Array InstalledIotaBinderRole
  minorCompatibility : Name
  hypotheses : Array PublicIotaHypothesisStep
  deriving Inhabited, BEq, Repr

/-- One source-shaped iota theorem for the fresh public constructor/recursor
pair. The proof may enter the private rule only through the exact installed
iota and the already checked finite-minor compatibility theorem. -/
structure PublicIotaCertificate where
  key : RuleKey
  adapter : Name
  exactType : Expr
  implementationIota : Name
  constructorAdapter : Name
  recursorAdapter : Name
  minorCompatibility : Name
  schema : PublicIotaProofSchema
  deriving Inhabited, BEq, Repr

/-- Atomic disabled-prototype public boundary. It exists only when every exact
member, constructor and rule has a checked declaration. -/
structure PublicAdapterCertificate where
  constructors : Array PublicConstructorCertificate
  recursors : Array PublicRecursorCertificate
  iotas : Array PublicIotaCertificate
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
  deriving Inhabited, BEq, Repr

/-- Source and implementation views of one recursive occurrence. -/
structure OccurrencePlan where
  key : OccurrenceKey
  sourceType : Expr
  implementationType : Expr
  deriving Inhabited, BEq, Repr

/-- Installed container/mimic equivalence assigned to one exact source
occurrence. The named implementation carrier binds its codomain to the private
mimic rather than trusting an otherwise self-consistent function type. Several
occurrences in one field may intentionally carry the same four declarations;
the occurrence key, not an array offset, is authoritative. -/
structure ContainerMapPlan where
  key : OccurrenceKey
  parameterArity : Nat
  indexArity : Nat
  implementationCarrier : Name
  sourceRecursor : Name
  implementationRecursor : Name
  sourceRecursorType : Expr
  implementationRecursorType : Expr
  recursorRuleKeys : Array (Name × Name)
  maps : EquivalenceCertificate
  forwardType : Expr
  backwardType : Expr
  backwardForwardType : Expr
  forwardBackwardType : Expr
  implementationCarrierType : Expr
  deriving Inhabited, BEq, Repr

/-- One exact public rule and its private proof oracle.  Occurrences are keyed
to minor hypotheses rather than accepted by a count comparison. -/
structure RulePlan where
  key : RuleKey
  ruleIndex : Nat
  exactRhs : Expr
  /-- Exact installed computation RHS on the public/source interface. -/
  publicRhs : Expr
  /-- Exact installed computation RHS on the private implementation. -/
  implementationRhs : Expr
  implementationIota : Name
  publicIota : Name
  implementationIotaType : Expr
  publicIotaType : Expr
  occurrences : Array OccurrenceKey := #[]
  deriving Inhabited, BEq, Repr

/-- Declaration-backed maps for a member correspondence. -/
structure MemberCertificate where
  key : MemberKey
  maps : EquivalenceCertificate
  deriving Inhabited, BEq, Repr

/-- Maps for one recursive occurrence.  For a direct family edge these are the
target member's maps.  For a nested edge they may be the generated
`G(P) <-> G(M)` maps, composed later with the existing mimic pack/unpack laws. -/
structure OccurrenceCertificate where
  key : OccurrenceKey
  maps : EquivalenceCertificate
  deriving Inhabited, BEq, Repr

/-- Proof evidence emitted only after a complete source-derived plan exists.
The shadow seam derives [`FamilyAdapterPlan`] without fabricating these names. -/
structure FamilyAdapterCertificate where
  members : Array MemberCertificate
  telescopes : Array TelescopeCertificate
  occurrences : Array OccurrenceCertificate
  minorHypotheses : Array MinorHypothesisCertificate
  rules : Array RuleCompatibilityCertificate
  publicAdapter? : Option PublicAdapterCertificate := none
  deriving Inhabited, BEq, Repr

/-- Complete finite plan for a single private/public family boundary. -/
structure FamilyAdapterPlan where
  root : MemberKey
  levelParams : List Name
  components : Array ComponentPlan
  members : Array MemberPlan
  constructors : Array ConstructorPlan
  rules : Array RulePlan
  occurrences : Array OccurrencePlan
  containerMaps : Array ContainerMapPlan := #[]
  support : Array Name := #[]
  deriving Inhabited, BEq, Repr

/-- Structural errors in a source-derived plan. Semantic checks against exact
source and installed metadata belong to the shadow or future generator. -/
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
  | constructorParameterArityMismatch (constructor : ConstructorKey)
      (expected actual : Nat)
  | constructorIndexArityMismatch (constructor : ConstructorKey)
      (expected source implementation : Nat)
  | duplicateRule (key : RuleKey)
  | memberRuleMismatch (member : MemberKey) (rule : RuleKey)
  | memberRuleSequenceMismatch (member : MemberKey)
  | unknownRuleOwner (key : RuleKey)
  | unknownRuleConstructor (key : RuleKey)
  | duplicateOccurrence (key : OccurrenceKey)
  | duplicateContainerMap (key : OccurrenceKey)
  | unknownContainerMapOccurrence (key : OccurrenceKey)
  | unknownOccurrenceConstructor (key : OccurrenceKey)
  | unknownOccurrenceTarget (key : OccurrenceKey)
  | occurrenceFieldOutOfBounds (key : OccurrenceKey) (fields : Nat)
  | occurrenceTelescopeMultiplicity (key : OccurrenceKey) (count : Nat)
  | telescopeConstructorMismatch (expected actual : ConstructorKey)
  | telescopeFieldOrder (constructor : ConstructorKey) (expected actual : Nat)
  | telescopeOccurrenceMismatch (key : OccurrenceKey)
  | ruleOccurrenceMismatch (key : OccurrenceKey)
  | ruleOccurrenceSequenceMismatch (rule : RuleKey)
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
    -- Partition coverage for one member identity, not a bound on component or
    -- family cardinality.
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
    if let some owner := plan.members.find? (·.key == constructor.key.owner) then
      unless owner.constructors.contains constructor.key do
        errors := errors.push (.memberConstructorMismatch owner.key constructor.key)
      unless constructor.telescope.parameters.size == owner.parameterArity do
        errors := errors.push (.constructorParameterArityMismatch constructor.key
          owner.parameterArity constructor.telescope.parameters.size)
      unless constructor.telescope.sourceResultIndices.size == owner.indexArity &&
          constructor.telescope.implementationResultIndices.size == owner.indexArity do
        errors := errors.push (.constructorIndexArityMismatch constructor.key owner.indexArity
          constructor.telescope.sourceResultIndices.size
          constructor.telescope.implementationResultIndices.size)
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
    if let some rule := duplicateKey? member.sourceRules then
      errors := errors.push (.memberRuleMismatch member.key rule)
    for rule in member.sourceRules do
      unless rule.recursorOwner == member.key && rule.recursor == member.sourceRecursor &&
          ruleExists plan rule do
        errors := errors.push (.memberRuleMismatch member.key rule)
    let installedRules := (plan.rules.filter (·.key.recursorOwner == member.key)).map (·.key)
    unless installedRules == member.sourceRules do
      errors := errors.push (.memberRuleSequenceMismatch member.key)

  if let some key := duplicateKey? (plan.rules.map (·.key)) then
    errors := errors.push (.duplicateRule key)
  for rule in plan.rules do
    unless memberExists plan rule.key.recursorOwner do
      errors := errors.push (.unknownRuleOwner rule.key)
    unless constructorExists plan rule.key.constructor do
      errors := errors.push (.unknownRuleConstructor rule.key)
    if let some owner := plan.members.find? (·.key == rule.key.recursorOwner) then
      unless owner.sourceRules.contains rule.key do
        errors := errors.push (.memberRuleMismatch owner.key rule.key)
    for key in rule.occurrences do
      unless key.constructor == rule.key.constructor do
        errors := errors.push (.ruleOccurrenceMismatch key)
    if let some telescope := telescopeFor? plan rule.key.constructor then
      unless rule.occurrences == telescopeOccurrences telescope do
        errors := errors.push (.ruleOccurrenceSequenceMismatch rule.key)

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

  if let some key := duplicateKey? (plan.containerMaps.map (·.key)) then
    errors := errors.push (.duplicateContainerMap key)
  for container in plan.containerMaps do
    unless plan.occurrences.any (·.key == container.key) do
      errors := errors.push (.unknownContainerMapOccurrence container.key)

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
