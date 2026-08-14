import InductiveModels.FamilyAdapterPlan

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
  | missingInstalledRecursor (member : MemberKey) (recursor : Name)
  | shortInstalledRecursorPrefix (member : MemberKey) (recursor : Name)
  | missingInstalledMinor (rule : RuleKey)
  | ambiguousInstalledMinor (rule : RuleKey)
  | malformedInstalledMinor (rule : RuleKey)
  | missingInstalledHypothesis (rule : RuleKey) (occurrence : OccurrenceKey)
  | ambiguousInstalledHypothesis (rule : RuleKey) (occurrence : OccurrenceKey)
  | installedHypothesisMismatch (rule : RuleKey) (occurrence : OccurrenceKey)
      (expected actual : Nat)
  | missingOccurrenceMap (occurrence : OccurrenceKey)
  | missingContainerMap (occurrence : OccurrenceKey)
  | dependentFieldTransport (constructor : ConstructorKey) (fieldIndex : Nat)
  | indexFibreMismatch (constructor : ConstructorKey)
  deriving Inhabited, BEq, Repr

private structure ExactBinder where
  type : Expr
  value : Expr
  deriving Inhabited

private partial def openExactForalls (tag : Name) (expression : Expr) :
    Array ExactBinder × Expr :=
  let rec loop (expression : Expr) (binders : Array ExactBinder) :=
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
      let mut fieldBinders : Array ExactBinder := #[]
      let mut malformed := false
      for field in fields do
        match binders.find? (·.value == field) with
        | some binder => fieldBinders := fieldBinders.push binder
        | none => malformed := true
      if malformed then
        issues := issues.push (.malformedInstalledMinor rule.key)
        continue
      let mut hypotheses : Array (Nat × ExactBinder) := #[]
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

end InductiveModels.FamilyAdapter
