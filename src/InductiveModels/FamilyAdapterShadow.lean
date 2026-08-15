import InductiveModels.FamilyAdapterPlan

/-!
# Shadow derivation of generic family-adapter plans

This module reads an exact source `EDecl` and an already kernel-checked `Iso`.
It derives the generic keyed plan and compares every public/private interface
name with installed metadata.  It does not select a route, emit a declaration,
or reject a model; callers retain the report only as shadow evidence.
-/

open Lean Meta

namespace InductiveModels.FamilyAdapter

inductive InterfaceSide where
  | privateModel
  | publicModel
  deriving Inhabited, BEq, Repr

/-- A source-keyed reason why one part of a shadow plan was not covered.  None
of these constructors classifies a family by a numeric bound or syntax route. -/
inductive ShadowReason where
  | sourceNotInductive
  | emptySourceFamily
  | missingSourceRecursor (member : MemberKey) (recursor : Name)
  | unrepresentedSourceRecursor (recursor : Name)
  | missingInterfaceMember (member : MemberKey) (side : InterfaceSide)
  | missingInterfaceRecursor (member : MemberKey) (side : InterfaceSide)
  | missingInterfaceConstructor (constructor : ConstructorKey) (side : InterfaceSide)
  | missingInterfaceRule (rule : RuleKey) (side : InterfaceSide)
  | missingInstalledDeclaration (name : Name) (side : InterfaceSide)
  | installedTypeMismatch (name : Name) (side : InterfaceSide)
  | installedRuleMismatch (rule : RuleKey) (side : InterfaceSide)
  | malformedConstructorTelescope (constructor : ConstructorKey)
  | malformedMinorTelescope (rule : RuleKey)
  | missingMinorHypothesis (constructor : ConstructorKey) (fieldIndex : Nat)
  | minorHypothesisMismatch (rule : RuleKey)
  | missingContainerMap (occurrence : OccurrenceKey)
  | ambiguousContainerMap (occurrence : OccurrenceKey)
  | missingInstalledContainerMap (occurrence : OccurrenceKey) (name : Name)
  | installedContainerMapTypeMismatch (occurrence : OccurrenceKey) (name : Name)
  | missingSourceContainerRecursor (occurrence : OccurrenceKey) (name : Name)
  | sourceContainerRecursorMismatch (occurrence : OccurrenceKey) (name : Name)
  | missingInstalledContainerRecursor (occurrence : OccurrenceKey) (name : Name)
  | installedContainerRecursorTypeMismatch (occurrence : OccurrenceKey) (name : Name)
  | installedContainerRecursorRulesMismatch (occurrence : OccurrenceKey) (name : Name)
  | invalidContainerRecursorAssociation (occurrence : OccurrenceKey)
  | unknownRuleConstructor (rule : RuleKey)
  | invalidPlan (error : PlanError)
  deriving Inhabited, BEq, Repr

/-- Successfully compared keys.  Absence from an array is accompanied by a
keyed [`ShadowReason`]. Occurrences have no declaration of their own; coverage
there means both exact source and rewritten implementation types were derived. -/
structure ShadowCoverage where
  members : Array MemberKey := #[]
  recursors : Array Name := #[]
  constructors : Array ConstructorKey := #[]
  rules : Array RuleKey := #[]
  occurrences : Array OccurrenceKey := #[]
  containerMaps : Array OccurrenceKey := #[]
  deriving Inhabited, BEq, Repr

structure ShadowReport where
  root : Name
  plan? : Option FamilyAdapterPlan
  coverage : ShadowCoverage := {}
  reasons : Array ShadowReason := #[]
  /-- Test-only exact evidence for a failed shadow comparison. Ordinary
  production callers discard the complete report and retain no diagnostics. -/
  diagnostics : Array String := #[]
  deriving Inhabited, BEq, Repr

def ShadowReport.complete (report : ShadowReport) : Bool :=
  report.plan?.isSome && report.reasons.isEmpty

def ShadowReport.summary (report : ShadowReport) : String :=
  s!"{report.root}: members {report.coverage.members.size}, recursors {
    report.coverage.recursors.size}, constructors {
    report.coverage.constructors.size}, rules {report.coverage.rules.size}, occurrences {
    report.coverage.occurrences.size}, container maps {
    report.coverage.containerMaps.size}, reasons {report.reasons.size}"

/-- Test-facing, value-only evidence retained after the full source-derived
plan has validated and been discarded. Production filtering does not collect
these observations. -/
structure ShadowObservation where
  root : Name
  coverage : ShadowCoverage
  reasons : Array ShadowReason
  diagnostics : Array String := #[]
  deriving Inhabited, BEq, Repr

def ShadowReport.observe (report : ShadowReport) : ShadowObservation :=
  { root := report.root, coverage := report.coverage, reasons := report.reasons,
    diagnostics := report.diagnostics }

def ShadowObservation.complete (observation : ShadowObservation) : Bool :=
  observation.reasons.isEmpty

private structure SourceBinder where
  info : BinderInfo
  type : Expr
  deriving Inhabited, BEq, Repr

private structure ExactBinder where
  type : Expr
  value : Expr
  deriving Inhabited

private structure OccurrenceSite where
  fieldIndex : Nat
  path : Array ExprPathStep
  binderDepth : Nat
  target : MemberKey
  type : Expr
  deriving Inhabited, BEq, Repr

private structure ResolvedMember where
  index : Nat
  source : EIndType
  key : MemberKey
  sourceRecursor? : Option ERec
  implementationCarrier : Name
  publicCarrier : Name
  implementationRecursor : Name
  publicRecursor : Name
  representation : MemberRepresentation
  deriving Inhabited

private structure ResolvedConstructor where
  source : ECtor
  key : ConstructorKey
  implementationName : Name
  publicName : Name
  deriving Inhabited

private def memberKeyFor (name : Name) : MemberKey := { owner := name }

private def constructorOwner? (members : Array ResolvedMember) (constructor : ECtor) :
    Option ResolvedMember :=
  members.find? (·.source.name == constructor.induct)

private def targetOf? (pairs : Array (Name × Name)) (source : Name) : Option Name :=
  pairs.find? (·.1 == source) |>.map (·.2)

private def familyMember? (iso : Iso) (owner : Name) : Option IsoFamilyMember :=
  iso.familyImplementation?.bind fun family => family.members.find? (·.owner == owner)

private def interfaceMemberName? (values : Array Name) (index : Nat) : Option Name :=
  values[index]?

private def sourceRecursorFor? (all : Array Name) (recursors : Array ERec)
    (index : Nat) : Option ERec :=
  recursors.find? (·.name == exportRecName all index)

private def rewriteWith (mapping : Array (Name × Name)) (expression : Expr) : Expr :=
  mapConstsE (fun name => targetOf? mapping name) expression

private def openBinders (count : Nat) (expression : Expr) :
    Option (Array SourceBinder × Expr) := Id.run do
  let mut binders := #[]
  let mut body := expression
  for _ in [:count] do
    let .forallE _ type next info := body | return none
    binders := binders.push { info, type }
    body := next
  return some (binders, body)

private partial def openExactForalls (tag : Name) (expression : Expr) :
    Array ExactBinder × Expr :=
  let rec loop (expression : Expr) (binders : Array ExactBinder) :=
    match expression with
    | .forallE _ type body _ =>
      let value := mkFVar (FVarId.mk (tag.mkNum binders.size))
      loop (body.instantiate1 value) (binders.push { type, value })
    | body => (binders, body)
  loop expression #[]

/-- Exact minor-hypothesis position for every literal constructor field. A
field under binders is matched through the major argument of the motive
application, so several syntactic occurrences inside one nested field share
the one hypothesis Lean actually provides. -/
private def minorHypothesisIndices? (recursor : ERec) (ruleIndex : Nat) :
    Option (Array (Option Nat)) := do
  let rule ← recursor.rules[ruleIndex]?
  let (recBinders, _) := openExactForalls ((`_family_adapter_rec).append recursor.name)
    recursor.type
  let numPre := recursor.numParams + recursor.numMotives + recursor.numMinors
  unless recBinders.size >= numPre do none
  let motives := recBinders.extract recursor.numParams
    (recursor.numParams + recursor.numMotives) |>.map (·.value)
  let minors := recBinders.extract (recursor.numParams + recursor.numMotives) numPre
  minors.findSome? fun minor => do
    let (minorBinders, motiveResult) :=
      openExactForalls ((`_family_adapter_minor).append rule.ctor) minor.type
    let major ← motiveResult.getAppArgs.back?
    let .const constructor _ := major.getAppFn | none
    unless constructor == rule.ctor do none
    let majorArgs := major.getAppArgs
    unless majorArgs.size >= rule.nfields do none
    let fieldValues := majorArgs.extract (majorArgs.size - rule.nfields) majorArgs.size
    let mut fields : Array ExactBinder := #[]
    for value in fieldValues do
      let binder ← minorBinders.find? (·.value == value)
      fields := fields.push binder
    let mut hypotheses : Array ExactBinder := #[]
    for binder in minorBinders do
      if fields.any (·.value == binder.value) then continue
      let (_, body) := openExactForalls (`_family_adapter_hypothesis) binder.type
      if motives.contains body.getAppFn then hypotheses := hypotheses.push binder
    let mut result : Array (Option Nat) := #[]
    for field in fields do
      let candidates := hypotheses.filter fun hypothesis =>
        let (_, body) := openExactForalls (`_family_adapter_hypothesis_body) hypothesis.type
        (body.getAppArgs.back?.map (·.getAppFn == field.value)).getD false
      if candidates.size > 1 then none
      result := result.push (candidates[0]?.bind fun candidate =>
        hypotheses.findIdx? (·.value == candidate.value))
    return result

/-- Literal binder position and IH ordinal for one occurrence in one exact
installed recursor minor.  These are deliberately returned separately: only
the ordinal groups occurrences, while the binder position indexes an iota RHS
application. -/
private def installedMinorHypothesisPosition? (parameterArity motiveArity minorArity : Nat)
    (recursorType : Expr) (constructorName : Name) (fieldCount : Nat)
    (occurrence : OccurrenceKey) : Option (Nat × Nat) := do
  let (recursorBinders, _) := openExactForalls
    ((`_family_adapter_shadow_installed_rec).append constructorName) recursorType
  let prefixSize := parameterArity + motiveArity + minorArity
  unless recursorBinders.size >= prefixSize do none
  let motives := recursorBinders.extract parameterArity
    (parameterArity + motiveArity) |>.map (·.value)
  let minors := recursorBinders.extract (parameterArity + motiveArity) prefixSize
  let matching := minors.filterMap fun minor =>
    let (binders, result) := openExactForalls
      ((`_family_adapter_shadow_installed_minor).append constructorName) minor.type
    if (result.getAppArgs.back?.bind (·.getAppFn.constName?)) == some constructorName then
      some (binders, result)
    else none
  unless matching.size == 1 do none
  let (binders, result) := matching[0]!
  let major ← result.getAppArgs.back?
  let arguments := major.getAppArgs
  unless arguments.size >= fieldCount do none
  let fields := arguments.extract (arguments.size - fieldCount) arguments.size
  let field ← fields[occurrence.fieldIndex]?
  let mut hypotheses : Array (Nat × ExactBinder) := #[]
  for binderIndex in [:binders.size] do
    let binder := binders[binderIndex]!
    if fields.contains binder.value then continue
    let (_, body) := openExactForalls (`_family_adapter_shadow_installed_hypothesis)
      binder.type
    if motives.contains body.getAppFn then
      hypotheses := hypotheses.push (binderIndex, binder)
  let candidates := hypotheses.filter fun (_, hypothesis) =>
    let (_, body) := openExactForalls (`_family_adapter_shadow_installed_hypothesis_body)
      hypothesis.type
    (body.getAppArgs.back?.map (·.getAppFn == field)).getD false
  unless candidates.size == 1 do none
  let (binderIndex, _) := candidates[0]!
  let hypothesisIndex ← hypotheses.findIdx? (·.1 == binderIndex)
  unless hypothesisIndex == occurrence.hypothesisIndex do none
  return (binderIndex, hypothesisIndex)

private partial def occurrenceSites (targets : Array MemberKey)
    (fieldIndex : Nat) (expression : Expr) (path : Array ExprPathStep := #[])
    (binderDepth : Nat := 0) : Array OccurrenceSite :=
  if let some target := targets.find? fun target =>
      expression.getAppFn.constName? == some target.owner then
    #[{ fieldIndex, path, binderDepth, target, type := expression }]
  else
    match expression with
    | .app function argument =>
      occurrenceSites targets fieldIndex function (path.push .appFunction) binderDepth ++
        occurrenceSites targets fieldIndex argument (path.push .appArgument) binderDepth
    | .lam _ type body _ | .forallE _ type body _ =>
      occurrenceSites targets fieldIndex type (path.push .binderDomain) binderDepth ++
        occurrenceSites targets fieldIndex body (path.push .binderBody) (binderDepth + 1)
    | .letE _ type value body _ =>
      occurrenceSites targets fieldIndex type (path.push .letType) binderDepth ++
        occurrenceSites targets fieldIndex value (path.push .letValue) binderDepth ++
        occurrenceSites targets fieldIndex body (path.push .letBody) (binderDepth + 1)
    | .mdata _ body =>
      occurrenceSites targets fieldIndex body (path.push .metadataBody) binderDepth
    | .proj _ _ body =>
      occurrenceSites targets fieldIndex body (path.push .projectionBody) binderDepth
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => #[]

private def componentPlans (members : Array MemberKey) (occurrences : Array OccurrencePlan) :
    Array ComponentPlan := Id.run do
  let count := members.size
  let mut edges : Array (Array Bool) := Array.replicate count (Array.replicate count false)
  for occurrence in occurrences do
    let some source := members.findIdx? (· == occurrence.key.constructor.owner) | continue
    let some target := members.findIdx? (· == occurrence.key.target) | continue
    edges := edges.modify source (·.set! target true)
  let mut reachable := edges
  for index in [:count] do reachable := reachable.modify index (·.set! index true)
  for pivot in [:count] do
    for source in [:count] do
      if reachable[source]![pivot]! then
        for target in [:count] do
          if reachable[pivot]![target]! then
            reachable := reachable.modify source (·.set! target true)
  let mut seen := Array.replicate count false
  let mut groups : Array (Array Nat) := #[]
  for source in [:count] do
    unless seen[source]! do
      let mut group := #[]
      for target in [:count] do
        if !seen[target]! && reachable[source]![target]! && reachable[target]![source]! then
          group := group.push target
          seen := seen.set! target true
      groups := groups.push group
  let keys := groups.map fun group => ({ anchor := members[group[0]!]! } : ComponentKey)
  return groups.mapIdx fun groupIndex group =>
    let dependencies := (Array.range groups.size).filterMap fun targetGroup =>
      if targetGroup == groupIndex then none
      else if group.any fun source => groups[targetGroup]!.any fun target => edges[source]![target]!
      then some keys[targetGroup]!
      else none
    { key := keys[groupIndex]!, members := group.map (members[·]!), dependencies }

private def componentFor (components : Array ComponentPlan) (member : MemberKey) : ComponentKey :=
  (components.find? (·.members.contains member) |>.map (·.key)).getD { anchor := member }

private def installedType? (env : Environment) (name : Name) : Option Expr :=
  env.constants.find? name |>.map (·.type)

private partial def forallCount : Expr → Nat
  | .forallE _ _ body _ => forallCount body + 1
  | _ => 0

private def installedRuleEvidence? (env : Environment) (rule recursor constructor : Name) :
    MetaM (Option InstalledRuleEvidence) := do
  match env.constants.find? rule with
  | some (.recInfo information) =>
    unless rule == recursor do return none
    let some installedRule := information.rules.find? (·.ctor == constructor)
      | return none
    return some {
      representation := .recursorRule
      declarationType := information.type
      application := (Array.range (forallCount information.type)).map
        InstalledRuleBinderRole.recursorArgument
      semanticRhs := installedRule.rhs }
  | some (.thmInfo information) =>
    try
      forallTelescope information.type fun binders proposition => do
        let some (_, lhs, rhs) ← matchEq? proposition | return none
        unless lhs.getAppFn.constName? == some recursor do return none
        let some major := lhs.getAppArgs.back? | return none
        unless major.getAppFn.constName? == some constructor do return none
        let recursorArguments := lhs.getAppArgs
        let constructorArguments := major.getAppArgs
        let mut application := #[]
        for binder in binders do
          if let some position := recursorArguments.findIdx? (· == binder) then
            application := application.push (.recursorArgument position)
          else if let some position := constructorArguments.findIdx? (· == binder) then
            application := application.push (.constructorArgument position)
          else
            return none
        return some {
          representation := .equalityTheorem
          declarationType := information.type
          application
          semanticRhs := (← mkLambdaFVars binders rhs) }
    catch _ => return none
  | _ => return none

private partial def exactLambdaBody (tag : Name) (expression : Expr) : Expr :=
  match expression with
  | .lam _ _ body _ =>
    exactLambdaBody tag (body.instantiate1 (mkFVar (FVarId.mk tag)))
  | body => body

private def exactRuleArgumentHead? (tag : Name) (rhs : Expr) (position : Nat) : Option Name := do
  let argument ← (exactLambdaBody tag rhs).getAppArgs[position]?
  let head := exactLambdaBody (tag.mkNum position) argument |>.getAppFn
  head.constName?

private def addInstalledCoverage (env : Environment) (name : Name) (expected : Expr)
    (missing mismatch : ShadowReason)
    (reasons : Array ShadowReason) : Array ShadowReason × Bool :=
  match installedType? env name with
  | none => (reasons.push missing, false)
  | some actual =>
    if actual == expected then (reasons, true) else (reasons.push mismatch, false)

private def isContainerOccurrence (key : OccurrenceKey) : Bool :=
  key.expressionPath.any (· != .binderBody)

private structure ExactRecursorLayoutView where
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat

private def ExactRecursorLayoutView.ofSource
    (recursor : IsoSourceRecursor) : ExactRecursorLayoutView :=
  { numParams := recursor.numParams
    numIndices := recursor.numIndices
    numMotives := recursor.numMotives
    numMinors := recursor.numMinors }

private def recursorMajorMatches (recursor : ExactRecursorLayoutView) (recursorType : Expr)
    (parameters : Array Expr) (expected : Expr) : MetaM Bool := do
  let majorPosition :=
    recursor.numParams + recursor.numMotives + recursor.numMinors + recursor.numIndices
  if parameters.size != recursor.numParams || parameters.size > majorPosition then return false
  let mut type ← instantiateForall recursorType parameters
  for _ in [parameters.size:majorPosition] do
    let .forallE name domain body _ := type | return false
    let value ← mkFreshExprMVar domain .natural name
    type := body.instantiate1 value
  let .forallE _ domain _ _ := type | return false
  return ← isDefEq domain expected

private partial def matchExactIndexPattern (indices : Array FVarId)
    (pattern target : Expr) (assignments : Array (Option Expr)) :
    Option (Array (Option Expr)) :=
  if let .fvar id := pattern then
    match indices.findIdx? (· == id) with
    | some index =>
      match assignments[index]! with
      | some assigned => if assigned == target then some assignments else none
      | none => some (assignments.set! index (some target))
    | none => if pattern == target then some assignments else none
  else
    match pattern, target with
    | .app pf pa, .app tf ta => do
      let assignments ← matchExactIndexPattern indices pf tf assignments
      matchExactIndexPattern indices pa ta assignments
    | .lam pn pt pb pi, .lam tn tt tb ti
    | .forallE pn pt pb pi, .forallE tn tt tb ti => do
      unless pn == tn && pi == ti do none
      let assignments ← matchExactIndexPattern indices pt tt assignments
      matchExactIndexPattern indices pb tb assignments
    | .letE pn pt pv pb pnondep, .letE tn tt tv tb tnondep => do
      unless pn == tn && pnondep == tnondep do none
      let assignments ← matchExactIndexPattern indices pt tt assignments
      let assignments ← matchExactIndexPattern indices pv tv assignments
      matchExactIndexPattern indices pb tb assignments
    | .mdata pm pb, .mdata tm tb => do
      unless pm == tm do none
      matchExactIndexPattern indices pb tb assignments
    | .proj pn pi pb, .proj tn ti tb => do
      unless pn == tn && pi == ti do none
      matchExactIndexPattern indices pb tb assignments
    | _, _ => if pattern == target then some assignments else none

/-- Compare the exact source recursor major with a live source occurrence
without asking the environment to unfold the not-yet-installed source owner.
Only the literal index binders are pattern variables. -/
private def exactSourceRecursorMajorMatches (recursor : ExactRecursorLayoutView)
    (recursorType : Expr) (parameters : Array Expr) (expected : Expr) : MetaM Bool := do
  unless parameters.size == recursor.numParams do return false
  let type ← instantiateForall recursorType parameters
  let remaining := recursor.numMotives + recursor.numMinors + recursor.numIndices + 1
  forallBoundedTelescope type (some remaining) fun binders _ => do
    let indexStart := recursor.numMotives + recursor.numMinors
    let indices := binders.extract indexStart (indexStart + recursor.numIndices)
    let some major := binders[remaining - 1]? | return false
    let pattern ← inferType major
    let indexIds := indices.map (·.fvarId!)
    return (matchExactIndexPattern indexIds pattern expected
      (Array.replicate indexIds.size none)).isSome

private def ExactRecursorLayoutView.ofInstalled
    (recursor : RecursorVal) : ExactRecursorLayoutView :=
  { numParams := recursor.numParams
    numIndices := recursor.numIndices
    numMotives := recursor.numMotives
    numMinors := recursor.numMinors }

private def recursorMajorFamily? (recursor : ExactRecursorLayoutView) (recursorType : Expr)
    (parameterArity indexArity : Nat) : MetaM (Option (Expr × Nat)) := do
  unless recursor.numParams == parameterArity && recursor.numIndices == indexArity do
    return none
  let majorPosition :=
    recursor.numParams + recursor.numMotives + recursor.numMinors + recursor.numIndices
  forallBoundedTelescope recursorType (some (majorPosition + 1)) fun binders result => do
    let some major := binders[majorPosition]? | return none
    let parameters := binders.extract 0 parameterArity
    let indexStart := recursor.numParams + recursor.numMotives + recursor.numMinors
    let indices := binders.extract indexStart (indexStart + indexArity)
    let family ← mkLambdaFVars (parameters ++ indices) (← inferType major)
    if family.hasFVar then return none
    let motives := binders.extract recursor.numParams
      (recursor.numParams + recursor.numMotives)
    let some resultMotiveIndex := motives.findIdx? (· == result.getAppFn)
      | return none
    return some (family, resultMotiveIndex)

private def closedFamilyBinderRoles? (family expected : Expr)
    (binders : Array ExactBinder) : MetaM (Option (Array Nat)) := do
  let rec lambdaCount : Expr → Nat
    | .lam _ _ body _ => lambdaCount body + 1
    | _ => 0
  let rec instantiate (remaining : Nat) (expression : Expr)
      (arguments : Array Expr) : MetaM (Option (Array Expr)) := do
    match remaining with
    | remaining + 1 =>
      let .lam name domain body _ := expression | return none
      let argument ← mkFreshExprMVar domain .natural name
      instantiate remaining (body.instantiate1 argument) (arguments.push argument)
    | 0 =>
      unless ← isDefEq expression expected do return none
      let resolved ← arguments.mapM instantiateMVars
      for argument in resolved do if ← hasAssignableMVar argument then return none
      return some resolved
  let some arguments ← instantiate (lambdaCount family) family #[] | return none
  let mut positions := #[]
  for argument in arguments do
    let matchingBinders := (binders.mapIdx fun index binder => (index, binder.value))
      |>.filter (fun (_, value) => value == argument)
    unless matchingBinders.size == 1 do return none
    positions := positions.push matchingBinders[0]!.1
  for position in positions do
    unless (positions.filter (· == position)).size == 1 do return none
  return some positions

private def endpointApplicationPlan? (sourceFamily targetFamily exactType : Expr)
    (law : Bool) : MetaM (Option CarrierEndpointApplicationPlan) := do
  forallTelescope exactType fun values result => do
    let binders ← values.mapM fun value => return ({ type := (← inferType value), value } : ExactBinder)
    let mut candidates : Array CarrierEndpointApplicationPlan := #[]
    for valueIndex in [:binders.size] do
      let candidate? ← withoutModifyingState do
        let value := binders[valueIndex]!
        let some familyPositions ← closedFamilyBinderRoles? sourceFamily value.type binders
          | return none
        unless binders.size == familyPositions.size + 1 &&
            !familyPositions.contains valueIndex do return none
        let familyArguments := familyPositions.map (binders[·]!.value)
        let target := mkAppN targetFamily familyArguments
        if law then
          let some (carrier, _, right) ← matchEq? result | return none
          unless ← isDefEq carrier value.type do return none
          unless ← isDefEq right value.value do return none
        else
          unless ← isDefEq result target do return none
        let mut roles : Array CarrierEndpointBinderRole := #[]
        for binderIndex in [:binders.size] do
          if binderIndex == valueIndex then
            roles := roles.push CarrierEndpointBinderRole.value
          else if let some familyIndex := familyPositions.findIdx? (· == binderIndex) then
            roles := roles.push (CarrierEndpointBinderRole.familyArgument familyIndex)
          else
            return none
        return some ({ exactType, binders := roles } : CarrierEndpointApplicationPlan)
      if let some candidate := candidate? then candidates := candidates.push candidate
    unless candidates.size == 1 do return none
    return candidates[0]?

private def installedBoundaryPlan? (maps : EquivalenceCertificate)
    (publicFamily implementationFamily forwardType backwardType backwardForwardType
      forwardBackwardType : Expr) : MetaM (Option ContainerRecursorBoundaryPlan) := do
  let some forward ← endpointApplicationPlan? publicFamily implementationFamily forwardType false
    | return none
  let some backward ← endpointApplicationPlan? implementationFamily publicFamily backwardType false
    | return none
  let some backwardForward ← endpointApplicationPlan? publicFamily implementationFamily
      backwardForwardType true | return none
  let some forwardBackward ← endpointApplicationPlan? implementationFamily publicFamily
      forwardBackwardType true | return none
  return some (.installed { maps, forward, backward, backwardForward, forwardBackward })

private def emittedWrapperType? (declarations : Array Declaration) (name : Name) : Option Expr :=
  let wrapperMatches := declarations.filterMap fun declaration => match declaration with
    | .defnDecl value => if value.name == name then some value.type else none
    | _ => none
  if wrapperMatches.size == 1 then wrapperMatches[0]? else none

private def emittedWrapperDiagnostics (aliases : Naming.AliasMap)
    (declarations : Array Declaration) (logicalName : Name) (logicalType : Expr) : Array String :=
  let exactName := aliases.exact logicalName
  let candidates := declarations.flatMap fun declaration => match declaration with
    | .axiomDecl value => #[("axiom", value.name, value.type)]
    | .defnDecl value => #[("definition", value.name, value.type)]
    | .thmDecl value => #[("theorem", value.name, value.type)]
    | .opaqueDecl value => #[("opaque", value.name, value.type)]
    | _ => #[]
  let related := candidates.filter fun (_, rawName, _) =>
    rawName == logicalName || aliases.exact rawName == exactName
  #[s!"wrapper logical={logicalName}, exact={exactName}, type={repr logicalType}"] ++
    related.map fun (kind, rawName, type) =>
      s!"wrapper candidate kind={kind}, raw={rawName}, exact={aliases.exact rawName}, type={repr type}"

private def recursorMajorDiagnostic (label : String) (recursor : ExactRecursorLayoutView)
    (recursorType : Expr) (parameters : Array Expr) (expected : Expr) : MetaM String := do
  let majorPosition :=
    recursor.numParams + recursor.numMotives + recursor.numMinors + recursor.numIndices
  if parameters.size != recursor.numParams then
    return s!"{label}: parameter count actual={parameters.size}, expected={recursor.numParams}"
  let mut type ← instantiateForall recursorType parameters
  for _ in [parameters.size:majorPosition] do
    let .forallE name domain body _ := type
      | return s!"{label}: missing binder before major in {repr type}"
    let value ← mkFreshExprMVar domain .natural name
    type := body.instantiate1 value
  let .forallE _ actual _ _ := type
    | return s!"{label}: missing major binder in {repr type}"
  return s!"{label}: actualHead={repr actual.getAppFn.constName?}, \
    expectedHead={repr expected.getAppFn.constName?}, actual={repr actual}, expected={repr expected}"

private def sourceRecursorMajorDiagnostic (label : String)
    (recursor : ExactRecursorLayoutView) (recursorType : Expr)
    (parameters : Array Expr) (expected : Expr) : MetaM String := do
  if parameters.size != recursor.numParams then
    return s!"{label}: parameter count actual={parameters.size}, expected={recursor.numParams}"
  let type ← instantiateForall recursorType parameters
  let remaining := recursor.numMotives + recursor.numMinors + recursor.numIndices + 1
  forallBoundedTelescope type (some remaining) fun binders _ => do
    let some major := binders[remaining - 1]?
      | return s!"{label}: missing source major in {repr type}"
    let actual ← inferType major
    return s!"{label}: actualHead={repr actual.getAppFn.constName?}, \
      expectedHead={repr expected.getAppFn.constName?}, actual={repr actual}, expected={repr expected}"

/-- Source-side representation is settled before maps or the callable wrapper
are considered.  This is the exact boundary used by the source-recursors
census: later interface failures must not turn a represented recursor into an
apparently absent one. -/
private def validatedContainerSourceRecursor? (environment : Environment)
    (sourceRecursors : Array ERec) (semanticMapping : Array (Name × Name))
    (container : IsoContainerImplementation) : Option Name := do
  let sourceMatches := sourceRecursors.filter (·.name == container.sourceRecursor)
  if sourceMatches.size != 1 then none else
  let exact := IsoSourceRecursor.ofERec sourceMatches[0]!
  if exact != container.sourceRecursorEvidence || exact.name != container.sourceRecursor ||
      exact.type != container.sourceRecursorType then none else
  let some (.recInfo implementation) := environment.constants.find? container.implementationRecursor
    | none
  if implementation.type != container.implementationRecursorType ||
      exact.rules.size != container.recursorRuleKeys.size ||
      implementation.rules.length != container.recursorRuleKeys.size then none else
  if rewriteWith semanticMapping (.const container.sourceRecursor []) !=
      .const container.implementationRecursor [] then none else
  if (Array.range container.recursorRuleKeys.size).all fun index =>
      let sourceRule := exact.rules[index]!
      let implementationRule := implementation.rules[index]!
      let pair := container.recursorRuleKeys[index]!
      pair.1 == sourceRule.ctor && pair.2 == implementationRule.ctor &&
        rewriteWith semanticMapping (.const pair.1 []) == .const pair.2 [] &&
        sourceRule.nfields == implementationRule.nfields then
    some container.sourceRecursor
  else none

private def containerMetadataInstalled (environment : Environment)
    (aliases : Naming.AliasMap) (declarations : Array Declaration)
    (sourceRecursors : Array ERec) (semanticMapping : Array (Name × Name))
    (sourceParameters implementationParameters : Array Expr)
    (sourceType implementationType : Expr)
    (occurrence : OccurrenceKey) (container : IsoContainerImplementation) :
    MetaM (Array ShadowReason × Array String) := do
  let mut reasons := #[]
  let mut diagnostics := #[]
  for (name, expected) in #[(container.forward, container.forwardType),
      (container.backward, container.backwardType),
      (container.backwardForward, container.backwardForwardType),
      (container.forwardBackward, container.forwardBackwardType),
      (container.implementationCarrier, container.implementationCarrierType)] do
    match installedType? environment name with
    | none => reasons := reasons.push (.missingInstalledContainerMap occurrence name)
    | some actual => unless actual == expected do
        reasons := reasons.push (.installedContainerMapTypeMismatch occurrence name)
  let sourceMatches := sourceRecursors.filter (·.name == container.sourceRecursor)
  if sourceMatches.size != 1 then
    reasons := reasons.push (.missingSourceContainerRecursor occurrence container.sourceRecursor)
  else
    let exact := IsoSourceRecursor.ofERec sourceMatches[0]!
    unless exact == container.sourceRecursorEvidence &&
        exact.name == container.sourceRecursor && exact.type == container.sourceRecursorType &&
        exact.rules.map (·.ctor) == container.recursorRuleKeys.map (·.1) do
      reasons := reasons.push (.sourceContainerRecursorMismatch occurrence container.sourceRecursor)
    unless rewriteWith semanticMapping (.const exact.name []) ==
        .const container.implementationRecursor [] &&
        container.recursorRuleKeys.all fun pair =>
          rewriteWith semanticMapping (.const pair.1 []) == .const pair.2 [] do
      reasons := reasons.push (.sourceContainerRecursorMismatch occurrence container.sourceRecursor)
    unless ← exactSourceRecursorMajorMatches (ExactRecursorLayoutView.ofSource exact)
        exact.type sourceParameters sourceType do
      reasons := reasons.push (.invalidContainerRecursorAssociation occurrence)
      diagnostics := diagnostics.push (← sourceRecursorMajorDiagnostic
        "source-major" (ExactRecursorLayoutView.ofSource exact) exact.type sourceParameters
          sourceType)
  let name := container.implementationRecursor
  match environment.constants.find? name with
  | none => reasons := reasons.push (.missingInstalledContainerRecursor occurrence name)
  | some information =>
    unless information.type == container.implementationRecursorType do
      reasons := reasons.push (.installedContainerRecursorTypeMismatch occurrence name)
    match information with
    | .recInfo recursor =>
      unless recursor.rules.toArray.map (·.ctor) == container.recursorRuleKeys.map (·.2) do
        reasons := reasons.push (.installedContainerRecursorRulesMismatch occurrence name)
      unless ← recursorMajorMatches (ExactRecursorLayoutView.ofInstalled recursor)
          container.implementationRecursorType implementationParameters implementationType do
        reasons := reasons.push (.invalidContainerRecursorAssociation occurrence)
        diagnostics := diagnostics.push (← recursorMajorDiagnostic
          "implementation-major" (ExactRecursorLayoutView.ofInstalled recursor)
          container.implementationRecursorType implementationParameters implementationType)
    | _ => reasons := reasons.push (.installedContainerRecursorRulesMismatch occurrence name)
  if let some exactType := emittedWrapperType? declarations
      container.implementationRecursorWrapper then
    unless exactType == container.implementationRecursorWrapperType do
      reasons := reasons.push (.installedContainerRecursorTypeMismatch occurrence
        container.implementationRecursorWrapper)
  else
    reasons := reasons.push
      (.missingInstalledContainerRecursor occurrence container.implementationRecursorWrapper)
    diagnostics := diagnostics ++ emittedWrapperDiagnostics aliases declarations
      container.implementationRecursorWrapper container.implementationRecursorWrapperType
  return (reasons, diagnostics)

private def containerTarget? (container : IsoContainerImplementation)
    (parameters : Array Expr) (sourceType : Expr) : MetaM (Option Expr) := do
  unless parameters.size == container.parameterArity do return none
  let mut type ← instantiateForall container.forwardType parameters
  for _ in [:container.indexArity] do
    let .forallE name domain body _ := type | return none
    let index ← mkFreshExprMVar domain .natural name
    type := body.instantiate1 index
  let .forallE _ domain target _ := type | return none
  unless ← isDefEq domain sourceType do return none
  let target ← instantiateMVars target
  if ← hasAssignableMVar target then return none
  unless target.getAppFn.constName? == some container.implementationCarrier do return none
  return some target

private partial def withBinderBody (type : Expr) (depth : Nat)
    (k : Expr → MetaM α) : MetaM α := do
  if depth == 0 then return ← k type
  let .forallE name domain body info := type
    | return ← k type
  withLocalDecl name info domain fun value =>
    withBinderBody (body.instantiate1 value) (depth - 1) k

private def implementationIota? (iso : Iso) (member : ResolvedMember)
    (constructor : Name) : Option Name :=
  if let some familyMember := familyMember? iso member.source.name then
    familyMember.privateIotas.find? (fun (_, key, _) => key == constructor) |>.map (·.2.2)
  else
    iso.implementationInterface.iotas.find?
      (fun (ownerIndex, key, _) => ownerIndex == member.index && key == constructor) |>.map (·.2.2)

private def publicIota? (iso : Iso) (member : ResolvedMember)
    (constructor : Name) : Option Name :=
  iso.publicInterface.iotas.find?
    (fun (ownerIndex, key, _) => ownerIndex == member.index && key == constructor) |>.map (·.2.2)

/-- Derive and shadow-check a generic adapter plan.  The function deliberately
returns reasons rather than throwing: existing generation remains authoritative
until the generic certificate is complete and explicitly enabled. -/
def deriveShadowPlan (source : EDecl) (iso : Iso) : MetaM ShadowReport := do
  let .induct sourceTypesList sourceConstructorsList sourceRecursorsList := source
    | return { root := source.names.head?.getD .anonymous
               plan? := none
               coverage := {}
               reasons := #[.sourceNotInductive] }
  let sourceTypes := sourceTypesList.toArray
  let sourceConstructors := sourceConstructorsList.toArray
  let sourceRecursors := sourceRecursorsList.toArray
  let some firstType := sourceTypes[0]?
    | return { root := .anonymous
               plan? := none
               coverage := {}
               reasons := #[.emptySourceFamily] }
  let all := sourceTypes.map (·.name)
  let publicInterface := iso.publicInterface
  let implementationInterface := iso.implementationInterface
  let mut reasons := #[]
  let mut diagnostics := #[]
  let mut resolvedMembers : Array ResolvedMember := #[]

  for index in [:sourceTypes.size] do
    let sourceType := sourceTypes[index]!
    let key := memberKeyFor sourceType.name
    let sourceRecursor? := sourceRecursorFor? all sourceRecursors index
    if sourceRecursor?.isNone then
      reasons := reasons.push (.missingSourceRecursor key (exportRecName all index))
    let publicCarrier := (interfaceMemberName? publicInterface.selfNames index).getD .anonymous
    if publicCarrier.isAnonymous then
      reasons := reasons.push (.missingInterfaceMember key .publicModel)
    let familyMember := familyMember? iso sourceType.name
    let implementationCarrier := (familyMember.map (·.privateSelf)).orElse
      (fun _ => interfaceMemberName? implementationInterface.selfNames index) |>.getD .anonymous
    if implementationCarrier.isAnonymous then
      reasons := reasons.push (.missingInterfaceMember key .privateModel)
    let publicRecursor := (interfaceMemberName? publicInterface.recs index).getD .anonymous
    if publicRecursor.isAnonymous then
      reasons := reasons.push (.missingInterfaceRecursor key .publicModel)
    let implementationRecursor := (familyMember.map (·.privateRecursor)).orElse
      (fun _ => interfaceMemberName? implementationInterface.recs index) |>.getD .anonymous
    if implementationRecursor.isAnonymous then
      reasons := reasons.push (.missingInterfaceRecursor key .privateModel)
    let representation := match familyMember with
      | some member => if member.changed then .layer else .identity
      | none => if implementationCarrier == publicCarrier then .identity else .layer
    resolvedMembers := resolvedMembers.push
      { index, source := sourceType, key, sourceRecursor?, implementationCarrier,
        publicCarrier, implementationRecursor, publicRecursor, representation }

  let mut resolvedConstructors : Array ResolvedConstructor := #[]
  for constructor in sourceConstructors do
    let some owner := constructorOwner? resolvedMembers constructor | continue
    let key : ConstructorKey := { owner := owner.key, constructor := constructor.name }
    let familyMember := familyMember? iso owner.source.name
    let implementationName := (familyMember.bind fun member =>
      targetOf? member.privateConstructors constructor.name).orElse
        (fun _ => targetOf? implementationInterface.ctors constructor.name) |>.getD .anonymous
    if implementationName.isAnonymous then
      reasons := reasons.push (.missingInterfaceConstructor key .privateModel)
    let publicName := (targetOf? publicInterface.ctors constructor.name).getD .anonymous
    if publicName.isAnonymous then
      reasons := reasons.push (.missingInterfaceConstructor key .publicModel)
    resolvedConstructors := resolvedConstructors.push
      { source := constructor, key, implementationName, publicName }

  let sourceMemberMapping := resolvedMembers.map fun member =>
    (member.source.name, member.implementationCarrier)
  let publicMemberMapping := resolvedMembers.map fun member =>
    (member.source.name, member.publicCarrier)
  let implementationMapping := sourceMemberMapping ++ resolvedConstructors.map fun constructor =>
    (constructor.source.name, constructor.implementationName)
  let publicMapping := publicMemberMapping ++ resolvedConstructors.map fun constructor =>
    (constructor.source.name, constructor.publicName)
  let implementationMapping := implementationMapping ++ resolvedMembers.filterMap fun member =>
    member.sourceRecursor?.map fun recursor => (recursor.name, member.implementationRecursor)
  let publicMapping := publicMapping ++ resolvedMembers.filterMap fun member =>
    member.sourceRecursor?.map fun recursor => (recursor.name, member.publicRecursor)

  let targets := resolvedMembers.map (·.key)
  let mut constructorPlans := #[]
  let mut occurrencePlans := #[]
  let mut uncoveredOccurrences : Array OccurrenceKey := #[]
  let mut uncoveredRules : Array RuleKey := #[]
  for constructor in resolvedConstructors do
    let owner := resolvedMembers.find? (·.key == constructor.key.owner) |>.get!
    let sourceRule? := owner.sourceRecursor?.bind fun recursor =>
      recursor.rules.toArray.findIdx? (·.ctor == constructor.source.name) |>.map fun index =>
        (recursor, index)
    let hypothesisIndices? := sourceRule?.bind fun (recursor, index) =>
      minorHypothesisIndices? recursor index
    if sourceRule?.isSome && hypothesisIndices?.isNone then
      let (recursor, _) := sourceRule?.get!
      let key : RuleKey :=
        { recursorOwner := owner.key, recursor := recursor.name, constructor := constructor.key }
      reasons := reasons.push (.malformedMinorTelescope key)
      uncoveredRules := uncoveredRules.push key
    let totalBinders := constructor.source.numParams + constructor.source.numFields
    let opened? := openBinders totalBinders constructor.source.type
    if opened?.isNone then
      reasons := reasons.push (.malformedConstructorTelescope constructor.key)
    let (opened, result) := opened?.getD (#[], constructor.source.type)
    if result matches .forallE .. then
      reasons := reasons.push (.malformedConstructorTelescope constructor.key)
    unless result.getAppFn.constName? == some owner.source.name do
      reasons := reasons.push (.malformedConstructorTelescope constructor.key)
    let parameterBinders := opened.extract 0 (min constructor.source.numParams opened.size)
    let fieldBinders := opened.extract (min constructor.source.numParams opened.size) opened.size
    let mut telescopeBinders := #[]
    for fieldIndex in [:fieldBinders.size] do
      let field := fieldBinders[fieldIndex]!
      let sites := occurrenceSites targets fieldIndex field.type
      let hypothesisIndex? := hypothesisIndices?.bind fun indices => indices[fieldIndex]?.join
      if !sites.isEmpty && hypothesisIndex?.isNone then
        reasons := reasons.push (.missingMinorHypothesis constructor.key fieldIndex)
      let mut keys := #[]
      for site in sites do
        let key : OccurrenceKey :=
          { constructor := constructor.key, fieldIndex := site.fieldIndex,
            expressionPath := site.path, binderDepth := site.binderDepth,
            hypothesisIndex := hypothesisIndex?.getD 0, target := site.target }
        if hypothesisIndex?.isNone then uncoveredOccurrences := uncoveredOccurrences.push key
        if let some target := resolvedMembers.find? (·.key == site.target) then
          if target.implementationCarrier.isAnonymous || target.publicCarrier.isAnonymous then
            uncoveredOccurrences := uncoveredOccurrences.push key
        else
          uncoveredOccurrences := uncoveredOccurrences.push key
        keys := keys.push key
        occurrencePlans := occurrencePlans.push
          { key, sourceType := site.type,
            implementationType := rewriteWith implementationMapping site.type }
      telescopeBinders := telescopeBinders.push
        { fieldIndex, info := field.info, sourceType := field.type,
          implementationType := rewriteWith implementationMapping field.type,
          occurrences := keys }
    let resultArguments := result.getAppArgs
    let sourceIndices := resultArguments.extract owner.source.numParams
      (min resultArguments.size (owner.source.numParams + owner.source.numIndices))
    if sourceIndices.size != owner.source.numIndices then
      reasons := reasons.push (.malformedConstructorTelescope constructor.key)
    let sourceType := constructor.source.type
    let implementationType := rewriteWith implementationMapping sourceType
    let publicType := rewriteWith publicMapping sourceType
    constructorPlans := constructorPlans.push
      { key := constructor.key, sourceName := constructor.source.name,
        implementationName := constructor.implementationName, publicName := constructor.publicName,
        sourceType, implementationType, publicType,
        telescope :=
          { constructor := constructor.key,
            parameters := parameterBinders.map (·.type), binders := telescopeBinders,
            sourceResultIndices := sourceIndices,
            implementationResultIndices := sourceIndices.map (rewriteWith implementationMapping),
            sourcePackedType := sourceType, implementationPackedType := implementationType } }

  let occurrencesFor := fun key =>
    occurrencePlans.filter (·.key.constructor == key) |>.map (·.key)
  let environment ← getEnv
  let containerSemanticMapping := iso.containerImplementations.flatMap fun container =>
    #[(container.sourceRecursor, container.implementationRecursor)] ++
      container.recursorRuleKeys
  let mut containerMapPlans := #[]
  for constructor in constructorPlans do
    let containerOccurrences := (occurrencesFor constructor.key).filter isContainerOccurrence
    if containerOccurrences.isEmpty then continue
    let some owner := resolvedMembers.find? (·.key == constructor.key.owner) | continue
    let totalBinders := owner.source.numParams + constructor.telescope.binders.size
    let (addedPlans, addedReasons, addedDiagnostics) ←
      forallBoundedTelescope constructor.sourceType (some totalBinders) fun sourceBinders _ =>
      forallBoundedTelescope constructor.publicType (some totalBinders) fun publicBinders _ => do
        let sourceParameters := sourceBinders.extract 0 owner.source.numParams
        let sourceFields := sourceBinders.extract owner.source.numParams sourceBinders.size
        let publicParameters := publicBinders.extract 0 owner.source.numParams
        let fields := publicBinders.extract owner.source.numParams publicBinders.size
        let mut addedPlans := #[]
        let mut addedReasons := #[]
        let mut addedDiagnostics := #[]
        for occurrence in containerOccurrences do
          let some sourceField := sourceFields[occurrence.fieldIndex]? | continue
          let some field := fields[occurrence.fieldIndex]? | continue
          let sourceFieldType ← inferType sourceField
          let fieldType ← inferType field
          let candidates ← withBinderBody fieldType occurrence.binderDepth fun body =>
            iso.containerImplementations.filterMapM fun container => do
              -- Domain unification assigns an occurrence to a generated map;
              -- the inferred target must be the exact recorded private mimic.
              let target? ← try containerTarget? container publicParameters body catch _ => pure none
              return target?.map fun target => (container, body, target)
          if candidates.size > 1 then
            addedReasons := addedReasons.push (.ambiguousContainerMap occurrence)
            continue
          if let some (container, _publicSourceType, implementationType) := candidates[0]? then
            let (metadataReasons, metadataDiagnostics) ←
              withBinderBody sourceFieldType occurrence.binderDepth fun literalSourceType =>
                containerMetadataInstalled environment iso.aliases iso.decls sourceRecursors
                  containerSemanticMapping sourceParameters publicParameters literalSourceType
                  implementationType occurrence container
            if metadataReasons.isEmpty then
              addedPlans := addedPlans.push
                { key := occurrence
                  parameterArity := container.parameterArity
                  indexArity := container.indexArity
                  implementationCarrier := container.implementationCarrier
                  sourceRecursor := container.sourceRecursor
                  sourceRecursorEvidence := container.sourceRecursorEvidence
                  implementationRecursor := container.implementationRecursor
                  implementationRecursorWrapper := container.implementationRecursorWrapper
                  sourceRecursorType := container.sourceRecursorType
                  implementationRecursorType := container.implementationRecursorType
                  implementationRecursorWrapperType :=
                    container.implementationRecursorWrapperType
                  recursorRuleKeys := container.recursorRuleKeys
                  maps :=
                    { forward := container.forward
                      backward := container.backward
                      backwardForward := container.backwardForward
                      forwardBackward := container.forwardBackward }
                  forwardType := container.forwardType
                  backwardType := container.backwardType
                  backwardForwardType := container.backwardForwardType
                  forwardBackwardType := container.forwardBackwardType
                  implementationCarrierType := container.implementationCarrierType }
            else
              addedReasons := addedReasons ++ metadataReasons
              addedDiagnostics := addedDiagnostics ++ metadataDiagnostics
          else
            let some binder := constructor.telescope.binders[occurrence.fieldIndex]? | continue
            let publicField := rewriteWith publicMapping binder.sourceType
            unless publicField == binder.implementationType do
              addedReasons := addedReasons.push (.missingContainerMap occurrence)
        return (addedPlans, addedReasons, addedDiagnostics)
    containerMapPlans := containerMapPlans ++ addedPlans
    reasons := reasons ++ addedReasons
    diagnostics := diagnostics ++ addedDiagnostics
  -- Internal RecursorVal names and block constructors are semantic evidence;
  -- callable rule theorems instead mention the checked wrapper at the literal
  -- source occurrence.  Keep those two name spaces disjoint.
  let containerInterfaceMapping := containerMapPlans.map fun container =>
    (container.sourceRecursor, container.implementationRecursorWrapper)
  let implementationRuleMapping := implementationMapping ++ containerInterfaceMapping
  let publicRuleMapping := publicMapping ++ containerInterfaceMapping
  let mut containerRecursorPlans : Array ContainerRecursorPlan := #[]
  for container in containerMapPlans do
    let key : ContainerRecursorKey :=
      { publicRecursor := container.sourceRecursor
        implementationRecursor := container.implementationRecursor }
    if containerRecursorPlans.any (·.key == key) then continue
    let grouped := containerMapPlans.filter fun current =>
      current.sourceRecursor == key.publicRecursor &&
        current.implementationRecursor == key.implementationRecursor
    let sameMetadata := grouped.all fun current =>
      current.parameterArity == container.parameterArity &&
        current.indexArity == container.indexArity &&
        current.sourceRecursorType == container.sourceRecursorType &&
        current.implementationRecursorType == container.implementationRecursorType &&
        current.implementationRecursorWrapper == container.implementationRecursorWrapper &&
        current.implementationRecursorWrapperType ==
          container.implementationRecursorWrapperType &&
        current.recursorRuleKeys == container.recursorRuleKeys &&
        current.maps == container.maps
    unless sameMetadata do
      for current in grouped do reasons := reasons.push (.ambiguousContainerMap current.key)
      continue
    let sourceMatches := sourceRecursors.filter (·.name == key.publicRecursor)
    unless sourceMatches.size == 1 do
      for current in grouped do
        reasons := reasons.push (.missingSourceContainerRecursor current.key key.publicRecursor)
      continue
    let publicInfo := IsoSourceRecursor.ofERec sourceMatches[0]!
    unless publicInfo == container.sourceRecursorEvidence do
      for current in grouped do
        reasons := reasons.push (.sourceContainerRecursorMismatch current.key key.publicRecursor)
      continue
    let some (.recInfo implementationInfo) :=
        environment.constants.find? key.implementationRecursor | do
      for current in grouped do
        reasons := reasons.push
          (.missingInstalledContainerRecursor current.key key.implementationRecursor)
      continue
    let publicMajor? ← try
        recursorMajorFamily? (ExactRecursorLayoutView.ofSource publicInfo)
          container.implementationRecursorWrapperType
          container.parameterArity container.indexArity
      catch _ => pure none
    let implementationMajor? ← try
        recursorMajorFamily? (ExactRecursorLayoutView.ofInstalled implementationInfo)
          container.implementationRecursorType
          container.parameterArity container.indexArity
      catch _ => pure none
    let some (publicMajorFamily, publicResultMotive) := publicMajor? | do
      for current in grouped do
        reasons := reasons.push (.invalidContainerRecursorAssociation current.key)
      continue
    let some (implementationMajorFamily, implementationResultMotive) := implementationMajor? | do
      for current in grouped do
        reasons := reasons.push (.invalidContainerRecursorAssociation current.key)
      continue
    unless publicInfo.numMotives == implementationInfo.numMotives &&
        publicInfo.numMinors == implementationInfo.numMinors &&
        publicResultMotive == implementationResultMotive do
      for current in grouped do
        reasons := reasons.push (.invalidContainerRecursorAssociation current.key)
      continue
    let rules := container.recursorRuleKeys.map fun (publicConstructor,
        implementationConstructor) =>
      { recursor := key, publicConstructor, implementationConstructor }
    let boundary? ← try
        installedBoundaryPlan? container.maps publicMajorFamily
          implementationMajorFamily container.forwardType container.backwardType
          container.backwardForwardType container.forwardBackwardType
      catch _ => pure none
    let some boundary := boundary? | do
      for current in grouped do
        reasons := reasons.push (.invalidContainerRecursorAssociation current.key)
      continue
    containerRecursorPlans := containerRecursorPlans.push
      { key, parameterArity := container.parameterArity, indexArity := container.indexArity,
        motiveArity := publicInfo.numMotives, minorArity := publicInfo.numMinors,
        resultMotiveIndex := publicResultMotive,
        publicType := container.implementationRecursorWrapperType,
        implementationType := container.implementationRecursorType,
        publicMajorFamily, implementationMajorFamily, rules,
        occurrences := grouped.map (·.key), boundary }
  let mut rulePlans := #[]
  for member in resolvedMembers do
    if let some recursor := member.sourceRecursor? then
      for ruleIndex in [:recursor.rules.length] do
        let rule := recursor.rules[ruleIndex]!
        let some constructor := resolvedConstructors.find? (·.source.name == rule.ctor) | do
          let unknown : RuleKey :=
            { recursorOwner := member.key, recursor := recursor.name,
              constructor := { owner := member.key, constructor := rule.ctor } }
          reasons := reasons.push (.unknownRuleConstructor unknown)
          continue
        let key : RuleKey :=
          { recursorOwner := member.key, recursor := recursor.name,
            constructor := constructor.key }
        match minorHypothesisIndices? recursor ruleIndex with
        | none =>
          reasons := reasons.push (.malformedMinorTelescope key)
          uncoveredRules := uncoveredRules.push key
          uncoveredOccurrences := uncoveredOccurrences ++ occurrencesFor constructor.key
        | some indices =>
          unless (occurrencesFor constructor.key).all fun occurrence =>
              indices[occurrence.fieldIndex]?.join == some occurrence.hypothesisIndex do
            reasons := reasons.push (.minorHypothesisMismatch key)
            uncoveredRules := uncoveredRules.push key
            uncoveredOccurrences := uncoveredOccurrences ++ occurrencesFor constructor.key
        let implementationIota := (implementationIota? iso member rule.ctor).getD .anonymous
        if implementationIota.isAnonymous then
          reasons := reasons.push (.missingInterfaceRule key .privateModel)
        let publicIota := (publicIota? iso member rule.ctor).getD .anonymous
        if publicIota.isAnonymous then reasons := reasons.push (.missingInterfaceRule key .publicModel)
        let implementationEvidence? ← try
            installedRuleEvidence? environment implementationIota
              member.implementationRecursor constructor.implementationName
          catch _ => pure none
        let publicEvidence? ← try
            installedRuleEvidence? environment publicIota member.publicRecursor
              constructor.publicName
          catch _ => pure none
        let implementationRhs? := implementationEvidence?.map (·.semanticRhs)
        let publicRhs? := publicEvidence?.map (·.semanticRhs)
        let expectedImplementationRhs := rewriteWith implementationRuleMapping rule.rhs
        let expectedPublicRhs := rewriteWith publicRuleMapping rule.rhs
        unless implementationRhs? == some expectedImplementationRhs do
          reasons := reasons.push (.installedRuleMismatch key .privateModel)
          uncoveredRules := uncoveredRules.push key
        unless publicRhs? == some expectedPublicRhs do
          reasons := reasons.push (.installedRuleMismatch key .publicModel)
          uncoveredRules := uncoveredRules.push key
        rulePlans := rulePlans.push
          { key, ruleIndex, exactRhs := rule.rhs,
            publicRhs := publicRhs?.getD expectedPublicRhs,
            implementationRhs := implementationRhs?.getD expectedImplementationRhs,
            implementationIota, publicIota,
            implementationIotaType := implementationEvidence?.map (·.declarationType) |>.getD
              (.sort .zero),
            publicIotaType := publicEvidence?.map (·.declarationType) |>.getD (.sort .zero),
            implementationEvidence := implementationEvidence?.getD default,
            publicEvidence := publicEvidence?.getD default,
            occurrences := occurrencesFor constructor.key }

  -- Identity nested fields need no external container map, but their exact
  -- installed iota RHS still calls an independent specialised recursor. Build
  -- that recursor boundary from the paired literal IH slot itself.
  for rule in rulePlans do
    let some owner := resolvedMembers.find? (·.key == rule.key.recursorOwner) | continue
    let some constructor := resolvedConstructors.find? (·.key == rule.key.constructor) | continue
    let some publicRecursorType := installedType? environment owner.publicRecursor | continue
    let some implementationRecursorType :=
        installedType? environment owner.implementationRecursor | continue
    let motiveArity := owner.sourceRecursor?.map (·.numMotives) |>.getD 0
    let minorArity := owner.sourceRecursor?.map (·.numMinors) |>.getD 0
    let mut seenHypotheses : Array Nat := #[]
    for occurrence in rule.occurrences do
      let hypothesisIndex := occurrence.hypothesisIndex
      if seenHypotheses.contains hypothesisIndex then continue
      seenHypotheses := seenHypotheses.push hypothesisIndex
      let grouped := rule.occurrences.filter (·.hypothesisIndex == hypothesisIndex)
      let some (publicBinderIndex, publicHypothesisIndex) :=
          installedMinorHypothesisPosition? owner.source.numParams motiveArity minorArity
            publicRecursorType constructor.publicName constructor.source.numFields occurrence
        | continue
      let some (implementationBinderIndex, implementationHypothesisIndex) :=
          installedMinorHypothesisPosition? owner.source.numParams motiveArity minorArity
            implementationRecursorType constructor.implementationName
            constructor.source.numFields occurrence
        | continue
      unless publicHypothesisIndex == hypothesisIndex &&
          implementationHypothesisIndex == hypothesisIndex && grouped.all fun current =>
            installedMinorHypothesisPosition? owner.source.numParams motiveArity minorArity
                publicRecursorType constructor.publicName constructor.source.numFields current ==
              some (publicBinderIndex, hypothesisIndex) &&
            installedMinorHypothesisPosition? owner.source.numParams motiveArity minorArity
                implementationRecursorType constructor.implementationName
                  constructor.source.numFields current ==
              some (implementationBinderIndex, hypothesisIndex) do
        continue
      let publicHead? := exactRuleArgumentHead?
        ((`_family_adapter_identity_public_call).append rule.key.recursor)
        rule.publicRhs publicBinderIndex
      let implementationHead? := exactRuleArgumentHead?
        ((`_family_adapter_identity_private_call).append rule.key.recursor)
        rule.implementationRhs implementationBinderIndex
      let some publicRecursor := publicHead? | continue
      let some implementationRecursor := implementationHead? | continue
      if resolvedMembers.any fun member =>
          member.publicRecursor == publicRecursor &&
            member.implementationRecursor == implementationRecursor then
        continue
      let key : ContainerRecursorKey := { publicRecursor, implementationRecursor }
      let callRole : ContainerRecursiveCallRole :=
        { rule := rule.key, hypothesisIndex, publicBinderIndex,
          implementationBinderIndex, occurrences := grouped }
      let exactPlans := containerRecursorPlans.filter fun plan =>
        grouped.all plan.occurrences.contains
      if exactPlans.size > 1 then
        for key in grouped do reasons := reasons.push (.ambiguousContainerMap key)
        continue
      if let some exactPlan := exactPlans[0]? then
        let position := containerRecursorPlans.findIdx? (·.key == exactPlan.key) |>.get!
        let current := containerRecursorPlans[position]!
        let mut occurrences := current.occurrences
        for key in grouped do unless occurrences.contains key do occurrences := occurrences.push key
        let mut callRoles := current.callRoles
        unless callRoles.contains callRole do callRoles := callRoles.push callRole
        containerRecursorPlans := containerRecursorPlans.set! position
          { current with occurrences, callRoles }
        continue
      if let some position := containerRecursorPlans.findIdx? (·.key == key) then
        let current := containerRecursorPlans[position]!
        let mut occurrences := current.occurrences
        for key in grouped do unless occurrences.contains key do occurrences := occurrences.push key
        let mut callRoles := current.callRoles
        unless callRoles.contains callRole do callRoles := callRoles.push callRole
        containerRecursorPlans := containerRecursorPlans.set! position
          { current with occurrences, callRoles }
        continue
      let wrapperMetadata := iso.containerImplementations.filter fun container =>
        container.implementationRecursorWrapper == publicRecursor ||
          container.implementationRecursorWrapper == implementationRecursor
      unless wrapperMetadata.isEmpty do
        -- A callable wrapper is exact emitted interface evidence, never an
        -- ambient RecursorVal. A valid association was consumed above; reaching
        -- this branch means its keyed container plan failed earlier.
        let validWrappers := wrapperMetadata.all fun container =>
          emittedWrapperType? iso.decls container.implementationRecursorWrapper ==
            some container.implementationRecursorWrapperType
        for occurrence in grouped do
          reasons := reasons.push (.invalidContainerRecursorAssociation occurrence)
        unless validWrappers do
          diagnostics := diagnostics ++ wrapperMetadata.flatMap fun container =>
            emittedWrapperDiagnostics iso.aliases iso.decls
              container.implementationRecursorWrapper container.implementationRecursorWrapperType
        continue
      let some (.recInfo publicInfo) := environment.constants.find? publicRecursor | do
        for key in grouped do reasons := reasons.push (.missingInstalledContainerRecursor
          key publicRecursor)
        continue
      let some (.recInfo implementationInfo) :=
          environment.constants.find? implementationRecursor | do
        for key in grouped do reasons := reasons.push (.missingInstalledContainerRecursor
          key implementationRecursor)
        continue
      let publicType := publicInfo.type
      let implementationType := implementationInfo.type
      let publicMajor? ← try
          recursorMajorFamily? (ExactRecursorLayoutView.ofInstalled publicInfo) publicType
            publicInfo.numParams publicInfo.numIndices
        catch _ => pure none
      let implementationMajor? ← try
          recursorMajorFamily? (ExactRecursorLayoutView.ofInstalled implementationInfo)
            implementationType
            implementationInfo.numParams implementationInfo.numIndices
        catch _ => pure none
      let some (publicMajorFamily, publicResultMotive) := publicMajor? | do
        for key in grouped do reasons := reasons.push (.invalidContainerRecursorAssociation key)
        continue
      let some (implementationMajorFamily, implementationResultMotive) :=
          implementationMajor? | do
        for key in grouped do reasons := reasons.push (.invalidContainerRecursorAssociation key)
        continue
      let mut pairedRules : Array ContainerRecursorRuleKey := #[]
      let mut exactRules := publicInfo.rules.length == implementationInfo.rules.length
      for publicRule in publicInfo.rules do
        let ruleMatches := implementationInfo.rules.toArray.filter fun implementationRule =>
          implementationRule.ctor == publicRule.ctor && implementationRule.rhs == publicRule.rhs
        if ruleMatches.size == 1 then
          pairedRules := pairedRules.push
            { recursor := key, publicConstructor := publicRule.ctor,
              implementationConstructor := ruleMatches[0]!.ctor }
        else
          exactRules := false
      let recursorTypesDefeq ← try isDefEq publicType implementationType
        catch _ => pure false
      let majorFamiliesDefeq ← try isDefEq publicMajorFamily implementationMajorFamily
        catch _ => pure false
      unless publicInfo.numParams == implementationInfo.numParams &&
          publicInfo.numIndices == implementationInfo.numIndices &&
          publicInfo.numMotives == implementationInfo.numMotives &&
          publicInfo.numMinors == implementationInfo.numMinors &&
          publicResultMotive == implementationResultMotive && exactRules &&
          recursorTypesDefeq && majorFamiliesDefeq do
        for key in grouped do reasons := reasons.push (.invalidContainerRecursorAssociation key)
        continue
      containerRecursorPlans := containerRecursorPlans.push
        { key, parameterArity := publicInfo.numParams, indexArity := publicInfo.numIndices,
          motiveArity := publicInfo.numMotives, minorArity := publicInfo.numMinors,
          resultMotiveIndex := publicResultMotive, publicType, implementationType,
          publicMajorFamily, implementationMajorFamily, boundary := .defeq,
          rules := pairedRules, occurrences := grouped, callRoles := #[callRole] }

  let representedContainerRecursors := iso.containerImplementations.filterMap
    (validatedContainerSourceRecursor? environment sourceRecursors containerSemanticMapping)
  let representedRecursors :=
    resolvedMembers.filterMap (·.sourceRecursor?.map (·.name)) ++
      representedContainerRecursors
  for recursor in sourceRecursors do
    unless representedRecursors.contains recursor.name do
      reasons := reasons.push (.unrepresentedSourceRecursor recursor.name)

  let memberKeys := resolvedMembers.map (·.key)
  let components := componentPlans memberKeys occurrencePlans
  let memberPlans := resolvedMembers.map fun member =>
    -- Keep the exact source sequences independent of the global plan arrays so
    -- validation detects an accidentally omitted constructor or recursor rule.
    let constructors := sourceConstructors.filterMap fun constructor =>
      if constructor.induct == member.source.name then
        some ({ owner := member.key, constructor := constructor.name } : ConstructorKey)
      else none
    let sourceRules := member.sourceRecursor?.map (fun recursor =>
      recursor.rules.toArray.filterMap fun rule =>
        resolvedConstructors.find? (·.source.name == rule.ctor) |>.map fun constructor =>
          { recursorOwner := member.key, recursor := recursor.name,
            constructor := constructor.key }) |>.getD #[]
    { key := member.key, component := componentFor components member.key, role := .source,
      parameterArity := member.source.numParams, indexArity := member.source.numIndices,
      sourceType := member.source.type, implementationCarrier := member.implementationCarrier,
      publicCarrier := member.publicCarrier, representation := member.representation,
      constructors, sourceRules, sourceRecursor := member.sourceRecursor?.map (·.name) |>.getD .anonymous,
      recursorMotiveArity := member.sourceRecursor?.map (·.numMotives) |>.getD 0,
      recursorMinorArity := member.sourceRecursor?.map (·.numMinors) |>.getD 0,
      implementationRecursor := member.implementationRecursor,
      publicRecursor := member.publicRecursor }
  let plan : FamilyAdapterPlan :=
    { root := memberKeyFor firstType.name, levelParams := firstType.levelParams,
      components, members := memberPlans, constructors := constructorPlans,
      rules := rulePlans, occurrences := occurrencePlans, containerMaps := containerMapPlans,
      containerRecursors := containerRecursorPlans,
      support := iso.familyImplementation?.map (·.support) |>.getD #[] }
  for error in plan.validate do reasons := reasons.push (.invalidPlan error)

  let env ← getEnv
  let mut coverage : ShadowCoverage := {}
  for member in resolvedMembers do
    let implementationExpected := rewriteWith implementationMapping member.source.type
    let publicExpected := rewriteWith publicMapping member.source.type
    let (next, implementationOk) := addInstalledCoverage env member.implementationCarrier
      implementationExpected
      (.missingInstalledDeclaration member.implementationCarrier .privateModel)
      (.installedTypeMismatch member.implementationCarrier .privateModel) reasons
    reasons := next
    let (next, publicOk) := addInstalledCoverage env member.publicCarrier publicExpected
      (.missingInstalledDeclaration member.publicCarrier .publicModel)
      (.installedTypeMismatch member.publicCarrier .publicModel) reasons
    reasons := next
    if implementationOk && publicOk then coverage := { coverage with members := coverage.members.push member.key }
    if let some recursor := member.sourceRecursor? then
      let implementationRecursorExpected := rewriteWith implementationMapping recursor.type
      let publicRecursorExpected := rewriteWith publicMapping recursor.type
      let (next, implementationRecursorOk) := addInstalledCoverage env
        member.implementationRecursor implementationRecursorExpected
        (.missingInstalledDeclaration member.implementationRecursor .privateModel)
        (.installedTypeMismatch member.implementationRecursor .privateModel) reasons
      reasons := next
      let (next, publicRecursorOk) := addInstalledCoverage env member.publicRecursor
        publicRecursorExpected
        (.missingInstalledDeclaration member.publicRecursor .publicModel)
        (.installedTypeMismatch member.publicRecursor .publicModel) reasons
      reasons := next
      if implementationRecursorOk && publicRecursorOk &&
          coverage.members.contains member.key then
        coverage := { coverage with recursors := coverage.recursors.push recursor.name }
  for constructor in constructorPlans do
    let (next, implementationOk) := addInstalledCoverage env constructor.implementationName
      constructor.implementationType
      (.missingInstalledDeclaration constructor.implementationName .privateModel)
      (.installedTypeMismatch constructor.implementationName .privateModel) reasons
    reasons := next
    let (next, publicOk) := addInstalledCoverage env constructor.publicName constructor.publicType
      (.missingInstalledDeclaration constructor.publicName .publicModel)
      (.installedTypeMismatch constructor.publicName .publicModel) reasons
    reasons := next
    if implementationOk && publicOk then
      coverage := { coverage with constructors := coverage.constructors.push constructor.key }
  let publicToImplementation :=
    resolvedMembers.map (fun member => (member.publicCarrier, member.implementationCarrier)) ++
    resolvedMembers.map (fun member => (member.publicRecursor, member.implementationRecursor)) ++
    resolvedConstructors.map (fun constructor =>
      (constructor.publicName, constructor.implementationName)) ++
    rulePlans.map (fun rule => (rule.publicIota, rule.implementationIota))
  for rule in rulePlans do
    let implementationType? := installedType? env rule.implementationIota
    let publicType? := installedType? env rule.publicIota
    if implementationType?.isNone then
      reasons := reasons.push (.missingInstalledDeclaration rule.implementationIota .privateModel)
    if publicType?.isNone then
      reasons := reasons.push (.missingInstalledDeclaration rule.publicIota .publicModel)
    let typesAgree := match implementationType?, publicType? with
      | some implementationType, some publicType =>
        implementationType == rewriteWith publicToImplementation publicType
      | _, _ => false
    if implementationType?.isSome && publicType?.isSome && !typesAgree then
      reasons := reasons.push (.installedTypeMismatch rule.implementationIota .privateModel)
    if typesAgree && !uncoveredRules.contains rule.key &&
        coverage.recursors.contains rule.key.recursor &&
        coverage.members.contains rule.key.recursorOwner &&
        coverage.members.contains rule.key.constructor.owner &&
        coverage.constructors.contains rule.key.constructor then
      coverage := { coverage with rules := coverage.rules.push rule.key }
  let coveredOccurrences := occurrencePlans.filterMap fun occurrence =>
    let rules := rulePlans.filter (·.key.constructor == occurrence.key.constructor)
    if uncoveredOccurrences.contains occurrence.key ||
        !coverage.members.contains occurrence.key.constructor.owner ||
        !coverage.members.contains occurrence.key.target ||
        !coverage.constructors.contains occurrence.key.constructor || rules.isEmpty ||
        !(rules.all fun rule => coverage.rules.contains rule.key) then
      none
    else
      some occurrence.key
  coverage := { coverage with occurrences := coveredOccurrences }
  let coveredContainerMaps := containerMapPlans.filterMap fun container =>
    if coverage.occurrences.contains container.key then some container.key else none
  coverage := { coverage with containerMaps := coveredContainerMaps }
  return { root := firstType.name, plan? := some plan, coverage, reasons, diagnostics }

end InductiveModels.FamilyAdapter
