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
  | missingInterfaceMember (member : MemberKey) (side : InterfaceSide)
  | missingInterfaceConstructor (constructor : ConstructorKey) (side : InterfaceSide)
  | missingInterfaceRule (rule : RuleKey) (side : InterfaceSide)
  | missingInstalledDeclaration (name : Name) (side : InterfaceSide)
  | installedTypeMismatch (name : Name) (side : InterfaceSide)
  | malformedConstructorTelescope (constructor : ConstructorKey)
  | unknownRuleConstructor (rule : RuleKey)
  | invalidPlan (error : PlanError)
  deriving Inhabited, BEq, Repr

/-- Successfully compared keys.  Absence from an array is accompanied by a
keyed [`ShadowReason`]. Occurrences have no declaration of their own; coverage
there means both exact source and rewritten implementation types were derived. -/
structure ShadowCoverage where
  members : Array MemberKey := #[]
  constructors : Array ConstructorKey := #[]
  rules : Array RuleKey := #[]
  occurrences : Array OccurrenceKey := #[]
  deriving Inhabited, BEq, Repr

structure ShadowReport where
  root : Name
  plan? : Option FamilyAdapterPlan
  coverage : ShadowCoverage := {}
  reasons : Array ShadowReason := #[]
  deriving Inhabited, BEq, Repr

def ShadowReport.complete (report : ShadowReport) : Bool :=
  report.plan?.isSome && report.reasons.isEmpty

def ShadowReport.summary (report : ShadowReport) : String :=
  s!"{report.root}: members {report.coverage.members.size}, constructors {
    report.coverage.constructors.size}, rules {report.coverage.rules.size}, occurrences {
    report.coverage.occurrences.size}, reasons {report.reasons.size}"

/-- Test-facing, value-only evidence retained after the full source-derived
plan has validated and been discarded. Production filtering does not collect
these observations. -/
structure ShadowObservation where
  root : Name
  coverage : ShadowCoverage
  reasons : Array ShadowReason
  deriving Inhabited, BEq, Repr

def ShadowReport.observe (report : ShadowReport) : ShadowObservation :=
  { root := report.root, coverage := report.coverage, reasons := report.reasons }

def ShadowObservation.complete (observation : ShadowObservation) : Bool :=
  observation.reasons.isEmpty

private structure SourceBinder where
  info : BinderInfo
  type : Expr
  deriving Inhabited, BEq, Repr

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

private def addInstalledCoverage (env : Environment) (name : Name) (expected : Expr)
    (missing mismatch : ShadowReason)
    (reasons : Array ShadowReason) : Array ShadowReason × Bool :=
  match installedType? env name with
  | none => (reasons.push missing, false)
  | some actual =>
    if actual == expected then (reasons, true) else (reasons.push mismatch, false)

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
    let implementationRecursor := (familyMember.map (·.privateRecursor)).orElse
      (fun _ => interfaceMemberName? implementationInterface.recs index) |>.getD .anonymous
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
  for constructor in resolvedConstructors do
    let totalBinders := constructor.source.numParams + constructor.source.numFields
    let opened? := openBinders totalBinders constructor.source.type
    if opened?.isNone then
      reasons := reasons.push (.malformedConstructorTelescope constructor.key)
    let (opened, result) := opened?.getD (#[], constructor.source.type)
    let parameterBinders := opened.extract 0 (min constructor.source.numParams opened.size)
    let fieldBinders := opened.extract (min constructor.source.numParams opened.size) opened.size
    let mut telescopeBinders := #[]
    let mut hypothesisIndex := 0
    for fieldIndex in [:fieldBinders.size] do
      let field := fieldBinders[fieldIndex]!
      let sites := occurrenceSites targets fieldIndex field.type
      let mut keys := #[]
      for site in sites do
        let key : OccurrenceKey :=
          { constructor := constructor.key, fieldIndex := site.fieldIndex,
            expressionPath := site.path, binderDepth := site.binderDepth,
            hypothesisIndex, target := site.target }
        hypothesisIndex := hypothesisIndex + 1
        keys := keys.push key
        occurrencePlans := occurrencePlans.push
          { key, sourceType := site.type,
            implementationType := rewriteWith implementationMapping site.type }
      telescopeBinders := telescopeBinders.push
        { fieldIndex, info := field.info, sourceType := field.type,
          implementationType := rewriteWith implementationMapping field.type,
          occurrences := keys }
    let owner := resolvedMembers.find? (·.key == constructor.key.owner) |>.get!
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
        let implementationIota := (implementationIota? iso member rule.ctor).getD .anonymous
        if implementationIota.isAnonymous then
          reasons := reasons.push (.missingInterfaceRule key .privateModel)
        let publicIota := (publicIota? iso member rule.ctor).getD .anonymous
        if publicIota.isAnonymous then reasons := reasons.push (.missingInterfaceRule key .publicModel)
        rulePlans := rulePlans.push
          { key, ruleIndex, exactRhs := rule.rhs, implementationIota, publicIota,
            occurrences := occurrencesFor constructor.key }

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
      implementationRecursor := member.implementationRecursor,
      publicRecursor := member.publicRecursor }
  let plan : FamilyAdapterPlan :=
    { root := memberKeyFor firstType.name, levelParams := firstType.levelParams,
      components, members := memberPlans, constructors := constructorPlans,
      rules := rulePlans, occurrences := occurrencePlans,
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
    if typesAgree then coverage := { coverage with rules := coverage.rules.push rule.key }
  coverage := { coverage with occurrences := occurrencePlans.map (·.key) }
  return { root := firstType.name, plan? := some plan, coverage, reasons }

end InductiveModels.FamilyAdapter
