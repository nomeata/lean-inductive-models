import InductiveModels.OneLayer
import InductiveModels.Mutual

/-!
# Partial one-layer adapter for plain mutual families

This module is deliberately downstream of the established mutual encoding.
The tag/aux family remains the recursion oracle; this adapter publishes one
simultaneous family whose selected members expose a constructor layer and
whose unselected members are identity aliases of the private carriers.
-/

open Lean Meta

namespace InductiveModels

private structure MutualFieldShape where
  target? : Option Name
  deriving Inhabited

private structure MutualMemberShape where
  owner : Name
  changed : Bool
  level : Level
  constructorFields : Array (Name × Array MutualFieldShape)
  deriving Inhabited

private def generatedType (name : Name) : GenM Expr := do
  let some info := (← getEnv).constants.find? name
    | badShape s!"generated declaration {name} is absent"
  return info.type

private def ensureFresh (reserved : Std.HashSet Name) (name : Name) : GenM Unit := do
  if reserved.contains name || (← getEnv).constants.contains name then
    declineWith (.nameTaken name)

private def exactCarrierLevel (memberTy : Expr) (np : Nat) : GenM Level :=
  forallBoundedTelescope memberTy (some np) fun _ result => match result with
    | .sort level => pure level
    | _ => badShape "a mutual one-layer owner does not end in a sort"

private def directMutualTarget? (all : Array Name) (np : Nat) (type : Expr) :
    GenM (Option Name) := do
  for owner in all do
    if (← ownerAppArgs? owner np 0 type).isSome then return some owner
  return none

private def mutualFieldShape (all : Array Name) (np : Nat) (constructorType : Expr) :
    GenM (Option (Array MutualFieldShape)) := do
  forallBoundedTelescope constructorType (some np) fun parameters _ => do
    let telescope ← instForall constructorType parameters
    let fieldCount := numForalls telescope
    forallBoundedTelescope telescope (some fieldCount) fun fields _ => do
      let mut result := #[]
      for index in [0:fields.size] do
        let fieldType ← inferType fields[index]!
        let target? ← directMutualTarget? all np fieldType
        if target?.isNone && mentionsAny all fieldType then
          return none
        if target?.isSome then
          let .fvar fieldId := fields[index]!
            | return none
          for later in [index + 1:fields.size] do
            if (← inferType fields[later]!).containsFVar fieldId then
              return none
        result := result.push { target? }
      return some result

/-- Select the production tranche symmetrically across a source SCC.  Every
member is unindexed, unnested, safe, and never-zero.  A changed member has one
constructor and at least one direct recursive field; all recursive fields in
the block must be direct and independent of later fields.

**How many** recursive fields a constructor has is never asked: the ι rules
are proved by [`InductiveModels.oneLayerNaryCompatibility`], which eliminates
one field per step. -/
private def classifyMutualOneLayer (types : Array EIndType)
    (constructors : Array ECtor) : GenM (Option (Array MutualMemberShape)) := do
  unless types.size ≥ 2 do return none
  let all := types.map (·.name)
  unless types.all fun type => type.all.toArray == all && type.numIndices == 0 &&
      type.numNested == 0 && type.isRec && !type.isUnsafe do return none
  let np := types[0]!.numParams
  unless types.all (·.numParams == np) do return none
  let mut members := #[]
  let mut edges : Array (Name × Name) := #[]
  let mut anyChanged := false
  for type in types do
    let level ← exactCarrierLevel type.type np
    unless level.normalize.isNeverZero do return none
    let mut constructorFields := #[]
    for constructorName in type.ctors do
      let some constructor := constructors.find? fun constructor =>
          constructor.name == constructorName && constructor.induct == type.name
        | badShape s!"{constructorName} has no exact constructor record"
      let some shape ← mutualFieldShape all np constructor.type | return none
      for field in shape do
        if let some target := field.target? then edges := edges.push (type.name, target)
      constructorFields := constructorFields.push (constructor.name, shape)
    let changed := type.ctors.length == 1 &&
      constructorFields.any fun (_, fields) => fields.any (·.target?.isSome)
    anyChanged := anyChanged || changed
    members := members.push { owner := type.name, changed, level, constructorFields }
  unless anyChanged do return none
  -- `isRec` is block-wide metadata; require the source declarations to be an
  -- actual strongly connected component rather than merely members of one
  -- recursive `mutual` command.
  for source in all do
    let mut reached : Std.HashSet Name := { source }
    let mut progress := true
    while progress do
      progress := false
      for edge in edges do
        if reached.contains edge.1 && !reached.contains edge.2 then
          reached := reached.insert edge.2
          progress := true
    unless all.all reached.contains do return none
  return some members

/-- Owner-keyed selection result used by downstream certificate validation. -/
def mutualOneLayerChangedMembers? (source : EDecl) : GenM (Option (Array (Name × Bool))) := do
  let .induct types constructors _ := source | return none
  return (← classifyMutualOneLayer types.toArray constructors.toArray).map fun members =>
    members.map fun member => (member.owner, member.changed)

/-- Pure selection boundary used by the driver before it mutates the
environment.  Construction repeats the classification and therefore cannot
turn an incomplete source block into a partial family certificate. -/
def mutualOneLayerEligible (source : EDecl) : GenM Bool :=
  return (← mutualOneLayerChangedMembers? source).isSome

private def exactFamilySource (env : Environment) (all : Array Name)
    (publicIso : Iso) (expression : Expr) : Expr :=
  let mapping := modelTable env all publicIso
  restore mapping expression

/-! ## The `!` lookups, and why they are total

`panic!` prints and returns the `Inhabited` default; it does not abort.  A
`getD (panic! …)` that fired would therefore hand `Name.anonymous` to the rest
of construction and emit a model built from it, so "cannot happen" has to mean
*established before the lookup*, not *never seen*.

These four helpers are pure — `badShape` is a `GenM` action and is not
available in them — and they are read at some fifty sites.  Threading `GenM`
through them would put a monad on every reader for a condition none of them
can act on differently, so the preconditions are established once instead, at
the single entry point every path runs through
([`mutualOneLayerBase`], reached from [`mutualOneLayerIso`] via
[`mutualOneLayerFields`], which is the module's only external caller):

* `classifyMutualOneLayer` returns one `MutualMemberShape` per source type in
  `types` order, so `familyMember!` is total for any owner in `all`; and
  `certificateMembers` is `all.map`, so `familyCertificateMember!` is too.
  Every owner either comes from `all` or is a field's `directMutualTarget?`,
  which only ever answers with a member of `all`.
* `classifyMutualOneLayer` also declines unless every name in a `type.ctors`
  has an exact constructor record whose `induct` is that type, and
  `privateConstructors` is exactly that filter, so `privateConstructor!` is
  total for any constructor of its member's owner.
* `mutualOneLayerBase` declines unless each owner has its own `rec` record
  whose rules cover that owner's constructors, which is what `privateIotas` is
  built from, so `privateIota!` is total for the same constructors; and unless
  every recursor in the block belongs to an owner in it, which is what
  `sourceRecursorOwner!` and the recursor-plan owner lookup read.

Keep that guard in step with these lookups: it, and not the `panic!` strings,
is what makes a malformed source block a decline. -/

private def familyMember! (members : Array MutualMemberShape) (owner : Name) :
    MutualMemberShape :=
  members.find? (·.owner == owner) |>.getD (panic! s!"missing mutual member {owner}")

private def familyCertificateMember! (certificate : IsoFamilyImplementation) (owner : Name) :
    IsoFamilyMember :=
  certificate.members.find? (·.owner == owner) |>.getD
    (panic! s!"missing mutual certificate member {owner}")

private def privateConstructor! (member : IsoFamilyMember) (constructor : Name) : Name :=
  member.privateConstructors.find? (·.1 == constructor) |>.map (·.2) |>.getD
    (panic! s!"missing private constructor {constructor}")

private def privateIota! (member : IsoFamilyMember) (constructor : Name) : Name :=
  member.privateIotas.find? (fun (_, key, _) => key == constructor) |>.map (·.2.2) |>.getD
    (panic! s!"missing private iota {constructor}")

private def publicSelf (owner : Name) : Name := Naming.modelName owner
private def publicConstructor (constructor : Name) : Name := Naming.modelName constructor
private def publicRecursor (owner : Name) : Name := Naming.modelName (Name.str owner "rec")
private def publicIota (owner : Name) (index : Nat) : Name :=
  Naming.iotaName (Name.str owner "rec") index

private def transportMotiveAlong (eqi : EqInfo) (v level : Level)
    (carrier source target equality base : Expr) (family : Expr → GenM Expr) : GenM Expr := do
  let sourceType ← family source
  let targetType ← family target
  let congrMotive ← withLocalDeclD `z carrier fun z =>
    withLocalDeclD `hz (eqi.mk' level carrier source z) fun hz => do
      mkLambdaFVars #[z, hz]
        (eqi.mk' (.succ v) (.sort v) sourceType (← family z))
  let congruence := eqi.recAt .zero level carrier source congrMotive
    (eqi.refl' (.succ v) (.sort v) sourceType) target equality
  let castMotive ← withLocalDeclD `target (.sort v) fun targetType =>
    withLocalDeclD `h (eqi.mk' (.succ v) (.sort v) sourceType targetType) fun h =>
      mkLambdaFVars #[targetType, h] targetType
  return eqi.recAt v (.succ v) (.sort v) sourceType castMotive base targetType congruence

private def familyCongrChain (eqi : EqInfo) (level : Level) (carrier : Expr)
    (mkStep : Array Expr → GenM Expr) (before after proofs : Array Expr)
    (changed : Array Bool) : GenM Expr := do
  unless before.size == after.size && proofs.size == before.size && changed.size == before.size do
    badShape "a mutual one-layer congruence certificate has inconsistent cardinalities"
  let mixed := fun (j : Nat) => (Array.range before.size).map fun i =>
    if i < j then after[i]! else before[i]!
  let base ← mkStep before
  let mut acc := eqi.refl' level carrier base
  for j in [0:before.size] do
    if !changed[j]! then continue
    let type ← inferType before[j]!
    let fieldLevel ← ilevel type
    let atBefore ← mkStep ((mixed j).set! j before[j]!)
    let factor ← transportAlong eqi .zero fieldLevel type before[j]! after[j]! proofs[j]!
      (eqi.refl' level carrier atBefore) fun value => do
        pure (eqi.mk' level carrier atBefore (← mkStep ((mixed j).set! j value)))
    acc ← transOf eqi level carrier base (← mkStep (mixed j))
      (← mkStep (mixed (j + 1))) acc factor
  return acc

private structure MutualUnrollPlan where
  motives : Array Expr
  minors : Array Expr
  deriving Inhabited

/-- Open a private mutual minor and recover its constructor fields by reading
the constructor application in the result.  Every remaining binder is an
induction hypothesis.  This mirrors Lean's recursor layout without assuming
that hypotheses are all after the fields: Lean interleaves a hypothesis after
its recursive field. -/
private def withMutualMinorBinders (minorType : Expr) (constructor : Name)
    (numFields : Nat)
    (k : Array Expr → Array Expr → Array Expr → Expr → GenM α) : GenM α := do
  forallBoundedTelescope minorType (some (numForalls minorType)) fun binders result => do
    let some major := result.getAppArgs.back?
      | badShape s!"{constructor}'s private minor has no constructor major"
    unless major.getAppFn.constName? == some constructor do
      badShape s!"{constructor}'s private minor ends at {major.getAppFn}, not its constructor"
    let majorArgs := major.getAppArgs
    unless majorArgs.size >= numFields do
      badShape s!"{constructor}'s private minor major has too few fields"
    let fields := majorArgs.extract (majorArgs.size - numFields) majorArgs.size
    let hypotheses := binders.filter fun binder => !fields.contains binder
    k binders fields hypotheses result

/-- Recover a source constructor key from a minor's result major.  The table
contains `(source, modeled)` names, so both public and private simultaneous
minor telescopes use the same name-only association. -/
private def mutualMinorKey (candidates : Array (Name × Name)) (minorType : Expr) :
    GenM Name := do
  forallBoundedTelescope minorType (some (numForalls minorType)) fun _ result => do
    let some major := result.getAppArgs.back?
      | badShape "a mutual minor has no constructor major"
    let some modeled := major.getAppFn.constName?
      | badShape "a mutual minor major is not a constructor application"
    let found := candidates.filter (·.2 == modeled)
    unless found.size == 1 do
      badShape s!"a mutual minor constructor {modeled} has no unique source key"
    return found[0]!.1

private def keyedMutualMinors (candidates : Array (Name × Name))
    (minors : Array Expr) : GenM (Array (Name × Expr)) := do
  let mut keyed := #[]
  for minor in minors do
    let key ← mutualMinorKey candidates (← inferType minor)
    if keyed.any (·.1 == key) then badShape s!"duplicate mutual minor key {key}"
    keyed := keyed.push (key, minor)
  unless keyed.size == candidates.size do
    badShape "the mutual minor table is incomplete"
  return keyed

private def mutualUnrollPlan (all : Array Name) (constructors : Array ECtor)
    (members : Array MutualMemberShape) (certificate : IsoFamilyImplementation)
    (target : Name) (parameters : Array Expr) (level : Level) (levels : List Level) :
    GenM MutualUnrollPlan := do
  let targetMember := familyMember! members target
  let targetCertificate := familyCertificateMember! certificate target
  let publicTarget := mkAppN (.const targetCertificate.publicSelf levels) parameters
  let mut motives := #[]
  for owner in all do
    let ownerCertificate := familyCertificateMember! certificate owner
    let privateCarrier := mkAppN (.const ownerCertificate.privateSelf levels) parameters
    let motive ← withLocalDeclD `value privateCarrier fun value =>
      mkLambdaFVars #[value]
        (if owner == target then publicTarget else unitAt level)
    motives := motives.push motive
  let recursorType ← generatedType targetCertificate.privateRecursor
  let mut current ← instantiateForall recursorType parameters
  for motive in motives do
    let .forallE _ _ body _ := current
      | badShape s!"{targetCertificate.privateRecursor} has too few motives"
    current := body.instantiate1 motive
  let mut minors := #[]
  for constructor in constructors do
    let .forallE _ minorType body _ := current
      | badShape s!"{targetCertificate.privateRecursor} has too few minors"
    let ownerCertificate := familyCertificateMember! certificate constructor.induct
    let privateConstructor := privateConstructor! ownerCertificate constructor.name
    let minor ← withMutualMinorBinders minorType privateConstructor constructor.numFields
        fun binders fields _ _ => do
      let value ← if constructor.induct == target then
          wTowerMkOf targetMember.level fields fields
        else pure (unitAtCanon level)
      mkLambdaFVars binders value
    minors := minors.push minor
    current := body.instantiate1 minor
  return { motives, minors }

private def mutualRollUnrollPlan (all : Array Name) (constructors : Array ECtor)
    (members : Array MutualMemberShape) (certificate : IsoFamilyImplementation)
    (eqi : EqInfo) (target : Name) (parameters : Array Expr) (levels : List Level) :
    GenM MutualUnrollPlan := do
  let targetMember := familyMember! members target
  let targetCertificate := familyCertificateMember! certificate target
  let privateTarget := mkAppN (.const targetCertificate.privateSelf levels) parameters
  let mut motives := #[]
  for owner in all do
    let ownerCertificate := familyCertificateMember! certificate owner
    let privateCarrier := mkAppN (.const ownerCertificate.privateSelf levels) parameters
    let motive ← withLocalDeclD `value privateCarrier fun value => do
      let result := if owner == target then
        let unrolled := mkAppN (.const targetCertificate.unroll levels)
          (parameters.push value)
        let rerolled := mkAppN (.const targetCertificate.roll levels)
          (parameters.push unrolled)
        eqi.mk' targetMember.level privateTarget rerolled value
      else unitAt .zero
      mkLambdaFVars #[value] result
    motives := motives.push motive
  let recursorType ← generatedType targetCertificate.privateRecursor
  let mut current ← instantiateForall recursorType parameters
  for motive in motives do
    let .forallE _ _ body _ := current
      | badShape s!"{targetCertificate.privateRecursor} has too few equality motives"
    current := body.instantiate1 motive
  let mut minors := #[]
  for constructor in constructors do
    let .forallE _ minorType body _ := current
      | badShape s!"{targetCertificate.privateRecursor} has too few equality minors"
    let ownerCertificate := familyCertificateMember! certificate constructor.induct
    let privateConstructor := privateConstructor! ownerCertificate constructor.name
    let minor ← withMutualMinorBinders minorType privateConstructor constructor.numFields
        fun binders fields _ _ => do
      let value ← if constructor.induct == target then
          let major := mkAppN (.const privateConstructor levels) (parameters ++ fields)
          pure (eqi.refl' targetMember.level privateTarget major)
        else pure (unitAtCanon .zero)
      mkLambdaFVars binders value
    minors := minors.push minor
    current := body.instantiate1 minor
  return { motives, minors }

/-- Build only the simultaneous private/public carrier boundary.  Constructor,
recursor, and projection publication is attached below, after all maps and
laws exist. -/
def mutualOneLayerBase (source : EDecl) (reserved : Std.HashSet Name)
    (buildRoot? : Option Name := none) : GenM (Iso × Array MutualMemberShape) := do
  let .induct sourceTypes sourceConstructors sourceRecursors := source
    | badShape "a mutual one-layer adapter needs an exact inductive block"
  let types := sourceTypes.toArray
  let constructors := sourceConstructors.toArray
  let recursors := sourceRecursors.toArray
  let some members ← classifyMutualOneLayer types constructors
    | badShape "the mutual family is outside the bounded one-layer tranche"
  -- **The recursor half of the totality precondition** — see the note above
  -- `familyMember!`.  `classifyMutualOneLayer` has already established that
  -- `members` covers `all` and that every name in a `type.ctors` has its own
  -- exact constructor record; nothing yet says the block carries a recursor
  -- per owner, whose rules cover that owner's constructors, and no recursor
  -- belonging to an owner outside the block.  Those are the facts the
  -- certificate's `privateIotas` and `privateRules` are read back through, and
  -- the source is the only thing that can falsify them, so they are checked
  -- here, once, where a failure is a decline instead of a `panic!` that
  -- continues.
  for type in types do
    let some recursor := recursors.find? (·.name == Name.str type.name "rec")
      | badShape s!"the mutual block has no exact recursor for {type.name}"
    for constructorName in type.ctors do
      unless recursor.rules.any (·.ctor == constructorName) do
        badShape s!"{recursor.name} has no rule for {constructorName}"
  for recursor in recursors do
    unless types.any (Name.str ·.name "rec" == recursor.name) do
      badShape s!"{recursor.name} is not a recursor of the mutual block"
  let all := types.map (·.name)
  let root := all[0]!
  let buildRoot := buildRoot?.getD root
  let lparams := types[0]!.levelParams
  let np := types[0]!.numParams
  let memberTys := types.map (·.type)
  let constructorTys := types.map fun type => type.ctors.toArray.map fun name =>
    let constructor := constructors.find? (·.name == name) |>.get!
    (constructor.name, constructor.type)
  let privateIso ← mutualIso all lparams np memberTys constructorTys reserved
    buildRoot? (some source) true
  let familyNames := MutualFamilyNames.forBuild buildRoot
  let certificateMembers := all.map fun owner =>
    let shape := familyMember! members owner
    let recursor := recursors.find? (·.name == Name.str owner "rec") |>.get!
    let ownerConstructors := constructors.filter (·.induct == owner)
    { owner, changed := shape.changed
      publicSelf := publicSelf owner
      privateSelf := familyNames.privateSelf owner
      privateRecursor := familyNames.privateRecursor owner
      privateConstructors := ownerConstructors.map fun constructor =>
        (constructor.name, familyNames.privateConstructor owner constructor.name)
      privateIotas := recursor.rules.toArray.map fun rule =>
        (recursor.name, rule.ctor, familyNames.privateIota owner rule.ctor)
      privateRules := recursor.rules.toArray.map fun rule =>
        (recursor.name, rule.ctor, familyNames.privateRule owner rule.ctor)
      roll := familyNames.roll owner, unroll := familyNames.unroll owner
      unrollRoll := familyNames.unrollRoll owner
      rollUnroll := familyNames.rollUnroll owner }
  let certificate : IsoFamilyImplementation :=
    { root := familyNames.familyRoot, support := #[familyNames.tag, familyNames.aux]
      members := certificateMembers }
  let exactFamilyNames := MutualFamilyNames.forBuild root
  for member in certificate.members do
    for name in #[member.publicSelf, member.roll, member.unroll,
        member.unrollRoll, member.rollUnroll] do
      ensureFresh reserved name
    for (_, _, name) in member.privateRules do ensureFresh reserved name
    if buildRoot != root then
      for name in #[exactFamilyNames.roll member.owner, exactFamilyNames.unroll member.owner,
          exactFamilyNames.unrollRoll member.owner, exactFamilyNames.rollUnroll member.owner] do
        ensureFresh reserved name
      for (_, constructor, _) in member.privateRules do
        ensureFresh reserved (exactFamilyNames.privateRule member.owner constructor)
  let mut declarations := privateIso.decls
  for member in certificate.members do
    for (recursor, constructor, ruleName) in member.privateRules do
      let iotaName := member.privateIotas.find? (fun entry =>
          entry.1 == recursor && entry.2.1 == constructor) |>.map (·.2.2) |>.getD
        (panic! s!"missing private iota for {recursor}/{constructor}")
      let some sourceRule := privateIso.decls.findSome? fun declaration => match declaration with
          | .thmDecl value => if value.name == iotaName then some value else none
          | _ => none
        | badShape s!"private mutual rule {iotaName} is absent"
      let declaration := Declaration.thmDecl { sourceRule with name := ruleName }
      addChecked declaration
      declarations := declarations.push declaration
  let support ← ensureExactSortLift
  declarations := declarations ++ support
  let mut spliced := privateIso.spliced ++ support.flatMap (·.getNames.toArray)
  let levels := lparams.map Level.param
  let publicSkeleton : Iso := { privateIso with
    selfNames := all.map publicSelf
    ctors := constructors.map fun constructor =>
      (constructor.name, publicConstructor constructor.name)
    recs := all.map publicRecursor
    iotas := recursors.flatMap fun recursor => recursor.rules.toArray.mapIdx fun index rule =>
      (all.idxOf recursor.name.getPrefix, rule.ctor, publicIota recursor.name.getPrefix index) }
  let env ← getEnv
  let exact := exactFamilySource env all publicSkeleton
  -- Public carriers are installed as one batch before any map mentions them.
  for type in types do
    let shape := familyMember! members type.name
    let member := familyCertificateMember! certificate type.name
    let privateCarrier := fun parameters =>
      mkAppN (.const member.privateSelf levels) parameters
    let value ← forallBoundedTelescope type.type (some np) fun parameters _ => do
      if shape.changed then
        let constructor := constructors.find? (·.induct == type.name) |>.get!
        let privateConstructorType ← generatedType (privateConstructor! member constructor.name)
        let telescope ← instForall privateConstructorType parameters
        forallBoundedTelescope telescope (some constructor.numFields) fun fields _ => do
          mkLambdaFVars parameters (← wTowerTyOf shape.level fields)
      else
        mkLambdaFVars parameters (privateCarrier parameters)
    let declaration := Declaration.defnDecl
      { name := member.publicSelf, levelParams := lparams, type := exact type.type
        value, hints := .abbrev, safety := .safe }
    addChecked declaration
    declarations := declarations.push declaration
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok info => pure info
    | .error message => badShape message
  -- Rolls do not depend on any unroll, so install the whole vector first.
  for type in types do
    let shape := familyMember! members type.name
    let member := familyCertificateMember! certificate type.name
    let rollType ← forallBoundedTelescope type.type (some np) fun parameters _ =>
      withLocalDeclD `value (mkAppN (.const member.publicSelf levels) parameters) fun value =>
        mkForallFVars (parameters.push value)
          (mkAppN (.const member.privateSelf levels) parameters)
    let rollValue ← forallBoundedTelescope type.type (some np) fun parameters _ => do
      if shape.changed then
        let constructor := constructors.find? (·.induct == type.name) |>.get!
        let privateConstructorType ← generatedType
          (privateConstructor! member constructor.name)
        let telescope ← instForall privateConstructorType parameters
        forallBoundedTelescope telescope (some constructor.numFields) fun fields _ =>
          withLocalDeclD `value (mkAppN (.const member.publicSelf levels) parameters)
              fun value => do
            let values ← wTowerProjsOf shape.level fields value
            mkLambdaFVars (parameters.push value) <|
              mkAppN (.const (privateConstructor! member constructor.name) levels)
                (parameters ++ values)
      else
        withLocalDeclD `value (mkAppN (.const member.publicSelf levels) parameters) fun value =>
          mkLambdaFVars (parameters.push value) value
    let declaration := Declaration.defnDecl
      { name := member.roll, levelParams := lparams, type := rollType, value := rollValue
        hints := ← hintsFor rollValue, safety := .safe }
    addChecked declaration
    declarations := declarations.push declaration
  -- Unrolls use the simultaneous private recursors but only expose one layer.
  for type in types do
    let shape := familyMember! members type.name
    let member := familyCertificateMember! certificate type.name
    let unrollType ← forallBoundedTelescope type.type (some np) fun parameters _ =>
      withLocalDeclD `value (mkAppN (.const member.privateSelf levels) parameters) fun value =>
        mkForallFVars (parameters.push value)
          (mkAppN (.const member.publicSelf levels) parameters)
    let unrollValue ← forallBoundedTelescope type.type (some np) fun parameters _ =>
      withLocalDeclD `value (mkAppN (.const member.privateSelf levels) parameters) fun value => do
        let body ← if shape.changed then
            let plan ← mutualUnrollPlan all constructors members certificate type.name
              parameters shape.level levels
            pure <| mkAppN (.const member.privateRecursor (shape.level :: levels))
              (parameters ++ plan.motives ++ plan.minors ++ #[value])
          else pure value
        mkLambdaFVars (parameters.push value) body
    let declaration := Declaration.defnDecl
      { name := member.unroll, levelParams := lparams, type := unrollType, value := unrollValue
        hints := ← hintsFor unrollValue, safety := .safe }
    addChecked declaration
    declarations := declarations.push declaration
  -- Both laws are explicit for every owner, including identity siblings.
  for type in types do
    let shape := familyMember! members type.name
    let member := familyCertificateMember! certificate type.name
    let publicCarrierAt := fun ps => mkAppN (.const member.publicSelf levels) ps
    let privateCarrierAt := fun ps => mkAppN (.const member.privateSelf levels) ps
    let unrollRollType ← forallBoundedTelescope type.type (some np) fun parameters _ =>
      withLocalDeclD `value (publicCarrierAt parameters) fun value => do
        let rolled := mkAppN (.const member.roll levels) (parameters.push value)
        let lhs := mkAppN (.const member.unroll levels) (parameters.push rolled)
        mkForallFVars (parameters.push value)
          (eqi.mk' shape.level (publicCarrierAt parameters) lhs value)
    let unrollRollValue ← forallBoundedTelescope type.type (some np) fun parameters _ => do
      if shape.changed then
        let constructor := constructors.find? (·.induct == type.name) |>.get!
        let privateConstructorType ← generatedType
          (privateConstructor! member constructor.name)
        let telescope ← instForall privateConstructorType parameters
        forallBoundedTelescope telescope (some constructor.numFields) fun fields _ =>
          withLocalDeclD `value (publicCarrierAt parameters) fun value => do
            let values ← wTowerProjsOf shape.level fields value
            let plan ← mutualUnrollPlan all constructors members certificate type.name
              parameters shape.level levels
            let proof := mkAppN (.const (privateIota! member constructor.name)
              (shape.level :: levels))
              (parameters ++ plan.motives ++ plan.minors ++ values)
            mkLambdaFVars (parameters.push value) proof
      else
        withLocalDeclD `value (publicCarrierAt parameters) fun value =>
          mkLambdaFVars (parameters.push value)
            (eqi.refl' shape.level (publicCarrierAt parameters) value)
    let unrollRoll := Declaration.thmDecl
      { name := member.unrollRoll, levelParams := lparams, type := unrollRollType
        value := unrollRollValue }
    addChecked unrollRoll
    declarations := declarations.push unrollRoll
    let rollUnrollType ← forallBoundedTelescope type.type (some np) fun parameters _ =>
      withLocalDeclD `value (privateCarrierAt parameters) fun value => do
        let unrolled := mkAppN (.const member.unroll levels) (parameters.push value)
        let lhs := mkAppN (.const member.roll levels) (parameters.push unrolled)
        mkForallFVars (parameters.push value)
          (eqi.mk' shape.level (privateCarrierAt parameters) lhs value)
    let rollUnrollValue ← forallBoundedTelescope type.type (some np) fun parameters _ =>
      withLocalDeclD `value (privateCarrierAt parameters) fun value => do
        let proof ← if shape.changed then
            let plan ← mutualRollUnrollPlan all constructors members certificate eqi type.name
              parameters levels
            pure <| mkAppN (.const member.privateRecursor (.zero :: levels))
              (parameters ++ plan.motives ++ plan.minors ++ #[value])
          else pure (eqi.refl' shape.level (privateCarrierAt parameters) value)
        mkLambdaFVars (parameters.push value) proof
    let rollUnroll := Declaration.thmDecl
      { name := member.rollUnroll, levelParams := lparams, type := rollUnrollType
        value := rollUnrollValue }
    addChecked rollUnroll
    declarations := declarations.push rollUnroll
  let result := { publicSkeleton with
    decls := declarations
    implementation? := none
    familyImplementation? := some certificate
    projectionOverrides := #[]
    spliced := spliced
    aliases := privateIso.aliases.register (declarations.flatMap (·.getNames.toArray)) }
  return (result, members)

private def mapMutualField (certificate : IsoFamilyImplementation) (operation : Bool)
    (levels : List Level) (parameters : Array Expr) (shape : MutualFieldShape)
    (value : Expr) : Expr :=
  match shape.target? with
  | none => value
  | some target =>
    let member := familyCertificateMember! certificate target
    let name := if operation then member.roll else member.unroll
    mkAppN (.const name levels) (parameters.push value)

/-- Build a public layer against the carrier that was already installed.
Unlike `wTowerMkOf`, the stored recursive values need not themselves be free
variables: they have crossed the callee owner's `roll` map. -/
private def mutualTowerValue (stage : String) (level : Level) (carrier : Expr)
    (values : Array Expr) : GenM Expr := do
  let rec build (index : Nat) (current : Expr) : GenM Expr := do
    if index < values.size then
      let current ← withTransparency .all <| whnf current
      let .const name _ := current.getAppFn
        | badShape s!"{stage}: a mutual one-layer carrier is not a PSigma'"
      unless name == `PSigma' do
        badShape s!"{stage}: a mutual one-layer carrier is not a PSigma'"
      let arguments := current.getAppArgs
      unless arguments.size == 2 do
        badShape s!"{stage}: a mutual one-layer PSigma' is malformed"
      let alpha := arguments[0]!
      let beta := arguments[1]!
      unless ← isDefEq (← inferType values[index]!) alpha do
        badShape s!"{stage}: stored field {index} has type {← inferType values[index]!}, expected {alpha}"
      let tail ← build (index + 1) (mkApp beta values[index]!)
      return psigmaMk (← ilevel alpha) level alpha beta values[index]! tail
    unless ← withTransparency .all <| isDefEq current (unitAt level) do
      badShape s!"{stage}: a mutual one-layer carrier does not terminate in PUnit"
    return unitAtCanon level
  build 0 carrier

/-- Equality between a public constructor at fields read through `unroll` and
`unroll` of the corresponding private constructor.  Recursive slots are
changed one at a time with the callee owner's retraction. -/
private def mutualConstructorAgreement (all : Array Name) (constructors : Array ECtor)
    (members : Array MutualMemberShape) (certificate : IsoFamilyImplementation)
    (eqi : EqInfo) (owner : Name) (constructor : ECtor) (parameters privateFields : Array Expr)
    (levels : List Level) : GenM Expr := do
  let shape := familyMember! members owner
  let member := familyCertificateMember! certificate owner
  let fieldShape := shape.constructorFields.find? (·.1 == constructor.name)
    |>.map (·.2) |>.getD #[]
  unless fieldShape.size == privateFields.size do
    badShape s!"{constructor.name}'s agreement has the wrong field arity"
  let publicFields := privateFields.mapIdx fun index field =>
    mapMutualField certificate false levels parameters fieldShape[index]! field
  let storedFields := publicFields.mapIdx fun index field =>
    mapMutualField certificate true levels parameters fieldShape[index]! field
  let mut proofs := #[]
  let mut changed := #[]
  for index in [0:privateFields.size] do
    match fieldShape[index]!.target? with
    | some target =>
      let targetMember := familyCertificateMember! certificate target
      proofs := proofs.push <| mkAppN (.const targetMember.rollUnroll levels)
        (parameters.push privateFields[index]!)
      changed := changed.push true
    | none =>
      let fieldType ← inferType privateFields[index]!
      proofs := proofs.push <| eqi.refl' (← ilevel fieldType) fieldType privateFields[index]!
      changed := changed.push false
  let publicCarrier := mkAppN (.const member.publicSelf levels) parameters
  let privateConstructor := privateConstructor! member constructor.name
  let mkStep := if shape.changed then
      fun values => mutualTowerValue s!"{constructor.name}'s agreement" shape.level
        publicCarrier values
    else fun values => pure <| mkAppN (.const privateConstructor levels) (parameters ++ values)
  let storageEquality ← familyCongrChain eqi shape.level publicCarrier mkStep
    storedFields privateFields proofs changed
  if !shape.changed then return storageEquality
  let plan ← mutualUnrollPlan all constructors members certificate owner
    parameters shape.level levels
  let unrollEquality := mkAppN (.const (privateIota! member constructor.name)
      (shape.level :: levels))
    (parameters ++ plan.motives ++ plan.minors ++ privateFields)
  let privateMajor := mkAppN (.const privateConstructor levels) (parameters ++ privateFields)
  let unrolledMajor := mkAppN (.const member.unroll levels) (parameters.push privateMajor)
  let storedMajor ← mkStep privateFields
  let reverse ← symmOf eqi shape.level publicCarrier unrolledMajor storedMajor unrollEquality
  transOf eqi shape.level publicCarrier (← mkStep storedFields) storedMajor unrolledMajor
    storageEquality reverse

private structure MutualRecursorPlan where
  privateMotives : Array Expr
  privateMinors : Array Expr
  cores : Array Expr
  publicRecursors : Array Expr
  recLevels : List Level
  deriving Inhabited

/-- One source recursor prefix interpreted simultaneously over the private
mutual fixpoint.  Public minors are pulled back along every member's `unroll`;
their results are transported only across the owner-keyed constructor
agreement. -/
private def mutualRecursorPlan (types : Array EIndType) (constructors : Array ECtor)
    (members : Array MutualMemberShape) (certificate : IsoFamilyImplementation)
    (eqi : EqInfo) (sourceRecursor : ERec) (parameters publicMotives publicMinors : Array Expr)
    (levels : List Level) : GenM MutualRecursorPlan := do
  let all := types.map (·.name)
  let lparams := types[0]!.levelParams
  let motiveLevel := if sourceRecursor.levelParams.length == lparams.length + 1 then
      Level.param sourceRecursor.levelParams[0]!
    else .zero
  let recLevels := if sourceRecursor.levelParams.length == lparams.length + 1 then
      motiveLevel :: levels
    else levels
  unless publicMotives.size == all.size && publicMinors.size == constructors.size do
    badShape s!"{sourceRecursor.name}'s public prefix has inconsistent cardinalities"
  let publicConstructorKeys := constructors.map fun constructor =>
    (constructor.name, publicConstructor constructor.name)
  let publicMinorTable ← keyedMutualMinors publicConstructorKeys publicMinors
  let privateConstructorKeys := constructors.map fun constructor =>
    let member := familyCertificateMember! certificate constructor.induct
    (constructor.name, privateConstructor! member constructor.name)
  let mut privateMotives := #[]
  for index in [0:all.size] do
    let owner := all[index]!
    let member := familyCertificateMember! certificate owner
    let privateCarrier := mkAppN (.const member.privateSelf levels) parameters
    let motive ← withLocalDeclD `value privateCarrier fun value =>
      mkLambdaFVars #[value] <| mkApp publicMotives[index]!
        (mkAppN (.const member.unroll levels) (parameters.push value))
    privateMotives := privateMotives.push motive
  let targetOwner := (types.find? fun type => Name.str type.name "rec" == sourceRecursor.name)
    |>.map (·.name) |>.getD (panic! s!"no owner for {sourceRecursor.name}")
  let targetMember := familyCertificateMember! certificate targetOwner
  let privateRecursorType ← generatedType targetMember.privateRecursor
  let mut current ← instantiateForall privateRecursorType parameters
  for motive in privateMotives do
    let .forallE _ _ body _ := current
      | badShape s!"{targetMember.privateRecursor} has too few motives"
    current := body.instantiate1 motive
  let mut privateMinors := #[]
  for _ in [0:constructors.size] do
    let .forallE _ privateMinorType body _ := current
      | badShape s!"{targetMember.privateRecursor} has too few minors"
    let constructorKey ← mutualMinorKey privateConstructorKeys privateMinorType
    let some constructor := constructors.find? (·.name == constructorKey)
      | badShape s!"private mutual minor names absent constructor {constructorKey}"
    let some (_, publicMinor) := publicMinorTable.find? (·.1 == constructor.name)
      | badShape s!"{constructor.name}'s public mutual minor is absent"
    let ownerShape := familyMember! members constructor.induct
    let ownerMember := familyCertificateMember! certificate constructor.induct
    let privateConstructor := privateConstructor! ownerMember constructor.name
    let fieldShape := ownerShape.constructorFields.find? (·.1 == constructor.name)
      |>.map (·.2) |>.getD #[]
    let minor ← withMutualMinorBinders privateMinorType privateConstructor constructor.numFields
        fun binders fields hypotheses _ => do
      let recursiveCount := fieldShape.filter (·.target?.isSome) |>.size
      unless hypotheses.size == recursiveCount do
        badShape s!"{constructor.name}'s direct recursive fields and hypotheses differ"
      let publicFields := fields.mapIdx fun index field =>
        mapMutualField certificate false levels parameters fieldShape[index]! field
      let mut mappedBinders := #[]
      let mut hypothesisIndex := 0
      for binder in binders do
        if let some fieldIndex := fields.findIdx? (· == binder) then
          mappedBinders := mappedBinders.push publicFields[fieldIndex]!
        else
          mappedBinders := mappedBinders.push hypotheses[hypothesisIndex]!
          hypothesisIndex := hypothesisIndex + 1
      let publicResult := mkAppN publicMinor mappedBinders
      let agreement ← mutualConstructorAgreement all constructors members certificate eqi
        constructor.induct constructor parameters fields levels
      let ownerCarrier := mkAppN (.const ownerMember.publicSelf levels) parameters
      let publicMajor := mkAppN (.const (publicConstructor constructor.name) levels)
        (parameters ++ publicFields)
      let privateMajor := mkAppN (.const privateConstructor levels) (parameters ++ fields)
      let privatePublicMajor := mkAppN (.const ownerMember.unroll levels)
        (parameters.push privateMajor)
      let transported ← transportMotiveAlong eqi motiveLevel ownerShape.level ownerCarrier
        publicMajor privatePublicMajor agreement publicResult
        (fun value => pure <| mkApp publicMotives[all.idxOf constructor.induct]! value)
      mkLambdaFVars binders transported
    privateMinors := privateMinors.push minor
    current := body.instantiate1 minor
  let mut cores := #[]
  for owner in all do
    let member := familyCertificateMember! certificate owner
    let privateCarrier := mkAppN (.const member.privateSelf levels) parameters
    let core ← withLocalDeclD `value privateCarrier fun value =>
      mkLambdaFVars #[value] <| mkAppN (.const member.privateRecursor recLevels)
        (parameters ++ privateMotives ++ privateMinors ++ #[value])
    cores := cores.push core
  let mut publicRecursors := #[]
  for index in [0:all.size] do
    let owner := all[index]!
    let shape := familyMember! members owner
    let member := familyCertificateMember! certificate owner
    let publicCarrier := mkAppN (.const member.publicSelf levels) parameters
    let publicRec ← withLocalDeclD `value publicCarrier fun value => do
      let rolled := mkAppN (.const member.roll levels) (parameters.push value)
      let base := mkApp cores[index]! rolled
      let equality := mkAppN (.const member.unrollRoll levels) (parameters.push value)
      let source := mkAppN (.const member.unroll levels) (parameters.push rolled)
      let transported ← transportMotiveAlong eqi motiveLevel shape.level publicCarrier
        source value equality base (fun result => pure <| mkApp publicMotives[index]! result)
      mkLambdaFVars #[value] transported
    publicRecursors := publicRecursors.push publicRec
  return { privateMotives, privateMinors, cores, publicRecursors, recLevels }

/-- Attach exact public constructors and direct layer-projection
implementations.  `operation = true` above denotes public-to-private `roll`;
the reverse direction is used only while reading a stored recursive field. -/
def buildMutualOneLayerFields (source : EDecl) (reserved : Std.HashSet Name)
    (base : Iso) (members : Array MutualMemberShape) : GenM Iso := do
  let .induct sourceTypes sourceConstructors _ := source
    | badShape "mutual public fields need an exact inductive block"
  let types := sourceTypes.toArray
  let constructors := sourceConstructors.toArray
  let all := types.map (·.name)
  let some certificate := base.familyImplementation?
    | badShape "mutual public fields have no family certificate"
  let lparams := types[0]!.levelParams
  let levels := lparams.map Level.param
  let np := types[0]!.numParams
  let env ← getEnv
  let exact := exactFamilySource env all base
  let mut declarations := base.decls
  let mut overrides := #[]
  let eqi ← match EqInfo.check env with
    | .ok info => pure info
    | .error message => badShape message
  for constructor in constructors do
    let shape := familyMember! members constructor.induct
    let member := familyCertificateMember! certificate constructor.induct
    let fieldsShape := shape.constructorFields.find? (·.1 == constructor.name)
      |>.map (·.2) |>.getD #[]
    unless fieldsShape.size == constructor.numFields do
      badShape s!"{constructor.name}'s mutual field shape has the wrong arity"
    let name := publicConstructor constructor.name
    ensureFresh reserved name
    let type := exact constructor.type
    let value ← forallBoundedTelescope type (some (np + constructor.numFields))
        fun binders _ => do
      let parameters := binders.extract 0 np
      let fields := binders.extract np binders.size
      let stored := fields.mapIdx fun index field =>
        mapMutualField certificate true levels parameters fieldsShape[index]! field
      let body ← if shape.changed then
          mutualTowerValue s!"{constructor.name}'s public constructor" shape.level
            (mkAppN (.const member.publicSelf levels) parameters) stored
        else pure (mkAppN (.const (privateConstructor! member constructor.name) levels)
          (parameters ++ stored))
      mkLambdaFVars binders body
    let hints ← hintsFor value
    let declaration := Declaration.defnDecl
      { name, levelParams := lparams, type, value
        hints, safety := .safe }
    addChecked declaration
    declarations := declarations.push declaration
  -- A changed member's projections read the public tower directly.  The
  -- driver remains the authority for public names and exact declaration types;
  -- these closed terms are route-specific implementations only.
  for type in types do
    let shape := familyMember! members type.name
    unless shape.changed do continue
    let member := familyCertificateMember! certificate type.name
    let constructor := constructors.find? (·.induct == type.name) |>.get!
    let fieldsShape := shape.constructorFields.find? (·.1 == constructor.name)
      |>.map (·.2) |>.getD #[]
    let privateConstructorType ← generatedType (privateConstructor! member constructor.name)
    for index in [0:constructor.numFields] do
      let projectionValue ← forallBoundedTelescope type.type (some np) fun parameters _ => do
        let telescope ← instForall privateConstructorType parameters
        forallBoundedTelescope telescope (some constructor.numFields) fun fields _ =>
          withLocalDeclD `self (mkAppN (.const member.publicSelf levels) parameters)
              fun self => do
            let stored ← wTowerProjsOf shape.level fields self
            let value := mapMutualField certificate false levels parameters
              fieldsShape[index]! stored[index]!
            mkLambdaFVars (parameters.push self) value
      let projectionProof ← forallBoundedTelescope (exact constructor.type)
          (some (np + constructor.numFields)) fun binders _ => do
        let ps := binders.extract 0 np
        let fields := binders.extract np binders.size
        let field := fields[index]!
        let proof ← match fieldsShape[index]!.target? with
          | some target =>
            let targetMember := familyCertificateMember! certificate target
            pure <| mkAppN (.const targetMember.unrollRoll levels) (ps.push field)
          | none =>
            let fieldType ← inferType field
            pure <| eqi.refl' (← ilevel fieldType) fieldType field
        mkLambdaFVars binders proof
      overrides := overrides.push (type.name, index, projectionValue, projectionProof)
  return { base with decls := declarations, projectionOverrides := overrides }

/-- Complete constructor-layer boundary.  Public recursors are added by the
final stage, so callers must not serialize this intermediate value. -/
def mutualOneLayerFields (source : EDecl) (reserved : Std.HashSet Name)
    (buildRoot? : Option Name := none) : GenM (Iso × Array MutualMemberShape) := do
  let (base, members) ← mutualOneLayerBase source reserved buildRoot?
  return (← buildMutualOneLayerFields source reserved base members, members)

private def sourceRecursorOwner! (types : Array EIndType) (recursor : ERec) : Name :=
  (types.find? fun type => Name.str type.name "rec" == recursor.name)
    |>.map (·.name) |>.getD (panic! s!"no source owner for {recursor.name}")

private partial def mutualRecursorApplicationCount (all : Array Name)
    (expression : Expr) : Nat :=
  if all.any fun owner => expression.getAppFn.constName? == some (publicRecursor owner) then
    expression.getAppArgs.foldl
      (fun total argument => total + mutualRecursorApplicationCount all argument) 1
  else
    match expression with
    | .app function argument =>
      mutualRecursorApplicationCount all function + mutualRecursorApplicationCount all argument
    | .lam _ type body _ | .forallE _ type body _ =>
      mutualRecursorApplicationCount all type + mutualRecursorApplicationCount all body
    | .letE _ type value body _ =>
      mutualRecursorApplicationCount all type + mutualRecursorApplicationCount all value +
        mutualRecursorApplicationCount all body
    | .mdata _ body => mutualRecursorApplicationCount all body
    | .proj _ _ projected => mutualRecursorApplicationCount all projected
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => 0

private def replaceMutualRecursorCalls (all : Array Name) (pre : Array Expr)
    (locals : Array Expr) (expression : Expr) : Expr × Nat :=
  let replaced := mutualRecursorApplicationCount all expression
  let result := expression.replace fun subexpression => Id.run do
    let .const name _ := subexpression.getAppFn | return none
    let some ownerIndex := all.findIdx? fun owner => publicRecursor owner == name
      | return none
    let arguments := subexpression.getAppArgs
    unless arguments.size == pre.size + 1 do return none
    for index in [:pre.size] do
      unless arguments[index]! == pre[index]! do return none
    return some (mkApp locals[ownerIndex]! arguments[pre.size]!)
  (result, replaced)

/-- Attach exact public mutual recursors and source-shaped iota theorems.  The
definitions and proofs share one `MutualRecursorPlan`, so no installed public
recursor is used as a syntax oracle. -/
def buildMutualOneLayerRecursors (source : EDecl) (reserved : Std.HashSet Name)
    (fieldsIso : Iso) (members : Array MutualMemberShape) : GenM Iso := do
  let .induct sourceTypes sourceConstructors sourceRecursors := source
    | badShape "mutual public recursors need an exact inductive block"
  let types := sourceTypes.toArray
  let constructors := sourceConstructors.toArray
  let recursors := sourceRecursors.toArray
  let all := types.map (·.name)
  let some certificate := fieldsIso.familyImplementation?
    | badShape "mutual public recursors have no family certificate"
  let lparams := types[0]!.levelParams
  let levels := lparams.map Level.param
  let np := types[0]!.numParams
  let env ← getEnv
  let exact := exactFamilySource env all fieldsIso
  let eqi ← match EqInfo.check env with
    | .ok info => pure info
    | .error message => badShape message
  let mut declarations := fieldsIso.decls
  -- Install all public recursors before any exact source rule can refer to a
  -- sibling recursor.
  for sourceRecursor in recursors do
    let owner := sourceRecursorOwner! types sourceRecursor
    let ownerIndex := all.idxOf owner
    let name := publicRecursor owner
    ensureFresh reserved name
    let type := exact sourceRecursor.type
    let numPre := sourceRecursor.numParams + sourceRecursor.numMotives +
      sourceRecursor.numMinors
    let value ← forallBoundedTelescope type (some (numPre + 1)) fun binders _ => do
      let parameters := binders.extract 0 np
      let motives := binders.extract sourceRecursor.numParams
        (sourceRecursor.numParams + sourceRecursor.numMotives)
      let minors := binders.extract (sourceRecursor.numParams + sourceRecursor.numMotives)
        numPre
      let major := binders[numPre]!
      let plan ← mutualRecursorPlan types constructors members certificate eqi sourceRecursor
        parameters motives minors levels
      mkLambdaFVars binders (mkApp plan.publicRecursors[ownerIndex]! major)
    let declaration := Declaration.defnDecl
      { name, levelParams := sourceRecursor.levelParams, type, value
        hints := ← hintsFor value, safety := .safe }
    addChecked declaration
    declarations := declarations.push declaration
  let recursorIso := { fieldsIso with decls := declarations }
  let exact := exactFamilySource (← getEnv) all recursorIso
  let mut iotas := #[]
  for sourceRecursor in recursors do
    let owner := sourceRecursorOwner! types sourceRecursor
    let ownerIndex := all.idxOf owner
    let ownerShape := familyMember! members owner
    let ownerMember := familyCertificateMember! certificate owner
    let recursorType := exact sourceRecursor.type
    let numPre := sourceRecursor.numParams + sourceRecursor.numMotives +
      sourceRecursor.numMinors
    let recLevels := sourceRecursor.levelParams.map Level.param
    for ruleIndex in [0:sourceRecursor.rules.length] do
      let rule := sourceRecursor.rules[ruleIndex]!
      let some constructor := constructors.find? (·.name == rule.ctor)
        | badShape s!"{sourceRecursor.name}'s rule names absent constructor {rule.ctor}"
      unless constructor.induct == owner do
        badShape s!"{sourceRecursor.name}'s rule {ruleIndex} belongs to {constructor.induct}"
      let name := publicIota owner ruleIndex
      ensureFresh reserved name
      let declaration ← forallBoundedTelescope recursorType (some numPre) fun pre _ => do
        let parameters := pre.extract 0 np
        let motives := pre.extract sourceRecursor.numParams
          (sourceRecursor.numParams + sourceRecursor.numMotives)
        let minors := pre.extract (sourceRecursor.numParams + sourceRecursor.numMotives) numPre
        let publicMinorTable ← keyedMutualMinors
          (constructors.map fun constructor =>
            (constructor.name, publicConstructor constructor.name)) minors
        let plan ← mutualRecursorPlan types constructors members certificate eqi sourceRecursor
          parameters motives minors levels
        let constructorType := exact constructor.type
        let telescope ← instForall constructorType parameters
        forallBoundedTelescope telescope (some constructor.numFields) fun fields _ => do
          let fieldShape := ownerShape.constructorFields.find? (·.1 == constructor.name)
            |>.map (·.2) |>.getD #[]
          let recursiveFields := (Array.range fieldShape.size).filter fun index =>
            fieldShape[index]!.target?.isSome
          let privateFields := fields.mapIdx fun index field =>
            mapMutualField certificate true levels parameters fieldShape[index]! field
          let publicMajor := mkAppN (.const (publicConstructor constructor.name) levels)
            (parameters ++ fields)
          let lhs := mkAppN (.const (publicRecursor owner) recLevels) (pre.push publicMajor)
          let rhs := exact rule.rhs |>.beta (pre ++ fields)
          let (localRhs, replaced) := replaceMutualRecursorCalls all pre
            plan.publicRecursors rhs
          unless replaced == recursiveFields.size do
            badShape s!"{name}'s source rule has {replaced} recursive calls, expected \
              {recursiveFields.size}"
          let some alphaSyntax := exactRecursorMotiveResult? sourceRecursor ruleIndex pre fields
            | badShape s!"{name}'s exact source rule has no motive result"
          let alpha := exact alphaSyntax
          let equalityLevel ← ilevel alpha
          let localProposition := eqi.mk' equalityLevel alpha
            (mkApp plan.publicRecursors[ownerIndex]! publicMajor) localRhs
          let ownerPublicCarrier := mkAppN (.const ownerMember.publicSelf levels) parameters
          let ownerUnroll := mkAppN (.const ownerMember.unroll levels) parameters
          let ownerUnrollRoll := mkAppN (.const ownerMember.unrollRoll levels) parameters
          let privateConstructor := privateConstructor! ownerMember constructor.name
          let privateMajor := mkAppN (.const privateConstructor levels)
            (parameters ++ privateFields)
          let some (_, publicMinor) := publicMinorTable.find? (·.1 == constructor.name)
            | badShape s!"{constructor.name}'s public mutual minor is absent"
          -- Lean interleaves a minor's induction hypothesis after its recursive
          -- field, so the minor's argument order is read off its own binders
          -- rather than assumed: a field binder keeps its field, and the k-th
          -- remaining binder belongs to the k-th recursive field.
          let minorLayout ← withMutualMinorBinders (← inferType publicMinor)
              (publicConstructor constructor.name) constructor.numFields
              fun binders minorFields _ _ => do
            let mut layout : Array (Option Nat) := #[]
            let mut hypothesisSlots := 0
            for binder in binders do
              match minorFields.findIdx? (· == binder) with
              | some fieldIndex => layout := layout.push (some fieldIndex)
              | none =>
                layout := layout.push none
                hypothesisSlots := hypothesisSlots + 1
            unless hypothesisSlots == recursiveFields.size do
              badShape s!"{constructor.name}'s public minor has {hypothesisSlots} \
                hypotheses, expected {recursiveFields.size}"
            return layout
          let targetIndices := recursiveFields.map fun index =>
            all.idxOf fieldShape[index]!.target?.get!
          let targetMembers := recursiveFields.map fun index =>
            familyCertificateMember! certificate fieldShape[index]!.target?.get!
          let substitute := fun (values : Array Expr) => Id.run do
            let mut result := fields
            for slot in [0:recursiveFields.size] do
              result := result.set! recursiveFields[slot]! values[slot]!
            return result
          let minorArguments := fun (values hypotheses : Array Expr) => Id.run do
            let fieldValues := substitute values
            let mut arguments := #[]
            let mut slot := 0
            for entry in minorLayout do
              match entry with
              | some fieldIndex => arguments := arguments.push fieldValues[fieldIndex]!
              | none =>
                arguments := arguments.push hypotheses[slot]!
                slot := slot + 1
            return arguments
          let layerAt := fun (values : Array Expr) =>
            pure (mkAppN (.const (publicConstructor constructor.name) levels)
              (parameters ++ substitute values))
          let minorAt := fun (values hypotheses : Array Expr) =>
            pure (mkAppN publicMinor (minorArguments values hypotheses))
          let publicIHAt := fun (slot : Nat) (value : Expr) =>
            pure (mkApp plan.publicRecursors[targetIndices[slot]!]! value)
          let fieldTypes ← recursiveFields.mapM fun index => inferType fields[index]!
          let sources := recursiveFields.mapIdx fun slot index =>
            mkAppN (.const targetMembers[slot]!.unroll levels)
              (parameters.push privateFields[index]!)
          let targets := recursiveFields.map fun index => fields[index]!
          let roundTrips := recursiveFields.mapIdx fun slot index =>
            mkAppN (.const targetMembers[slot]!.unrollRoll levels)
              (parameters.push fields[index]!)
          let privateIHs := recursiveFields.mapIdx fun slot index =>
            mkApp plan.cores[targetIndices[slot]!]! privateFields[index]!
          let ihAgreements ← (Array.range recursiveFields.size).mapM fun slot => do
            let index := recursiveFields[slot]!
            let targetIndex := targetIndices[slot]!
            let targetShape := familyMember! members fieldShape[index]!.target?.get!
            let targetMember := targetMembers[slot]!
            let ihResultType ← inferType privateIHs[slot]!
            let ihLevel ← ilevel ihResultType
            let expected := eqi.mk' ihLevel ihResultType
              (mkApp plan.publicRecursors[targetIndex]! sources[slot]!) privateIHs[slot]!
            let arguments := #[
              mkAppN (.const targetMember.privateSelf levels) parameters,
              mkAppN (.const targetMember.publicSelf levels) parameters,
              motives[targetIndex]!,
              mkAppN (.const targetMember.roll levels) parameters,
              mkAppN (.const targetMember.unroll levels) parameters,
              mkAppN (.const targetMember.unrollRoll levels) parameters,
              mkAppN (.const targetMember.rollUnroll levels) parameters,
              plan.cores[targetIndex]!, privateFields[index]!]
            match ← applyOneLayerIHCompatibility
                [targetShape.level.normalize.dec.getD .zero, ihLevel]
                arguments expected with
            | .ok proof => pure proof
            | .error message => badShape s!"{name}'s IH compatibility failed: {message}"
          let agreement ← mutualConstructorAgreement all constructors members certificate eqi
            owner constructor parameters privateFields levels
          let coreIota := mkAppN (.const (privateIota! ownerMember constructor.name)
              plan.recLevels)
            (parameters ++ plan.privateMotives ++ plan.privateMinors ++ privateFields)
          let rolledMajor := mkAppN (.const ownerMember.roll levels)
            (parameters.push publicMajor)
          unless ← isDefEq rolledMajor privateMajor do
            badShape s!"{constructor.name}'s roll compatibility is not definitional"
          let theoremRhs ← minorAt targets
            (← (Array.range recursiveFields.size).mapM fun slot =>
              publicIHAt slot targets[slot]!)
          unless ← withTransparency .all <| isDefEq theoremRhs localRhs do
            badShape s!"{name}'s local minor does not match its exact source rule"
          let proof ← oneLayerNaryCompatibility eqi ownerShape.level equalityLevel
            ownerPublicCarrier motives[ownerIndex]!
            (mkApp ownerUnroll privateMajor) agreement
            (mkApp plan.cores[ownerIndex]! privateMajor) coreIota
            (mkApp ownerUnrollRoll publicMajor)
            fieldTypes sources targets roundTrips privateIHs ihAgreements
            layerAt minorAt publicIHAt
          let proof ← match ← checkOneLayerCompatibility s!"{name}'s compatibility"
              proof localProposition with
            | .ok proof => pure proof
            | .error message => badShape message
          let body := eqi.mk' equalityLevel alpha lhs rhs
          let some fieldsType := closeForallsExact? telescope fields body
            | badShape s!"{constructor.name}'s exact field telescope is too short"
          let some theoremType := closeForallsExact? recursorType pre fieldsType
            | badShape s!"{sourceRecursor.name}'s exact prefix is too short"
          let value ← mkLambdaFVars (pre ++ fields) proof
          pure <| Declaration.thmDecl
            { name, levelParams := sourceRecursor.levelParams, type := theoremType, value }
      addChecked declaration
      declarations := declarations.push declaration
      iotas := iotas.push (ownerIndex, constructor.name, name)
  return { recursorIso with decls := declarations, iotas }

/-- Complete bounded plain-mutual one-layer adapter. -/
def mutualOneLayerIso (source : EDecl) (reserved : Std.HashSet Name)
    (buildRoot? : Option Name := none) : GenM Iso := do
  let (fields, members) ← mutualOneLayerFields source reserved buildRoot?
  buildMutualOneLayerRecursors source reserved fields members

end InductiveModels
