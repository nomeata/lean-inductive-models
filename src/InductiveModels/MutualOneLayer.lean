import InductiveModels.OneLayer

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
    GenM (Array MutualFieldShape) := do
  forallBoundedTelescope constructorType (some np) fun parameters _ => do
    let telescope ← instForall constructorType parameters
    let fieldCount := numForalls telescope
    forallBoundedTelescope telescope (some fieldCount) fun fields _ => do
      let mut result := #[]
      for index in [0:fields.size] do
        let fieldType ← inferType fields[index]!
        let target? ← directMutualTarget? all np fieldType
        if target?.isNone && mentionsAny all fieldType then
          badShape "a mutual recursive field is not a direct unindexed occurrence"
        if target?.isSome then
          let .fvar fieldId := fields[index]!
            | badShape "a mutual recursive field is not constructor-local"
          for later in [index + 1:fields.size] do
            if (← inferType fields[later]!).containsFVar fieldId then
              badShape "a later constructor field depends on a mutual recursive field"
        result := result.push { target? }
      return result

/-- Select the bounded production tranche symmetrically across a source SCC.
Every member is unindexed, unnested, safe, and never-zero.  A changed member
has one constructor and at least one direct recursive field; all recursive
fields in the block must be direct and independent of later fields. -/
private def classifyMutualOneLayer (types : Array EIndType)
    (constructors : Array ECtor) : GenM (Option (Array MutualMemberShape)) := do
  unless types.size ≥ 2 do return none
  let all := types.map (·.name)
  unless types.all fun type => type.all.toArray == all && type.numIndices == 0 &&
      type.numNested == 0 && type.isRec && !type.isUnsafe do return none
  let np := types[0]!.numParams
  unless types.all (·.numParams == np) do return none
  let mut members := #[]
  let mut anyChanged := false
  for type in types do
    let level ← exactCarrierLevel type.type np
    unless level.normalize.isNeverZero do return none
    let mut constructorFields := #[]
    for constructorName in type.ctors do
      let some constructor := constructors.find? fun constructor =>
          constructor.name == constructorName && constructor.induct == type.name
        | badShape s!"{constructorName} has no exact constructor record"
      let shape ← mutualFieldShape all np constructor.type
      constructorFields := constructorFields.push (constructor.name, shape)
    let changed := type.ctors.length == 1 &&
      constructorFields.any fun (_, fields) => fields.any (·.target?.isSome)
    anyChanged := anyChanged || changed
    members := members.push { owner := type.name, changed, level, constructorFields }
  if anyChanged then return some members else return none

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
      roll := familyNames.roll owner, unroll := familyNames.unroll owner
      unrollRoll := familyNames.unrollRoll owner
      rollUnroll := familyNames.rollUnroll owner }
  let certificate : IsoFamilyImplementation :=
    { root := familyNames.familyRoot, support := #[familyNames.tag, familyNames.aux]
      members := certificateMembers }
  for member in certificate.members do
    for name in #[member.publicSelf, member.roll, member.unroll,
        member.unrollRoll, member.rollUnroll] do
      ensureFresh reserved name
  let support ← ensureExactSortLift reserved
  let mut declarations := privateIso.decls ++ support
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
      let body ← if shape.changed then
          let constructor := constructors.find? (·.induct == type.name) |>.get!
          let privateConstructorType ← generatedType (privateConstructor! member constructor.name)
          let telescope ← instForall privateConstructorType parameters
          forallBoundedTelescope telescope (some constructor.numFields) fun fields _ =>
            wTowerTyOf shape.level fields
        else pure (privateCarrier parameters)
      mkLambdaFVars parameters body
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
    let rollValue ← forallBoundedTelescope type.type (some np) fun parameters _ =>
      withLocalDeclD `value (mkAppN (.const member.publicSelf levels) parameters) fun value => do
        let body ← if shape.changed then
            let constructor := constructors.find? (·.induct == type.name) |>.get!
            let privateConstructorType ← generatedType
              (privateConstructor! member constructor.name)
            let telescope ← instForall privateConstructorType parameters
            forallBoundedTelescope telescope (some constructor.numFields) fun fields _ => do
              let values ← wTowerProjsOf shape.level fields value
              pure <| mkAppN (.const (privateConstructor! member constructor.name) levels)
                (parameters ++ values)
          else pure value
        mkLambdaFVars (parameters.push value) body
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
    let unrollRollValue ← forallBoundedTelescope type.type (some np) fun parameters _ =>
      withLocalDeclD `value (publicCarrierAt parameters) fun value => do
        let proof ← if shape.changed then
            let constructor := constructors.find? (·.induct == type.name) |>.get!
            let privateConstructorType ← generatedType
              (privateConstructor! member constructor.name)
            let telescope ← instForall privateConstructorType parameters
            forallBoundedTelescope telescope (some constructor.numFields) fun fields _ => do
              let values ← wTowerProjsOf shape.level fields value
              let plan ← mutualUnrollPlan all constructors members certificate type.name
                parameters shape.level levels
              pure <| mkAppN (.const (privateIota! member constructor.name)
                (shape.level :: levels))
                (parameters ++ plan.motives ++ plan.minors ++ values)
          else pure (eqi.refl' shape.level (publicCarrierAt parameters) value)
        mkLambdaFVars (parameters.push value) proof
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
    spliced := spliced }
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
      fun values => wTowerMkOf shape.level values values
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
  for constructorIndex in [0:constructors.size] do
    let constructor := constructors[constructorIndex]!
    let .forallE _ privateMinorType body _ := current
      | badShape s!"{targetMember.privateRecursor} has too few minors"
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
      let publicResult := mkAppN publicMinors[constructorIndex]! mappedBinders
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
          wTowerMkOf shape.level stored stored
        else pure (mkAppN (.const (privateConstructor! member constructor.name) levels)
          (parameters ++ stored))
      mkLambdaFVars binders body
    let declaration := Declaration.defnDecl
      { name, levelParams := lparams, type, value
        hints := ← hintsFor value, safety := .safe }
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
    let projectionValues ← forallBoundedTelescope type.type (some np) fun parameters _ => do
      let telescope ← instForall privateConstructorType parameters
      forallBoundedTelescope telescope (some constructor.numFields) fun fields _ =>
        withLocalDeclD `self (mkAppN (.const member.publicSelf levels) parameters) fun self => do
          let stored ← wTowerProjsOf shape.level fields self
          let values := stored.mapIdx fun index field =>
            mapMutualField certificate false levels parameters fieldsShape[index]! field
          pure (parameters, self, values)
    let (parameters, self, values) := projectionValues
    for index in [0:constructor.numFields] do
      let projectionValue ← mkLambdaFVars (parameters.push self) values[index]!
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
        let plan ← mutualRecursorPlan types constructors members certificate eqi sourceRecursor
          parameters motives minors levels
        let constructorType := exact constructor.type
        let telescope ← instForall constructorType parameters
        forallBoundedTelescope telescope (some constructor.numFields) fun fields _ => do
          let fieldShape := ownerShape.constructorFields.find? (·.1 == constructor.name)
            |>.map (·.2) |>.getD #[]
          let recursiveFields := (Array.range fieldShape.size).filter fun index =>
            fieldShape[index]!.target?.isSome
          unless recursiveFields.size ≤ 1 do
            badShape s!"{constructor.name} has more than one direct recursive field"
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
          let ownerPrivateCarrier := mkAppN (.const ownerMember.privateSelf levels) parameters
          let ownerPublicCarrier := mkAppN (.const ownerMember.publicSelf levels) parameters
          let roll := mkAppN (.const ownerMember.roll levels) parameters
          let unroll := mkAppN (.const ownerMember.unroll levels) parameters
          let unrollRoll := mkAppN (.const ownerMember.unrollRoll levels) parameters
          let privateConstructor := privateConstructor! ownerMember constructor.name
          let privateMajor := mkAppN (.const privateConstructor levels)
            (parameters ++ privateFields)
          let publicMinor := minors[constructors.findIdx? (·.name == constructor.name) |>.get!]!
          let proof ← if recursiveFields.isEmpty then do
              let publicResult := mkAppN publicMinor fields
              let rollCtor := eqi.refl' ownerShape.level ownerPrivateCarrier
                (mkApp roll publicMajor)
              let agreement ← mutualConstructorAgreement all constructors members certificate eqi
                owner constructor parameters privateFields levels
              let coreIota := mkAppN (.const (privateIota! ownerMember constructor.name)
                  plan.recLevels)
                (parameters ++ plan.privateMotives ++ plan.privateMinors ++ privateFields)
              let arguments := #[ownerPrivateCarrier, ownerPublicCarrier, motives[ownerIndex]!,
                roll, unroll, unrollRoll, privateMajor, publicMajor, rollCtor,
                publicResult, plan.cores[ownerIndex]!, agreement, coreIota]
              match ← applyZeroFieldOneLayerCompatibility
                  [ownerShape.level.normalize.dec.getD .zero, equalityLevel]
                  arguments localProposition with
              | .ok proof => pure proof
              | .error message => badShape s!"{name}'s zero-field compatibility failed: {message}"
            else do
              let recursiveIndex := recursiveFields[0]!
              let target := fieldShape[recursiveIndex]!.target?.get!
              let targetIndex := all.idxOf target
              let targetShape := familyMember! members target
              let targetMember := familyCertificateMember! certificate target
              let publicField := fields[recursiveIndex]!
              let privateField := privateFields[recursiveIndex]!
              let publicFieldType ← inferType publicField
              let privateFieldType ← inferType privateField
              let rollField := mkAppN (.const targetMember.roll levels) parameters
              let unrollField := mkAppN (.const targetMember.unroll levels) parameters
              let sectionField := mkAppN (.const targetMember.unrollRoll levels) parameters
              let privateCtor ← withLocalDeclD `field privateFieldType fun field =>
                mkLambdaFVars #[field] <| mkAppN (.const privateConstructor levels)
                  (parameters ++ privateFields.set! recursiveIndex field)
              let publicCtor ← withLocalDeclD `field publicFieldType fun field =>
                mkLambdaFVars #[field] <| mkAppN (.const (publicConstructor constructor.name) levels)
                  (parameters ++ fields.set! recursiveIndex field)
              let rollCtor ← withLocalDeclD `field publicFieldType fun field => do
                let lhs := mkApp roll (mkApp publicCtor field)
                mkLambdaFVars #[field] <| eqi.refl' ownerShape.level ownerPrivateCarrier lhs
              let privateIH ← withLocalDeclD `field privateFieldType fun field =>
                mkLambdaFVars #[field] (mkApp plan.cores[targetIndex]! field)
              let publicIH ← withLocalDeclD `field publicFieldType fun field =>
                mkLambdaFVars #[field] (mkApp plan.publicRecursors[targetIndex]! field)
              let ihAgreement ← withLocalDeclD `field privateFieldType fun field => do
                let expected := eqi.mk' (← ilevel (mkApp privateIH field))
                  (← inferType (mkApp privateIH field))
                  (mkApp publicIH (mkApp unrollField field)) (mkApp privateIH field)
                let arguments := #[
                  mkAppN (.const targetMember.privateSelf levels) parameters,
                  mkAppN (.const targetMember.publicSelf levels) parameters,
                  motives[targetIndex]!, rollField, unrollField, sectionField,
                  mkAppN (.const targetMember.rollUnroll levels) parameters,
                  plan.cores[targetIndex]!, field]
                let proof ← match ← applyOneLayerIHCompatibility
                    [targetShape.level.normalize.dec.getD .zero, ← ilevel (mkApp privateIH field)]
                    arguments expected with
                  | .ok proof => pure proof
                  | .error message => badShape s!"{name}'s IH compatibility failed: {message}"
                mkLambdaFVars #[field] proof
              let minor ← withMutualMinorBinders (← inferType publicMinor)
                  (publicConstructor constructor.name) constructor.numFields
                  fun binders minorFields hypotheses _ => do
                unless hypotheses.size == 1 do
                  badShape s!"{constructor.name}'s public minor has {hypotheses.size} hypotheses"
                withLocalDeclD `field publicFieldType fun field => do
                  let ihType ← inferType (mkApp publicIH field)
                  withLocalDeclD `ih ihType fun ih => do
                    let mut arguments := #[]
                    for binder in binders do
                      if let some fieldIndex := minorFields.findIdx? (· == binder) then
                        arguments := arguments.push <|
                          if fieldIndex == recursiveIndex then field else fields[fieldIndex]!
                      else arguments := arguments.push ih
                    mkLambdaFVars #[field, ih] (mkAppN publicMinor arguments)
              let agreement ← withLocalDeclD `field privateFieldType fun field => do
                let proof ← mutualConstructorAgreement all constructors members certificate eqi
                  owner constructor parameters (privateFields.set! recursiveIndex field) levels
                mkLambdaFVars #[field] proof
              let coreIota ← withLocalDeclD `field privateFieldType fun field =>
                mkLambdaFVars #[field] <| mkAppN
                  (.const (privateIota! ownerMember constructor.name) plan.recLevels)
                  (parameters ++ plan.privateMotives ++ plan.privateMinors ++
                    privateFields.set! recursiveIndex field)
              let H := motives[targetIndex]!
              let arguments := #[ownerPrivateCarrier, ownerPublicCarrier,
                privateFieldType, publicFieldType, motives[ownerIndex]!, H,
                roll, unroll, unrollRoll, rollField, unrollField, sectionField,
                privateCtor, publicCtor, rollCtor, privateIH, publicIH, ihAgreement,
                minor, plan.cores[ownerIndex]!, agreement, coreIota, publicField]
              let proof ← match ← applyOneLayerCompatibility
                  [ownerShape.level.normalize.dec.getD .zero,
                    targetShape.level.normalize.dec.getD .zero,
                    equalityLevel, ← ilevel (mkApp H publicField)]
                  arguments localProposition with
                | .ok proof => pure proof
                | .error message => badShape s!"{name}'s compatibility failed: {message}"
              pure proof
          let body := eqi.mk' equalityLevel alpha lhs rhs
          let some fieldsType := closeForallsExact? constructorType fields body
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
