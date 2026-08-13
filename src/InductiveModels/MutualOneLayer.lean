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
    let minor ← forallBoundedTelescope minorType (some (numForalls minorType))
        fun binders _ => do
      let value ← if constructor.induct == target then
          let fields := binders.extract 0 constructor.numFields
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
    let minor ← forallBoundedTelescope minorType (some (numForalls minorType))
        fun binders _ => do
      let value ← if constructor.induct == target then
          let fields := binders.extract 0 constructor.numFields
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

end InductiveModels
