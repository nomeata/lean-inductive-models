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

end InductiveModels
