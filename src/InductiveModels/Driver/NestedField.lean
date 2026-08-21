import InductiveModels.Model
import InductiveModels.Driver.GeneratedInfo
import InductiveModels.MutualOneLayer

/-!
# The nested rung's definitional field selector, and projection eligibility

The block-recursor route to a nested model's fields, the eligibility test a
projected field must pass, and the two one-layer projection certificates.

These names were file-private while the driver was one file.  They are
module-visible here because [`InductiveModels.Driver.Projections`] is the one
caller of the selector and the certificates, and
[`InductiveModels.Driver.Tower`] asks the eligibility question when it checks
whether an exact public projection name is already taken.
-/

open Lean Meta

namespace InductiveModels

/-! ### the nested rung's definitional field selector

The nested construction declares its specialised block as a genuine kernel
`inductDecl` and every public carrier and constructor as a definition onto it
([`InductiveModels.iso`]).  Two eliminators therefore exist over the same
values: the block's own recursor, whose ι rule is the kernel's primitive one,
and the public recursor, whose ι rules are theorems stated along the container
congruences and which reduces nothing.  A projection routed through the public
recursor reaches its field only propositionally; one built from the block's
recursor reaches it **definitionally**, up to the round trip a *packed* field
makes through its container's `pack`/`unpack` — and that round trip is the
container's own retraction, not a dependency transport.

That is what puts a nested owner's projection rules on the literal contract.
The block stores every field a later field's type can mention exactly as the
source declares it: Lean's positivity and nesting rules leave no spelling in
which a constructor field type reads the *value* of a nested occurrence
(`test/fixtures/inductive-models/nested_value_dependency.lean` pins every
attempt), so a projected codomain never names a packed position and the
definitional part of the selector is exactly the part the codomain needs. -/

/-- What an intrinsic projection needs of a nested model: the block member
carrying this owner, the container maps, and the `funext` the model's own
proofs already use. -/
structure NestedProjectionBlock where
  /-- The block member carrying this owner, `T._model._impl.k`. -/
  member : Name
  /-- Its position in the block's motive vector.  The block lists the export's
  own members first, in `all` order, so this is the owner's member index. -/
  memberIndex : Nat
  containers : Array IsoContainerImplementation
  funext? : Option Name

/-- The nested model under construction, or `none` for every other rung.
`containerImplementations` is the nested construction's own checked record of
its specialised containers and no other route produces one. -/
def nestedProjectionBlock? (is : Iso) (memberIndex : Nat) :
    Option NestedProjectionBlock := do
  if is.containerImplementations.isEmpty then none
  let member ← is.members[memberIndex]?
  return { member, memberIndex, containers := is.containerImplementations,
           funext? := is.funext? }

/-- The container a block field's type sits at, and how deep under a binder
telescope.  `none` is a field the block stores exactly as the source declares
it — the fields a packed tower selects on the nose. -/
private def nestedContainerUnder? (block : NestedProjectionBlock) (type : Expr) :
    MetaM (Option (IsoContainerImplementation × Nat)) := do
  let container? := fun (candidate : Expr) => match (headNorm candidate).getAppFn with
    | .const name _ => block.containers.find? (·.implementationCarrier == name)
    | _ => none
  if let some container := container? type then return some (container, 0)
  forallTelescope (← whnf type) fun binders result => do
    let some container := container? (← whnf result) | return none
    return some (container, binders.size)

/-- Which of the constructor's fields the block packs, in field order.  The
block's constructor telescope is the source's with exactly the packed
positions retyped, so one table indexes both. -/
def nestedFieldPacking (block : NestedProjectionBlock)
    (blockConstructor : Name) (levels : List Level) (numParams numFields : Nat) :
    GenM (Array (Option (IsoContainerImplementation × Nat))) := do
  let info ← constInfo blockConstructor
  let type := info.type.instantiateLevelParams info.levelParams levels
  forallBoundedTelescope type (some (numParams + numFields)) fun binders _ => do
    unless binders.size == numParams + numFields do
      badShape s!"{blockConstructor} has fewer than {numParams + numFields} binders"
    (binders.extract numParams binders.size).mapM fun field => do
      nestedContainerUnder? block (← inferType field)

/-- The container's index vector at one occurrence of it.  The maps take the
model's parameters from the enclosing scope and the container's indices after
them, and both sides of the round trip carry those indices last: the block
member reads `Bₘ p⃗ ι⃗` and the export-side occurrence reads `C … ι⃗`, whose
leading arguments are the container's own parameters and not the model's.  The
trailing `indexArity` arguments are therefore the one reading which is right on
both, and it is [`InductiveModels.Gen.idxOf`]'s. -/
private def nestedContainerIndices (container : IsoContainerImplementation)
    (occurrence : Expr) : GenM (Array Expr) := do
  let arguments := (headNorm occurrence).getAppArgs
  unless arguments.size ≥ container.indexArity do
    badShape s!"{container.implementationCarrier} occurs at {arguments.size} arguments, \
      fewer than its {container.indexArity} indices"
  return arguments.extract (arguments.size - container.indexArity) arguments.size

/-- One block field as the source constructor declares it.  A packed position
comes back through its container's `unpack`, pointwise under whatever binder
telescope the block stored it under; every other position is already the
source's own field. -/
def nestedSourceField (us : List Level) (params : Array Expr)
    (packed? : Option (IsoContainerImplementation × Nat)) (field : Expr) : GenM Expr := do
  let some (container, depth) := packed? | return field
  Gen.underBinders depth (← inferType field) field fun _ result inner => do
    let indices ← nestedContainerIndices container result
    return mkAppN (.const container.backward us) (params ++ indices ++ #[inner])

/-- `funext` for a whole binder telescope, innermost first, at the `funext` the
nested model's own proofs use.  Each step η-reduces its two sides, so the
right-hand side closes back to the field itself rather than to its
η-expansion. -/
private def nestedFunextClose (fx : Name) (binders : Array Expr)
    (lhs rhs proof : Expr) : GenM Expr := do
  let mut lhs := lhs
  let mut rhs := rhs
  let mut proof := proof
  for step in [0:binders.size] do
    let binder := binders[binders.size - 1 - step]!
    let domain ← inferType binder
    let domainLevel ← ilevel domain
    let codomain ← inferType lhs
    let codomainLevel ← ilevel codomain
    let family ← mkLambdaFVars #[binder] codomain
    let closedLhs := (← mkLambdaFVars #[binder] lhs).eta
    let closedRhs := (← mkLambdaFVars #[binder] rhs).eta
    proof := mkAppN (.const fx [domainLevel, codomainLevel])
      #[domain, family, closedLhs, closedRhs, ← mkLambdaFVars #[binder] proof]
    lhs := closedLhs
    rhs := closedRhs
  return proof

/-- The nested projection rule's proof.  Where the block stores the field as
declared the selector reduces to it and the rule is reflexivity; where the
block packs it the selector reduces to `unpack (pack f)` and the rule is the
container's own retraction, closed pointwise under the field's binders. -/
def nestedProjectionProof (eqi : EqInfo) (block : NestedProjectionBlock)
    (us : List Level) (params : Array Expr)
    (packed? : Option (IsoContainerImplementation × Nat))
    (fieldLevel : Level) (codomain lhs field : Expr) : GenM Expr := do
  let some (container, depth) := packed? | return eqi.refl' fieldLevel codomain lhs
  if depth == 0 then
    let indices ← nestedContainerIndices container (← inferType field)
    return mkAppN (.const container.backwardForward us) (params ++ indices ++ #[field])
  let some fx := block.funext?
    | badShape s!"{container.implementationCarrier} is packed under a binder and \
        the nested model carries no funext"
  forallBoundedTelescope (← inferType field) (some depth) fun binders result => do
    let indices ← nestedContainerIndices container result
    let applied := field.beta binders
    let packedValue := mkAppN (.const container.forward us) (params ++ indices ++ #[applied])
    let roundTrip := mkAppN (.const container.backward us)
      (params ++ indices ++ #[packedValue])
    let pointwise := mkAppN (.const container.backwardForward us)
      (params ++ indices ++ #[applied])
    nestedFunextClose fx binders roundTrip applied pointwise

private partial def projectionFieldEligibleM (ownerIsProp : Bool) (fieldIndex : Nat)
    (current : Expr) : MetaM Bool := do
  let current ← whnf current
  let .forallE name fieldType body info := current | return false
  unless ownerIsProp do
    if fieldIndex == 0 then return true
    return ← withLocalDecl name info fieldType fun value =>
      projectionFieldEligibleM false (fieldIndex - 1) (body.instantiate1 value)
  let fieldIsProp ← isProp fieldType
  if fieldIndex == 0 then return !ownerIsProp || fieldIsProp
  if ownerIsProp && body.hasLooseBVars && !fieldIsProp then return false
  withLocalDecl name info fieldType fun value =>
    projectionFieldEligibleM ownerIsProp (fieldIndex - 1) (body.instantiate1 value)

/-- Mirror the kernel's `infer_proj` field walk.  A Prop-valued owner may only
project proof fields, and may not cross an earlier data field on which the
remaining constructor telescope depends. -/
def eligibleProjectionFieldsM (type : EIndType) (constructor : ECtor) : MetaM (Array Nat) := do
  let ownerIsProp ← isPropFormerType type.type
  forallBoundedTelescope constructor.type (some type.numParams) fun _ fieldsType => do
    let mut result := #[]
    for fieldIndex in [:constructor.numFields] do
      if ← projectionFieldEligibleM ownerIsProp fieldIndex fieldsType then
        result := result.push fieldIndex
    return result

/-- The indexed fibre adapter's own certificate, read back off the built
model.  The owner must be in the adapter's exact source shape *and* the eight
private declarations must be present and correctly keyed; a family that is one
without the other fails closed rather than being reinterpreted. -/
def indexedFibreOneLayerProjectionCertificate (type : EIndType)
    (constructor : ECtor) (recursor : ERec) (is : Iso) : GenM Bool := do
  unless indexedFibreOneLayerProjectionFamily type constructor recursor do return false
  let constructorName := constructor.name
  let some implementation := is.implementation? | return false
  let some publicModel := is.selfNames[0]? | return false
  let impl := Name.str publicModel "_impl"
  let expected : IsoInterface :=
    { selfNames := #[Name.str impl "self"]
      ctors := #[(constructorName, Name.str impl "ctor_0")]
      recs := #[Name.str impl "rec"]
      iotas := #[(0, constructorName, Name.str impl "rec_iota_0")] }
  unless implementation.selfNames == expected.selfNames &&
      implementation.ctors == expected.ctors &&
      implementation.recs == expected.recs &&
      implementation.iotas == expected.iotas do
    badShape s!"{type.name}'s indexed fibre implementation certificate is malformed"
  for name in #[Name.str impl "roll", Name.str impl "unroll",
      Name.str impl "unroll_roll", Name.str impl "roll_unroll"] do
    let _ ← generatedDeclInfo is name
  return true

/-- Validate the simultaneous adapter as one complete owner/rule-keyed
certificate.  No member can opt into literal projection rules independently:
an absent, partial, duplicated, or malformed family fails closed. -/
def mutualOneLayerProjectionCertificate (types : Array EIndType)
    (constructors : Array ECtor) (recursors : Array ERec) (type : EIndType)
    (constructorName : Name) (is : Iso) : GenM Bool := do
  let some certificate := is.familyImplementation? | return false
  let source := EDecl.induct types.toList constructors.toList recursors.toList
  let some changedMembers ← mutualOneLayerChangedMembers? source
    | badShape s!"{type.name}'s mutual one-layer certificate is outside the selected source shape"
  unless certificate.members.size == types.size && is.numAll == types.size &&
      is.selfNames.size == types.size && is.recs.size == types.size do
    badShape s!"{type.name}'s mutual one-layer family certificate is incomplete"
  let names : MutualFamilyNames :=
    { familyRoot := certificate.root
      tag := Name.str certificate.root "tag"
      aux := Name.str certificate.root "aux" }
  unless certificate.support == #[names.tag, names.aux] do
    badShape s!"{type.name}'s mutual one-layer support certificate is malformed"
  for name in certificate.support do
    unless is.decls.any fun declaration => declaration.getNames.contains name do
      badShape s!"{type.name}'s mutual one-layer support declaration {name} is absent"
  for memberIndex in [:types.size] do
    let sourceType := types[memberIndex]!
    let matching := certificate.members.filter fun member => member.owner == sourceType.name
    unless matching.size == 1 do
      badShape s!"{sourceType.name}'s mutual one-layer owner key is absent or duplicated"
    let member := matching[0]!
    let some (_, changed) := changedMembers.find? fun entry => entry.1 == sourceType.name
      | badShape s!"{sourceType.name}'s mutual one-layer source classification is incomplete"
    unless member.changed == changed && member.publicSelf == is.selfNames[memberIndex]! do
      badShape s!"{sourceType.name}'s mutual one-layer public member slot is malformed"
    let some sourceRecursor := recursors.find? fun recursor =>
        recursor.name == Name.str sourceType.name "rec"
      | badShape s!"{sourceType.name}'s exact mutual recursor record is absent"
    unless member.privateSelf == names.privateSelf sourceType.name &&
        member.privateRecursor == names.privateRecursor sourceType.name &&
        member.roll == names.roll sourceType.name &&
        member.unroll == names.unroll sourceType.name &&
        member.unrollRoll == names.unrollRoll sourceType.name &&
        member.rollUnroll == names.rollUnroll sourceType.name do
      badShape s!"{sourceType.name}'s mutual one-layer member names are malformed"
    let ownerConstructors := constructors.filter fun constructor =>
      constructor.induct == sourceType.name
    unless member.privateConstructors.size == ownerConstructors.size &&
        member.privateIotas.size == sourceRecursor.rules.length &&
        member.privateRules.size == sourceRecursor.rules.length do
      badShape s!"{sourceType.name}'s mutual one-layer constructor/rule certificate is incomplete"
    for constructor in ownerConstructors do
      let expected := names.privateConstructor sourceType.name constructor.name
      unless member.privateConstructors.filter (fun entry => entry.1 == constructor.name) ==
          #[(constructor.name, expected)] do
        badShape s!"{constructor.name}'s mutual one-layer constructor key is malformed"
      let _ ← generatedDeclInfo is expected
      let some (_, publicConstructor) := is.ctors.find? fun entry =>
          entry.1 == constructor.name
        | badShape s!"{constructor.name}'s mutual one-layer public constructor is absent"
      let _ ← generatedDeclInfo is publicConstructor
    for rule in sourceRecursor.rules do
      let expected := names.privateIota sourceType.name rule.ctor
      unless member.privateIotas.filter (fun entry =>
          entry.1 == sourceRecursor.name && entry.2.1 == rule.ctor) ==
          #[(sourceRecursor.name, rule.ctor, expected)] do
        badShape s!"{sourceRecursor.name}/{rule.ctor}'s mutual rule key is malformed"
      let _ ← generatedDeclInfo is expected
      let expectedRule := names.privateRule sourceType.name rule.ctor
      unless member.privateRules.filter (fun entry =>
          entry.1 == sourceRecursor.name && entry.2.1 == rule.ctor) ==
          #[(sourceRecursor.name, rule.ctor, expectedRule)] do
        badShape s!"{sourceRecursor.name}/{rule.ctor}'s mutual rule declaration is malformed"
      let _ ← generatedDeclInfo is expectedRule
    for name in #[member.publicSelf, member.privateSelf, member.privateRecursor,
        member.roll, member.unroll, member.unrollRoll, member.rollUnroll,
        is.recs[memberIndex]!] do
      let _ ← generatedDeclInfo is name
    for rule in sourceRecursor.rules do
      unless (is.iotas.filter fun entry =>
          entry.1 == memberIndex && entry.2.1 == rule.ctor).size == 1 do
        badShape s!"{sourceRecursor.name}/{rule.ctor}'s public rule key is absent or duplicated"
  let some member := certificate.members.find? fun member => member.owner == type.name
    | badShape s!"{type.name}'s mutual one-layer projection owner is absent"
  unless constructors.any fun constructor =>
      constructor.name == constructorName && constructor.induct == type.name do
    badShape s!"{constructorName}'s mutual one-layer projection constructor is absent"
  return member.changed
