import InductiveModels.EqKit
import InductiveModels.Format

/-!
# Intrinsic projection shapes, and the transporter their minors use

**The projection ι contract is literal, unconditionally.** Every generated
`T._model.proj_j.iota` states

```
∀ (constructor telescope), T._model.proj_j … (T._model.mk …) = fⱼ
```

with the constructor's own field binder `fⱼ` on the right, on every route.
Nothing selects that right-hand side and nothing can transport it.  A
transported right-hand side would be needed only if field `j` depended on the
*value* of an earlier recursive or nested occurrence field, whose modeled
projection reconstructs it merely propositionally; Lean's positivity and
nesting rules leave no spelling of a constructor field type that reads such a
value at all, and
`test/fixtures/inductive-models/nested_value_dependency.lean` writes out every
attempt for the kernel to reject.  Every field a later field can depend on is
therefore non-recursive, and a non-recursive field is selected definitionally.
`test/ProjectionTransportCensusTest.lean` re-derives this over the whole
fixture corpus with no allowlist.

The predicates below still decide two things the contract does not: which
construction a route is entitled to use, and — where the model is built from a
generic recursor rather than a definitionally reducing selector — the exact
binder telescope of the closed statement.

The `Eq.rec` builder at the bottom of this module survives for the one
remaining consumer, which is not the ι contract: a projection *value* built
through a model recursor gets its selected minor at the type obtained by
substituting the earlier projections, while the minor has the constructor's
own field in hand.  Those two types differ syntactically for a dependent
field, and the transporter is the one canonical term bridging them.  It is
deliberately expression-only; it never unfolds a definition or asks for
definitional equality.
-/

open Lean

namespace InductiveModels

/-- Whether a one-constructor owner's modeled selector reaches each constructor
field **definitionally**, including a dependent field.

The projection rule's *statement* no longer asks: its right-hand side is the
constructor field binder either way.  What this decides is the rule's proof —
a definitional selector proves it by `Eq.refl`, and everything else has to go
through the model recursor's own ι theorem — together with the exact binder
telescope the closed statement is stated over, and the agreement gate on the
nested rung's selector.

For a plain-mutual member the auxiliary inductive supplies primitive
constructor reduction, **whether or not the member is indexed**.  The mutual
construction puts each member's index telescope inside its own tag constructor
and declares `aux` as a real kernel inductive with the tag as its single index
([`InductiveModels.mutualIso`]); `R_k.ctor._model` δ-unfolds to `aux.k.c`, so
`aux.rec`'s primitive ι rule fires on the modeled constructor with the member's
indices present exactly as it does without them.  Indices are arguments of the
recursor, not conditions on its reduction, and the projection's minor lands on
the field literally either way.

A block with a nested occurrence reaches the nested rung and no other: the
plain-mutual and direct-simple routes both refuse it, so `numNested` selects a
construction rather than describing a shape.  That rung declares its
specialised block as a real kernel inductive and its carriers and constructors
as definitions onto it, so the **block's own** recursor selects a constructor
field with the kernel's primitive ι rule.  A field the block stores as declared
therefore reduces on the nose, and a field it packs reduces to
`unpack (pack f)`, whose rule is the container's own retraction — a round trip,
not a dependency transport.  Neither is the canonical transport below, and no
projected codomain can name a packed field's value in the first place, so
nesting is a reason for the literal contract rather than against it.

For a single unindexed, unnested, nonrecursive owner, the direct field/tight
route supplies explicit reflexive projection overrides; there is no auxiliary
inductive underneath, so that disjunct still needs its own shape conditions.

Plain recursive owners without nesting reconstruct a field only
propositionally, so their rules are proved through the model recursor's ι
theorem rather than by `Eq.refl` — at the same literal statement.  Callers
establish the one-constructor precondition while discovering intrinsic
projections. -/
def projectionIotaUsesLiteralField (types : Array EIndType) (type : EIndType) : Bool :=
  type.ctors.length == 1 &&
    (types.any (·.numNested > 0) ||
      (types.size > 1 && types.all (·.numNested == 0)) ||
      (types.size == 1 && type.numIndices == 0 && type.numNested == 0 && !type.isRec))

/-- Whether the exact exported former ends in the literal sort `Prop`.

This deliberately performs no unfolding or level normalization. Generation
and checking both receive the same exported `EIndType`, so a reducible alias or
a maybe-zero `Sort u` cannot make one side opt into the proof-irrelevant
projection contract while the other does not. -/
private partial def exactFormerEndsInProp : Expr → Bool
  | .forallE _ _ body _ => exactFormerEndsInProp body
  | .sort .zero => true
  | _ => false

/-- A kernel-projectable field of a one-constructor proposition has a literal
projection rule on the source-simple route, independently of recursion or
indices.

Callers invoke this only for fields accepted by the intrinsic-projection
predicate. Such a field is itself proposition-valued. Proof irrelevance then
identifies every earlier projected proof with its constructor local in the
dependent field type, and identifies the selected projection with the literal
constructor proof. Thus `Eq.refl` checks without a generated transport.

Nesting is not a condition on this. The contract is about the two *proofs*
the statement equates, and proof irrelevance settles them at whatever carrier
the route built; the route only has to state the theorem at the raw source
constructor telescope, because that is the telescope the exact statement
checker rebuilds. Both the single-block simple route
([`InductiveModels.addSourceStructureModels`]) and the nested route reach
[`InductiveModels.addProjectionModels`] with the export's own constructor
record, and the nested model declares its constructor at exactly that type.

A plain-mutual member is the one route that does not: its model is built from
the *installed* block, whose constructor-local binder types the kernel has
already beta-normalized, so the exact literal contract could not be stated
against the raw source syntax there. `all` pins that exclusion — and pins it
by the same single-member reading that the rest of this predicate uses.

Maybe-zero formers are also intentionally excluded: at a positive
instantiation their fields and values need not be proof-irrelevant. -/
def propositionProjectionIotaUsesLiteralField (type : EIndType) : Bool :=
  type.all == [type.name] && type.ctors.length == 1 &&
    exactFormerEndsInProp type.type

/-- The first production one-layer carrier tranche: one recursive member, one
constructor, no indices and no nested occurrences.  Generation and checking
share this predicate so a failed/collision fallback can never make the checker
silently accept the new literal contract from an old transported model. -/
def oneLayerProjectionFamily (types : Array EIndType) (type : EIndType) : Bool :=
  types.size == 1 && type.all == [type.name] && type.ctors.length == 1 &&
    type.numIndices == 0 && type.numNested == 0 && type.isRec &&
    !type.isUnsafe

/-- The literal serialized telescope boundary shared by generation and
checking.  Deliberately does not unfold a reducible result former: selection
must not depend on an environment the serialized certificate cannot replay. -/
def indexedFibreOneLayerTypeShape (numParams numIndices : Nat)
    (type : Expr) : Bool := Id.run do
  let mut type := type
  for _ in [0:numParams + numIndices] do
    let .forallE _ _ body _ := type | return false
    type := body
  let .sort level := type | return false
  return level.normalize.isNeverZero

private partial def occursIn (needle : Expr) : Expr → Bool
  | expression =>
    if expression == needle then true else
    match expression with
    | .app function argument => occursIn needle function || occursIn needle argument
    | .lam _ type body _ | .forallE _ type body _ =>
      occursIn needle type || occursIn needle body
    | .letE _ type value body _ =>
      occursIn needle type || occursIn needle value || occursIn needle body
    | .mdata _ body => occursIn needle body
    | .proj _ _ structureExpr => occursIn needle structureExpr
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => false

/-- Earlier binders on which binder `target` depends, transitively through the
intervening binder types, in telescope order.  `values` are the opened binder
locals and `types` their opened types.

This is the one dependency closure the module owns.  Two consumers read it:
[`InductiveModels.recursiveIndexedFibreOneLayerShape`] uses it as a capability
guard, refusing a constructor in which a projected field depends on a
recursive occurrence; and the transporter at the bottom of this module
eliminates along exactly these positions when a *minor* has to carry a
dependent field into the codomain the earlier projections produce.  Projection
ι statements do not consult it — their right-hand side is the field binder
unconditionally. -/
def dependencyClosure (values types : Array Expr) (target : Nat) : Array Nat := Id.run do
  if target >= values.size || target >= types.size then return #[]
  let mut needed := Array.replicate target false
  for i in (List.range target).reverse do
    let mut used := occursIn values[i]! types[target]!
    if !used then
      for k in [i + 1:target] do
        if needed[k]! && occursIn values[i]! types[k]! then
          used := true
          break
    if used then needed := needed.set! i true
  return (Array.range target).filter (needed[·]!)

private structure IndexedFibreShapeBinder where
  type : Expr
  value : Expr
  deriving Inhabited

private partial def openIndexedFibreShapeForalls (tag : Name) (expression : Expr) :
    Array IndexedFibreShapeBinder × Expr :=
  let rec loop (expression : Expr) (binders : Array IndexedFibreShapeBinder) :=
    match expression with
    | .forallE _ type body _ =>
      let value := mkFVar (FVarId.mk (tag.mkNum binders.size))
      loop (body.instantiate1 value) (binders.push { type, value })
    | body => (binders, body)
  loop expression #[]

/-- Exact serialized boundary for the recursive indexed fibre tranche.

Every recursive occurrence must itself be one constructor field, applied to
the owner's full parameter/index arity, rather than occur below another
former.  There is no bound on how many such fields a constructor has: the
certificate's `roll`/`unroll` are the identity and its laws are reflexivity,
so each field's rule is settled on its own and the count never enters.

The one remaining condition is that no projected field depend on a recursive
field — neither the constructor result nor any field's dependency closure may
mention a recursive binder.  That is what a recursive field's selector costs:
it reconstructs the field through `unroll`, so its rule is propositional and a
consumer of its *value* could not be stated literally.  A recursive
occurrence's own **index** may name earlier fields freely; those fields are
necessarily nonrecursive (Lean's positivity and nesting rules leave no
spelling of a constructor field type that reads a recursive occurrence's
value), so their selectors reduce and the dependent codomain is literal. -/
def recursiveIndexedFibreOneLayerShape (type : EIndType) (constructor : ECtor)
    (recursor : ERec) : Bool := Id.run do
  unless type.isRec && constructor.induct == type.name &&
      constructor.name == type.ctors.head?.getD .anonymous &&
      constructor.numParams == type.numParams && !constructor.isUnsafe &&
      recursor.name == Name.str type.name "rec" && recursor.all == [type.name] &&
      recursor.numParams == type.numParams && recursor.numIndices == type.numIndices &&
      recursor.numMotives == 1 && recursor.numMinors == 1 && !recursor.k &&
      !recursor.isUnsafe do return false
  let [rule] := recursor.rules | return false
  unless rule.ctor == constructor.name && rule.nfields == constructor.numFields do
    return false
  let (binders, result) := openIndexedFibreShapeForalls
    ((`_projection.indexedFibre).append type.name) constructor.type
  unless binders.size == constructor.numParams + constructor.numFields do return false
  let fields := binders.extract constructor.numParams binders.size
  let .const resultOwner _ := result.getAppFn | return false
  unless resultOwner == type.name &&
      result.getAppArgs.size == type.numParams + type.numIndices do return false
  let mut recursiveFields : Array Nat := #[]
  for fieldIndex in [:fields.size] do
    let fieldType := fields[fieldIndex]!.type
    if fieldType.getUsedConstants.contains type.name then
      let .const fieldOwner _ := fieldType.getAppFn | return false
      unless fieldOwner == type.name &&
          fieldType.getAppArgs.size == type.numParams + type.numIndices do return false
      recursiveFields := recursiveFields.push fieldIndex
  if recursiveFields.isEmpty then return false
  for recursiveIndex in recursiveFields do
    if result.containsFVar fields[recursiveIndex]!.value.fvarId! then return false
  let values := fields.map (·.value)
  let types := fields.map (·.type)
  for fieldIndex in [:fields.size] do
    for dependency in dependencyClosure values types fieldIndex do
      if recursiveFields.contains dependency then return false
  return true

/-- The indexed fibre adapter's complete source-syntax boundary.  The
nonrecursive and recursive families share this predicate in generation and
checking; the complete eight-declaration certificate, not shape alone,
authorizes literal dependent projection rules.

The owner's index telescope has no bound.  `roll`/`unroll` are the identity at
the owner's whole parameter-and-index arity and their laws are reflexivity, so
an index is an argument the certificate carries, never a condition on it.  A
single-member block is pinned by `all`; the caller's array is not consulted. -/
def indexedFibreOneLayerProjectionFamily
    (type : EIndType) (constructor : ECtor) (recursor : ERec) : Bool := Id.run do
  unless type.all == [type.name] &&
      type.ctors == [constructor.name] &&
      type.numNested == 0 && !type.isUnsafe && constructor.induct == type.name &&
      constructor.numParams == type.numParams && !constructor.isUnsafe &&
      recursor.all == [type.name] && recursor.name == Name.str type.name "rec" &&
      recursor.numParams == type.numParams && recursor.numIndices == type.numIndices &&
      recursor.numMotives == 1 && recursor.numMinors == 1 && !recursor.k &&
      !recursor.isUnsafe && indexedFibreOneLayerTypeShape
        type.numParams type.numIndices type.type do return false
  let [rule] := recursor.rules | return false
  unless rule.ctor == constructor.name && rule.nfields == constructor.numFields do
    return false
  let (binders, result) := openIndexedFibreShapeForalls
    ((`_projection.indexedFibreCommon).append type.name) constructor.type
  unless binders.size == constructor.numParams + constructor.numFields do return false
  let .const resultOwner _ := result.getAppFn | return false
  unless resultOwner == type.name &&
      result.getAppArgs.size == type.numParams + type.numIndices do return false
  return !type.isRec || recursiveIndexedFibreOneLayerShape type constructor recursor

/-- One opened constructor field, together with the corresponding modeled
projection and (for an earlier field) its constructor iota proof.

`type` is expressed in the original opened constructor telescope.  `projected`
is the intrinsic projection applied to the modeled constructor major. -/
structure ProjectionField where
  name : Name
  info : BinderInfo
  value : Expr
  type : Expr
  level : Level
  projected : Expr
  iota? : Option Expr := none
  deriving Inhabited

namespace ProjectionField

/-- Replace constructor-field variables simultaneously.  A replacement is not
walked again, which matters because a projected value contains the complete
constructor major and therefore contains the original field variables. -/
private def replaceFields (fields : Array ProjectionField) (values : Array Expr)
    (expression : Expr) : Expr :=
  expression.replace fun subexpression => Id.run do
    for i in [:fields.size] do
      if subexpression == fields[i]!.value then return some values[i]!
    return none

private def replaceExact (sources targets : Array Expr) (expression : Expr) : Expr :=
  expression.replace fun subexpression => Id.run do
    for i in [:sources.size] do
      if subexpression == sources[i]! then return some targets[i]!
    return none

/-- Earlier fields on which `target` depends, transitively through their own
binder types, in telescope order.  The literal route's shape boundary reads
the same closure off the serialized constructor telescope. -/
def dependencies (fields : Array ProjectionField) (target : Nat) : Array Nat :=
  dependencyClosure (fields.map (·.value)) (fields.map (·.type)) target

private structure Binder where
  name : Name
  type : Expr
  info : BinderInfo
  value : Expr

private def closeForalls (binders : Array Binder) (body : Expr) : Expr :=
  binders.reverse.foldl (fun body binder =>
    Expr.forallE binder.name binder.type (body.abstract #[binder.value]) binder.info) body

private def closeLambdas (binders : Array Binder) (body : Expr) : Expr :=
  binders.reverse.foldl (fun body binder =>
    Expr.lam binder.name binder.type (body.abstract #[binder.value]) binder.info) body

private def mkLocal (tag : Name) (target slot : Nat) (suffix : String)
    (name : Name) (type : Expr) (info : BinderInfo := .default) : Binder :=
  let id := FVarId.mk (Name.str ((tag.mkNum target).mkNum slot) suffix)
  { name, type, info, value := mkFVar id }

private def projectedValues (fields : Array ProjectionField) : Array Expr :=
  fields.map (·.projected)

private def resultType (fields : Array ProjectionField) (target : Nat) : Expr :=
  replaceFields fields (projectedValues fields) fields[target]!.type

/-- Sort of the tail following dependency `position`.  Equality-proof binders
land in `Prop`, so only the remaining field binders and the selected value
binder contribute `imax`es. -/
private def tailLevel (fields : Array ProjectionField) (dependencies : Array Nat)
    (target position : Nat) : Level :=
  let selected := fields[target]!.level
  let initial := (Level.imax selected selected).normalize
  (dependencies.extract position dependencies.size).foldr
    (fun index level =>
      (Level.imax fields[index]!.level (Level.imax .zero level)).normalize)
    initial

private def openForall (tag : Name) (target slot : Nat) (type : Expr) :
    Except String (Binder × Expr) := do
  let .forallE name domain body info := type
    | throw "the canonical projection transporter has a short telescope"
  let binder := mkLocal tag target slot "value" name domain info
  return (binder, body.instantiate1 binder.value)

mutual

  /-- The closed telescope transporter for one selected field. -/
  private partial def transporter (eqi : EqInfo) (tag : Name)
      (fields : Array ProjectionField) (target : Nat) : Except String Expr := do
    let type ← transporterType eqi tag fields target
    transporterValue eqi tag fields target type

  /-- Apply the canonical transporter to field values and iota proofs in the
  current scope.  Calls at a smaller target build the right-hand side of a
  later iota-proof binder, so the recursion is well founded by field index. -/
  private partial def normalizedWith (eqi : EqInfo) (tag : Name)
      (fields : Array ProjectionField) (target : Nat)
      (values : Array Expr) (proofs : Array (Option Expr)) : Except String Expr := do
    let dependencies := dependencies fields target
    if dependencies.isEmpty then return values[target]!
    let mut arguments : Array Expr := #[]
    for index in dependencies do
      arguments := arguments.push values[index]!
      let some (some proof) := proofs[index]?
        | throw s!"field {target}'s canonical transport has no iota proof for field {index}"
      arguments := arguments.push proof
    arguments := arguments.push values[target]!
    return mkAppN (← transporter eqi tag fields target) arguments

  /-- Type of the canonical transporter:

  `∀ x₀, p₀ = x₀ → … → ∀ xⱼ, Aⱼ(p⃗)`.

  A later equality binds `pᵢ = normᵢ xᵢ`, not `pᵢ = xᵢ`; this is the
  detail which makes arbitrary dependent telescopes type correctly. -/
  private partial def transporterType (eqi : EqInfo) (tag : Name)
      (fields : Array ProjectionField) (target : Nat) : Except String Expr := do
    if target >= fields.size then throw s!"projection field {target} is absent"
    let dependencies := dependencies fields target
    let mut values := fields.map (·.value)
    let mut proofs := fields.map (·.iota?)
    let mut binders : Array Binder := #[]
    for position in [:dependencies.size] do
      let index := dependencies[position]!
      let fieldType := replaceFields fields values fields[index]!.type
      let field := mkLocal tag target (2 * position) "field" fields[index]!.name
        fieldType fields[index]!.info
      values := values.set! index field.value
      binders := binders.push field
      let normalized ← normalizedWith eqi tag fields index values proofs
      let projectedType := replaceFields fields (projectedValues fields) fields[index]!.type
      let equalityType := eqi.mk' fields[index]!.level projectedType
        fields[index]!.projected normalized
      let proof := mkLocal tag target (2 * position + 1) "iota"
        (Name.str fields[index]!.name "iota") equalityType
      proofs := proofs.set! index (some proof.value)
      binders := binders.push proof
    let selectedType := replaceFields fields values fields[target]!.type
    let selected := mkLocal tag target (2 * dependencies.size) "selected"
      fields[target]!.name selectedType fields[target]!.info
    return closeForalls (binders.push selected) (resultType fields target)

  /-- Value of [`transporterType`], one nested `Eq.rec` per transitive
  dependency.  At each base case the preceding field and equality are
  instantiated with the corresponding projection and reflexivity; the next
  iota binder therefore reduces to a plain equality at that point. -/
  private partial def transporterValue (eqi : EqInfo) (tag : Name)
      (fields : Array ProjectionField) (target : Nat) (type : Expr) :
      Except String Expr := do
    let dependencies := dependencies fields target
    let rec go (position slot : Nat) (current : Expr) : Except String Expr := do
      if position == dependencies.size then
        let (selected, _) ← openForall tag target slot current
        return closeLambdas #[selected] selected.value
      let index := dependencies[position]!
      let (field, afterField) ← openForall tag target slot current
      let (proof, afterProof) ← openForall tag target (slot + 1) afterField
      let alpha := field.type
      let projected := fields[index]!.projected
      let z := mkLocal tag target (slot + 2) "motiveField" field.name alpha field.info
      let hz := mkLocal tag target (slot + 3) "motiveIota" proof.name
        (eqi.mk' fields[index]!.level alpha projected z.value)
      let motiveBody := replaceExact #[field.value, proof.value] #[z.value, hz.value] afterProof
      let motive := closeLambdas #[z, hz] motiveBody
      let refl := eqi.refl' fields[index]!.level alpha projected
      let baseType := replaceExact #[field.value, proof.value] #[projected, refl] afterProof
      let base ← go (position + 1) (slot + 4) baseType
      let body := eqi.recAt (tailLevel fields dependencies target (position + 1))
        fields[index]!.level alpha projected motive base field.value proof.value
      return closeLambdas #[field, proof] body
    go 0 0 type

end

/-- Put constructor field `target` in the codomain obtained by substituting
earlier intrinsic projections.

If the field is independent of every earlier field, this returns the field
itself.  Otherwise it emits one nested `Eq.rec` for each member of the
transitive dependency closure and no recursor for an irrelevant field.

The one caller is the selected minor of a projection *value* built through a
model recursor ([`InductiveModels.structureRecursorPreArguments`]).  No
projection ι statement passes through here: those state the constructor field
binder itself. -/
def normalizeProjectionField (eqi : EqInfo) (tag : Name)
    (fields : Array ProjectionField) (target : Nat) : Except String Expr := do
  if target >= fields.size then throw s!"projection field {target} is absent"
  normalizedWith eqi tag fields target (fields.map (·.value)) (fields.map (·.iota?))

end ProjectionField
end InductiveModels
