import InductiveModels.Model

/-!
# Canonical transport for dependent intrinsic projections

An intrinsic projection for field `j` has the constructor field telescope on
the right and the earlier intrinsic projections on the left.  Those types are
literally different when field `j` depends on an earlier field whose modeled
projection has only a propositional iota rule.  This module builds the one
canonical `Eq.rec` term used to put the constructor field in the projection's
codomain.

The builder is deliberately expression-only.  Generation and export checking
must construct exactly the same right-hand side; neither side unfolds a
definition or asks for definitional equality here.
-/

open Lean

namespace InductiveModels

/-- Whether a one-constructor owner's projection rules can use each constructor
field literally, including dependent fields.

For an unindexed plain-mutual member the auxiliary inductive supplies primitive
constructor reduction.  For a single unindexed, unnested, nonrecursive owner,
the direct field/tight route supplies explicit reflexive projection overrides.
Recursive, indexed, and nested-specialisation routes may reconstruct a field
only propositionally, so their dependent rules retain the canonical transport
below. Callers establish the one-constructor precondition while discovering
intrinsic projections. -/
def projectionIotaUsesLiteralField (types : Array EIndType) (type : EIndType) : Bool :=
  type.ctors.length == 1 && type.numIndices == 0 &&
    ((types.size > 1 && types.all (·.numNested == 0)) ||
      (types.size == 1 && type.numNested == 0 && !type.isRec))

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

The first tranche is deliberately limited to a single, unnested source block.
Those owners reach [`InductiveModels.addSourceStructureModels`] with their raw
constructor telescope. Nested and plain-mutual builders currently expose an
installed telescope instead; selecting the exact literal contract there would
discard a source head beta-redex before the theorem is stated. They remain on
the legacy transported contract until those routes carry the raw source
telescope too.

Maybe-zero formers are also intentionally excluded: at a positive
instantiation their fields and values need not be proof-irrelevant. -/
def propositionProjectionIotaUsesLiteralField (type : EIndType) : Bool :=
  type.all == [type.name] && type.ctors.length == 1 && type.numNested == 0 &&
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

/-- Exact serialized boundary for the first recursive indexed fibre tranche.

The sole recursive occurrence must itself be one constructor field, rather
than occur below another former.  Its index is fixed with respect to all
constructor fields, its binder is absent from the constructor result and all
later field types, and the exported recursor has the one-owner/one-rule layout
which the existing Arm-C public interface implements. -/
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
  let mut recursiveIndex? : Option Nat := none
  for fieldIndex in [:fields.size] do
    let fieldType := fields[fieldIndex]!.type
    if fieldType.getUsedConstants.contains type.name then
      let .const fieldOwner _ := fieldType.getAppFn | return false
      unless fieldOwner == type.name &&
          fieldType.getAppArgs.size == type.numParams + type.numIndices do return false
      unless recursiveIndex?.isNone do return false
      let recursiveIndices := fieldType.getAppArgs.extract type.numParams
        (type.numParams + type.numIndices)
      for index in recursiveIndices do
        for field in fields do
          if index.containsFVar field.value.fvarId! then return false
      recursiveIndex? := some fieldIndex
  let some recursiveIndex := recursiveIndex? | return false
  let recursiveId := fields[recursiveIndex]!.value.fvarId!
  if result.containsFVar recursiveId then return false
  for later in [recursiveIndex + 1:fields.size] do
    if fields[later]!.type.containsFVar recursiveId then return false
  return true

/-- The indexed fibre adapter's complete source-syntax boundary.  The original
nonrecursive family and the first fixed-index recursive family share this
predicate in generation and checking; the complete eight-declaration
certificate, not shape alone, authorizes literal dependent projection rules. -/
def indexedFibreOneLayerProjectionFamily (types : Array EIndType)
    (type : EIndType) (constructor : ECtor) (recursor : ERec) : Bool := Id.run do
  unless types.size == 1 && type.all == [type.name] &&
      type.ctors == [constructor.name] && type.numIndices == 1 &&
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

private partial def occurs (needle : Expr) : Expr → Bool
  | expression =>
    if expression == needle then true else
    match expression with
    | .app function argument => occurs needle function || occurs needle argument
    | .lam _ type body _ | .forallE _ type body _ =>
      occurs needle type || occurs needle body
    | .letE _ type value body _ =>
      occurs needle type || occurs needle value || occurs needle body
    | .mdata _ body => occurs needle body
    | .proj _ _ structureExpr => occurs needle structureExpr
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => false

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
binder types, in telescope order. -/
def dependencies (fields : Array ProjectionField) (target : Nat) : Array Nat := Id.run do
  if target >= fields.size then return #[]
  let mut needed := Array.replicate target false
  for i in (List.range target).reverse do
    let mut used := occurs fields[i]!.value fields[target]!.type
    if !used then
      for k in [i + 1:target] do
        if needed[k]! && occurs fields[i]!.value fields[k]!.type then
          used := true
          break
    if used then needed := needed.set! i true
  return (Array.range target).filter (needed[·]!)

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
transitive dependency closure and no recursor for an irrelevant field. -/
def normalizeProjectionField (eqi : EqInfo) (tag : Name)
    (fields : Array ProjectionField) (target : Nat) : Except String Expr := do
  if target >= fields.size then throw s!"projection field {target} is absent"
  normalizedWith eqi tag fields target (fields.map (·.value)) (fields.map (·.iota?))

end ProjectionField
end InductiveModels
