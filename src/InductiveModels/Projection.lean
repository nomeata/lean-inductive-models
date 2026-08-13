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

/-- The first production one-layer carrier tranche: one recursive member, one
constructor, no indices and no nested occurrences.  Generation and checking
share this predicate so a failed/collision fallback can never make the checker
silently accept the new literal contract from an old transported model. -/
def oneLayerProjectionFamily (types : Array EIndType) (type : EIndType) : Bool :=
  types.size == 1 && type.all == [type.name] && type.ctors.length == 1 &&
    type.numIndices == 0 && type.numNested == 0 && type.isRec &&
    !type.isUnsafe && !type.isReflexive

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
