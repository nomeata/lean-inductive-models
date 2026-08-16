import InductiveModels.Simple.Church

open Lean Meta

namespace InductiveModels

/-! ## Arm G: the recursive subsingleton, by the **graph** of the recursion

This is the arm that emits the graph-and-choice carrier for an arbitrary
supported shape, taking **`Acc` out of the basis** rather than putting it to
use.

The shape: an inductive `Prop` with **one** constructor, each of whose fields
is a proposition (possibly a recursive occurrence `∀ z⃗, T p⃗ e⃗`) or a piece of
data that is *literally* one of the conclusion's indices. Lean's kernel grants
that shape a `Sort v` motive by the subsingleton rule — a grant to a
*declaration* that an emitted `def` does not inherit — and the carrier the
Church route already emits eliminates only into `Prop`. So the large
eliminator has to be built, and it is built by defining the recursion by its
**graph**:

```text
Graph ι⃗ t val  := the least relation closed under "if the value at every
                   recursive sub-argument is g, then the value at (mk f⃗) is
                   step f⃗ g⃗", impredicatively encoded — so a Prop
Graph.mk        : that closure rule, as a theorem (the graph is a fixed
                   point, not merely a pre-fixed point)
GraphInv        : inversion, with the constructor's **proof** fields
                   universally quantified rather than existentially — any two
                   are definitionally equal, so quantifying gives the caller's
Graph.inv       : inversion holds, by folding at `Graph ∧ GraphInv`
Graph.unique    : single-valuedness, by the free `Prop`-motive recursor
Graph.exists    : totality, likewise, picking sub-values with Classical.choice
rec_0 step t    := (Classical.choice (Graph.exists step t)).fst
iota            : both sides are graph points and the graph is single-valued
```

**Do not** try `Classical.choice` at a bare `Nonempty (motive a t)` instead.
That recursor typechecks and is provably *blind to its step function* — the
two `Nonempty` proofs are definitionally equal — so its ι rule is not merely
unproved but derives `False`; expanding the construction gives the refutation.

**ι is propositional here, not `Eq.refl`** — the value is a `Classical.choice`
application, which reduces to nothing — and this is the only arm of the three
routes for which that is true. A consumer must rewrite with `iota_0_0` where
the kernel would have reduced.

**Two lines of the recipe are shape-sensitive**, and both are mechanical:
[`InductiveModels.congrChain`]'s n-ary congruence, one factor per recursive field,
and [`InductiveModels.funextUp`]'s chain, one `funext` per binder of a recursive
field. The recipe is checked across the three shapes that settle them.

**The axiom cost is per shape, not per arm.** `rec_0` is `Classical.choice`
uniformly; ι adds `funext` — hence the quotient and `Quot.sound` — only when
some recursive field has a binder, because that is the only thing
[`InductiveModels.funextUp`] is called for. A recursive field that is a bare
occurrence contributes none, and the degenerate shape's ι costs no
`Quot.sound` at all. -/

/-- `∀ D : Prop, (A → B → D) → D` — Church conjunction, so the folds below
need no `And` and the basis needs no sixth member for one. -/
def andCOf (A B : Expr) : Expr :=
  .forallE `D (.sort .zero)
    (.forallE `k (.forallE `a A (.forallE `b B (.bvar 2) .default) .default)
      (.bvar 1) .default) .default

/-- `Eq α x z` from `Eq α x y` and `Eq α y z`, as one `Eq.rec` at a `Prop`
motive — the companion of [`InductiveModels.symmOf`], and built the same way so that
nothing is added to the input that this module does not need to name. -/
def transOf (eqi : EqInfo) (ℓ : Level) (α x y z h1 h2 : Expr) : GenM Expr :=
  transportAlong eqi .zero ℓ α y z h2 h1 fun w => pure (eqi.mk' ℓ α x w)

/-- Bind a vector of **independent** locals in one scope. Independent is the
precondition and it is met at every call: the value functions `g⃗` depend only
on the constructor's fields, and the graph hypotheses `hg⃗` only on those and
on `g⃗`, which are bound first. -/
partial def withLocalsD (tys : Array (Name × Expr)) (i : Nat) (acc : Array Expr)
    (k : Array Expr → GenM Expr) : GenM Expr := do
  if i == tys.size then k acc
  else withLocalDeclD tys[i]!.1 tys[i]!.2 fun x => withLocalsD tys (i + 1) (acc.push x) k

/-- **Walk the constructor's field telescope**, binding one variable per
field — except that with `subst` set the *data* fields are **supplied** from
`is` rather than bound, because in this shape a data field is literally one of
the conclusion's indices.

That substitution is what `GraphInv` is stated by: inversion at an arbitrary
index `ι⃗` must conclude `val = step f⃗ g⃗`, whose right-hand side lands at the
quantified fields' own index expressions, so those expressions have to *be*
`ι⃗` — **definitionally**, which at a pivot means the same term and at an
index position typed by a `Prop` means proof irrelevance. Quantifying the data
fields instead would need the index's injectivity, which is not uniform.

`k` receives the full field vector, the ones actually bound, and the
telescope's result type. -/
partial def ctorFieldsAux (subst : Bool) (isData : Array Bool) (idxPos : Array Nat)
    (is : Array Expr) (n i : Nat) (tele : Expr) (fs bound : Array Expr)
    (k : Array Expr → Array Expr → Expr → GenM Expr) : GenM Expr := do
  if n == 0 then return ← k fs bound tele
  let .forallE x d b bi := tele | badShape "telescope shorter than its field count"
  if subst && isData[i]! then
    let a := is[idxPos[i]!]!
    ctorFieldsAux subst isData idxPos is (n - 1) (i + 1) (b.instantiate1 a) (fs.push a) bound k
  else
    withLocalDecl x bi d fun xv =>
      ctorFieldsAux subst isData idxPos is (n - 1) (i + 1) (b.instantiate1 xv)
        (fs.push xv) (bound.push xv) k

/-- **The `funext` chain, one per binder of a recursive field.** `pt` proves
`ga z⃗ = gb z⃗` at the field's own binders `z⃗`; this closes them one at a time,
innermost first, into `ga = gb`.

At **zero** binders it is the identity and no `funext` is reached at all —
which is why the degenerate shape's ι costs no `Quot.sound`, and why the
`funext` is asked for lazily and only when some recursive field has a
binder. -/
partial def funextUp (fx? : Option Name) (zs : Array Expr) (k : Nat)
    (ga gb pt : Expr) : GenM Expr := do
  if k == 0 then return pt
  let j := k - 1
  let z := zs[j]!
  let some fxN := fx?
    | badShape "a recursive field under a binder needs funext and none was available"
  let αz ← ityp z
  let lu ← ilevel αz
  let fa := mkAppN ga (zs.extract 0 j)
  let fb := mkAppN gb (zs.extract 0 j)
  let bty ← ityp (mkApp fa z)
  let lv ← ilevel bty
  let β ← mkLambdaFVars #[z] bty
  let h ← mkLambdaFVars #[z] pt
  funextUp fx? zs j ga gb (mkAppN (.const fxN [lu, lv]) #[αz, β, fa, fb, h])

/-- **The n-ary congruence in the recursive fields**, as an `Eq.trans` chain
with one `congrArg` per field:

```text
step f⃗ ga₁ ga₂ … = step f⃗ gb₁ ga₂ … = step f⃗ gb₁ gb₂ … = … = step f⃗ gb⃗
```

The single `congrArg (step x h)` is the `n = 1` case of this and is
insufficient at two recursive fields. Each `congrArg` is one `Eq.rec`, inlined here for the same
reason [`InductiveModels.funextDecl`] inlines its own. -/
def congrChain (eqi : EqInfo) (v : Level) (α : Expr) (mkStep : Array Expr → Expr)
    (ga gb pfs : Array Expr) : GenM Expr := do
  let n := ga.size
  let mixed := fun (j : Nat) => (Array.range n).map fun m => if m < j then gb[m]! else ga[m]!
  let base := mkStep ga
  let mut acc := eqi.refl' v α base
  for j in [0:n] do
    let A ← ityp ga[j]!
    let ℓA ← ilevel A
    let famAt := fun (x : Expr) => mkStep ((mixed j).set! j x)
    let factor ← transportAlong eqi .zero ℓA A ga[j]! gb[j]! pfs[j]!
      (eqi.refl' v α (famAt ga[j]!)) fun z => pure (eqi.mk' v α (famAt ga[j]!) (famAt z))
    acc ← transOf eqi v α base (mkStep (mixed j)) (mkStep (mixed (j + 1))) acc factor
  return acc

end InductiveModels
