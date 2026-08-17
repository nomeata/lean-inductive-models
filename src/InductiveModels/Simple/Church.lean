import InductiveModels.Simple.Chain

open Lean Meta

namespace InductiveModels

/-! ## The Type route's recursor tower -/

/-- What one constructor contributes, at a given parameter scope. -/
structure PCtor where
  /-- The instantiated field telescope. -/
  tele : Expr
  nf : Nat
  pad? : Option Pad
  /-- Which fields are stored boxed ([`InductiveModels.boxTyOf`]). -/
  boxed : Array Bool
  /-- The chain type. -/
  chain : Expr

instance : Inhabited PCtor := ⟨⟨default, 0, none, #[], default⟩⟩

/-- `F`'s cases tower over `scrut`: `chain_j` at tag `j̄`, empty above. -/
partial def fibreTower (w : Level) (cs : Array PCtor) (j : Nat) (scrut : Expr) :
    GenM Expr := do
  if j == cs.size then
    return emptyAt w
  let natT : Expr := .const `Nat []
  let sc ← withLocalDeclD `n natT fun n' => do
    withLocalDeclD `ih (.sort w) fun ih => do
      mkLambdaFVars #[n', ih] (← fibreTower w cs (j + 1) n')
  return natRec (.succ w) (.lam `x natT (.sort w) .default) cs[j]!.chain sc scrut

/-- The recursor's cases tower over the tag: at level `j` the zero case is
constructor `j`'s destructor and the successor case descends; past the last
constructor the fibre is empty and [`InductiveModels.emptyAtElim`] closes it. `scrut`
is the level's own binder; the original tag is `succ^j scrut`.

**At `cs.size = 0` every tag is already past the last constructor**, so the
tower is that closing case alone with no `Nat.rec` over it at all — which is
the same term the caller used to build beside this function for a
constructorless declaration, and the same term a tag tower with no base
constructor needs. Writing it here rather than at the call site is what makes
this function total: the `cs[j]!` below is otherwise a partial index whose
out-of-range case is a native panic, and "this tower has no constructors" is a
shape, not a fault. -/
partial def stepTower (v w : Level) (eqi : EqInfo) (fib : Expr)
    (tgt : Expr → Expr) (minorOf : Nat → Array Expr → Expr)
    (cs : Array PCtor) (j : Nat) (scrut : Expr) : GenM Expr := do
  let natT : Expr := .const `Nat []
  let mkAt := fun (tag tup : Expr) => psigmaMk (.succ .zero) w natT fib tag tup
  if cs.isEmpty then
    return ← withLocalDeclD `f (emptyAt w) fun f => do
      mkLambdaFVars #[f] (← emptyAtElim eqi v w (tgt (mkAt scrut f)) f)
  let mot ← withLocalDeclD `m natT fun m => do
    let tag := natSuccs j m
    withLocalDeclD `f (mkApp fib tag).headBeta fun f => do
      mkLambdaFVars #[m] (← mkForallFVars #[f] (tgt (mkAt tag f)))
  let zc ← do
    let c := cs[j]!
    withLocalDeclD `f c.chain fun f => do
      let target := fun (tup : Expr) => pure (tgt (mkAt (natNumeral j) tup))
      let minorAt := minorOf j
      mkLambdaFVars #[f]
        (← chainDestruct v eqi c.pad? c.boxed c.nf c.tele c.chain f id target minorAt)
  let sc ← withLocalDeclD `m natT fun m => do
    let inner ←
      if j + 1 == cs.size then
        let tag := natSuccs (j + 1) m
        withLocalDeclD `f (emptyAt w) fun f => do
          mkLambdaFVars #[f] (← emptyAtElim eqi v w (tgt (mkAt tag f)) f)
      else
        stepTower v w eqi fib tgt minorOf cs (j + 1) m
    withLocalDeclD `ih (mkApp mot m).headBeta fun ih =>
      mkLambdaFVars #[m, ih] inner
  return natRec (mkLevelIMax' w v).normalize mot zc sc scrut

/-- The Church minor's type: the constructor's field telescope with the
result swapped for `C`. -/
partial def churchSwap (C : Expr) (nf : Nat) (t : Expr) : GenM Expr := do
  if nf == 0 then return C
  let .forallE x d b bi := t | badShape "telescope shorter than its field count"
  withLocalDecl x bi d fun xv => do
    mkForallFVars #[xv] (← churchSwap C (nf - 1) (b.instantiate1 xv))

/-- The `k_j` binders of the Church encoding, opened in one scope. -/
partial def churchBinders (kTys : Array Expr) (j : Nat) (ks : Array Expr)
    (k : Array Expr → GenM Expr) : GenM Expr := do
  if j == kTys.size then k ks
  else withLocalDeclD (Name.mkSimple s!"k{j}") kTys[j]! fun kv =>
    churchBinders kTys (j + 1) (ks.push kv) k

/-! ## Indices and recursion in the Church encoding

Two features the encoding above does not have, and both are one rewrite of the
minor-premise types away.

**Indices.** Quantify `C` over the whole index telescope instead of over
nothing: `T' p⃗ ι⃗ := ∀ C : (∀ ι⃗, Prop), k⃗ → C ι⃗`, with each minor `k_j`
ending in `C` applied to *constructor j's own* index expressions. The
declaration's parameters are only ever context, never analysed.

**Recursion.** A recursive field `f : ∀ z⃗, T p⃗ e⃗` becomes `∀ z⃗, C e⃗` in the
minor's type and `fun z⃗ => f z⃗ C k⃗` in the fold. Strict positivity for a
single non-nested inductive admits exactly that shape, so a field that mentions
`T` in any *other* position is a nested occurrence and is declined rather than
mis-rewritten. -/

/-- A field of a constructor, classified. `rec? = some nb` says the field is a
recursive occurrence under `nb` binders — `nb = 0` for a bare `T p⃗ e⃗`. -/
structure PField where
  /-- The binder telescope's length, for a recursive field. -/
  rec? : Option Nat
  deriving Inhabited

/-- Recognize an application of `owner` through transparent definitional
wrappers, and return its complete argument vector when its arity is exact.

`whnfUntil` is important here: ordinary `whnf` may continue by unfolding the
owner itself, while a syntactic `getAppFn` rejects a field written through a
transparent former such as `At T i := T i`.  This helper stops at the named
owner.  It is used only for route selection and for recovering recursive
indices; the exported constructor, recursor and iota types are never replaced
by the reduced expression. -/
def ownerAppArgs? (owner : Name) (np ni : Nat) (e : Expr) : GenM (Option (Array Expr)) := do
  let some app ← whnfUntil e owner | return none
  let args := app.getAppArgs
  return if args.size == np + ni then some args else none

/-- Rewrite a constructor's telescope for the Church encoding: recursive
fields' types and the result both get `C` in place of `T p⃗`. Returns the
rewritten telescope and the per-field classification.

`ni` is the index count; the arguments after the first `np` of an occurrence
of `T` are its index expressions, and they are copied verbatim. -/
partial def churchSwapAt (tname : Name) (np ni : Nat) (C : Expr) (nf : Nat) (t : Expr)
    (acc : Array PField := #[]) : GenM (Expr × Array PField) := do
  if nf == 0 then
    -- the constructor's result: `T p⃗ ι⃗_j` ↦ `C ι⃗_j`
    let some args ← ownerAppArgs? tname np ni t
      | badShape s!"a constructor of {tname} does not end in {tname} applied to \
        {np} parameters and {ni} indices"
    return (mkAppN C (args.extract np args.size), acc)
  let .forallE x d b bi := t | badShape "telescope shorter than its field count"
  let mut d' := d
  let mut fld : PField := { rec? := none }
  if mentionsAny #[tname] d then
    let (dd, nb) ← forallTelescope d fun zs res => do
      let some args ← ownerAppArgs? tname np ni res
        | badShape s!"a field of {tname} mentions {tname} other than as a recursive \
          occurrence (∀ z, {tname} p e) — a nested occurrence, which is layer 1's business"
      for z in zs do
        if mentionsAny #[tname] (← ityp z) then
          badShape s!"a recursive field of {tname} binds an argument whose type \
            mentions {tname}"
      return (← mkForallFVars zs (mkAppN C (args.extract np args.size)), zs.size)
    d' := dd
    fld := { rec? := some nb }
  withLocalDecl x bi d' fun xv => do
    -- A later field's type never depends on a recursive one (strict
    -- positivity forbids it), so instantiating with the rewritten binder is
    -- safe exactly where it matters and irrelevant elsewhere.
    let (rest, acc') ← churchSwapAt tname np ni C (nf - 1) (b.instantiate1 xv) (acc.push fld)
    return (← mkForallFVars #[xv] rest, acc')

/-! ## Packing an index telescope

The subsingleton arm's degenerate `r := ⊥` case states
its Henry-Ford equations as **one** `Eq` at the whole index telescope packed
into a right-nested `PSigma'`, rather than one `Eq` per index. It has to: a
later index's type may mention an earlier one — `HEq`'s telescope is
`{β : Sort u} (b : β)`, which is already the dependent worst case — and
separate equations cannot be stated, let alone transported along, in that
situation.

The three functions below are driven by the *packed type* rather than by the
telescope. That is deliberate: reading a component's type back off a built
expression is only valid while nothing has beta-reduced it, and that
assumption has already cost this file two attempts (see
[`InductiveModels.pairArm`]). A `PSigma'` application is stable under everything the
elaborator does to it, so destructuring it is safe. -/

/-- `Σ'(x₁ : A₁) … A_n` over a **subsequence** `sel` of an opened index
telescope, right-nested, with the last selected index's *type* as the final
component — so a one-element selection packs to that type alone, with no
`PSigma'` at all. Closed over the *selected* telescope entries and over nothing
else: an unselected index stays free, which is exactly what the subsingleton
arms need when some index positions are **pivots** — positions the model
substitutes rather than equates — whose variables remain in scope while the
rest are packed around them (`Fmid` in
`test/fixtures/inductive-models/prim_idx.lean` is the shape that
pins it: a pivot sitting *between* two dependent non-pivots, so the second
selected type still mentions the first while the pivot between them is
skipped).

`packTyOf` is this at the full telescope, and every call site that packs every
index goes on using it. -/
partial def packTyAt (is : Array Expr) (sel : Array Nat) (k : Nat) :
    GenM (Expr × Level) := do
  let x := is[sel[k]!]!
  let ty ← ityp x
  let ℓ ← ilevel ty
  if k + 1 == sel.size then return (ty, ℓ)
  let (inner, ℓi) ← packTyAt is sel (k + 1)
  let β ← mkLambdaFVars #[x] inner
  return (psigmaT ℓ ℓi ty β,
    (mkLevelMax' ℓ ℓi).normalize)

/-- `Σ'(x₁ : A₁) … A_n` over an opened index telescope, right-nested, with the
last index's *type* as the final component — so a one-index telescope packs to
that type alone, with no `PSigma'` at all. Closed over the telescope. -/
def packTyOf (is : Array Expr) (k : Nat) : GenM (Expr × Level) :=
  packTyAt is (Array.range is.size) k

/-- Read a `PSigma'` application apart: its two levels, its `α` and its `β`. -/
def psigmaParts (R : Expr) : GenM (Level × Level × Expr × Expr) := do
  let args := R.getAppArgs
  unless R.getAppFn.isConstOf `PSigma' && args.size == 2 do
    badShape "the packed index type is not a PSigma' application"
  let [u, v] := R.getAppFn.constLevels! | badShape "PSigma' carries the wrong level list"
  return (u, v, args[0]!, args[1]!)

/-- The packing of a value vector, driven by the packed type. -/
partial def packChain (n : Nat) (R : Expr) (vs : Array Expr) (k : Nat) : GenM Expr := do
  if n <= 1 then return vs[k]!
  let (u, v, α, β) ← psigmaParts R
  let snd ← packChain (n - 1) (Expr.app β vs[k]!).headBeta vs (k + 1)
  return psigmaMk u v α β vs[k]! snd

/-- The `n` components read back out of a packed term. Structure eta makes
`pack (unpack y) ≡ y`, which is what lets the recursor's motive be stated
about a packed variable and still apply to the declaration's own indices. -/
partial def unpackChain (n : Nat) (R : Expr) (y : Expr) : GenM (Array Expr) := do
  if n <= 1 then return #[y]
  let (u, v, α, β) ← psigmaParts R
  let f := psigmaFst u v α β y
  let sn := psigmaSnd u v α β y
  return #[f] ++ (← unpackChain (n - 1) (Expr.app β f).headBeta sn)

end InductiveModels
