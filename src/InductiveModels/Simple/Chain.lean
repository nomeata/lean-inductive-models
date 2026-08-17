import InductiveModels.Simple.Box

open Lean Meta

namespace InductiveModels

/-! ## One constructor's chain

A constructor's field telescope becomes a right-nested `PSigma'` at exactly
`Sort w`. The builders below recurse on the (progressively instantiated)
telescope expression, so nothing is stored across scopes. `pad?` closes the
chain when the field levels do not already reach `w` — and always for a
nullary constructor. `boxed` says, per field, whether the field is stored
boxed ([`InductiveModels.boxTyOf`]); a later field's type always depends on the
*unboxed* value, so the recursions instantiate with `unbox` of the bound
variable and the real value stays what the minor is applied to. -/

/-- The chain's type and level. `nf` is the field count; the telescope's
trailing result type is never entered.

**A rung whose tail does not mention the field is written down rather than
abstracted.** `mkLambdaFVars #[xv] inner` traverses everything above the rung
to abstract a variable out of it and then binds it at `xv`'s own name, binder
info and (head-beta-reduced) type; where the tail holds no `xv` there is
nothing to abstract, and the direct `.lam` is the term it would have returned
to the byte — `Lean.MetavarContext.mkBinding` binds a `cdecl` at
`mkLambda' userName binderInfo type.headBeta`, and `abstractRange` over a
variable that does not occur is the identity.

**And the question is asked before the instantiation, so there is no mask to
build.** This walk descends by `rest.instantiate1`, and `instantiate1` is what
renumbers the loose variables, so at every rung `rest`'s own `bvar 0` is this
field and `rest.hasLooseBVar 0` is exactly "does what is left mention it" — one
header comparison on `Expr`, with no per-telescope precomputation and nothing
carried between rungs. The whole binder is then skipped: with the field absent
from `rest` the instantiation is the identity, so the tail is built in the
outer scope and `withLocalDeclD` is never entered.

The question is asked of the remaining telescope entire, which includes the
constructor's trailing result type. That is conservative in the one direction
that costs only instructions: an index the field appears in keeps the binder a
field alone would not have needed.

**And a constant family is a binder holding nothing.** `PSigma' α (fun _ => β)`
is `PProd' α β` with a lambda in front of it, so with `pairs` the rung is built
at the binder-free pair outright — the same pair at the same `Sort (max u v)`,
carrying the tail as a type rather than as a family
([`InductiveModels.pprodPrimeDecl`]). `pairs` is false at one owner only, the
pair itself, which may not be modelled by a tower built out of it; the never-zero
tuple tower does not in fact reach `PProd'`, whose own `Sort (max u v)` is
maybe-zero and takes the direct route, so the flag is a guard and not a
branch this arm exercises. -/
partial def chainTy (pairs : Bool) (pad? : Option Pad) (boxed : Array Bool) (nf : Nat)
    (tele : Expr) (i : Nat := 0) : GenM (Expr × Level) := do
  if nf == 0 then
    let some p := pad? | badShape "a chain with no fields needs a pad"
    return (p.ty, p.lv)
  let .forallE x t rest _ := tele | badShape "field telescope shorter than the field count"
  let bx := boxed[i]?.getD false
  let st ← if bx then boxTyOf t else pure t
  let ℓt ← ilevel st
  if nf == 1 && pad?.isNone then
    return (st, ℓt)
  unless rest.hasLooseBVar 0 do
    let (inner, ℓi) ← chainTy pairs pad? boxed (nf - 1) rest (i + 1)
    let second := if pairs then inner else .lam x st.headBeta inner .default
    return ((if pairs then pprodT else psigmaT) ℓt ℓi st second,
      (mkLevelMax' ℓt ℓi).normalize)
  withLocalDeclD x st fun xv => do
    let rv ← if bx then unboxValOf t xv else pure xv
    let (inner, ℓi) ← chainTy pairs pad? boxed (nf - 1) (rest.instantiate1 rv) (i + 1)
    return (psigmaT ℓt ℓi st (← mkLambdaFVars #[xv] inner),
      (mkLevelMax' ℓt ℓi).normalize)

/-- **The rung a chain type already spells out**: its two levels, its stored
component's type and its tail family, read back off the pair
[`InductiveModels.chainTy`] built rather than rebuilt from the telescope.

`chain` is the type of the value being taken apart or put together, so it is
already in every caller's hand — `stepTower` binds its scrutinee at it and
[`InductiveModels.PCtor`] carries it beside the telescope it was built from.
Rebuilding it was the tower's quadratic: at rung `i` both the tuple and the
destructor called `chainTy` again on the *whole* tail, and each rebuild ends in
a `mkLambdaFVars` that traverses everything above the rung, so a chain of `n`
fields paid `O(n²)` rung constructions over terms that grow with the fields'
own size.

Reading the rung off the type is also the stronger statement, and it is what
makes the binder-free rung cost nothing to agree about. The rebuilt rung had to
*agree* with the scrutinee's type for the recursor to be well typed, and nothing
but the kernel gate said it did; the components below are that type's own, so
the constructor and the destructor cannot disagree with the carrier about which
of the two pairs a rung was built at — `binderFree` is read off the carrier
rather than re-derived beside it, and there is no second dependency question to
answer the same way twice.

`β` is the tail's **family** at a `PSigma'` rung and the tail's **type** at a
binder-free `PProd'` one; `binderFree` is which. -/
def chainRung (chain : Expr) : GenM (Bool × Level × Level × Expr × Expr) := do
  match chain with
  | .app (.app (.const `PSigma' [ℓt, ℓi]) st) β => return (false, ℓt, ℓi, st, β)
  | .app (.app (.const `PProd' [ℓt, ℓi]) st) β => return (true, ℓt, ℓi, st, β)
  | _ => badShape "the chain's rung is not either pair its carrier could be built at"

/-- The tuple `⟨v₁, ⟨v₂, …⟩⟩` at the given field values — each boxed where its
plan says so — closed by the pad's canonical element when there is one.
`chain` is [`InductiveModels.chainTy`] of `tele`, i.e. the tuple's own type. -/
partial def chainTuple (pairs : Bool) (pad? : Option Pad) (boxed : Array Bool) (nf : Nat)
    (tele : Expr) (chain : Expr) (vals : Array Expr) (i : Nat := 0) : GenM Expr := do
  if nf == 0 then
    let some p := pad? | badShape "a chain with no fields needs a pad"
    return p.canon
  let .forallE _ t rest _ := tele | badShape "field telescope shorter than the field count"
  let bx := boxed[i]?.getD false
  let sv ← if bx then boxValOf t vals[i]! else pure vals[i]!
  if nf == 1 && pad?.isNone then
    return sv
  let (binderFree, ℓt, ℓi, st, β) ← chainRung chain
  let tailTele := rest.instantiate1 vals[i]!
  -- **The tail's own chain type.** Where a later field's type mentions this
  -- one the tuple descends at the *value* while `β` abstracts at a variable,
  -- so the two are the same type only up to that substitution and the tail is
  -- built for real. Where it does not, the rung carries the tail with no binder
  -- at all — or, at a tower denied the pair, a constant family whose body is
  -- that same tail, at the identical telescope since `rest` survives either
  -- instantiation — so the descent costs nothing.
  let tailChain ←
    if binderFree then pure β
    else if rest.hasLooseBVar 0 then
      Prod.fst <$> chainTy pairs pad? boxed (nf - 1) tailTele (i + 1)
    else
      pure (mkApp β vals[i]!).headBeta
  let snd ← chainTuple pairs pad? boxed (nf - 1) tailTele tailChain vals (i + 1)
  return (if binderFree then pprodMk else psigmaMk) ℓt ℓi st β sv snd

/-- The recursor's destructor for one chain: from `scrut : chain`, an
element of `target (wrap scrut)` — `wrap` embeds a suffix value into the
full tuple (the identity at the top) and `target` is `fun tup => M ⟨j̄,
tup⟩`. The minor is applied to the collected fields, each unboxed where the
plan boxed it. A canonical pad costs nothing — `scrut` is defeq to its
canonical element. A [`InductiveModels.unitAt`] pad is discharged by transporting
the applied minor along [`InductiveModels.unitAtUniq`], and on a constructor
application that proof is a closed self-equality which K-like reduction on
`Eq.rec` erases — ι stays `Eq.refl` on both.

`chain` is `scrut`'s type, [`InductiveModels.chainTy`] of `tele`, and it is
what every rung is read off ([`InductiveModels.chainRung`]): the walk down the
chain builds no type at all, because each rung's second component already
carries the next rung's — and it is that component, and not a mask recomputed
here, that says whether the rung is the tight pair or the binder-free one and
so which projection-derived `rec'` takes it apart. -/
partial def chainDestruct (v : Level) (eqi : EqInfo)
    (pad? : Option Pad) (boxed : Array Bool) (nf : Nat) (tele : Expr) (chain : Expr)
    (scrut : Expr)
    (wrap : Expr → Expr) (target : Expr → GenM Expr)
    (minorAt : Array Expr → Expr) (vals : Array Expr := #[]) (i : Nat := 0) : GenM Expr := do
  if nf == 0 then
    let some p := pad? | badShape "a chain with no fields needs a pad"
    if p.canonical then
      -- `scrut` is defeq to the pad's canonical element, so the applied minor
      -- already has the target type.
      return minorAt vals
    -- A lift pad: transport along its eta. No axiom rides along.
    return ← transportAlong eqi v p.lv p.ty p.canon scrut
      (unitAtUniq eqi p.lv scrut) (minorAt vals) (fun z => target (wrap z))
  let .forallE x t rest _ := tele | badShape "field telescope shorter than the field count"
  let bx := boxed[i]?.getD false
  if nf == 1 && pad?.isNone then
    let rv ← if bx then unboxValOf t scrut else pure scrut
    return minorAt (vals.push rv)
  let (binderFree, ℓt, ℓi, st, β) ← chainRung chain
  let mkAt := if binderFree then pprodMk else psigmaMk
  let motive ← withLocalDeclD `s chain fun s => do
    mkLambdaFVars #[s] (← target (wrap s))
  let m ← withLocalDeclD x st fun xv => do
    let rv ← if bx then unboxValOf t xv else pure xv
    -- The tail's chain type, which the rung's second component already carries:
    -- at a binder-free rung it *is* that component, and at a rung with a family
    -- the recursion descends at the very variable the family abstracts, so this
    -- is what rebuilding the tail would have returned. It is `s`'s type either
    -- way.
    let tailChain := if binderFree then β else (mkApp β xv).headBeta
    withLocalDeclD `s tailChain fun s => do
      let wrap' := fun (z : Expr) => wrap (mkAt ℓt ℓi st β xv z)
      mkLambdaFVars #[xv, s] (← chainDestruct v eqi pad? boxed (nf - 1)
        (rest.instantiate1 rv) tailChain s wrap' target minorAt (vals.push rv) (i + 1))
  return (if binderFree then pprodRec else psigmaRec) v ℓt ℓi st β motive m scrut

end InductiveModels
