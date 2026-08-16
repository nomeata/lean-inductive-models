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
trailing result type is never entered. -/
partial def chainTy (pad? : Option Pad) (boxed : Array Bool) (nf : Nat) (tele : Expr)
    (i : Nat := 0) : GenM (Expr × Level) := do
  if nf == 0 then
    let some p := pad? | badShape "a chain with no fields needs a pad"
    return (p.ty, p.lv)
  let .forallE x t rest _ := tele | badShape "field telescope shorter than the field count"
  let bx := boxed[i]?.getD false
  let st ← if bx then boxTyOf t else pure t
  let ℓt ← ilevel st
  if nf == 1 && pad?.isNone then
    return (st, ℓt)
  withLocalDeclD x st fun xv => do
    let rv ← if bx then unboxValOf t xv else pure xv
    let (inner, ℓi) ← chainTy pad? boxed (nf - 1) (rest.instantiate1 rv) (i + 1)
    return (psigmaT ℓt ℓi st (← mkLambdaFVars #[xv] inner),
      (mkLevelMax' ℓt ℓi).normalize)

/-- The tuple `⟨v₁, ⟨v₂, …⟩⟩` at the given field values — each boxed where its
plan says so — closed by the pad's canonical element when there is one. -/
partial def chainTuple (pad? : Option Pad) (boxed : Array Bool) (nf : Nat) (tele : Expr)
    (vals : Array Expr) (i : Nat := 0) : GenM Expr := do
  if nf == 0 then
    let some p := pad? | badShape "a chain with no fields needs a pad"
    return p.canon
  let .forallE x t rest _ := tele | badShape "field telescope shorter than the field count"
  let bx := boxed[i]?.getD false
  let sv ← if bx then boxValOf t vals[i]! else pure vals[i]!
  if nf == 1 && pad?.isNone then
    return sv
  let st ← if bx then boxTyOf t else pure t
  let ℓt ← ilevel st
  let (β, ℓi) ← withLocalDeclD x st fun xv => do
    let rv ← if bx then unboxValOf t xv else pure xv
    let (inner, ℓi) ← chainTy pad? boxed (nf - 1) (rest.instantiate1 rv) (i + 1)
    return (← mkLambdaFVars #[xv] inner, ℓi)
  let snd ← chainTuple pad? boxed (nf - 1) (rest.instantiate1 vals[i]!) vals (i + 1)
  return psigmaMk ℓt ℓi st β sv snd

/-- The recursor's destructor for one chain: from `scrut : chainTy`, an
element of `target (wrap scrut)` — `wrap` embeds a suffix value into the
full tuple (the identity at the top) and `target` is `fun tup => M ⟨j̄,
tup⟩`. The minor is applied to the collected fields, each unboxed where the
plan boxed it. A canonical pad costs nothing — `scrut` is defeq to its
canonical element. A [`InductiveModels.unitAt`] pad is discharged by transporting
the applied minor along [`InductiveModels.unitAtUniq`], and on a constructor
application that proof is a closed self-equality which K-like reduction on
`Eq.rec` erases — ι stays `Eq.refl` on both. -/
partial def chainDestruct (v : Level) (eqi : EqInfo)
    (pad? : Option Pad) (boxed : Array Bool) (nf : Nat) (tele : Expr) (scrut : Expr)
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
  let st ← if bx then boxTyOf t else pure t
  let ℓt ← ilevel st
  let (β, ℓi) ← withLocalDeclD x st fun xv => do
    let rv ← if bx then unboxValOf t xv else pure xv
    let (inner, ℓi) ← chainTy pad? boxed (nf - 1) (rest.instantiate1 rv) (i + 1)
    return (← mkLambdaFVars #[xv] inner, ℓi)
  let motive ← withLocalDeclD `s (psigmaT ℓt ℓi st β) fun s => do
    mkLambdaFVars #[s] (← target (wrap s))
  let m ← withLocalDeclD x st fun xv => do
    let rv ← if bx then unboxValOf t xv else pure xv
    withLocalDeclD `s (mkApp β xv).headBeta fun s => do
      let wrap' := fun (z : Expr) => wrap (psigmaMk ℓt ℓi st β xv z)
      mkLambdaFVars #[xv, s] (← chainDestruct v eqi pad? boxed (nf - 1)
        (rest.instantiate1 rv) s wrap' target minorAt (vals.push rv) (i + 1))
  return psigmaRec v ℓt ℓi st β motive m scrut

end InductiveModels
