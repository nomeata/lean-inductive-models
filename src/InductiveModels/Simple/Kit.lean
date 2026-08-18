import InductiveModels.Simple.Basis

open Lean Meta

namespace InductiveModels

/-! ## Expression kit -/

/-- `succ^j zero` — a tag, as constructor chains so the splice needs no
literal support. -/
def natNumeral : Nat → Expr
  | 0 => .const `Nat.zero []
  | j + 1 => .app (.const `Nat.succ []) (natNumeral j)

/-- `succ^j e`. -/
def natSuccs : Nat → Expr → Expr
  | 0, e => e
  | j + 1, e => .app (.const `Nat.succ []) (natSuccs j e)

def psigmaT (u v : Level) (α β : Expr) : Expr :=
  psigmaPrimeT u v α β

def psigmaMk (u v : Level) (α β fst snd : Expr) : Expr :=
  psigmaPrimeMk u v α β fst snd

def psigmaRec (s u v : Level) (α β motive m t : Expr) : Expr :=
  psigmaPrimeRec u v s α β motive m t

/-- `PSigma'.fst`. Structure eta makes `⟨fst y, snd y⟩ ≡ y`
for a neutral `y`, which is what lets a tuple be taken apart and put back
together with no transport. -/
def psigmaFst (u v : Level) (α β y : Expr) : Expr :=
  psigmaPrimeFst u v α β y

/-- `PSigma'.snd`, at the dependent fibre `β (fst y)`. -/
def psigmaSnd (u v : Level) (α β y : Expr) : Expr :=
  psigmaPrimeSnd u v α β y

/-! ### The binder-free pair

`PProd'` is the tight pair with the second component's binder removed, at the
same `Sort (max u v)` ([`InductiveModels.pprodPrimeDecl`]).  The fields no later
field's type mentions need no binder at all, so both storage towers carry them
beneath their spine in a balanced binary tree of this pair
([`InductiveModels.blockTy`]).  Spelled through the same thin wrappers the tight
pair is, so a construction reads one shape or the other and never a bare
`.const`.

There is no eliminator wrapper here, and there is no eliminator to wrap: the
block is *read* by primitive projection ([`InductiveModels.blockPaths`],
[`InductiveModels.tightBlockProjs`]), so the pair is only ever built and
projected. -/

def pprodT (u v : Level) (α β : Expr) : Expr :=
  pprodPrimeT u v α β

def pprodMk (u v : Level) (α β fst snd : Expr) : Expr :=
  pprodPrimeMk u v α β fst snd

def natRec (s : Level) (motive z sc t : Expr) : Expr :=
  mkAppN (.const `Nat.rec [s]) #[motive, z, sc, t]

/-! ### The two Church propositions, and the derived exact-sort lift

`False` is no longer a primitive, so the two propositions the constructions
seed with are written out: `⊥ := ∀ p : Prop, p` and `⊤ := ∀ C : Prop, C → C`.
Both are pure Π — they consume no primitive at all. What they lack is `⊥`'s
`Sort w` eliminator, which [`InductiveModels.cfalseElim`] supplies from `Nat` and
`Eq`. -/

/-- The always-true proposition `∀ C : Prop, C → C`, and its inhabitant. -/
def trueP : Expr :=
  .forallE `C (.sort .zero) (.forallE `c (.bvar 0) (.bvar 1) .default) .default
def trueI : Expr :=
  .lam `C (.sort .zero) (.lam `c (.bvar 0) (.bvar 0) .default) .default

/-- **Church `False`**: `∀ p : Prop, p`. Small elimination is instantiation;
large elimination is [`InductiveModels.cfalseElim`]. -/
def falseP : Expr :=
  .forallE `p (.sort .zero) (.bvar 0) .default

/-- `PUnit.{ℓ}` and its canonical inhabitant. -/
def punitT (ℓ : Level) : Expr := .const `PUnit [ℓ]
def punitUnit (ℓ : Level) : Expr := .const `PUnit.unit [ℓ]

/-- The proposition `p` at exactly `Sort ℓ`, for **any** `ℓ` whatsoever,
empty exactly when `p` is: `PSigma'.{0,ℓ} (fun _ : p => PUnit.{ℓ})`.
No declaration named `PULiftP` is emitted or referenced. -/
def puliftT (ℓ : Level) (p : Expr) : Expr :=
  psigmaPrimeT .zero ℓ p (.lam `h p (punitT ℓ) .default)

/-- The derived lift constructor `⟨h, PUnit.unit⟩`. -/
def puliftUp (ℓ : Level) (p h : Expr) : Expr :=
  let fibre := .lam `h p (punitT ℓ) .default
  psigmaPrimeMk .zero ℓ p fibre h (punitUnit ℓ)

/-- The derived lift's arbitrary-sort eliminator, implemented by
`PSigma'.rec'`.  The ignored `PUnit` field is definitionally canonical. -/
def puliftRec (v ℓ : Level) (p motive m t : Expr) : Expr :=
  let fibre := .lam `h p (punitT ℓ) .default
  let minor := .lam `h p
    (.lam `unit (punitT ℓ) (mkApp m (.bvar 1)) .default) .default
  psigmaPrimeRec .zero ℓ v p fibre motive minor t

/-- The derived lift's `down`, its tight pair's first projection. -/
def puliftDown (ℓ : Level) (p t : Expr) : Expr :=
  psigmaPrimeFst .zero ℓ p (.lam `h p (punitT ℓ) .default) t

/-- **The lift's eta is definitional.** Tight-pair structure eta gives
`t ≡ ⟨t.1,t.2⟩`, and polymorphic-unit structure eta gives
`t.2 ≡ PUnit.unit`; hence `t ≡ up (down t)` at every level, including zero.
This is `Eq.refl`, not a recursor call, and exists only for the one place that
needs an equation rather than a conversion.

**The rule fires on a redex, and only on one.** Eta-for-structures expands one
side when the *other* is already a constructor application. So `t ≡ up (down
t)` holds for an opaque `t`, and `t ≡ canon` holds for a literal `canon = up
h`, but `x ≡ y` for two opaque inhabitants does **not** — the kernel refuses it
even when forced past the unifier with `@Eq.refl _ x`, because neither side
gets expanded. It is refused as a *conversion* only: `x = y` is provable, with
no axiom, by routing through `up (down ·)` where every step is a redex, so the
conversion is simply not transitive at this shape. Direct kernel checks pin all
of it.

Two consequences the construction leans on, **both at a redex**. Every element
of the lifted `⊤` is defeq to [`InductiveModels.unitAtCanon`], which is a literal pair,
so a pad built from it needs no transport — the strict improvement on the
`False`-Π pad, whose uniqueness was `funext`. And `motive (up (down t))` and
`motive t` are convertible, so the maybe-zero route's recursor is the `Prop`
route's with `up`/`down` at the ends and nothing in between. Nowhere does the
construction compare two opaque inhabitants, so nothing rests on the claim
that fails. -/
def puliftEta (eqi : EqInfo) (ℓ : Level) (p t : Expr) : Expr :=
  eqi.refl' ℓ (puliftT ℓ p) t

/-- An **empty** type at exactly `Sort w`, for any `w`: the lift of Church
`False`. This is the fibre beyond a tag tower's last constructor, and — at a
maybe-zero `w` — the whole of `PEmpty`'s carrier. -/
def emptyAt (w : Level) : Expr :=
  puliftT w falseP

/-- `Eq.rec.{v,ℓ} α a (fun z _ => fam z) base b h` — transport
`base : fam a` to `fam b` along `h : Eq a b`. -/
def transportAlong (eqi : EqInfo) (v ℓ : Level) (α a b h base : Expr)
    (fam : Expr → GenM Expr) : GenM Expr := do
  let motive ← withLocalDeclD `z α fun z => do
    withLocalDeclD `hz (eqi.mk' ℓ α a z) fun hz => do
      mkLambdaFVars #[z, hz] (← fam z)
  return eqi.recAt v ℓ α a motive base b h

/-- `Eq b a` from `h : Eq a b`, as one `Eq.rec` at a `Prop` motive. -/
def symmOf (eqi : EqInfo) (ℓ : Level) (α a b h : Expr) : GenM Expr :=
  transportAlong eqi .zero ℓ α a b h (eqi.refl' ℓ α a) fun z => pure (eqi.mk' ℓ α z a)

/-- **Church `False`'s `Sort v` eliminator**, which is what lets `False` leave
the basis: from `h : ∀ p : Prop, p` take `h (0 = 1) : 0 = 1`, build the family
`fun n => Nat.rec (fun _ => Sort v) (lift.{v} ⊤) (fun _ _ => C) n` — whose
value at `0` is an *inhabited* type and at `1` is `C` — and transport the
inhabitant along the equation.

`Nat`'s large elimination is what makes the family; `Eq`'s is what transports;
The tight-pair/PUnit lift puts an inhabited type at `Sort v` for a **bare**
`v`, exactly the gap the old basis filled with `False` itself. -/
def cfalseElim (eqi : EqInfo) (v : Level) (C h : Expr) : GenM Expr := do
  let natT : Expr := .const `Nat []
  let unitAt := puliftT v trueP
  let fam := fun (n : Expr) =>
    natRec (.succ v) (.lam `x natT (.sort v) .default) unitAt
      (.lam `m natT (.lam `ih (.sort v) C .default) .default) n
  let eqn := eqi.mk' (.succ .zero) natT (natNumeral 0) (natNumeral 1)
  transportAlong eqi v (.succ .zero) natT (natNumeral 0) (natNumeral 1)
    (.app h eqn) (puliftUp v trueP trueI) (fun z => pure (fam z))

/-- Anything at all out of an inhabitant of [`InductiveModels.emptyAt`]: project the
Church `⊥` out of the lift, then eliminate it. -/
def emptyAtElim (eqi : EqInfo) (v w : Level) (C e : Expr) : GenM Expr :=
  cfalseElim eqi v C (puliftDown w falseP e)

end InductiveModels
