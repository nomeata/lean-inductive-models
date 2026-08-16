import InductiveModels.Simple.Kit

open Lean Meta

namespace InductiveModels

/-! ## The singleton at an arbitrary level

`Sort ℓ` for a **bare or variable** `ℓ` is out of every *other* basis former's
reach — `Eq` and `Acc` land in `Prop`, `Nat` in `Type`, and a Π lands there
only through an `imax` collapse, which needs
a `Sort ℓ`-valued *body*. The tight-pair/PUnit composite lands there for
**any** `ℓ` whatsoever and — unlike the `False`-Π family the old basis used —
is empty exactly when its proposition is. Thus its lifted `⊤` is the
singleton below and its lifted `⊥` is [`InductiveModels.emptyAt`].

Like [`InductiveModels.dsingAt`]'s pads the singleton **is** definitionally
canonical — *every element is defeq to [`InductiveModels.unitAtCanon`]*, by structure
eta on `PSigma'` and `PUnit` against the literal pair plus proof irrelevance on `⊤` — so
wherever one is destructed the applied minor already has the target type and
no transport rides along. This is where the `False`-Π singleton cost a
`funext`, and it is why the destructor needs no transport at all and ι is
`Eq.refl` with nothing to erase.

**Read "canonical" narrowly.** What holds is `t ≡ canon`, where one side is a
constructor application and eta expands the other. What does *not* hold is
`x ≡ y` for two opaque inhabitants: no side is a redex, so the kernel refuses
it — see [`InductiveModels.puliftEta`].
Every use below is of the first kind. -/

/-- The singleton at exactly `Sort ℓ`: the lift of `⊤`. -/
def unitAt (ℓ : Level) : Expr := puliftT ℓ trueP

/-- Its canonical element. -/
def unitAtCanon (ℓ : Level) : Expr := puliftUp ℓ trueP trueI

/-- `Eq canon t` for `t : unitAt ℓ`. [`InductiveModels.puliftEta`] proves
`Eq (up (down t)) t`, and `up (down t)` is *definitionally* the canonical
element: both components are proofs of `⊤`, and proof irrelevance closes it.
No `funext`.

[`InductiveModels.padsAt`] marks both current pad families `canonical := true`, because
`t ≡ canon` is a conversion the kernel performs (the canonical element is a
literal `up`, so eta expands `t` against it). Consequently
[`InductiveModels.chainDestruct`] takes its no-transport branch for the lift pad as
well as for the `D` pad. This function makes the generic `canonical := false`
branch total, and its behavior is measured rather than assumed: forcing the
lift pad through here by setting
`canonical := false` leaves every `prim_shapes` occupant modelling, and
forcing the `D` pad through here — where the proof is about the wrong type —
is red at `Tri`, `Opt`, `Dec` and `Big`. -/
def unitAtUniq (eqi : EqInfo) (ℓ : Level) (t : Expr) : Expr :=
  puliftEta eqi ℓ trueP t

/-- Is a pad at this level buildable? [`InductiveModels.dsingAt`]'s domain, asked
before anything is spliced so that a decline costs no splice. -/
partial def dsingOk (ℓ : Level) : Bool :=
  match ℓ.normalize with
  | .succ _ => true
  | .max a b => dsingOk a && dsingOk b
  | _ => false

/-- A **definitionally-canonical singleton at exactly `Sort ℓ`**: every
element is *defeq* to the canonical one, by `PUnit` eta, tight-pair eta and
proof irrelevance on the components — so a pad costs no transport and no
`funext`, and ι stays `Eq.refl`.

`D 1 := PUnit.{1}`; `D (a+1) :=
(α : Sort a) → D 1`, whose Π is at `imax (a+1) 1 = a+1`; `D (max a b) :=
Σ'(_ : D a), D b`. -/
partial def dsingAt (ℓ : Level) : GenM (Expr × Expr) := do
  let d1 := punitT (.succ .zero)
  let c1 := punitUnit (.succ .zero)
  match ℓ.normalize with
  | .succ .zero => return (d1, c1)
  | .succ a =>
    return (.forallE `α (.sort a) d1 .default, .lam `α (.sort a) c1 .default)
  | .max a b =>
    let (ta, ca) ← dsingAt a
    let (tb, cb) ← dsingAt b
    let β := Expr.lam `x ta tb .default
    return (psigmaT a b ta β, psigmaMk a b ta β ca cb)
  | _ => badShape s!"no pad at Sort {ℓ}"

/-- A chain's pad: its type, its type's level, and its canonical element.

`canonical` says whether every element is **defeq** to `canon`, in which case
no uniqueness proof rides along. **Both families set it**: the
[`InductiveModels.dsingAt`] pad by `PSigma'`/`PUnit` structure eta, and
the [`InductiveModels.unitAt`] lift — used at a level `dsingOk` cannot build, a bare
parameter in the gap, `PULift`'s shape — by tight-pair and unit structure eta
against the literal pair that `canon` is. Thus current planners do not select
the `false` case; [`InductiveModels.unitAtUniq`] is the generic transport branch, and
the measurement that validates it is in that docstring. -/
structure Pad where
  ty : Expr
  lv : Level
  canon : Expr
  canonical : Bool

/-! ## Boxing a field whose level is an `imax`

A Π-typed field's level is an `imax` chain — `Trans.mk`'s field `(a b c : …) →
r a b → s b c → t a c` reaches `Sort (imax u₁ (imax u₂ (imax u₃ (imax u
(imax v w)))))` — and no pad absorbs an `imax`: level defeq is normal-form
equality, and a `max` does not subsume an `imax` term even when both its sides
are present. What collapses it is making every Π codomain never-`Prop`:
`imax a b = max a b` once `b` cannot be zero.

The boxing below is therefore recursive.  At an atomic type `S` it uses
`Σ' (_ : S), D 1`; at `∀ x : A, B x` it stores a function from the recursively
boxed `A` to the recursively boxed `B (unbox x)`.  The contravariant domain
conversion is essential for a field such as `((α → β) → β)`: boxing only its
outer codomain leaves the inner domain level `imax u v`, while recursive
boxing produces `(Box α → Box β) → Box β` at the literal level `max 1 u v`.

The box pad is `D 1`, every element of which is defeq to canonical.  By
induction over the Π telescope, `unbox (box v) ≡ v` and `box (unbox y) ≡ y`
hold by βι, `PSigma'` structure eta, proof irrelevance and function eta alone:
no transport, no axiom, and ι stays `Eq.refl`. -/

/-- Is there an `imax` anywhere in the level? Asked of normal forms: a level
the pads cannot absorb. -/
partial def levelHasIMax : Level → Bool
  | .imax .. => true
  | .max a b => levelHasIMax a || levelHasIMax b
  | .succ a => levelHasIMax a
  | _ => false

/-- The universe of [`InductiveModels.boxTyOf`] without constructing its `PSigma'`
terms. The W arm asks its tower-level question before primitives are spliced,
so this level-only mirror keeps that early, rollback-free guard while using the
same recursive Π shape as the actual box. -/
partial def boxLevelOf (t : Expr) : GenM Level := do
  match ← whnf t with
  | .forallE name domain body info =>
    let domainLevel ← boxLevelOf domain
    withLocalDecl name info domain fun x => do
      let bodyLevel ← boxLevelOf (body.instantiate1 x)
      return (mkLevelIMax domainLevel bodyLevel).normalize
  | atomic =>
    let level ← ilevel atomic
    return (mkLevelMax' (.succ .zero) level).normalize

mutual

  /-- The recursively boxed type.  Atomic leaves are paired with `D 1`; a Π
  recursively boxes its domain and codomain, substituting the unboxed domain
  value into the dependent codomain. -/
  partial def boxTyOf (t : Expr) : GenM Expr := do
    match ← whnf t with
    | .forallE name domain body info =>
      let boxedDomain ← boxTyOf domain
      withLocalDecl name info boxedDomain fun boxedValue => do
        let value ← unboxValOf domain boxedValue
        let boxedBody ← boxTyOf (body.instantiate1 value)
        mkForallFVars #[boxedValue] boxedBody
    | atomic =>
      let level ← ilevel atomic
      let (d1, _) ← dsingAt (.succ .zero)
      return psigmaT level (.succ .zero) atomic (.lam `x atomic d1 .default)

  /-- Recursively box a value, contravariantly unboxing each Π argument before
  applying the original function. -/
  partial def boxValOf (t v : Expr) : GenM Expr := do
    match ← whnf t with
    | .forallE name domain body info =>
      let boxedDomain ← boxTyOf domain
      withLocalDecl name info boxedDomain fun boxedValue => do
        let value ← unboxValOf domain boxedValue
        let result ← boxValOf (body.instantiate1 value) (mkApp v value)
        mkLambdaFVars #[boxedValue] result
    | atomic =>
      let level ← ilevel atomic
      let (d1, c1) ← dsingAt (.succ .zero)
      return psigmaMk level (.succ .zero) atomic (.lam `x atomic d1 .default) v c1

  /-- Recursively unbox a value, boxing each original Π argument before
  applying the stored function. -/
  partial def unboxValOf (t v : Expr) : GenM Expr := do
    match ← whnf t with
    | .forallE name domain body info =>
      withLocalDecl name info domain fun value => do
        let boxedValue ← boxValOf domain value
        let result ← unboxValOf (body.instantiate1 value) (mkApp v boxedValue)
        mkLambdaFVars #[value] result
    | atomic =>
      let level ← ilevel atomic
      let (d1, _) ← dsingAt (.succ .zero)
      let β := Expr.lam `x atomic d1 .default
      let motive := Expr.lam `p (psigmaT level (.succ .zero) atomic β) atomic .default
      let minor := Expr.lam `fst atomic (.lam `snd d1 (.bvar 1) .default) .default
      return psigmaRec level level (.succ .zero) atomic β motive minor v

end

end InductiveModels
