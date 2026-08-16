import InductiveModels.Simple.Box

open Lean Meta

namespace InductiveModels

/-! ## Arm W's kit

This arm directly emits the tagged W scheme. For a declaration at
`Sort w = Type u`
with constructors `c⃗`:

    D   p⃗ t   := Σ' (a : nrᵗ₁), … Σ' (a : nrᵗₖ), 𝟙        -- ⊥ off the end
    Tel p⃗ t j := Σ' (x : Xⱼ,₁), … Σ' (x : Xⱼ,ₘ), 𝟙        -- ⊥ off the end
    B'  p⃗ t   := Σ' j : Nat, Tel p⃗ t j
    A   p⃗     := Σ' t : Nat, D p⃗ t
    tg  p⃗     := PSigma'.fst

**Both towers end in a unit at exactly `Sort w` and neither may collapse**, and
that is what makes the universes come out: the core fixes `A` and `B'` at the
same `Type u`, a tower over the field types alone lands at `Type (max v⃗)` —
below `u` in general — and there is no `ULift` here to close the gap. Ending
every tower at [`InductiveModels.unitAt`] `w`, which is at exactly `Sort w`, makes the
max exactly `w` for free at every arity including zero.

`Σ'` is `PSigma'` rather than the fragment's `Sigma` for a second reason beside
the levels: a non-recursive field may sit at `Prop`, and `Sigma`'s domain may
not. `PSigma'` is on [`InductiveModels.inductiveBasis`] and its eta is the kernel's
structure eta.

**The junk is uninhabited in both directions and that is load-bearing for
elaboration, not only for correctness.** `D p⃗ t` for `t ≥ nc` and `Tel p⃗ t j`
for `j` past that constructor's recursive-field count are
[`InductiveModels.emptyAt`] `w`; the constructors' and the recursor's junk arms are
discharged from that emptiness, so a junk arm sent to the *unit* does not
quietly produce a `W` bigger than the target — it fails to typecheck. -/

/-- **A `Nat.rec` cascade over a tag**: `armAt k` at `k` for `k < n`, and
`junkAt` from `n` on. This is the shape a generator emits where a human writes
a `match`, and it is a cascade rather than a `match` because a `match` would
mint a `T.match_1` that the model would then owe the output.

`motAt k` is the motive **at depth `k`** — a lambda over the *remaining* index,
whose body speaks of `succ^k` of it — and `s` is the sort that motive lands in.
The two `succ` chains meet because `succ^k (succ t)` and `succ^(k+1) t` are the
same term, so the succ-minor built at depth `k+1` already has the type depth
`k` asks for and no transport rides along.

`n = 0` degenerates to `junkAt` with no `Nat.rec` at all, which is the branch
tower of a constructor with no children. -/
partial def natCascade (s : Level) (n : Nat) (motAt : Nat → GenM Expr)
    (armAt : Nat → GenM Expr) (junkAt : Expr → GenM Expr) (k : Nat) (sc : Expr) :
    GenM Expr := do
  if k == n then return ← junkAt sc
  let mot ← motAt k
  let base ← armAt k
  let step ← withLocalDeclD `t (.const `Nat []) fun t =>
    withLocalDeclD `ih (mkApp mot t).headBeta fun ih => do
      mkLambdaFVars #[t, ih] (← natCascade s n motAt armAt junkAt (k + 1) t)
  return natRec s mot base step sc

/-- The W towers box exactly the components whose level retains an `imax`.
The recursive box is the same one the tuple route uses: exposed Π domains and
codomains are transformed all the way to atomic leaves, so a nested domain such
as `((α → β) → β)` does not leave an `imax` hidden contravariantly. -/
def wTowerBoxed (xs : Array Expr) : GenM (Array Bool) :=
  xs.mapM fun x => return levelHasIMax (← ilevel (← ityp x)).normalize

/-- **One tower's type**, over the fields `xs⟦i…⟧` and ending at the unit at
`Sort w`. `pre` are the unboxed values of earlier components. A boxed binder is
unboxed before it is substituted into later component types, preserving the
original dependent telescope. -/
partial def wTowerTy (w : Level) (xs : Array Expr) (boxed : Array Bool)
    (i : Nat) (pre : Array Expr := #[]) : GenM Expr := do
  if i == xs.size then return unitAt w
  let sub := fun (e : Expr) => e.replaceFVars (xs.extract 0 pre.size) pre
  let original := sub (← ityp xs[i]!)
  let stored ← if boxed[i]! then boxTyOf original else pure original
  let ℓ ← ilevel stored
  withLocalDeclD (← xs[i]!.fvarId!.getUserName) stored fun x => do
    let value ← if boxed[i]! then unboxValOf original x else pure x
    let β ← mkLambdaFVars #[x] (← wTowerTy w xs boxed (i + 1) (pre.push value))
    return psigmaT ℓ w stored β

/-- **Is a tower over these fields at `Sort w`?** `max ℓᵢ w ≡ w` at every field,
which is Lean's own constraint on the declaration re-asked as a conversion:
a field of an inductive at `Sort w` sits at some `Sort ℓ` with `max ℓ w = w`.
Asked before anything is spliced, so a declaration this refuses costs no
splice, and asked of the *expression* rather than assumed. Components with an
exposed `imax` are measured after recursive boxing; this still refuses an
opaque atomic type whose level contains an `imax`, because no available box can
inspect that type far enough to normalize its level. -/
def wTowerLevel (w : Level) (xs : Array Expr) (boxed : Array Bool) : GenM (Option Level) := do
  for i in [0:xs.size] do
    let original ← ityp xs[i]!
    let ℓ ← if boxed[i]! then boxLevelOf original else ilevel original
    unless ← isLevelDefEq (mkLevelMax' ℓ w) w do return some ℓ
  return none

/-- **One level of a tower at a substitution** — the `α` and `β` that
[`InductiveModels.wTowerTy`] wrote at field `i`, with the earlier fields replaced by
whatever the caller has in their place (projections when a tower is being taken
apart, values when one is being built).

**The binder type is substituted too**, and that is the whole reason this is a
function rather than two lines at each call site: `β` is `fun (x : Xᵢ) => …`,
`Xᵢ` mentions the earlier fields, and abstracting the field variable closes the
*body* over it while leaving the domain pointing at a variable that is no
longer in scope. A tower whose fields do not depend on each other never notices;
`test/fixtures/inductive-models/prim_w.lean`'s `Dep` is the occupant that does, and it found this as a
kernel `declaration has free variables`. -/
def wTowerAt (w : Level) (xs : Array Expr) (boxed : Array Bool) (i : Nat)
    (pre : Array Expr) : GenM (Level × Expr × Expr × Expr) := do
  let sub := fun (vs : Array Expr) (e : Expr) => e.replaceFVars (xs.extract 0 vs.size) vs
  let original := sub pre (← ityp xs[i]!)
  let stored ← if boxed[i]! then boxTyOf original else pure original
  let ℓ ← ilevel stored
  let β ← withLocalDeclD (← xs[i]!.fvarId!.getUserName) stored fun x => do
    let value ← if boxed[i]! then unboxValOf original x else pure x
    mkLambdaFVars #[x] (← wTowerTy w xs boxed (i + 1) (pre.push value))
  return (ℓ, original, stored, β)

/-- **The components of a tower, read back out of it.** At step `i` the earlier
fields are already projections, so the `α` and `β` this rebuilds are the ones
`wTowerTy` wrote with those substituted in — which is what makes the projection
well-typed when a later field's type mentions an earlier one. -/
partial def wTowerProjs (w : Level) (xs : Array Expr) (boxed : Array Bool)
    (i : Nat) (d : Expr)
    (acc : Array Expr) : GenM (Array Expr) := do
  if i == xs.size then return acc
  let (ℓ, original, stored, β) ← wTowerAt w xs boxed i acc
  let fst := psigmaFst ℓ w stored β d
  let value ← if boxed[i]! then unboxValOf original fst else pure fst
  wTowerProjs w xs boxed (i + 1) (psigmaSnd ℓ w stored β d) (acc.push value)

/-- **A tower built from field values** — the same `α` and `β` as
[`InductiveModels.wTowerProjs`] rebuilds, so `⟨proj⃗ d⟩` and `d` are the same tower and
structure eta closes the round trip with no transport. -/
partial def wTowerMk (w : Level) (xs : Array Expr) (boxed : Array Bool)
    (i : Nat) (vals : Array Expr) : GenM Expr := do
  if i == xs.size then return unitAtCanon w
  let (ℓ, original, stored, β) ← wTowerAt w xs boxed i (vals.extract 0 i)
  let value ← if boxed[i]! then boxValOf original vals[i]! else pure vals[i]!
  return psigmaMk ℓ w stored β value (← wTowerMk w xs boxed (i + 1) vals)

def wTowerTyOf (w : Level) (xs : Array Expr) : GenM Expr := do
  wTowerTy w xs (← wTowerBoxed xs) 0

def wTowerLevelOf (w : Level) (xs : Array Expr) : GenM (Option Level) := do
  wTowerLevel w xs (← wTowerBoxed xs)

def wTowerProjsOf (w : Level) (xs : Array Expr) (d : Expr) : GenM (Array Expr) := do
  wTowerProjs w xs (← wTowerBoxed xs) 0 d #[]

def wTowerMkOf (w : Level) (xs vals : Array Expr) : GenM Expr := do
  wTowerMk w xs (← wTowerBoxed xs) 0 vals

/-- The two universe levels at which arm W exposes and builds its carrier.

Most declarations expose the W core directly, so both levels are the public
carrier level.  A predecessor-free, provably positive public level instead
uses a small `Type` core and stores it in the exact-sort `PSigma'` described by
[`WCarrierPlan.carrier`].  Keeping this plan and its term builders outside
`primIso` is also important: that definition is already close to Lean's
default elaboration budget. -/
structure WCarrierPlan where
  publicLevel : Level
  coreLevel : Level
  lifted : Bool

/-- Choose the constrained lift exactly when `w` has no syntactic predecessor
but `max 1 w` is definitionally `w`. -/
def wCarrierPlan (eligible : Bool) (w : Level) : GenM WCarrierPlan := do
  let lifted ← if eligible && w.normalize.dec.isNone then
      isLevelDefEq (mkLevelMax' (.succ .zero) w) w
    else pure false
  return { publicLevel := w, coreLevel := if lifted then .succ .zero else w, lifted }

def WCarrierPlan.liftFam (p : WCarrierPlan) (lowTy : Expr) : Expr :=
  .lam `low lowTy (puliftT p.publicLevel trueP) .default

/-- Expose `lowTy : Sort core` at the plan's exact public carrier sort. -/
def WCarrierPlan.carrier (p : WCarrierPlan) (lowTy : Expr) : Expr :=
  if p.lifted then
    psigmaT p.coreLevel p.publicLevel lowTy (p.liftFam lowTy)
  else lowTy

/-- Insert the canonical proof carried only to make the constrained lift land
at the exact public sort. -/
def WCarrierPlan.wrap (p : WCarrierPlan) (lowTy low : Expr) : Expr :=
  if p.lifted then
    psigmaMk p.coreLevel p.publicLevel lowTy (p.liftFam lowTy) low
      (unitAtCanon p.publicLevel)
  else low

def WCarrierPlan.unwrap (p : WCarrierPlan) (lowTy value : Expr) : Expr :=
  if p.lifted then
    psigmaFst p.coreLevel p.publicLevel lowTy (p.liftFam lowTy) value
  else value

/-- Pull a public motive back along `wrap`, for the low W recursor. -/
def WCarrierPlan.motive (p : WCarrierPlan) (lowTy motive : Expr) : GenM Expr := do
  if p.lifted then
    withLocalDeclD `low lowTy fun low =>
      mkLambdaFVars #[low] (mkApp motive (p.wrap lowTy low))
  else
    pure motive

end InductiveModels
