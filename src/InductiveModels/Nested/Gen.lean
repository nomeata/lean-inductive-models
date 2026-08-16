import Lean
import InductiveModels.EqKit
import InductiveModels.Plan
import InductiveModels.Gen.Monad
import InductiveModels.Gen.MetaKit
import InductiveModels.Gen.ExportShape

/-!
# The nested construction's context, and the terms it builds

**Rung three of the tower.** `Gen` is the read-only context one nested
declaration's model is built against, and the `Gen` namespace is every term
that model is made of: `pack`/`unpack`, both round trips, the declared type's
own constructors and the block's recursors.

Nothing below this rung imports this module. The simple and mutual
constructions reach the shared core in `InductiveModels.Gen.*` directly.
-/

open Lean Meta

namespace InductiveModels
/-! ## The generator -/

/-- The generator's read-only context. -/
structure Gen where
  /-- Exact declaration owner and the collision-safe owner used in this build. -/
  owner : Name
  buildOwner : Name
  /-- The private implementation namespace below the primary carrier. -/
  model : Name
  /-- Original constructors in flattened declaration order. -/
  exportCtors : Array Name
  /-- Original recursors in motive order, including nested recursors. -/
  exportRecs : Array Name
  /-- `R_k._model` for each **real** member `R_k` — the carriers. One
  unless the declaration is a mutual block. -/
  selfNames : Array Name
  /-- How many block members are the export's own; the rest are mimics. Written
  `r` throughout: member `k` is real iff `k < r`, and mimic `k − r` otherwise. -/
  numAll : Nat
  np : Nat
  /-- The block's resultant sort. -/
  u : Level
  /-- **The declaration's own level parameters, as levels.** Every generated
  constant carries exactly these, in the export's own order, so a reference to
  one is written at `g.us` and a block recursor at `v :: g.us`. Empty for a
  monomorphic declaration, which is why nothing in the fixture set noticed
  their absence. -/
  us : List Level
  /-- The block's members, root first: `T._model.0`, `T._model.1`, … -/
  members : Array Name
  /-- Each member's constructor names, in order. -/
  blockCtors : Array (Array Name)
  /-- **How many indices each block member has.** A real member's are the
  export's own and a mimic's are the container's; both are carried. Every index
  vector in this file is *read off a type in hand* using this count and never
  rebuilt, which is what keeps an index telescope from becoming another de
  Bruijn arithmetic. -/
  nidx : Array Nat
  /-- The occurrences, each **the container at its parameters** and at the
  block's parameter telescope depth, with the export's `T` already rewritten to
  the carrier. `Vec T._model.self` is one, and it is a type only once the
  container's index telescope is applied. -/
  occs : Array Expr
  eqi : EqInfo
  /-- **The `funext` this declaration's proofs use.** Asked for lazily and only
  by a declaration with a field at a mimic *under a binder*, because that is
  the one shape whose proofs need it: the block types such a field `∀ x⃗, Bₘ ι⃗`
  and something has to transport along `(fun x⃗ => pack (unpack (f x⃗))) = f`.
  `none` for every other declaration. It is the **input's own** `funext` where
  the input has one and `T._model.funext` — derived from `Quot.sound`, spliced
  into the output — where it does not; [`InductiveModels.ensureFunext`] is the choice
  between them and this field is only its answer. -/
  fx : Option Name
  /-- **Do the block's recursors carry a motive universe?** Lean mints one only
  when the block supports large elimination; `inductive S : Prop | mk : PL S →
  S` eliminates into `Prop` alone and `S.rec` carries the block's own level
  parameters and nothing in front of them. Every level list this module writes
  for a recursor goes through [`InductiveModels.Gen.recLs`] for that reason. -/
  largeElim : Bool

namespace Gen

def packName (g : Gen) (i : Nat) : Name := .str g.model s!"pack_{i}"
def unpackName (g : Gen) (i : Nat) : Name := .str g.model s!"unpack_{i}"
def retractName (g : Gen) (i : Nat) : Name := .str g.model s!"unpackPack_{i}"
def sectionName (g : Gen) (i : Nat) : Name := .str g.model s!"packUnpack_{i}"
def ctorName (g : Gen) (j : Nat) : Name :=
  Naming.modelName (Naming.relocateSource g.owner g.buildOwner g.exportCtors[j]!)
def recName (g : Gen) (k : Nat) : Name :=
  Naming.modelName (Naming.relocateSource g.owner g.buildOwner g.exportRecs[k]!)
def congrPackName (g : Gen) (i : Nat) : Name := .str g.model s!"congrPack_{i}"
def iotaName (g : Gen) (k j : Nat) : Name :=
  Naming.iotaName (Naming.relocateSource g.owner g.buildOwner g.exportRecs[k]!) j
def ruleKName (g : Gen) (k : Nat) : Name :=
  Naming.ruleKName (Naming.relocateSource g.owner g.buildOwner g.exportRecs[k]!)

/-- Is block member `k` one of the export's own, rather than a mimic? -/
def isReal (g : Gen) (k : Nat) : Bool := k < g.numAll

/-- The mimic index of a block member that is not real. -/
def mimicOf (g : Gen) (k : Nat) : Nat := k - g.numAll

/-- Occurrence `i` at the parameter `fvar`s in scope — **the container at its
parameters**, so `Vec T._model.self` and not a type. -/
def occAt (g : Gen) (i : Nat) (ps : Array Expr) : Expr := g.occs[i]!.instantiateRev ps

/-- **Mimic `i`'s index count**, which is the container's. In particular it is
not zero for `Vec α : N → Type`. -/
def midx (g : Gen) (i : Nat) : Nat := g.nidx[i + g.numAll]!

/-- Occurrence `i` **at an index vector** — the type `pack_i` takes and
`unpack_i` returns. -/
def occAtIdx (g : Gen) (i : Nat) (ps idxs : Array Expr) : Expr :=
  mkAppN (g.occAt i ps) idxs

/-! ### reading a type's head and its argument vector, through β

**A container's parameter may be a *family*, and then the block's constructor
types hold β-redexes.** `RBNode α β`'s `β : α → Type`, so specialising it at
`fun _ => Json` turns the field `β k` into `(fun _ => B₀) k` — and that
expression is what the block *stores*, because the specialisation is `Expr`
surgery and `Expr.instantiate1` does not reduce. `getAppFn` then answers with a
lambda and `getAppArgs` with the wrong vector: the head test says the field is
at no member, and the index vector reads `k` where the type says `N.z`.

`Lean.Json` and `Lean.PrefixTreeNode` are exactly that shape. The repair is at
the three readers rather than at
their callers — [`InductiveModels.Gen.occIdx?`], [`InductiveModels.Gen.idxOf`],
[`InductiveModels.Gen.memberOf`] and the family's [`InductiveModels.Gen.Family.memberAt?`]
— because *every* question this module asks of a field's type goes through one
of them, and a repair at one caller would leave the rest reading a lambda.
[`InductiveModels.headNorm`] and not `whnf`: β and `let` are the whole of the
difference, and unfolding definitions here would make a carrier look like a
block member. -/

/-- Is `t` occurrence `i` at some index vector, and if so which? The container
is matched at its **parameters**, so `Vec self N.z` and `Vec self (N.s N.z)`
are the same occurrence at two indices and one mimic serves both. -/
def occIdx? (g : Gen) (i : Nat) (ps : Array Expr) (t : Expr) : Option (Array Expr) :=
  let t := headNorm t
  let m := g.midx i
  let as := t.getAppArgs
  if as.size < m then none
  else if mkAppN t.getAppFn (as.extract 0 (as.size - m)) == g.occAt i ps then
    some (as.extract (as.size - m) as.size)
  else none

/-- **The container's own index telescope for mimic `i`**, read off the
occurrence's type — `Vec T._model.self : N → Type` — rather than rebuilt. -/
def withOccIndices (g : Gen) (i : Nat) (ps : Array Expr)
    (f : Array Expr → GenM α) : GenM α := do
  forallBoundedTelescope (← ityp (g.occAt i ps)) (some (g.midx i)) fun idxs _ => f idxs

/-- `Bₖ p⃗`. **Not a type when member `k` is indexed** — an index vector still
has to be applied, and [`InductiveModels.Gen.idxOf`] is where every one of them comes
from. -/
def memAt (g : Gen) (k : Nat) (ps : Array Expr) : Expr := mkAppN (.const g.members[k]! g.us) ps

/-- The index arguments of a value's type at member `k`. `t` is `Bₖ p⃗ idx⃗` in
the block and `Rₖ._model.self p⃗ idx⃗` at the export's side, and either way the
indices are the last `nidx k` arguments. -/
def idxOf (g : Gen) (k : Nat) (t : Expr) : Array Expr :=
  let as := (headNorm t).getAppArgs
  as.extract (as.size - g.nidx[k]!) as.size

/-- The member's index telescope, opened at the parameters in scope. -/
def withIndices (g : Gen) (k : Nat) (ps : Array Expr)
    (f : Array Expr → GenM α) : GenM α := do
  let ty ← instForall (← constInfo g.members[k]!).type ps
  forallBoundedTelescope ty (some g.nidx[k]!) fun idxs _ => f idxs

/-- `f p⃗ ι⃗ x` — every generated map takes the parameters first and then the
**container's** index telescope, which is empty unless the container has
indices. Every caller reads `ι⃗` off a type in hand. -/
def call (g : Gen) (f : Name) (ps idxs : Array Expr) (x : Expr) : Expr :=
  mkAppN (.const f g.us) (ps ++ idxs ++ #[x])

/-- `Bₖ.c p⃗ args`. -/
def blockCtorAt (g : Gen) (k : Nat) (c : Name) (ps args : Array Expr) : Expr :=
  mkAppN (.const (.str g.members[k]! (lastStr c)) g.us) (ps ++ args)

/-- Which block member a field's type is at, if any. -/
def memberOf (g : Gen) (t : Expr) : Option Nat :=
  match (headNorm t).getAppFn with
  | .const n _ => g.members.findIdx? (· == n)
  | _ => none

/-- **Which member a field's induction hypothesis is at**, which is not the
same question as [`InductiveModels.Gen.memberOf`]. Lean gives a field of type
`∀ x⃗, Bₘ …` an induction hypothesis `∀ x⃗, motiveₘ (f x⃗)` — infinitary
constructors are supported and `FTree.branch : (N → FTree) → FTree` is one — so
a minor's hypothesis vector has an entry for it and a treatment that counted
only the fields *at* a member loses its place in that vector.

Read the way Lean reads it, after `whnf` and through the telescope: `(fun x : B₀
=> N) x`, which is `Ctr.mk`'s second field at `Ctr KTree (fun _ => N)`, mentions
a member but is not recursive and gets no hypothesis.

A field that is a bare redex — `(fun _ => B₀) k`, which is what `Lean.Json`
is — needs no telescope at all, and `memberOf` sees it: that reader is
β-transparent, and the kernel's own `is_rec_argument` reduces too, so it gives
such a field a hypothesis and this counts one. -/
def ihMemberOf (g : Gen) (t : Expr) : GenM (Option Nat) := do
  if let some m := g.memberOf t then return some m
  forallTelescope (← whnf t) fun bs res => do
    if bs.isEmpty then return none
    return g.memberOf (← whnf res)

/-- Each field's induction-hypothesis member, and its **position in the
minor's hypothesis vector** — which counts every field that has one, in field
order, and is what `Bₖ.rec` binds. -/
def ihVector (g : Gen) (ftys : Array Expr) : GenM (Array (Option Nat) × Array (Option Nat)) := do
  let ihm ← ftys.mapM g.ihMemberOf
  let mut pos : Array (Option Nat) := #[]
  let mut k := 0
  for m in ihm do
    if m.isSome then pos := pos.push (some k); k := k + 1 else pos := pos.push none
  return (ihm, pos)

/-! ### fields at a mimic under a binder, and the funext they cost

Lean supports `HTree.node : (N → List HTree) → HTree`, and the block types the
field `∀ x⃗, Bₘ ι⃗`. Everything below is the machinery for a *packed position
under a binder*: which fields are one, how to rebuild a value under the
telescope, and how to close a pointwise equation with `funext`. At `nb = 0`
these paths write no lambda and ask for no `funext`. -/

/-- **`funext` for a whole binder telescope**, innermost first: from `p : Eq a
b` in the scope of `x⃗`, `Eq (fun x⃗ => a) (fun x⃗ => b)`. Each step η-reduces
its two sides, so closing over `f x⃗` gives `f` back rather than its
η-expansion and the fold downstream compares equal to the field. -/
def funextFor (g : Gen) (xs : Array Expr) (a b p : Expr) : GenM Expr := do
  -- `g.fx` is set by [`InductiveModels.ensureFunext`] for exactly the declarations
  -- that have a packed position under a binder, which is exactly the
  -- declarations that reach here; `none` is an internal inconsistency and not
  -- an input's shortcoming.
  let some fx := g.fx | badShape "a packed position under a binder without a funext"
  let mut a := a; let mut b := b; let mut p := p
  for i in [0:xs.size] do
    let x := xs[xs.size - 1 - i]!
    let α ← ityp x
    let lu ← ilevel α
    let lv ← ilevel (← ityp a)
    let β ← mkLambdaFVars #[x] (← ityp a)
    let la := (← mkLambdaFVars #[x] a).eta
    let lb := (← mkLambdaFVars #[x] b).eta
    p := mkAppN (.const fx [lu, lv]) #[α, β, la, lb, ← mkLambdaFVars #[x] p]
    a := la; b := lb
  return p

/-- Is `t` a field the block holds at a **mimic**, possibly under a binder
telescope? Returns the member and the telescope's length; `0` is the ordinary
case. `∀ x⃗, Bₘ ι⃗` on the block's side. -/
def mimicUnder? (g : Gen) (t : Expr) : GenM (Option (Nat × Nat)) := do
  if let some m := g.memberOf t then
    return if g.isReal m then none else some (m, 0)
  forallTelescope (← whnf t) fun bs res => do
    let some m := g.memberOf (← whnf res) | return none
    return if g.isReal m then none else some (m, bs.size)


/-- Is `t` occurrence `i` at some index vector, possibly under a binder
telescope? Returns the telescope's length. -/
def occUnder? (g : Gen) (i : Nat) (ps : Array Expr) (t : Expr) : GenM (Option Nat) := do
  if (g.occIdx? i ps t).isSome then return some 0
  forallTelescope (← whnf t) fun bs res => do
    if (g.occIdx? i ps (← whnf res)).isSome then return some bs.size else return none

/-- Which occurrence `t` is at, possibly under a binder telescope, and how deep. -/
def occOfUnder? (g : Gen) (ps : Array Expr) (t : Expr) : GenM (Option (Nat × Nat)) := do
  for i in [0:g.occs.size] do
    if let some nb ← g.occUnder? i ps t then return some (i, nb)
  return none

/-- **Rebuild a field under its binder telescope**: `fun x⃗ => k resTy (f x⃗)`.
`nb = 0` applies `k` to the field itself and writes no lambda. -/
def underBinders (nb : Nat) (ty f : Expr)
    (k : Array Expr → Expr → Expr → GenM Expr) : GenM Expr := do
  if nb == 0 then k #[] ty f
  else forallBoundedTelescope ty (some nb) fun xs res => do
    mkLambdaFVars xs (← k xs res (f.beta xs))

/-- **A moved position and its proof, under the binder telescope.** `k` returns
the moved value and a *pointwise* proof of `Eq (that value) (f x⃗)`; this
abstracts both over `x⃗` and closes the equation with [`InductiveModels.Gen.funextFor`],
which is the only place in this module an equality Lean did not write is used —
and it is read from the export, never fabricated. -/
def underEq (g : Gen) (nb : Nat) (ty f : Expr)
    (k : Array Expr → Expr → Expr → GenM (Expr × Expr)) : GenM (Expr × Expr) := do
  if nb == 0 then k #[] ty f
  else forallBoundedTelescope ty (some nb) fun xs res => do
    let fx := f.beta xs
    let (l, p) ← k xs res fx
    return ((← mkLambdaFVars xs l).eta, ← g.funextFor xs l fx p)

/-- `(member, constructor)` for every constructor of the block, in the order
`Bₖ.rec` binds its minors. -/
def ctorPairs (g : Gen) : Array (Nat × Name) :=
  (Array.range g.members.size).flatMap fun k => g.blockCtors[k]!.map (k, ·)

/-- The total number of the block's constructors — the recursors' minor count. -/
def numMinors (g : Gen) : Nat := g.ctorPairs.size

/-- **A recursor's level list**: the motive universe in front of `ℓ⃗`, or just
`ℓ⃗` when the block eliminates only into `Prop` and Lean minted no motive
universe for it. -/
def recLs (g : Gen) (v : Level) : List Level := if g.largeElim then v :: g.us else g.us

/-- **A *container's* recursor at a motive universe**, or without one. Whether
the container carries a motive universe is its own affair and not the block's —
a `Prop`-valued container without large elimination has none — so it is read
off the recursor rather than assumed. -/
def contRecAt (n : Name) (v : Level) (cls : List Level) : GenM Expr := do
  let .recInfo rv ← constInfo n | badShape s!"{n} is not a recursor"
  if rv.levelParams.length == cls.length + 1 then return .const n (v :: cls)
  else if rv.levelParams.length == cls.length then return .const n cls
  else badShape s!"{n} carries {rv.levelParams.length} level parameters, not {cls.length}"

/-- The same list, for `instantiateLevelParams`. -/
def contRecLs (n : Name) (v : Level) (cls : List Level) : GenM (List Level) := do
  let .recInfo rv ← constInfo n | badShape s!"{n} is not a recursor"
  if rv.levelParams.length == cls.length + 1 then return v :: cls else return cls

/-- `Bₖ.rec`, the block's own. -/
def blockRec (g : Gen) (k : Nat) : Name := .str g.members[k]! "rec"

/-- `Bₖ.rec` at motive universe `v`. Lean puts the motive universe **first**
and the block's own level parameters after it, and it mints the same fresh
name for `T._model.0.rec` as for `T.rec` because both are generated from the
same level parameter list. -/
def blockRecAt (g : Gen) (k : Nat) (v : Level) : Expr :=
  .const (g.blockRec k) (g.recLs v)

/-- The container of occurrence `i` at `ps`: its name, level list and **its
parameters**. An indexed container's index telescope is not here — it rides
outside the occurrence and every use reads it off a type in hand. -/
def container (g : Gen) (i : Nat) (ps : Array Expr) :
    GenM (Name × List Level × Array Expr) := do
  let occ := g.occAt i ps
  let .const c cls := occ.getAppFn | badShape "the occurrence is not headed by a constant"
  let .inductInfo _ ← constInfo c | badShape s!"{c} is not an inductive"
  return (c, cls, occ.getAppArgs)

/-- The real container constructor a mimic's constructor stands for, by its
last name component — the correspondence [`InductiveModels.plan`] built it from. -/
def realCtor (g : Gen) (i : Nat) (ps : Array Expr) (cn : Name) : GenM Name := do
  let (c, _, _) ← g.container i ps
  let last := lastStr cn
  let some r := (← ctorsOf c).find? (fun r => lastStr r == last)
    | badShape s!"no real constructor for {cn}"
  return r

/-- **One congruence per moving argument.** From `pⱼ : Eq lhsⱼ rhsⱼ` at the
positions that move, build `Eq (f lhs⃗) (f rhs⃗)` by transporting one position at
a time: at step `j` the accumulator proves `Eq (f lhs⃗) (f mix(j))`, where
`mix(j)` is `rhs` below `j` and `lhs` at and above it.

This is where a constructor with **two or more** moving positions is paid for,
and it is why the fold exists rather than a single transport. It is also why
`congrCtor` is not a declaration: each step abstracts a *different* position of
the same constructor, so a named lemma would be one per position. -/
def foldCongr (g : Gen) (goalTy : Expr) (fieldTys lhs rhs : Array Expr)
    (proofs : Array (Option Expr)) (rebuild : Array Expr → Expr) : GenM Expr := do
  let n := lhs.size
  let start := rebuild lhs
  let ug ← ilevel goalTy
  let mut acc := g.eqi.refl' ug goalTy start
  for j in [0:n] do
    let some p := proofs[j]! | continue
    if lhs[j]! == rhs[j]! then continue
    let α := fieldTys[j]!
    -- **The moved position's own sort, not the block's.** A packed field under
    -- a binder lands at `imax` of the binder's sort and the block's, and the
    -- two coincide only when there is no binder.
    let uα ← ilevel α
    let mot ← withLocalDeclD `x α fun x => do
      withLocalDeclD `hx (g.eqi.mk' uα α lhs[j]! x) fun hx => do
        let mix := (Array.range n).map fun k =>
          if k < j then rhs[k]! else if k == j then x else lhs[k]!
        mkLambdaFVars #[x, hx] (g.eqi.mk' ug goalTy start (rebuild mix))
    acc := g.eqi.recAt .zero uα α lhs[j]! mot acc rhs[j]! p
  return acc

/-- The value-transport counterpart of [`InductiveModels.Gen.foldCongr`]: from
`v : M (f lhs⃗)` and `pⱼ : Eq lhsⱼ rhsⱼ`, produce `M (f rhs⃗)`, one position at a
time. The motive lands at the eliminator's universe, which is the one place in
this file an `Eq.rec` is not `Prop`-valued. -/
def foldValue (g : Gen) (v : Level) (m0 : Expr) (fieldTys lhs rhs : Array Expr)
    (proofs : Array (Option Expr)) (rebuild : Array Expr → Expr) (base : Expr) :
    GenM Expr := do
  let n := lhs.size
  let mut acc := base
  for j in [0:n] do
    let some p := proofs[j]! | continue
    if lhs[j]! == rhs[j]! then continue
    let α := fieldTys[j]!
    let uα ← ilevel α
    let mot ← withLocalDeclD `x α fun x => do
      withLocalDeclD `hx (g.eqi.mk' uα α lhs[j]! x) fun hx => do
        let mix := (Array.range n).map fun k =>
          if k < j then rhs[k]! else if k == j then x else lhs[k]!
        mkLambdaFVars #[x, hx] (mkApp m0 (rebuild mix))
    acc := g.eqi.recAt v uα α lhs[j]! mot acc rhs[j]! p
  return acc

/-- **`Eq (f x⃗) (g x⃗)` from `h : Eq f g`** — `congrFun`, iterated, and built
from `Eq.rec` alone rather than read from the export.

It is what makes a packed position *under a binder* work at all. The fold
carries one equation for the whole function, closed with `funext`; the
induction hypothesis on the other side is **pointwise**, `fun x⃗ => rec_m (f
x⃗)`, and each of its points transports along `Eq (y x⃗) (f x⃗)`. Instantiated,
that is the same proposition as the retraction at `f x⃗`, so **proof
irrelevance** identifies the two and the rule's two sides meet. Abstracting the
function and transporting it whole does not: `Eq.rec` on the funext'd equation
is not the pointwise transport `T._model.rec_m` δ-unfolds to. -/
def congrFunFor (g : Gen) (α y target h : Expr) (xs : Array Expr) : GenM Expr := do
  let uα ← ilevel α
  let yx := y.beta xs
  let β ← ityp yx
  let uβ ← ilevel β
  let mot ← withLocalDeclD `z α fun z =>
    withLocalDeclD `hz (g.eqi.mk' uα α y z) fun hz => do
      mkLambdaFVars #[z, hz] (g.eqi.mk' uβ β yx (z.beta xs))
  return g.eqi.recAt .zero uα α y mot (g.eqi.refl' uβ β yx) target h

/-- **`Eq (m l₀) (m l)` from `h : Eq l₀ l`, inline.** `congrPack_i` is this at a
position that needs no binder, as a declaration; a position *under* a binder
abstracts a whole function and no one lemma covers it, so it is built here the
way [`InductiveModels.Gen.foldCongr`] builds its steps. `β` is the type of `m l₀`. -/
def congrOne (g : Gen) (α β : Expr) (m : Expr → GenM Expr) (l0 l h : Expr) :
    GenM Expr := do
  let uα ← ilevel α
  let uβ ← ilevel β
  let m0 ← m l0
  let mot ← withLocalDeclD `x α fun x =>
    withLocalDeclD `hx (g.eqi.mk' uα α l0 x) fun hx => do
      mkLambdaFVars #[x, hx] (g.eqi.mk' uβ β m0 (← m x))
  return g.eqi.recAt .zero uα α l0 mot (g.eqi.refl' uβ β m0) l h

/-! ### pack -/

/-- `fun f⃗ ih⃗ => Bᵢ.c p⃗ g⃗`, where a field recursive in the container is its own
induction hypothesis, a field at another mimic is packed, and anything else —
a plain field, or one at the root, which the block types at `B₀ p⃗` and
`T._model.self p⃗` unfolds to — goes through untouched. -/
def packMinor (g : Gen) (i member : Nat) (ps : Array Expr) (cn : Name) (mty : Expr) :
    GenM Expr := do
  forallTelescope mty fun bs _ => do
    let n ← numFieldsOf cn
    let fields := bs.extract 0 n
    let ihs := bs.extract n bs.size
    let ftys ← fields.mapM ftyp
    -- The container's own recursive positions: occurrence `i` at **any** index
    -- vector, because `Vec.vcons`' recursive field sits at `n` and its result
    -- at `N.s n` — and **under any binder telescope**, because `Rose.node :
    -- (N → Rose α) → Rose α` is recursive under one and Lean gives it a
    -- hypothesis all the same.
    let mut recs : Array Nat := #[]
    for x in [0:n] do
      if (← g.occUnder? i ps ftys[x]!).isSome then recs := recs.push x
    -- Every recursive position, infinitary or not, has exactly one hypothesis,
    -- so the two vectors line up. An infinitary one's hypothesis is already
    -- `∀ x⃗, B_{r+i} ι⃗`, which is what the block's constructor wants: no
    -- lambda is written here and no funext is needed.
    unless recs.size == ihs.size do
      badShape s!"{cn}'s recursive positions and hypotheses do not line up"
    let mut args : Array Expr := #[]
    for x in [0:n] do
      if let some t := recs.findIdx? (· == x) then
        args := args.push ihs[t]!
      else if let some (o, nb) ← g.occOfUnder? ps ftys[x]! then
        args := args.push (← underBinders nb ftys[x]! fields[x]! fun _ res v =>
          return g.call (g.packName o) ps ((g.occIdx? o ps res).getD #[]) v)
      else
        args := args.push fields[x]!
    mkLambdaFVars bs (g.blockCtorAt member cn ps args)

/-! ### the container family a cycle of mimics is one recursion over -/

/-- **The recursors Lean minted for the block `c` belongs to**, in block-index
order: `c`'s own members first, then one per nested occurrence of that block.
An ordinary container gives `#[C.rec]`; a container that is **itself** a nested
inductive gives `#[Tree.rec, Tree.rec_1]`, and those two are the simultaneous
recursion a cycle of mimics needs. -/
def familyRecs (c : Name) : GenM (Array Name) := do
  let .inductInfo iv ← constInfo c | badShape s!"{c} is not an inductive"
  let all := iv.all.toArray
  if all.isEmpty then badShape s!"{c} has no block"
  return (Array.range (all.size + iv.numNested)).map (exportRecName all ·)

/-- **One container block, seen as the recursion a group of mimics is.** -/
structure Family where
  /-- The recursor family, in block-index order. -/
  recs : Array Name
  /-- The anchoring occurrence's level list and parameters. -/
  cls : List Level
  qs : Array Expr
  /-- Family member `j`'s **occurrence** at `qs` — the container at its
  parameters, so a type only once its index telescope is applied. -/
  doms : Array Expr
  /-- Family member `j`'s index count. -/
  fidx : Array Nat
  /-- Family member `j` is the group's mimic `mimic[j]`. -/
  mimic : Array Nat
  /-- `(family member, its constructor)` in the order the family's recursors
  bind their minors: every member's rules, member by member. -/
  rules : Array (Nat × Name)

/-- Which family member mimic `i` is. -/
def Family.indexOf (f : Family) (i : Nat) : Nat := (f.mimic.findIdx? (· == i)).getD 0

/-- Family member `j`'s constructors are the real container's at *its* own
parameters, which the member's type carries: `List (Tree α)`'s `cons` is
`List.cons` at `#[Tree α]`. -/
def Family.ctorPrefix (f : Family) (j : Nat) : List Level × Array Expr :=
  match f.doms[j]!.getAppFn with
  | .const _ cls => (cls, f.doms[j]!.getAppArgs)
  | _ => ([], f.doms[j]!.getAppArgs)

/-- Which family member a type is at, and at which indices. Through β, for
[`InductiveModels.Gen.occIdx?`]'s reason. -/
def Family.memberAt? (f : Family) (t : Expr) : Option (Nat × Array Expr) :=
  let t := headNorm t
  (Array.range f.doms.size).findSome? fun j =>
    let m := f.fidx[j]!
    let as := t.getAppArgs
    if as.size < m then none
    else if mkAppN t.getAppFn (as.extract 0 (as.size - m)) == f.doms[j]! then
      some (j, as.extract (as.size - m) as.size)
    else none

/-- Which family member `t` is at, and how deep under a binder — the
[`InductiveModels.Gen.mimicUnder?`] of a cyclic group's own recursion. `Tr.node :
(N → List (Tr α)) → Tr α` is one, and a cycle through it is a binder inside a
simultaneous recursion. -/
def Family.memberUnder? (f : Family) (t : Expr) : GenM (Option (Nat × Nat)) := do
  if let some (j, _) := f.memberAt? t then return some (j, 0)
  forallTelescope (← whnf t) fun bs res => do
    if bs.isEmpty then return none
    let some (j, _) := f.memberAt? (← whnf res) | return none
    return some (j, bs.size)

/-- Family member `j`'s index telescope, read off its occurrence's type. -/
def Family.withIndices (f : Family) (j : Nat) (k : Array Expr → GenM α) : GenM α := do
  forallBoundedTelescope (← ityp f.doms[j]!) (some f.fidx[j]!) fun idxs _ => k idxs

/-- **The family a group of mutually recursive mimics is one recursion over**.

`nest_through_nested`'s `T` nests into `Tree T`, `Tree`'s own `node` field is
`List (Tree T)` and *that* copy's `cons` head is `Tree T` again, so mimics 0
and 1 depend on each other and no emission order exists for them one at a
time. They are not two recursions: they are the two components of **one**, and
Lean already generated it — `Tree.rec` and `Tree.rec_1`, over a single motive
and minor vector. This finds that vector by trying each mimic in the group as
the anchor and asking whether its container's family covers the group exactly.

**Exactly** is required in both directions. A family member the group does not
contain would need a motive this cannot invent, and a group member outside the
family would have no component to be. -/
def familyFor (g : Gen) (grp : Array Nat) (ps : Array Expr) : GenM Family := do
  for anchor in grp do
    let (c, cls, qs) ← g.container anchor ps
    let recs ← familyRecs c
    if recs.size != grp.size then continue
    let .recInfo rv ← constInfo recs[0]! | continue
    let ty ← instForall
      (rv.type.instantiateLevelParams rv.levelParams (← contRecLs recs[0]! g.u cls)) qs
    -- **A motive is `∀ ι⃗ x, Sort v`, and the occurrence is `x`'s type with the
    -- index telescope stripped.** For an unindexed family that is the motive's
    -- single binder domain and nothing has moved; for an indexed one — `XT`'s
    -- cycle runs over `ITr.rec`/`ITr.rec_1`, both indexed — the indices sit in
    -- front of it.
    let doms? ← forallBoundedTelescope ty (some rv.numMotives) fun ms _ =>
      ms.mapM fun m => do
        forallTelescope (← ityp m) fun bs _ => do
          let some last := bs.back? | return none
          let t ← ityp last
          let ni := bs.size - 1
          let as := t.getAppArgs
          if as.size < ni then return none
          return some (mkAppN t.getAppFn (as.extract 0 (as.size - ni)), ni)
    if doms?.any (·.isNone) then continue
    let doms := doms?.map fun d => (d.getD default).1
    let fidx := doms?.map fun d => (d.getD default).2
    -- Every family member is one of the group's occurrences, and every one of
    -- the group's is a family member.
    let mimic? := doms.map fun d => grp.find? (g.occAt · ps == d)
    if mimic?.any (·.isNone) then continue
    let mimic := mimic?.map (·.getD 0)
    if grp.any fun i => !mimic.contains i then continue
    let mut rules : Array (Nat × Name) := #[]
    for j in [0:recs.size] do
      let .recInfo rj ← constInfo recs[j]! | badShape s!"{recs[j]!} is not a recursor"
      for rl in rj.rules do rules := rules.push (j, rl.ctor)
    return { recs, cls, qs, doms, fidx, mimic, rules }
  -- **This exit is an internal error on purpose, and the purpose is statable.**
  -- The anchor loop is a *lookup* and not a search over constructions: nothing
  -- is installed or spliced by an anchor that does not fit, and the five
  -- `continue`s above are the one exactness criterion the docstring states,
  -- asked once per candidate. What reaching here would mean is that a group
  -- [`InductiveModels.mimicGroups`] calls mutually recursive has no Lean-generated
  -- simultaneous recursion covering it — and a cycle among mimics exists only
  -- when some container in it is *itself* a nested inductive, whose own block
  -- is that recursion. So this is not a shape the arm declines to reach: it is
  -- the claim that Lean already minted the recursors, failing. That is a fault
  -- in this module's reading of the block, not an incompleteness to record
  -- against the input, and it must stop the stream rather than be counted as a
  -- decline beside the shapes the construction genuinely does not model.
  badShape s!"a mutually recursive mimic group has no matching recursor family: \
    no container of mimics {grp.toList} has a block covering exactly that group"

/-- The minor types the family's recursors bind at this motive vector. They are
the same for every component, so they are read off component 0 once. -/
def withFamilyMinors (_g : Gen) (f : Family) (v : Level) (motives : Array Expr)
    (k : Array Expr → GenM (Array Expr)) : GenM (Array Expr) := do
  let head : Expr ← contRecAt f.recs[0]! v f.cls
  withMinorTypes (mkAppN head (f.qs ++ motives)) f.rules.size k

/-- One minor of the family's `pack`: a field at **any** member of the family
is its own induction hypothesis — that is what makes the recursion
simultaneous — a field at a mimic outside the family is packed by that mimic's
own `pack`, and everything else goes through. -/
def packFamMinor (g : Gen) (f : Family) (ps : Array Expr) (j : Nat) (cn : Name)
    (mty : Expr) : GenM Expr := do
  forallTelescope mty fun bs _ => do
    let n ← numFieldsOf cn
    let fields := bs.extract 0 n
    let ihs := bs.extract n bs.size
    let ftys ← fields.mapM ftyp
    let mut recs : Array Nat := #[]
    for x in [0:n] do
      if (← f.memberUnder? ftys[x]!).isSome then recs := recs.push x
    let mut args : Array Expr := #[]
    for x in [0:n] do
      if let some t := recs.findIdx? (· == x) then
        -- Its hypothesis is already `∀ x⃗, B ι⃗` when there is a binder, which
        -- is what the block's constructor wants: no lambda, no funext.
        args := args.push ihs[t]!
      else if let some (o, nb) ← g.occOfUnder? ps ftys[x]! then
        args := args.push (← underBinders nb ftys[x]! fields[x]! fun _ res v =>
          return g.call (g.packName o) ps ((g.occIdx? o ps res).getD #[]) v)
      else
        args := args.push fields[x]!
    mkLambdaFVars bs (g.blockCtorAt (f.mimic[j]! + g.numAll) cn ps args)

/-- **`pack` for family member `j`**, as the `j`-th component of one recursion
over the whole family — the same motive and minor vector for every component,
so `pack₀` and `pack₁` never mention each other. -/
def packFamilyValue (g : Gen) (f : Family) (j : Nat) (ps : Array Expr) : GenM Expr := do
  let motives ← (Array.range f.doms.size).mapM fun t =>
    f.withIndices t fun idxs =>
      withLocalDeclD `x (mkAppN f.doms[t]! idxs) fun x =>
        mkLambdaFVars (idxs.push x) (mkAppN (g.memAt (f.mimic[t]! + g.numAll) ps) idxs)
  let minors ← g.withFamilyMinors f g.u motives fun mtys =>
    (Array.range f.rules.size).mapM fun t =>
      g.packFamMinor f ps f.rules[t]!.1 f.rules[t]!.2 mtys[t]!
  return mkAppN (← contRecAt f.recs[j]! g.u f.cls) (f.qs ++ motives ++ minors)

/-- **The retraction for family member `j`**, likewise simultaneous: the same
recursion at `Prop`, whose `j`-th motive is `unpackⱼ ∘ packⱼ = id`. A field at
a sibling member gets the sibling's own induction hypothesis, which is that
sibling's retraction up to proof irrelevance — the same identification the
one-at-a-time path already makes between `ih` and `unpackPack_o f`. -/
def retractFamilyValue (g : Gen) (f : Family) (j : Nat) (ps : Array Expr) : GenM Expr := do
  let trip := fun (o : Nat) (idxs : Array Expr) (x : Expr) =>
    g.call (g.unpackName o) ps idxs (g.call (g.packName o) ps idxs x)
  let motives ← (Array.range f.doms.size).mapM fun t =>
    f.withIndices t fun idxs => do
      let dom := mkAppN f.doms[t]! idxs
      withLocalDeclD `l dom fun l =>
        mkLambdaFVars (idxs.push l) (g.eqi.mk' g.u dom (trip f.mimic[t]! idxs l) l)
  let minors ← g.withFamilyMinors f .zero motives fun mtys =>
    (Array.range f.rules.size).mapM fun t => do
      let (jj, cn) := f.rules[t]!
      forallTelescope mtys[t]! fun bs _ => do
        let n ← numFieldsOf cn
        let fields := bs.extract 0 n
        let ihs := bs.extract n bs.size
        let ftys ← fields.mapM ftyp
        let mut recs : Array Nat := #[]
        for x in [0:n] do
          if (← f.memberUnder? ftys[x]!).isSome then recs := recs.push x
        let mut lhs : Array Expr := #[]
        let mut proofs : Array (Option Expr) := #[]
        for x in [0:n] do
          if let some t' := recs.findIdx? (· == x) then
            let (d, nb) := (← f.memberUnder? ftys[x]!).getD (0, 0)
            let (l, pf) ← g.underEq nb ftys[x]! fields[x]! fun xs res v => do
              let idxs := (f.memberAt? res).map (·.2) |>.getD #[]
              return (trip f.mimic[d]! idxs v, mkAppN ihs[t']! xs)
            lhs := lhs.push l
            proofs := proofs.push (some pf)
          else if let some (o, nb) ← g.occOfUnder? ps ftys[x]! then
            let (l, pf) ← g.underEq nb ftys[x]! fields[x]! fun _ res v => do
              let idxs := (g.occIdx? o ps res).getD #[]
              return (trip o idxs v, g.call (g.retractName o) ps idxs v)
            lhs := lhs.push l
            proofs := proofs.push (some pf)
          else
            lhs := lhs.push fields[x]!
            proofs := proofs.push none
        let (ccls, cqs) := f.ctorPrefix jj
        let rebuild := fun (a : Array Expr) => mkAppN (.const cn ccls) (cqs ++ a)
        -- The constructor application's own type, indices and all: `∀ ι⃗` is
        -- not a type and the family member's indices come from the result.
        let goalTy ← ftyp (rebuild fields)
        mkLambdaFVars bs (← g.foldCongr goalTy ftys lhs fields proofs rebuild)
  return mkAppN (← contRecAt f.recs[j]! .zero f.cls) (f.qs ++ motives ++ minors)

/-- `packᵢ := C.rec q⃗ (fun _ => Bᵢ p⃗) minors…`, partially applied — its type is
`∀ _ : occᵢ, Bᵢ p⃗` on the nose, the motive being constant.

The recursor's level list is `u :: cls` and not `u :: C`'s *declared*
parameters: a polymorphic container instantiated at a concrete level — `List.{0}
Syntax` — is exactly `Lean.Syntax`'s shape, and writing the declared parameter
there leaves a free universe variable. -/
def packValue (g : Gen) (i member : Nat) (ps : Array Expr) : GenM Expr := do
  let (c, cls, qs) ← g.container i ps
  -- The motive binds the container's index telescope in front of its major,
  -- which is where `C.rec` puts it; for an unindexed container the telescope is
  -- empty and this is the constant motive it always was.
  let motive ← g.withOccIndices i ps fun idxs =>
    withLocalDeclD `x (g.occAtIdx i ps idxs) fun x =>
      mkLambdaFVars (idxs.push x) (mkAppN (g.memAt member ps) idxs)
  let head : Expr ← Gen.contRecAt (.str c "rec") g.u cls
  let cs ← ctorsOf c
  let pre := qs.push motive
  let minors ← withMinorTypes (mkAppN head pre) cs.size fun mtys =>
    (Array.range cs.size).mapM fun t => g.packMinor i member ps cs[t]! mtys[t]!
  return mkAppN head (pre ++ minors)

/-! ### unpack -/

/-- A member's minor for `unpack`: at the root, rebuild the constructor; at a
mimic, build the **real** container's constructor, taking each field at another
mimic from its induction hypothesis. -/
def unpackMinor (g : Gen) (k : Nat) (ps : Array Expr) (cn : Name) (mty : Expr) :
    GenM Expr := do
  forallTelescope mty fun bs _ => do
    let n ← numFieldsOf cn
    let fields := bs.extract 0 n
    let ihs := bs.extract n bs.size
    let ftys ← fields.mapM ftyp
    let (ihm, ihPos) ← g.ihVector ftys
    let mut args : Array Expr := #[]
    for x in [0:n] do
      match ihm[x]! with
      | some m =>
        if !g.isReal m then
          -- A field at a *mimic* is unpacked, and its unpacked value is exactly
          -- this recursor's induction hypothesis for it. **Including under a
          -- binder**: the hypothesis for `∀ x⃗, Bₘ ι⃗` is `∀ x⃗, occₘ ι⃗`,
          -- because a mimic's motive is the occurrence, so no lambda is
          -- written here either.
          let some t := ihPos[x]! | badShape "no hypothesis for a mimic field"
          args := args.push ihs[t]!
        else
          -- A field at a **real** member passes through: the block types it at
          -- `Bₘ p⃗`, and the real constructor wants `Rₘ._model.self p⃗`, which is
          -- that by δ.
          args := args.push fields[x]!
      | none =>
        args := args.push fields[x]!
    let body ←
      if g.isReal k then
        pure (g.blockCtorAt k cn ps fields)
      else do
        let (_, cls, qs) ← g.container (g.mimicOf k) ps
        let real ← g.realCtor (g.mimicOf k) ps cn
        pure (mkAppN (.const real cls) (qs ++ args))
    mkLambdaFVars bs body

/-- `unpackᵢ := Bᵢ.rec p⃗ motives… minors…`, partially applied.

The motive at the root is `fun _ => B₀ p⃗` and at each mimic the occurrence:
that is the only choice inhabited for every block whatever its constructors
are, and `fun _ => Bⱼ` would not do because `unpack₁` for `Box BTree` needs
`unpack₂`'s result as its `mk` field. -/
def unpackValue (g : Gen) (member : Nat) (ps : Array Expr) : GenM Expr := do
  let motives ← (Array.range g.members.size).mapM fun k =>
    g.withIndices k ps fun idxs => do
      let mem := mkAppN (g.memAt k ps) idxs
      withLocalDeclD `b mem fun b =>
        mkLambdaFVars (idxs.push b)
          (if g.isReal k then mem else g.occAtIdx (g.mimicOf k) ps idxs)
  let head : Expr := g.blockRecAt member g.u
  let pre := ps ++ motives
  let pairs := g.ctorPairs
  let minors ← withMinorTypes (mkAppN head pre) g.numMinors fun mtys =>
    (Array.range pairs.size).mapM fun t => g.unpackMinor pairs[t]!.1 ps pairs[t]!.2 mtys[t]!
  return mkAppN head (pre ++ minors)

/-! ### the two round trips -/

/-- `unpackPackᵢ : ∀p⃗ l, Eq (unpackᵢ p⃗ (packᵢ p⃗ l)) l`, by the container's own
recursor, one congruence per field the round trip moves. -/
def retractValue (g : Gen) (i : Nat) (ps : Array Expr) : GenM Expr := do
  let (c, cls, qs) ← g.container i ps
  let trip := fun (idxs : Array Expr) (x : Expr) =>
    g.call (g.unpackName i) ps idxs (g.call (g.packName i) ps idxs x)
  let motive ← g.withOccIndices i ps fun idxs => do
    let occ := g.occAtIdx i ps idxs
    withLocalDeclD `l occ fun l =>
      mkLambdaFVars (idxs.push l) (g.eqi.mk' g.u occ (trip idxs l) l)
  let head : Expr ← Gen.contRecAt (.str c "rec") .zero cls
  let cs ← ctorsOf c
  let pre := qs.push motive
  let minors ← withMinorTypes (mkAppN head pre) cs.size fun mtys =>
    (Array.range cs.size).mapM fun t => do
      let cn := cs[t]!
      forallTelescope mtys[t]! fun bs _ => do
        let n ← numFieldsOf cn
        let fields := bs.extract 0 n
        let ihs := bs.extract n bs.size
        let ftys ← fields.mapM ftyp
        let mut recs : Array Nat := #[]
        for x in [0:n] do
          if (← g.occUnder? i ps ftys[x]!).isSome then recs := recs.push x
        unless recs.size == ihs.size do
          badShape s!"{cn}'s recursive positions and hypotheses do not line up"
        let mut lhs : Array Expr := #[]
        let mut proofs : Array (Option Expr) := #[]
        for x in [0:n] do
          if let some t := recs.findIdx? (· == x) then
            -- **Under a binder the induction hypothesis is pointwise**, so it
            -- is closed with funext; with no binder it is the equation itself
            -- and `underEq` writes neither a lambda nor a `funext`.
            let nb := (← g.occUnder? i ps ftys[x]!).getD 0
            let (l, pf) ← g.underEq nb ftys[x]! fields[x]! fun xs res v => do
              let idxs := (g.occIdx? i ps res).getD #[]
              return (trip idxs v, mkAppN ihs[t]! xs)
            lhs := lhs.push l
            proofs := proofs.push (some pf)
          else if let some (o, nb) ← g.occOfUnder? ps ftys[x]! then
            let (l, pf) ← g.underEq nb ftys[x]! fields[x]! fun _ res v => do
              let idxs := (g.occIdx? o ps res).getD #[]
              return (g.call (g.unpackName o) ps idxs (g.call (g.packName o) ps idxs v),
                      g.call (g.retractName o) ps idxs v)
            lhs := lhs.push l
            proofs := proofs.push (some pf)
          else
            lhs := lhs.push fields[x]!
            proofs := proofs.push none
        let rebuild := fun (a : Array Expr) => mkAppN (.const cn cls) (qs ++ a)
        -- The application's own type, indices and all: the occurrence is the
        -- container at its *parameters* and is not a type on its own.
        let goalTy ← ftyp (rebuild fields)
        mkLambdaFVars bs (← g.foldCongr goalTy ftys lhs fields proofs rebuild)
  return mkAppN head (pre ++ minors)

/-- The section's motive at member `k`, applied to `x`. **The round trip only
where the round trip exists**: a mimic this development has not reached yet has
no `pack`, so its motive is reflexivity — which is all its own minors need,
because a field at such a mimic is at one this group does not depend on. The
caller passes the live set: it is the group being emitted together with
everything already emitted, and for a **cyclic** group that is more than one
member at once.

`ty` is the member's type **at its indices**, which the caller has in hand and
`Bₖ p⃗` is not. -/
def sectionMotive (g : Gen) (k : Nat) (ty : Expr) (ps idxs : Array Expr) (x : Expr)
    (live : Nat → Bool) : Expr :=
  if live k then
    let i := g.mimicOf k
    g.eqi.mk' g.u ty (g.call (g.packName i) ps idxs (g.call (g.unpackName i) ps idxs x)) x
  else
    g.eqi.mk' g.u ty x x

/-- `packUnpackᵢ : ∀p⃗ b, Eq (packᵢ p⃗ (unpackᵢ p⃗ b)) b`, by the block's
recursor. -/
def sectionValue (g : Gen) (member : Nat) (ps : Array Expr) (live : Nat → Bool) :
    GenM Expr := do
  let motives ← (Array.range g.members.size).mapM fun k =>
    g.withIndices k ps fun idxs => do
      let mem := mkAppN (g.memAt k ps) idxs
      withLocalDeclD `b mem fun b =>
        mkLambdaFVars (idxs.push b) (g.sectionMotive k mem ps idxs b live)
  let head : Expr := g.blockRecAt member .zero
  let pre := ps ++ motives
  let pairs := g.ctorPairs
  let minors ← withMinorTypes (mkAppN head pre) g.numMinors fun mtys =>
    (Array.range pairs.size).mapM fun t => do
      let (k, cn) := pairs[t]!
      forallTelescope mtys[t]! fun bs _ => do
        let n ← numFieldsOf cn
        let fields := bs.extract 0 n
        let ihs := bs.extract n bs.size
        let ftys ← fields.mapM ftyp
        let (_, ihPos) ← g.ihVector ftys
        let rebuild := fun (a : Array Expr) => g.blockCtorAt k cn ps a
        -- The constructor application's own type, indices and all, rather than
        -- `Bₖ p⃗` — which is not a type when member `k` is indexed.
        let ty ← ftyp (rebuild fields)
        if !live k then
          mkLambdaFVars bs (g.eqi.refl' g.u ty (rebuild fields))
        else
          let mut lhs : Array Expr := #[]
          let mut proofs : Array (Option Expr) := #[]
          for x in [0:n] do
            match ← g.mimicUnder? ftys[x]! with
            | some (m, nb) =>
              if live m then
                let some t := ihPos[x]! | badShape "no hypothesis for a member field"
                let o := g.mimicOf m
                -- Under a binder the hypothesis is pointwise and funext closes
                -- it; with none, `underEq` writes neither.
                let (l, pf) ← g.underEq nb ftys[x]! fields[x]! fun xs res v => do
                  let fidx := g.idxOf m res
                  return (g.call (g.packName o) ps fidx (g.call (g.unpackName o) ps fidx v),
                          mkAppN ihs[t]! xs)
                lhs := lhs.push l
                proofs := proofs.push (some pf)
              else
                lhs := lhs.push fields[x]!
                proofs := proofs.push none
            | none =>
              lhs := lhs.push fields[x]!
              proofs := proofs.push none
          mkLambdaFVars bs (← g.foldCongr ty ftys lhs fields proofs rebuild)
  return mkAppN head (pre ++ minors)

/-! ### the declared type's own constructors -/

/-- `T._model.ctor_j := fun p⃗ f⃗ => B₀.c p⃗ g⃗`, where a field the block types at a
**mimic** is packed on the way in and everything else passes through. The field
telescope is read off the *export's* declared type, so the parameters this binds
are the ones the export declared and not ones reconstructed here. -/
def ctorValue (g : Gen) (k j : Nat) (realTy : Expr) (ps : Array Expr) : GenM Expr := do
  let cn := g.blockCtors[k]![j]!
  let blkTys ← withFields (← instCtor cn g.us ps) fun _ tys => pure tys
  forallTelescope (← instForall realTy ps) fun fields _ => do
    if fields.size != blkTys.size then
      badShape s!"{cn}: the export declares {fields.size} fields, the block {blkTys.size}"
    let mut args : Array Expr := #[]
    for x in [0:fields.size] do
      match ← g.mimicUnder? blkTys[x]! with
      -- The index vector comes from the **export-side** field's own type,
      -- which is the occurrence at those indices; the block's copy is at
      -- the block's own binders and would not name them. Under a binder the
      -- packing happens pointwise — `fun x⃗ => pack (f x⃗)` — which needs a
      -- lambda but no funext: no equation is being moved here.
      | some (m, nb) =>
        let fty ← ftyp fields[x]!
        args := args.push (← underBinders nb fty fields[x]! fun _ res v =>
          return g.call (g.packName (g.mimicOf m)) ps (g.idxOf m res) v)
      | none => args := args.push fields[x]!
    mkLambdaFVars fields (g.blockCtorAt k cn ps args)

/-! ### the recursors -/

/-- **The block's motive vector** — the caller's own at the root, the caller's
composed with `unpack` at each mimic. -/
def blockMotives (g : Gen) (ps motives : Array Expr) : GenM (Array Expr) :=
  (Array.range g.members.size).mapM fun j =>
    if g.isReal j then pure motives[j]!
    else g.withIndices j ps fun idxs =>
      withLocalDeclD `b (mkAppN (g.memAt j ps) idxs) fun b =>
        mkLambdaFVars (idxs.push b)
          (mkAppN motives[j]! (idxs.push (g.call (g.unpackName (g.mimicOf j)) ps idxs b)))

/-- One minor of the block's recursor, built from the caller's own.

The caller's minor wants the fields at their **real** types, so a field the
block holds at a mimic is unpacked on the way in; the induction hypotheses pass
through, because the block's are already at the composed motive. **Only a root
constructor with a packed field transports**, and it transports along
`packUnpack`, one position at a time. -/
def recMinor (g : Gen) (j : Nat) (cn : Name) (mty sT : Expr) (ps motives : Array Expr)
    (v : Level) : GenM Expr := do
  forallTelescope mty fun bs _ => do
    let n ← numFieldsOf cn
    let fields := bs.extract 0 n
    let ihs := bs.extract n bs.size
    let ftys ← fields.mapM ftyp
    let mut real : Array Expr := #[]
    for x in [0:n] do
      match ← g.mimicUnder? ftys[x]! with
      | some (m, nb) =>
        real := real.push (← underBinders nb ftys[x]! fields[x]! fun _ res v =>
          return g.call (g.unpackName (g.mimicOf m)) ps (g.idxOf m res) v)
      | none => real := real.push fields[x]!
    let body := mkAppN sT (real ++ ihs)
    if !g.isReal j then
      mkLambdaFVars bs body
    else
      -- The caller's minor lands at `Mⱼ (T._model.ctor f⃗_real)`, which unfolds
      -- to `Mⱼ (Bⱼ.c (pack (unpack f⃗)))`, and the block hands it `Mⱼ (Bⱼ.c f⃗)`.
      let mut lhs : Array Expr := #[]
      let mut proofs : Array (Option Expr) := #[]
      for x in [0:n] do
        match ← g.mimicUnder? ftys[x]! with
        | some (m, nb) =>
          let o := g.mimicOf m
          let (l, pf) ← g.underEq nb ftys[x]! fields[x]! fun _ res v => do
            let fidx := g.idxOf m res
            return (g.call (g.packName o) ps fidx (g.call (g.unpackName o) ps fidx v),
                    g.call (g.sectionName o) ps fidx v)
          lhs := lhs.push l
          proofs := proofs.push (some pf)
        | none =>
          lhs := lhs.push fields[x]!
          proofs := proofs.push none
      let rebuild := fun (a : Array Expr) => g.blockCtorAt j cn ps a
      -- `Mⱼ` at the indices this constructor's result carries. They cannot
      -- mention a moved field — Lean rejects a nested field a later type
      -- depends on, and it rejects a *result index* about one for the
      -- same reason: `C α (llen l)` with `l : Lst α` nested fails Lean's own
      -- compilation with `application type mismatch: llen TT l ... has type
      -- _nested.Lst_2`. So they are constant across every fold in this file.
      let m0 := mkAppN motives[j]! (g.idxOf j (← ftyp (rebuild fields)))
      mkLambdaFVars bs (← g.foldValue v m0 ftys lhs fields proofs rebuild body)

/-- **The block's minor vector**, in the block's own order — every member's
constructors, member by member, which is the order `Bₖ.rec` binds them in and
the order the caller's own minors arrive in. -/
def blockMinors (g : Gen) (ps motives minors : Array Expr) (v : Level) :
    GenM (Array Expr) := do
  let bm ← g.blockMotives ps motives
  let head : Expr := g.blockRecAt 0 v
  let pairs := g.ctorPairs
  withMinorTypes (mkAppN head (ps ++ bm)) g.numMinors fun mtys =>
    (Array.range pairs.size).mapM fun t =>
      g.recMinor pairs[t]!.1 pairs[t]!.2 mtys[t]! minors[t]! ps motives v

/-- **One member's recursor, as the model restates it.** Read once and used by
both the recursor and its ι rules, which share the `np + nm + nmin` binders and
differ only past them. -/
structure RecShape where
  k : Nat
  /-- `Bₖ.rec`, the block's own. -/
  src : Name
  /-- The motive universe, the recursor's single level parameter. -/
  v : Level
  lparams : List Name
  nm : Nat
  nmin : Nat
  /-- The member's index count — the export's own for a real member and the
  container's for a mimic. -/
  nidx : Nat
  /-- The declared type, at the model's names. -/
  ty : Expr
  deriving Inhabited

/-- `Bₖ.rec`'s statement at the model's names — the same table `nested::add`
restores the *export's* recursor with, one set of names along, so
`T._model.rec_k` and `T.rec_k` are the same statement about different
constants. -/
def recShape (g : Gen) (k : Nat) (heads : Std.HashMap Name (Nat × Expr)) :
    GenM RecShape := do
  let src := g.blockRec k
  let .recInfo rv ← constInfo src | badShape s!"{src} is not a recursor"
  -- **A mimic's indices are the container's, and they are carried too.** The
  -- block member's count and the container's agree by construction — the mimic
  -- is the container at the occurrence's parameters — and this is where a
  -- disagreement would show.
  unless rv.numIndices == g.nidx[k]! do
    badShape s!"{src} has {rv.numIndices} indices where the block member has {g.nidx[k]!}"
  -- The motive universe first, the block's own after it — and the block's own
  -- are the declaration's, because that is what the block was declared with.
  -- **A block that eliminates only into `Prop` has no motive universe at all**,
  -- and then the motive is `Prop`-valued and every level list is just `ℓ⃗`.
  let v ←
    if g.largeElim then do
      let lp :: rest := rv.levelParams | badShape s!"{src} has no motive universe"
      unless rest.map Level.param == g.us do
        badShape s!"{src} carries the level parameters {rv.levelParams}"
      pure (Level.param lp)
    else do
      unless rv.levelParams.map Level.param == g.us do
        badShape s!"{src} carries the level parameters {rv.levelParams}"
      pure Level.zero
  if rv.numMotives != g.members.size then badShape s!"{src} has {rv.numMotives} motives"
  return { k, src, v, lparams := rv.levelParams
           nm := rv.numMotives, nmin := rv.numMinors, nidx := rv.numIndices
           ty := restore heads rv.type }

/-- The value of `T._model.rec_k`: the block's recursor at a **shifted motive
vector** — the caller's own at the root, the caller's composed with `unpack` at
each mimic. At a mimic the major itself has to move: the block eliminates `Bₖ`
and the export eliminates `occₖ`, so the recursor runs at `pack major` and the
result comes back along the **retraction** `unpackPack`. -/
def recValue (g : Gen) (sh : RecShape) : GenM Expr := do
  forallBoundedTelescope sh.ty (some (g.np + sh.nm + sh.nmin + sh.nidx + 1)) fun bs _ => do
    let ps := bs.extract 0 g.np
    let motives := bs.extract g.np (g.np + sh.nm)
    let minors := bs.extract (g.np + sh.nm) (g.np + sh.nm + sh.nmin)
    -- The indices sit between the minors and the major, which is where the
    -- recursor's own telescope puts them.
    let idxs := bs.extract (g.np + sh.nm + sh.nmin) (bs.size - 1)
    let major := bs[bs.size - 1]!
    let bm ← g.blockMotives ps motives
    let bmin ← g.blockMinors ps motives minors sh.v
    let head : Expr := g.blockRecAt sh.k sh.v
    let pre := ps ++ bm ++ bmin
    let value ←
      if g.isReal sh.k then
        pure (mkAppN head ((pre ++ idxs).push major))
      else do
        let o := g.mimicOf sh.k
        -- **The recursor's own index binders are the container's.** They sit
        -- between the minors and the major, and `pack`, `unpack` and the
        -- retraction all take them there too.
        let occ := g.occAtIdx o ps idxs
        let pk := g.call (g.packName o) ps idxs major
        let base := mkAppN head ((pre ++ idxs).push pk)
        let trip := g.call (g.unpackName o) ps idxs pk
        let mot ← withLocalDeclD `x occ fun x =>
          withLocalDeclD `h (g.eqi.mk' g.u occ trip x) fun h =>
            mkLambdaFVars #[x, h] (mkAppN motives[sh.k]! (idxs.push x))
        pure (g.eqi.recAt sh.v g.u occ trip mot base major
          (g.call (g.retractName o) ps idxs major))
    mkLambdaFVars bs value

/-! ### the congruence the ι rules are stated along -/

/-- **`congrPackᵢ : ∀p⃗ l₀ l, Eq l₀ l → Eq (packᵢ l₀) (packᵢ l)`.**

Needed for a reason that is not obvious. The ι rule of a **root** constructor
with a packed field has, on its left, the transport `recₖ`'s minor performs —
along `packUnpack (pack f)`. Proving it means `Eq.rec` on `unpackPack f`, whose
motive has to name a proof of `Eq (pack (unpack (pack f))) (pack x)` for the
abstracted `x`, and only a *congruence* of `pack` is that. Proof irrelevance
then identifies the two at `x := f`, which is where the triangle identity would
otherwise have to be proved. -/
def congrPackDecl (g : Gen) (i : Nat) (ps : Array Expr) : GenM (Expr × Expr) := do
  g.withOccIndices i ps fun idxs => do
    let occ := g.occAtIdx i ps idxs
    let mem := mkAppN (g.memAt (i + g.numAll) ps) idxs
    let pk := fun (x : Expr) => g.call (g.packName i) ps idxs x
    withLocalDeclD `l0 occ fun l0 => withLocalDeclD `l occ fun l =>
      withLocalDeclD `h (g.eqi.mk' g.u occ l0 l) fun h => do
        let tel := ps ++ idxs ++ #[l0, l, h]
        let ty ← mkForallFVars tel (g.eqi.mk' g.u mem (pk l0) (pk l))
        let mot ← withLocalDeclD `x occ fun x =>
          withLocalDeclD `hx (g.eqi.mk' g.u occ l0 x) fun hx =>
            mkLambdaFVars #[x, hx] (g.eqi.mk' g.u mem (pk l0) (pk x))
        let base := g.eqi.refl' g.u mem (pk l0)
        let val ← mkLambdaFVars tel (g.eqi.recAt .zero g.u occ l0 mot base l h)
        return (ty, val)

end Gen

end InductiveModels
