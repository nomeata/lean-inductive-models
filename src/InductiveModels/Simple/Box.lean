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
hold by βι, `PSigma'` structure eta, proof irrelevance and function eta alone —
but the kernel decides them by taking the value apart at every Π of the field
type counted as a tree, so the constructions below state them as lemmas and
use the lemmas wherever no later field forces the conversion. -/

/-- Is there an `imax` anywhere in the level? Asked of normal forms: a level
the pads cannot absorb. -/
partial def levelHasIMax : Level → Bool
  | .imax .. => true
  | .max a b => levelHasIMax a || levelHasIMax b
  | .succ a => levelHasIMax a
  | _ => false

/-- The universe of [`InductiveModels.boxTyOf`] without constructing its `PSigma'`
terms. The tree arm asks its tower-level question before primitives are spliced,
so this level-only mirror keeps that early, rollback-free guard while using the
same recursive Π shape as the actual box.

Memoized on the type: a `Π` whose domain and codomain share a subterm would
otherwise be visited once per path through it. -/
partial def boxLevelOf (t : Expr) : GenM Level :=
  (go t).run' {}
where
  go (t : Expr) : StateT (Dag.Memo Level) GenM Level := Dag.memo t fun _ => do
    match ← whnf t with
    | .forallE name domain body info =>
      let domainLevel ← go domain
      withLocalDecl name info domain fun x => do
        let bodyLevel ← go (body.instantiate1 x)
        return (mkLevelIMax domainLevel bodyLevel).normalize
    | atomic =>
      let level ← ilevel atomic
      return (mkLevelMax' (.succ .zero) level).normalize


/-! ## The box's coercions, as terms over generic combinators

The boxed type is a type, and a type is a DAG like any other: the box walks it
memoized. The *coercions* between a type and its box are terms, and at
`Π x : D, C` each one mentions the coercions at `D` and at `C` — the box
coerces the argument contravariantly and the result covariantly. Written as
λ-terms, the coercion at a `Π` whose domain and codomain share structure is as
large as that structure's tree, because the sub-coercions are inlined under a
fresh variable each time. Here every coercion is instead an **application of a
generic combinator** — `arrBox uD bC`, `arrUnbox bD uC`, and their dependent
forms — to the coercions of its children, which are themselves such terms: a
node mentions each child's coercion once, and a child shared by several
parents is one object. The coercion terms are a DAG exactly as large as the
field type's.

**The round trips are lemmas, not conversions.** `unbox (box v) ≡ v` holds by
βδι and function eta, but Lean's kernel decides it by eta-expanding `v` at
every `Π` and comparing the argument's own round trip at a fresh variable —
one question per node of the *tree*. No cache of the kernel's can share those
questions: each is about a different variable, and a formulation over closed
per-node functions does not help either, since the kernel opens both sides
with a fresh variable before it reaches the recurring pair (measured, and
recorded in `docs/maintainers/DagSafety.md`). So each node has
`rt : ∀ v, unbox (box v) = v` and `sec : ∀ w, box (unbox w) = w`, again
applications of generic lemmas (`arrRt`, `arrSec`, `depRt`, `depSec`) to the
children's. The generic lemmas are proved once, about variables, from one
`Eq.rec` and one `funext` each; `funext` is the standard one, derived from
`Quot.sound` where the input has none ([`InductiveModels.ensureFunext`]).

At a dependent `Π` the codomain's box is indexed by the unboxed argument, so
`depUnbox` transports the stored result along the domain's `rt` rather than
asking the kernel for the domain's round trip. The transport is `cast`, whose
reducibility height is `0`: the kernel unfolds it last, when the other side of
a conversion is stuck, because unfolding it exposes an `Eq.rec` whose K-like
reduction asks the very round trip the lemma exists to avoid. `boxFix`, the
recursor's transport ([`InductiveModels.chainFinish`]), is kept at height `0`
for the same reason — and at a *regular* height rather than an opaque one,
because the kernel compares two applications of the same definition argument
by argument before unfolding them only for regular definitions.

The generic declarations live in the owner's implementation namespace, are
built lazily while the owner's model is built, and are handed back in
creation order by [`InductiveModels.boxScopeInsert`]. -/

/-- How a node's round-trip lemmas are built from its children. -/
inductive BoxKind where
  | atom
  | arr (d c : Expr)
  /-- A dependent `Π`: its domain and its codomain opened at `x`. -/
  | dep (d : Expr) (x : LocalDecl) (cx : Expr)
  deriving Inhabited

/-- One node of the box, in the context it was built in. -/
structure BoxNode where
  ty : Expr
  bty : Expr
  uT : Level
  uB : Level
  /-- `T → BT`. -/
  box : Expr
  /-- `BT → T`. -/
  unbox : Expr
  kind : BoxKind
  rt? : Option Expr := none
  sec? : Option Expr := none
  deriving Inhabited

/-- The box of an owner's model so far. -/
structure BoxScope where
  ns : Name
  reserved : Std.HashSet Name
  memo : Std.HashMap Dag.Key BoxNode := {}
  decls : Array Declaration := #[]
  spliced : Array Name := #[]
  next : Nat := 0
  funext? : Option Name := none
  /-- The generic declarations built so far, by role. -/
  support : Std.HashMap String Name := {}

/-- The open scopes, innermost last: a model's construction can build another
model's (the tree arm's core support does), and each has its own. -/
initialize boxScopeRef : IO.Ref (Array BoxScope) ← IO.mkRef #[]

/-- Open the box scope of one owner's model: its generic declarations are named
under `ns`. The answer is the scope's depth, which closes it. -/
def boxScopeOpen (ns : Name) (reserved : Std.HashSet Name) : GenM Nat := do
  let depth := (← boxScopeRef.get).size
  boxScopeRef.modify (·.push { ns, reserved })
  return depth

/-- Drop every scope from `depth` on, whatever became of the construction
that opened it. -/
def boxScopeRestore (depth : Nat) : GenM Unit := do
  boxScopeRef.modify (·.extract 0 depth)

/-- Close the scope at `depth`: the declarations it installed, in dependency
order, and the names among them that are spliced support rather than the
model's own. -/
def boxScopeClose (depth : Nat) : GenM (Array Declaration × Array Name) := do
  let stack ← boxScopeRef.get
  boxScopeRestore depth
  match stack[depth]? with
  | some s => return (s.decls, s.spliced)
  | none => return (#[], #[])

/-- Close the scope and put what it installed into an emitted declaration
sequence: after the support the construction spliced and before its first own
declaration, since a box names the former and nothing the latter defines. -/
def boxScopeInsert (depth : Nat) (decls : Array Declaration) (spliced : Array Name) :
    GenM (Array Declaration × Array Name) := do
  let (boxDecls, boxSpliced) ← boxScopeClose depth
  if boxDecls.isEmpty then return (decls, spliced)
  let firstOwn := (decls.findIdx? fun d => !d.getNames.all spliced.contains).getD decls.size
  return (decls.extract 0 firstOwn ++ boxDecls ++ decls.extract firstOwn decls.size,
    spliced ++ boxSpliced)

private def boxScope : GenM BoxScope := do
  let some s := (← boxScopeRef.get).back?
    | badShape "the recursive box was used outside an owner's box scope"
  return s

/-- The `Eq` the round trips are stated at: the one the construction has
installed by the time the box is first asked for anything. -/
private def boxEqi : GenM EqInfo := do
  match EqInfo.check (← getEnv) with
  | .ok eqi => return eqi
  | .error message => badShape s!"the recursive box has no Eq to state its round trips at: {message}"

private def modifyBoxScope (f : BoxScope → BoxScope) : GenM Unit :=
  boxScopeRef.modify fun stack => match stack.back? with
    | some s => stack.pop.push (f s)
    | none => stack

private def freshBoxName (base : String) : GenM Name := do
  let s ← boxScope
  let n := Name.str s.ns s!"{base}_{s.next}"
  modifyBoxScope fun s => { s with next := s.next + 1 }
  if s.reserved.contains n || (← getEnv).contains n then declineWith (.nameTaken n)
  return n

private def emitBox (d : Declaration) : GenM Unit := do
  addChecked d
  modifyBoxScope fun s => { s with decls := s.decls.push d }

/-- `funext`, spliced once per scope where the input has none. -/
private def boxFunext : GenM Name := do
  let s ← boxScope
  if let some n := s.funext? then return n
  let (n, ds) ← ensureFunext s.ns (← boxEqi) s.reserved
  modifyBoxScope fun s =>
    { s with funext? := some n, decls := s.decls ++ ds
             spliced := s.spliced ++ ds.flatMap (·.getNames.toArray) }
  return n

private def emitDef (n : Name) (lps : List Name) (ty val : Expr)
    (hints? : Option ReducibilityHints := none) : GenM Unit := do
  let hints ← match hints? with
    | some h => pure h
    | none => hintsFor val
  emitBox (.defnDecl { name := n, levelParams := lps, type := ty, value := val,
                       hints, safety := .safe })

private def emitThm (n : Name) (lps : List Name) (ty val : Expr) : GenM Unit :=
  emitBox (.thmDecl { name := n, levelParams := lps, type := ty, value := val })

/-- A generic declaration, built the first time a box needs it. -/
private def supportDecl (role : String) (build : Name → GenM Unit) : GenM Name := do
  if let some n := (← boxScope).support[role]? then return n
  let n ← freshBoxName role
  build n
  modifyBoxScope fun s => { s with support := s.support.insert role n }
  return n

private def lvA : Level := .param `a
private def lvB : Level := .param `b
private def lvC : Level := .param `c
private def lvD : Level := .param `d
private def lps4 : List Name := [`a, `b, `c, `d]
private def ls4 : List Level := [lvA, lvB, lvC, lvD]

/-- `cast.{u,v} {α : Sort u} {a b : α} (M : α → Sort v) (h : a = b) (x : M a) : M b`. -/
def boxCastName : GenM Name := supportDecl "cast" fun castN => do
  let eqi := (← boxEqi)
  let u := Level.param `u
  let v := Level.param `v
  let (castTy, castVal) ← withLocalDecl `α .implicit (.sort u) fun α => do
    withLocalDecl `a .implicit α fun a => withLocalDecl `b .implicit α fun b => do
    withLocalDeclD `M (← mkArrow α (.sort v)) fun M => do
    withLocalDeclD `h (eqi.mk' u α a b) fun h => withLocalDeclD `x (mkApp M a) fun x => do
      let motive ← withLocalDeclD `z α fun z => withLocalDeclD `hz (eqi.mk' u α a z) fun hz =>
        mkLambdaFVars #[z, hz] (mkApp M z)
      let bs := #[α, a, b, M, h, x]
      return (← mkForallFVars bs (mkApp M b), ← mkLambdaFVars bs (eqi.recAt v u α a motive x b h))
  emitDef castN [`u, `v] castTy castVal (some (.regular 0))

/-- `boxFix.{u,w,v} {T : Sort u} {B : Sort w} (bx : T → B) (ubx : B → T)
(sec : ∀ p, bx (ubx p) = p) (M : B → Sort v) (G : ∀ b, M (bx b)) (p : B) : M p`:
the minor at the unboxed value, transported back onto the stored one. -/
def boxFixName : GenM Name := supportDecl "boxFix" fun fixN => do
  let eqi := (← boxEqi)
  let u := Level.param `u
  let w := Level.param `w
  let v := Level.param `v
  let (fixTy, fixVal) ← withLocalDecl `T .implicit (.sort u) fun T => do
    withLocalDecl `B .implicit (.sort w) fun B => do
    withLocalDeclD `bx (← mkArrow T B) fun bx => do
    withLocalDeclD `ubx (← mkArrow B T) fun ubx => do
    let secTy ← withLocalDeclD `p B fun p =>
      mkForallFVars #[p] (eqi.mk' w B (mkApp bx (mkApp ubx p)) p)
    withLocalDeclD `sec secTy fun sec => do
    withLocalDeclD `M (← mkArrow B (.sort v)) fun M => do
    let gTy ← withLocalDeclD `b T fun b => mkForallFVars #[b] (mkApp M (mkApp bx b))
    withLocalDeclD `G gTy fun G => withLocalDeclD `p B fun p => do
      let bs := #[T, B, bx, ubx, sec, M, G, p]
      let motive ← withLocalDeclD `z B fun z =>
        withLocalDeclD `hz (eqi.mk' w B (mkApp bx (mkApp ubx p)) z) fun hz =>
          mkLambdaFVars #[z, hz] (mkApp M z)
      let body := eqi.recAt v w B (mkApp bx (mkApp ubx p)) motive (mkApp G (mkApp ubx p)) p
        (mkApp sec p)
      return (← mkForallFVars bs (mkApp M p), ← mkLambdaFVars bs body)
  emitDef fixN [`u, `w, `v] fixTy fixVal (some (.regular 0))

/-- `boxFix_iota … (rt : ∀ f, ubx (bx f) = f) … (f : T) : boxFix … (bx f) = G f`. -/
def boxFixIotaName : GenM Name := do
  let fixN ← boxFixName
  supportDecl "boxFix_iota" fun iotaN => do
  let eqi := (← boxEqi)
  let u := Level.param `u
  let w := Level.param `w
  let v := Level.param `v
  let (iotaTy, iotaVal) ← withLocalDecl `T .implicit (.sort u) fun T => do
    withLocalDecl `B .implicit (.sort w) fun B => do
    withLocalDeclD `bx (← mkArrow T B) fun bx => do
    withLocalDeclD `ubx (← mkArrow B T) fun ubx => do
    let secTy ← withLocalDeclD `p B fun p =>
      mkForallFVars #[p] (eqi.mk' w B (mkApp bx (mkApp ubx p)) p)
    let rtTy ← withLocalDeclD `f T fun f =>
      mkForallFVars #[f] (eqi.mk' u T (mkApp ubx (mkApp bx f)) f)
    withLocalDeclD `sec secTy fun sec => withLocalDeclD `rt rtTy fun rt => do
    withLocalDeclD `M (← mkArrow B (.sort v)) fun M => do
    let gTy ← withLocalDeclD `b T fun b => mkForallFVars #[b] (mkApp M (mkApp bx b))
    withLocalDeclD `G gTy fun G => withLocalDeclD `f T fun f => do
      let bs := #[T, B, bx, ubx, sec, rt, M, G, f]
      let bxf := mkApp bx f
      let fixAt := mkAppN (.const fixN [u, w, v]) #[T, B, bx, ubx, sec, M, G, bxf]
      let stmt := eqi.mk' v (mkApp M bxf) fixAt (mkApp G f)
      let a := mkApp ubx bxf
      let motive ← withLocalDeclD `b T fun b => withLocalDeclD `h (eqi.mk' u T f b) fun h => do
        -- `bx b = bx f`, from `h : f = b`.
        let e ← transportAlong eqi .zero u T f b h (eqi.refl' w B bxf)
          fun z => pure (eqi.mk' w B (mkApp bx z) bxf)
        let recMotive ← withLocalDeclD `z B fun z =>
          withLocalDeclD `hz (eqi.mk' w B (mkApp bx b) z) fun hz =>
            mkLambdaFVars #[z, hz] (mkApp M z)
        let lhs := eqi.recAt v w B (mkApp bx b) recMotive (mkApp G b) bxf e
        mkLambdaFVars #[b, h] (eqi.mk' v (mkApp M bxf) lhs (mkApp G f))
      let h0 ← symmOf eqi u T a f (mkApp rt f)
      let proof := eqi.recAt .zero u T f motive (eqi.refl' v (mkApp M bxf) (mkApp G f)) a h0
      return (← mkForallFVars bs stmt, ← mkLambdaFVars bs proof)
  emitThm iotaN [`u, `w, `v] iotaTy iotaVal

/-- The four sorts every arrow combinator quantifies over. -/
private def withSorts (k : Expr → Expr → Expr → Expr → GenM α) : GenM α :=
  withLocalDecl `D .implicit (.sort lvA) fun D => withLocalDecl `C .implicit (.sort lvB) fun C =>
  withLocalDecl `BD .implicit (.sort lvC) fun BD => withLocalDecl `BC .implicit (.sort lvD) fun BC =>
    k D C BD BC

/-- `arrBox (uD : BD → D) (bC : C → BC) (v : D → C) : BD → BC`. -/
def arrBoxName : GenM Name := supportDecl "arrBox" fun n => do
  let (t, val) ← withSorts fun D C BD BC => do
    withLocalDeclD `uD (← mkArrow BD D) fun uD => do
    withLocalDeclD `bC (← mkArrow C BC) fun bC => do
    withLocalDeclD `v (← mkArrow D C) fun v => withLocalDeclD `y BD fun y => do
      let bs := #[D, C, BD, BC, uD, bC, v]
      return (← mkForallFVars bs (← mkArrow BD BC),
        ← mkLambdaFVars (bs.push y) (mkApp bC (mkApp v (mkApp uD y))))
  emitDef n lps4 t val

/-- `arrUnbox (bD : D → BD) (uC : BC → C) (w : BD → BC) : D → C`. -/
def arrUnboxName : GenM Name := supportDecl "arrUnbox" fun n => do
  let (t, val) ← withSorts fun D C BD BC => do
    withLocalDeclD `bD (← mkArrow D BD) fun bD => do
    withLocalDeclD `uC (← mkArrow BC C) fun uC => do
    withLocalDeclD `w (← mkArrow BD BC) fun w => withLocalDeclD `x D fun x => do
      let bs := #[D, C, BD, BC, bD, uC, w]
      return (← mkForallFVars bs (← mkArrow D C),
        ← mkLambdaFVars (bs.push x) (mkApp uC (mkApp w (mkApp bD x))))
  emitDef n lps4 t val

/-- The four arrow coercions, shared by `arrRt` and `arrSec`. -/
private def withArr (k : Array Expr → Expr → Expr → Expr → Expr → Expr → Expr → Expr → Expr →
    GenM α) : GenM α := withSorts fun D C BD BC => do
  withLocalDeclD `bD (← mkArrow D BD) fun bD => do
  withLocalDeclD `uD (← mkArrow BD D) fun uD => do
  withLocalDeclD `bC (← mkArrow C BC) fun bC => do
  withLocalDeclD `uC (← mkArrow BC C) fun uC =>
    k #[D, C, BD, BC, bD, uD, bC, uC] D C BD BC bD uD bC uC

/-- `arrRt … (rtD : ∀ x, uD (bD x) = x) (rtC : ∀ z, uC (bC z) = z) (v : D → C) :
arrUnbox bD uC (arrBox uD bC v) = v`. -/
def arrRtName : GenM Name := do
  let boxN ← arrBoxName
  let unboxN ← arrUnboxName
  let fx ← boxFunext
  supportDecl "arrRt" fun n => do
  let eqi := (← boxEqi)
  let (t, val) ← withArr fun bs D C BD BC bD uD bC uC => do
    let rtDTy ← withLocalDeclD `x D fun x =>
      mkForallFVars #[x] (eqi.mk' lvA D (mkApp uD (mkApp bD x)) x)
    let rtCTy ← withLocalDeclD `z C fun z =>
      mkForallFVars #[z] (eqi.mk' lvB C (mkApp uC (mkApp bC z)) z)
    withLocalDeclD `rtD rtDTy fun rtD => withLocalDeclD `rtC rtCTy fun rtC => do
    withLocalDeclD `v (← mkArrow D C) fun v => do
      let bs := bs ++ #[rtD, rtC, v]
      let rtrip := mkApp (mkAppN (.const unboxN ls4) #[D, C, BD, BC, bD, uC])
        (mkApp (mkAppN (.const boxN ls4) #[D, C, BD, BC, uD, bC]) v)
      let stmt := eqi.mk' (mkLevelIMax' lvA lvB) (← mkArrow D C) rtrip v
      let pointwise ← withLocalDeclD `x D fun x => do
        let a := mkApp uD (mkApp bD x)
        let lhs := mkApp uC (mkApp bC (mkApp v a))
        let motive ← withLocalDeclD `b D fun b => withLocalDeclD `h (eqi.mk' lvA D a b) fun h =>
          mkLambdaFVars #[b, h] (eqi.mk' lvB C lhs (mkApp v b))
        mkLambdaFVars #[x] (eqi.recAt .zero lvA D a motive (mkApp rtC (mkApp v a)) x (mkApp rtD x))
      let proof := mkAppN (.const fx [lvA, lvB]) #[D, .lam `x D C .default, rtrip, v, pointwise]
      return (← mkForallFVars bs stmt, ← mkLambdaFVars bs proof)
  emitThm n lps4 t val

/-- `arrSec … (secD : ∀ y, bD (uD y) = y) (secC : ∀ w, bC (uC w) = w) (w : BD → BC) :
arrBox uD bC (arrUnbox bD uC w) = w`. -/
def arrSecName : GenM Name := do
  let boxN ← arrBoxName
  let unboxN ← arrUnboxName
  let fx ← boxFunext
  supportDecl "arrSec" fun n => do
  let eqi := (← boxEqi)
  let (t, val) ← withArr fun bs D C BD BC bD uD bC uC => do
    let secDTy ← withLocalDeclD `y BD fun y =>
      mkForallFVars #[y] (eqi.mk' lvC BD (mkApp bD (mkApp uD y)) y)
    let secCTy ← withLocalDeclD `z BC fun z =>
      mkForallFVars #[z] (eqi.mk' lvD BC (mkApp bC (mkApp uC z)) z)
    withLocalDeclD `secD secDTy fun secD => withLocalDeclD `secC secCTy fun secC => do
    withLocalDeclD `w (← mkArrow BD BC) fun w => do
      let bs := bs ++ #[secD, secC, w]
      let rtrip := mkApp (mkAppN (.const boxN ls4) #[D, C, BD, BC, uD, bC])
        (mkApp (mkAppN (.const unboxN ls4) #[D, C, BD, BC, bD, uC]) w)
      let stmt := eqi.mk' (mkLevelIMax' lvC lvD) (← mkArrow BD BC) rtrip w
      let pointwise ← withLocalDeclD `y BD fun y => do
        let c := mkApp bD (mkApp uD y)
        let lhs := mkApp bC (mkApp uC (mkApp w c))
        let motive ← withLocalDeclD `b BD fun b => withLocalDeclD `h (eqi.mk' lvC BD c b) fun h =>
          mkLambdaFVars #[b, h] (eqi.mk' lvD BC lhs (mkApp w b))
        mkLambdaFVars #[y]
          (eqi.recAt .zero lvC BD c motive (mkApp secC (mkApp w c)) y (mkApp secD y))
      let proof := mkAppN (.const fx [lvC, lvD]) #[BD, .lam `y BD BC .default, rtrip, w, pointwise]
      return (← mkForallFVars bs stmt, ← mkLambdaFVars bs proof)
  emitThm n lps4 t val

/-- The dependent forms' sorts: `C` and `BC` are families over the unboxed
argument. -/
private def withDSorts (k : Expr → Expr → Expr → Expr → GenM α) : GenM α :=
  withLocalDecl `D .implicit (.sort lvA) fun D => do
  withLocalDecl `C .implicit (← mkArrow D (.sort lvB)) fun C => do
  withLocalDecl `BD .implicit (.sort lvC) fun BD => do
  withLocalDecl `BC .implicit (← mkArrow D (.sort lvD)) fun BC =>
    k D C BD BC

private def piC (D C : Expr) : GenM Expr :=
  withLocalDeclD `x D fun x => mkForallFVars #[x] (mkApp C x)

private def piBC (BD BC uD : Expr) : GenM Expr :=
  withLocalDeclD `y BD fun y => mkForallFVars #[y] (mkApp BC (mkApp uD y))

private def bCTyOf (D C BC : Expr) : GenM Expr := withLocalDeclD `x D fun x => do
  mkForallFVars #[x] (← mkArrow (mkApp C x) (mkApp BC x))

private def uCTyOf (D C BC : Expr) : GenM Expr := withLocalDeclD `x D fun x => do
  mkForallFVars #[x] (← mkArrow (mkApp BC x) (mkApp C x))

private def rtDTyOf (eqi : EqInfo) (D bD uD : Expr) : GenM Expr := withLocalDeclD `x D fun x =>
  mkForallFVars #[x] (eqi.mk' lvA D (mkApp uD (mkApp bD x)) x)

/-- `depBox (uD : BD → D) (bC : ∀ x, C x → BC x) (v : ∀ x, C x) : ∀ y, BC (uD y)`. -/
def depBoxName : GenM Name := supportDecl "depBox" fun n => do
  let (t, val) ← withDSorts fun D C BD BC => do
    withLocalDeclD `uD (← mkArrow BD D) fun uD => do
    withLocalDeclD `bC (← bCTyOf D C BC) fun bC => do
    withLocalDeclD `v (← piC D C) fun v => withLocalDeclD `y BD fun y => do
      let bs := #[D, C, BD, BC, uD, bC, v]
      let uy := mkApp uD y
      return (← mkForallFVars bs (← piBC BD BC uD),
        ← mkLambdaFVars (bs.push y) (mkApp2 bC uy (mkApp v uy)))
  emitDef n lps4 t val

/-- `depUnbox (bD) (uD) (rtD) (uC : ∀ x, BC x → C x) (w : ∀ y, BC (uD y)) : ∀ x, C x`,
transporting the stored result along `rtD` onto the argument it is unboxed at. -/
def depUnboxName : GenM Name := do
  let castN ← boxCastName
  supportDecl "depUnbox" fun n => do
  let eqi := (← boxEqi)
  let (t, val) ← withDSorts fun D C BD BC => do
    withLocalDeclD `bD (← mkArrow D BD) fun bD => do
    withLocalDeclD `uD (← mkArrow BD D) fun uD => do
    withLocalDeclD `rtD (← rtDTyOf eqi D bD uD) fun rtD => do
    withLocalDeclD `uC (← uCTyOf D C BC) fun uC => do
    withLocalDeclD `w (← piBC BD BC uD) fun w => withLocalDeclD `x D fun x => do
      let bs := #[D, C, BD, BC, bD, uD, rtD, uC, w]
      let bx := mkApp bD x
      let stored := mkAppN (.const castN [lvA, lvD]) #[D, mkApp uD bx, x, BC, mkApp rtD x, mkApp w bx]
      return (← mkForallFVars bs (← piC D C), ← mkLambdaFVars (bs.push x) (mkApp2 uC x stored))
  emitDef n lps4 t val

/-- The dependent coercions, shared by `depRt` and `depSec`. -/
private def withDep (eqi : EqInfo) (k : Array Expr → Expr → Expr → Expr → Expr → Expr → Expr →
    Expr → Expr → Expr → GenM α) : GenM α := withDSorts fun D C BD BC => do
  withLocalDeclD `bD (← mkArrow D BD) fun bD => do
  withLocalDeclD `uD (← mkArrow BD D) fun uD => do
  withLocalDeclD `rtD (← rtDTyOf eqi D bD uD) fun rtD => do
  withLocalDeclD `bC (← bCTyOf D C BC) fun bC => do
  withLocalDeclD `uC (← uCTyOf D C BC) fun uC =>
    k #[D, C, BD, BC, bD, uD, rtD, bC, uC] D C BD BC bD uD rtD bC uC

/-- `depRt … (rtC : ∀ x z, uC x (bC x z) = z) (v : ∀ x, C x) :
depUnbox bD uD rtD uC (depBox uD bC v) = v`. -/
def depRtName : GenM Name := do
  let boxN ← depBoxName
  let unboxN ← depUnboxName
  let castN ← boxCastName
  let fx ← boxFunext
  supportDecl "depRt" fun n => do
  let eqi := (← boxEqi)
  let (t, val) ← withDep eqi fun bs D C BD BC bD uD rtD bC uC => do
    let rtCTy ← withLocalDeclD `x D fun x => withLocalDeclD `z (mkApp C x) fun z =>
      mkForallFVars #[x, z] (eqi.mk' lvB (mkApp C x) (mkApp2 uC x (mkApp2 bC x z)) z)
    withLocalDeclD `rtC rtCTy fun rtC => do withLocalDeclD `v (← piC D C) fun v => do
      let bs := bs ++ #[rtC, v]
      let rtrip := mkApp (mkAppN (.const unboxN ls4) #[D, C, BD, BC, bD, uD, rtD, uC])
        (mkApp (mkAppN (.const boxN ls4) #[D, C, BD, BC, uD, bC]) v)
      let stmt := eqi.mk' (mkLevelIMax' lvA lvB) (← piC D C) rtrip v
      let pointwise ← withLocalDeclD `x D fun x => do
        let a := mkApp uD (mkApp bD x)
        let stored := mkApp2 bC a (mkApp v a)
        let motive ← withLocalDeclD `b D fun b => withLocalDeclD `h (eqi.mk' lvA D a b) fun h => do
          let cast := mkAppN (.const castN [lvA, lvD]) #[D, a, b, BC, h, stored]
          mkLambdaFVars #[b, h] (eqi.mk' lvB (mkApp C b) (mkApp2 uC b cast) (mkApp v b))
        mkLambdaFVars #[x]
          (eqi.recAt .zero lvA D a motive (mkApp2 rtC a (mkApp v a)) x (mkApp rtD x))
      let proof := mkAppN (.const fx [lvA, lvB]) #[D, C, rtrip, v, pointwise]
      return (← mkForallFVars bs stmt, ← mkLambdaFVars bs proof)
  emitThm n lps4 t val

/-- `depSec … (secD : ∀ y, bD (uD y) = y) (secC : ∀ x w, bC x (uC x w) = w)
(w : ∀ y, BC (uD y)) : depBox uD bC (depUnbox bD uD rtD uC w) = w`. -/
def depSecName : GenM Name := do
  let boxN ← depBoxName
  let unboxN ← depUnboxName
  let castN ← boxCastName
  let fx ← boxFunext
  supportDecl "depSec" fun n => do
  let eqi := (← boxEqi)
  let (t, val) ← withDep eqi fun bs D C BD BC bD uD rtD bC uC => do
    let secDTy ← withLocalDeclD `y BD fun y =>
      mkForallFVars #[y] (eqi.mk' lvC BD (mkApp bD (mkApp uD y)) y)
    let secCTy ← withLocalDeclD `x D fun x => withLocalDeclD `z (mkApp BC x) fun z =>
      mkForallFVars #[x, z] (eqi.mk' lvD (mkApp BC x) (mkApp2 bC x (mkApp2 uC x z)) z)
    withLocalDeclD `secD secDTy fun secD => withLocalDeclD `secC secCTy fun secC => do
    withLocalDeclD `w (← piBC BD BC uD) fun w => do
      let bs := bs ++ #[secD, secC, w]
      let rtrip := mkApp (mkAppN (.const boxN ls4) #[D, C, BD, BC, uD, bC])
        (mkApp (mkAppN (.const unboxN ls4) #[D, C, BD, BC, bD, uD, rtD, uC]) w)
      let stmt := eqi.mk' (mkLevelIMax' lvC lvD) (← piBC BD BC uD) rtrip w
      let pointwise ← withLocalDeclD `y BD fun y => do
        let c := mkApp bD (mkApp uD y)
        let uc := mkApp uD c
        let wc := mkApp w c
        let motive ← withLocalDeclD `b BD fun b => withLocalDeclD `h (eqi.mk' lvC BD c b) fun h => do
          let ub := mkApp uD b
          let congrU ← transportAlong eqi .zero lvC BD c b h (eqi.refl' lvA D uc)
            fun z => pure (eqi.mk' lvA D uc (mkApp uD z))
          let cast := mkAppN (.const castN [lvA, lvD]) #[D, uc, ub, BC, congrU, wc]
          let lhs := mkApp2 bC ub (mkApp2 uC ub cast)
          mkLambdaFVars #[b, h] (eqi.mk' lvD (mkApp BC ub) lhs (mkApp w b))
        mkLambdaFVars #[y] (eqi.recAt .zero lvC BD c motive (mkApp2 secC uc wc) y (mkApp secD y))
      let fam ← withLocalDeclD `y BD fun y => mkLambdaFVars #[y] (mkApp BC (mkApp uD y))
      let proof := mkAppN (.const fx [lvC, lvD]) #[BD, fam, rtrip, w, pointwise]
      return (← mkForallFVars bs stmt, ← mkLambdaFVars bs proof)
  emitThm n lps4 t val

private def storeNode (n : BoxNode) : GenM Unit :=
  modifyBoxScope fun s => { s with memo := s.memo.insert n.ty n }

mutual

  /-- The node of `t` in the current context, built once. -/
  partial def boxNode (t : Expr) : GenM BoxNode := do
    if let some n := (← boxScope).memo[(t : Dag.Key)]? then return n
    let uT ← ilevel t
    let n ← match ← whnf t with
      | .forallE xn dom cod bi => do
        let nD ← boxNode dom
        if !cod.hasLooseBVars then
          let nC ← boxNode cod
          let ls := [nD.uT, nC.uT, nD.uB, nC.uB]
          let bt := Expr.forallE `y nD.bty nC.bty bi
          pure { ty := t, bty := bt, uT, uB := ← ilevel bt, kind := .arr dom cod
                 box := mkAppN (.const (← arrBoxName) ls)
                   #[dom, cod, nD.bty, nC.bty, nD.unbox, nC.box]
                 unbox := mkAppN (.const (← arrUnboxName) ls)
                   #[dom, cod, nD.bty, nC.bty, nD.box, nC.unbox] }
        else withLocalDecl xn bi dom fun x => do
          let cx := cod.instantiate1 x
          let nC ← boxNode cx
          let rtD ← boxRtOfNode nD
          let ls := [nD.uT, nC.uT, nD.uB, nC.uB]
          let cf := Expr.lam xn dom cod bi
          let bcf ← mkLambdaFVars #[x] nC.bty
          let bt ← withLocalDecl `y bi nD.bty fun y =>
            mkForallFVars #[y] (nC.bty.replaceFVar x (mkApp nD.unbox y))
          pure { ty := t, bty := bt, uT, uB := ← ilevel bt
                 kind := .dep dom (← x.fvarId!.getDecl) cx
                 box := mkAppN (.const (← depBoxName) ls)
                   #[dom, cf, nD.bty, bcf, nD.unbox, ← mkLambdaFVars #[x] nC.box]
                 unbox := mkAppN (.const (← depUnboxName) ls)
                   #[dom, cf, nD.bty, bcf, nD.box, nD.unbox, rtD, ← mkLambdaFVars #[x] nC.unbox] }
      | atomic => do
        let (d1, c1) ← dsingAt (.succ .zero)
        let β := Expr.lam `x atomic d1 .default
        let bt := psigmaT uT (.succ .zero) atomic β
        let motive := Expr.lam `p bt atomic .default
        let minor := Expr.lam `fst atomic (.lam `snd d1 (.bvar 1) .default) .default
        pure { ty := t, bty := bt, uT, uB := ← ilevel bt, kind := .atom
               box := .lam `a t (psigmaMk uT (.succ .zero) atomic β (.bvar 0) c1) .default
               unbox := .lam `p bt (psigmaRec uT uT (.succ .zero) atomic β motive minor (.bvar 0))
                 .default }
    storeNode n
    return n

  /-- `∀ v, unbox (box v) = v` at a node. -/
  partial def boxRtOfNode (n : BoxNode) : GenM Expr := do
    if let some r := n.rt? then return r
    if let some m := (← boxScope).memo[(n.ty : Dag.Key)]? then
      if let some r := m.rt? then return r
    let eqi := (← boxEqi)
    let r ← match n.kind with
      | .atom => withLocalDeclD `a n.ty fun a => mkLambdaFVars #[a] (eqi.refl' n.uT n.ty a)
      | .arr d c => do
        let nD ← boxNode d
        let nC ← boxNode c
        pure (mkAppN (.const (← arrRtName) [nD.uT, nC.uT, nD.uB, nC.uB])
          #[d, c, nD.bty, nC.bty, nD.box, nD.unbox, nC.box, nC.unbox,
            ← boxRtOfNode nD, ← boxRtOfNode nC])
      | .dep d xd cx => do
        let nD ← boxNode d
        let rtD ← boxRtOfNode nD
        let rtN ← depRtName
        withExistingLocalDecls [xd] do
          let x := mkFVar xd.fvarId
          let nC ← boxNode cx
          let rtC ← boxRtOfNode nC
          let lam := fun (e : Expr) => mkLambdaFVars #[x] e
          pure (mkAppN (.const rtN [nD.uT, nC.uT, nD.uB, nC.uB])
            #[d, ← lam cx, nD.bty, ← lam nC.bty, nD.box, nD.unbox, rtD, ← lam nC.box,
              ← lam nC.unbox, ← lam rtC])
    let m := (← boxScope).memo[(n.ty : Dag.Key)]?.getD n
    storeNode { m with rt? := some r }
    return r

  /-- `∀ w, box (unbox w) = w` at a node. -/
  partial def boxSecOfNode (n : BoxNode) : GenM Expr := do
    if let some r := n.sec? then return r
    if let some m := (← boxScope).memo[(n.ty : Dag.Key)]? then
      if let some r := m.sec? then return r
    let eqi := (← boxEqi)
    let r ← match n.kind with
      | .atom => withLocalDeclD `p n.bty fun p => mkLambdaFVars #[p] (eqi.refl' n.uB n.bty p)
      | .arr d c => do
        let nD ← boxNode d
        let nC ← boxNode c
        pure (mkAppN (.const (← arrSecName) [nD.uT, nC.uT, nD.uB, nC.uB])
          #[d, c, nD.bty, nC.bty, nD.box, nD.unbox, nC.box, nC.unbox,
            ← boxSecOfNode nD, ← boxSecOfNode nC])
      | .dep d xd cx => do
        let nD ← boxNode d
        let rtD ← boxRtOfNode nD
        let secD ← boxSecOfNode nD
        let secN ← depSecName
        withExistingLocalDecls [xd] do
          let x := mkFVar xd.fvarId
          let nC ← boxNode cx
          let secC ← boxSecOfNode nC
          let lam := fun (e : Expr) => mkLambdaFVars #[x] e
          pure (mkAppN (.const secN [nD.uT, nC.uT, nD.uB, nC.uB])
            #[d, ← lam cx, nD.bty, ← lam nC.bty, nD.box, nD.unbox, rtD, ← lam nC.box,
              ← lam nC.unbox, secD, ← lam secC])
    let m := (← boxScope).memo[(n.ty : Dag.Key)]?.getD n
    storeNode { m with sec? := some r }
    return r

end

/-- The recursively boxed type of `t`. -/
def boxTyOf (t : Expr) : GenM Expr := return (← boxNode t).bty

/-- `box v` at type `t`. -/
def boxValOf (t v : Expr) : GenM Expr := return mkApp (← boxNode t).box v

/-- `unbox w` at type `t`. -/
def unboxValOf (t w : Expr) : GenM Expr := return mkApp (← boxNode t).unbox w

/-- `∀ v, unbox (box v) = v` at type `t`. -/
def boxRtOf (t : Expr) : GenM Expr := do boxRtOfNode (← boxNode t)

/-- `∀ w, box (unbox w) = w` at type `t`. -/
def boxSecOf (t : Expr) : GenM Expr := do boxSecOfNode (← boxNode t)

end InductiveModels
