import Lean
import InductiveModels.Gen.Monad

/-!
# `MetaM` helpers at the generator's monad

Thin wrappers that lift `Meta` operations into `GenM`, plus the two head
normalisations every construction reads a field's type through. Nothing here
knows what is being generated.
-/

open Lean Meta

namespace InductiveModels
/-- `Meta.inferType`, at the generator's monad. -/
def ityp (e : Expr) : GenM Expr := inferType e

/-- The sort a type lives at. -/
def ilevel (e : Expr) : GenM Level := getLevel e

/-- Zeta-reduce the head of a type. Lean accepts a constructor field whose type
is a `let` — `(n : N) → (let m := n; Vec α m) → Let α` is one — and then the
member the field sits at is not the head of the expression as written. Only
`let` is unfolded and no definition is, so nothing else about the type moves. -/
partial def zetaHead : Expr → Expr
  | .letE _ _ v b _ => zetaHead (b.instantiate1 v)
  | e => e

/-- **A type's head, ζ- *and* β-reduced.** [`InductiveModels.zetaHead`] plus the redex
a container's **family** parameter leaves behind, iterated until neither moves.
Only `let` and β move and no constant is unfolded, so this answers "which
member / which occurrence / which index vector" and changes nothing about what
the type *is*. Every reader below goes through it; see the section on reading a
type's head, at [`InductiveModels.Gen.occIdx?`]. -/
partial def headNorm (e : Expr) : Expr :=
  match e with
  | .letE _ _ v b _ => headNorm (b.instantiate1 v)
  | .app .. => let e' := e.headBeta; if e' == e then e else headNorm e'
  | _ => e

/-- **A constructor field's type**, with any leading `let` gone. Every place in
this module that asks which member a field sits at reads it through here. -/
def ftyp (e : Expr) : GenM Expr := return zetaHead (← inferType e)

def constInfo (n : Name) : GenM ConstantInfo := do
  let some ci := (← getEnv).constants.find? n | badShape s!"{n} is not declared"
  return ci

/-- The container's constructors. -/
def ctorsOf (c : Name) : GenM (Array Name) := do
  let .inductInfo iv ← constInfo c | badShape s!"{c} is not an inductive"
  return iv.ctors.toArray

/-- How many fields a constructor has. -/
def numFieldsOf (c : Name) : GenM Nat := do
  let .ctorInfo cv ← constInfo c | badShape s!"{c} is not a constructor"
  return cv.numFields

/-- Peel `args.size` `∀` binders, substituting as it goes. -/
def instForall (ty : Expr) (args : Array Expr) : GenM Expr := do
  let mut cur := ty
  for a in args do
    match cur with
    | .forallE _ _ b _ => cur := b.instantiate1 a
    | _ => badShape "too few binders to instantiate"
  return cur

/-- A constructor's type at the given levels with `qs` substituted for its
leading binders, leaving the field telescope. -/
def instCtor (cn : Name) (ls : List Level) (qs : Array Expr) : GenM Expr := do
  let ci ← constInfo cn
  instForall (ci.type.instantiateLevelParams ci.levelParams ls) qs

/-- Open a type's telescope, with the binder types. -/
def withFields (ty : Expr) (k : Array Expr → Array Expr → GenM α) : GenM α := do
  forallTelescope ty fun fs _ => do k fs (← fs.mapM ftyp)

/-- A constructor's field types, with its binders instantiated left-to-right
by another constructor's corresponding fields. This keeps dependencies on an
earlier field in the caller's local context instead of returning types that
mention the temporary free variables introduced by [`withFields`]. -/
def fieldTypesAt (ty : Expr) (fields : Array Expr) : GenM (Array Expr) := do
  let mut cur := ty
  let mut tys := #[]
  for field in fields do
    match cur with
    | .forallE _ dom body _ =>
      tys := tys.push dom
      cur := body.instantiate1 field
    | _ => badShape "the constructors have different field counts"
  if cur.isForall then badShape "the constructors have different field counts"
  return tys

/-- **The dependency the congruence fold cannot survive, and only that one.**

The fold replaces one *packed* position of a constructor application at a time,
so a field whose type mentions an earlier packed field is ill-typed at every
intermediate stage. A dependency on a field that does **not** move is never
touched by the fold, and Lean supports it — `node : (n : N) → Vec N n → List
DTree → DTree` and `node : List ETree → (n : N) → Vec N n → ETree` are both
`test/fixtures/inductive-models/dependent_fields.lean`, and both are models now.

A dependency *on* a packed field is out of reach for a different reason: Lean
does not support it either. `node : (l : List GTree) → Len l N.z → GTree` fails
Lean's own nested compilation with `unknown constant 'GTree'`, because the
auxiliary block replaces `List GTree` with a fresh member and `Len l` is then
about a constant absent at that point in the block.

**The mention has to survive β**, which is why the type goes through
[`InductiveModels.headNorm`] first.
A container whose parameter is a *family* leaves its field as the redex
`(fun x => …) k`, and `k` is the field before it; when the family is constant —
`RB (RB N (fun _ => Key)) (fun _ => N)`, where the nesting is in the **key** —
the
redex mentions `k` and its reduct does not, so the fold has nothing to survive.
This used to decline that shape as a dependent field, which was a wrong reason
as well as a wrong answer: Lean compiles it. -/
def noDepOnPacked (packed : Array Expr) (fs tys : Array Expr) : GenM Unit := do
  for i in [0:tys.size] do
    let ti := headNorm tys[i]!
    for j in [0:i] do
      if packed.contains fs[j]! && ti.containsFVar fs[j]!.fvarId! then
        badShape "a field type depends on an earlier packed field"

/-- Read `n` minor premise types off a recursor application. -/
def withMinorTypes (recApp : Expr) (n : Nat) (k : Array Expr → GenM α) : GenM α := do
  let ty ← ityp recApp
  forallBoundedTelescope ty (some n) fun mvars _ => do
    k (← mvars.mapM ityp)

end InductiveModels
