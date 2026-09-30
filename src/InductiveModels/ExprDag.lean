import Lean

/-!
# DAG-safe expression traversal

**Every walk over an `Expr` in this tool is linear in the expression's DAG
size.** An `Expr` is a DAG: a subterm that occurs twice is one object with two
parents, and an export writes it once. A walk that forgets that — a rebuild,
a fold, a search, a size, a comparison, a printer — visits a subterm once per
*path* to it, and a term of a few hundred nodes can have 2^60 paths. That is
not an exotic input: `EulerMeanVariationalInverse.StrongMeanEvolution` in the
Lean Kernel Arena's `navier-stokes-euler` export is a structure whose
constructor type is 1,481 nodes as a DAG and 188,635,673 as a tree, and one
unmemoized rebuild of it cost more memory than the host had. The fixtures in
`test/fixtures/dag-towers/` put depth-60 towers into every record position the
tool reads, so any walk that expands one does not finish.

The rule, therefore: **a recursion over `Expr` either is one of the walks
below, or is one of Lean's own walks that is memoized (see the table in
`docs/maintainers/DagSafety.md`), or recurses only along a spine** (a binder
telescope, an application spine, one child per step) and never into two
children of the same node.

Each walk below is memoized on the node it visits — and on the binder depth,
where the answer depends on it — so every distinct subterm is visited once,
and a rebuild returns the *same object* for the same input, which keeps the
output shared as well. The memo key is [`Lean.ExprStructEq`]: pointer equality
first, then structural equality including binder names and binder info, with
Lean's cached hash. A structurally equal copy that lost pointer sharing
somewhere upstream is still visited once.
-/

open Lean

namespace InductiveModels.Dag

/-- The memo key: an expression by structure, binder names included. -/
abbrev Key := ExprStructEq

/-- A memo from expression nodes to answers. -/
abbrev Memo (α : Type) := Std.HashMap Key α

/-- A memo from expression nodes at a binder depth to answers. -/
abbrev DepthMemo (α : Type) := Std.HashMap (Key × Nat) α

/-- Look `e` up in a memo held in the state of `m`, and compute and record the
answer on a miss.  The building block every monadic walk below uses; a caller
with its own state layers a `StateT (Memo α)` or [`Lean.MonadCacheT`] over it. -/
@[inline] def memo [Monad m] [MonadStateOf (Memo α) m] (e : Expr) (k : Unit → m α) : m α := do
  if let some r := (← get)[(e : Key)]? then return r
  let r ← k ()
  modify fun t => t.insert e r
  return r

/-- [`memo`] at a binder depth. -/
@[inline] def memoAt [Monad m] [MonadStateOf (DepthMemo α) m] (e : Expr) (d : Nat)
    (k : Unit → m α) : m α := do
  if let some r := (← get)[((e : Key), d)]? then return r
  let r ← k ()
  modify fun t => t.insert (e, d) r
  return r

/-! ## Searches -/

/-- Does some subterm of `e` satisfy `p`?  Lean's `Expr.find?`, which is the
C++ `for_each` with a pointer-keyed visited set: linear in the DAG. -/
@[inline] def any (e : Expr) (p : Expr → Bool) : Bool :=
  (e.find? p).isSome

/-- Does `e` contain the free variable `fvarId`?  Lean's own
`Expr.containsFVar`/`Expr.hasAnyFVar` are *not* memoized — they recurse into
both children of every node that has a free variable — so this replaces them
everywhere. -/
def containsFVar (e : Expr) (fvarId : FVarId) : Bool :=
  e.hasFVar && (e.findExt? fun s =>
    if !s.hasFVar then .done
    else match s with
      | .fvar id => if id == fvarId then .found else .done
      | _ => .visit).isSome

/-- Does `e` contain a free variable satisfying `p`?  The memoized
`Expr.hasAnyFVar`. -/
def hasAnyFVar (e : Expr) (p : FVarId → Bool) : Bool :=
  e.hasFVar && (e.findExt? fun s =>
    if !s.hasFVar then .done
    else match s with
      | .fvar id => if p id then .found else .done
      | _ => .visit).isSome

/-- Does `e` mention `needle` as a subterm (up to `==`, i.e. `Expr.eqv`)? -/
def occurs (needle e : Expr) : Bool :=
  any e (· == needle)

/-- A search whose answer at a node depends on the binder depth: `visit d s`
answers `some b` to stop at `s` with `b`, or `none` to look at its children,
the binder body at `d + 1`.  Memoized on `(s, d)`. -/
partial def anyAt (visit : Nat → Expr → Option Bool) (e : Expr) (d : Nat := 0) : Bool :=
  let rec go (s : Expr) (d : Nat) : StateM (Std.HashSet (Key × Nat)) Bool := do
    if let some b := visit d s then return b
    if (← get).contains ((s : Key), d) then return false
    modify fun t => t.insert (s, d)
    match s with
    | .app f a => go f d <||> go a d
    | .lam _ t b _ | .forallE _ t b _ => go t d <||> go b (d + 1)
    | .letE _ t v b _ => go t d <||> go v d <||> go b (d + 1)
    | .mdata _ b => go b d
    | .proj _ _ b => go b d
    | _ => return false
  (go e d).run' {}

/-- [`any`] with the memo in the caller's hands: a walk that asks "does this
subterm satisfy `p`" of many subterms of one DAG — at every node it visits —
threads one table through all of them, and pays for each distinct subterm
once in total rather than once per question. -/
partial def anyMemo (p : Expr → Bool) (e : Expr) : StateM (Memo Bool) Bool :=
  memo e fun _ => do
    if p e then return true
    match e with
    | .app f a | .lam _ f a _ | .forallE _ f a _ => anyMemo p f <||> anyMemo p a
    | .letE _ t v b _ => anyMemo p t <||> anyMemo p v <||> anyMemo p b
    | .mdata _ b | .proj _ _ b => anyMemo p b
    | _ => return false

/-- The first subterm of `e`, in preorder (a node before its children,
children left to right: function before argument, binder domain before body),
at which `f` answers `some`.  Linear in the DAG, and the same answer as the
preorder walk over the tree: a subterm seen before was already searched, and
found nothing. -/
def findSome? (f : Expr → Option α) (e : Expr) : Option α :=
  (e.find? fun s => (f s).isSome).bind f

/-- Fold `f` over the **distinct** subterms of `e` in preorder — a node before
its children, function before argument, binder domain before body — visiting
each once, at its first occurrence.  A tree fold would visit a shared subterm
once per path to it; this is the fold every "collect what occurs" walk uses. -/
partial def foldPreorder (f : σ → Expr → σ) (init : σ) (e : Expr) : σ :=
  let rec go (s : Expr) : StateM (Std.HashSet Key × σ) Unit := do
    if (← get).1.contains s then return
    modify fun (seen, acc) => (seen.insert s, f acc s)
    match s with
    | .app fn a => go fn; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b | .proj _ _ b => go b
    | _ => pure ()
  ((go e).run ({}, init)).2.2

/-! ## Rewrites -/

/-- A rewrite that does not depend on the binder depth: Lean's `Expr.replace`,
the C++ `replace_fn` with a pointer-keyed cache on every shared node.  `f`
answers `some r` to replace a node, `none` to rebuild it from its rewritten
children. -/
@[inline] def map (f : Expr → Option Expr) (e : Expr) : Expr :=
  e.replace f

/-- Rebuild `e` from new children, returning `e` itself when nothing changed
(the `update*!` functions compare pointers), so an untouched subterm stays the
same object and the output stays shared. -/
@[inline] private def rebuild (e : Expr) (kids : Array Expr) : Expr :=
  match e with
  | .app .. => e.updateApp! kids[0]! kids[1]!
  | .lam .. => e.updateLambdaE! kids[0]! kids[1]!
  | .forallE .. => e.updateForallE! kids[0]! kids[1]!
  | .letE .. => e.updateLetE! kids[0]! kids[1]! kids[2]!
  | .mdata .. => e.updateMData! kids[0]!
  | .proj .. => e.updateProj! kids[0]!
  | _ => e

/-- A rewrite whose answer depends on the binder depth: `f d s` answers
`some r` to replace `s`, found under `d` binders of `e`, by `r`, or `none` to
rebuild it from its rewritten children, the binder body at `d + 1`.  Memoized
on `(s, d)`. -/
partial def mapAt (f : Nat → Expr → Option Expr) (e : Expr) (d : Nat := 0) : Expr :=
  let rec go (s : Expr) (d : Nat) : StateM (DepthMemo Expr) Expr := do
    if let some r := f d s then return r
    memoAt s d fun _ => do
      match s with
      | .app fn a => return rebuild s #[← go fn d, ← go a d]
      | .lam _ t b _ | .forallE _ t b _ => return rebuild s #[← go t d, ← go b (d + 1)]
      | .letE _ t v b _ => return rebuild s #[← go t d, ← go v d, ← go b (d + 1)]
      | .mdata _ b | .proj _ _ b => return rebuild s #[← go b d]
      | _ => return s
  (go e d).run' {}

/-- A monadic rewrite in which the callback may recurse: `f visit s` answers
`some r` to replace `s` — computing `r` with `visit`, the memoized rewrite
itself, on whatever subterms it likes — or `none` to rebuild `s` from its
rewritten children.  Every node is rewritten once. -/
partial def mapM [Monad m] (f : (Expr → StateT (Memo Expr) m Expr) → Expr →
    StateT (Memo Expr) m (Option Expr)) (e : Expr) : StateT (Memo Expr) m Expr :=
  let rec visit (s : Expr) : StateT (Memo Expr) m Expr :=
    memo s fun _ => do
      if let some r ← f visit s then return r
      match s with
      | .app fn a => return rebuild s #[← visit fn, ← visit a]
      | .lam _ t b _ | .forallE _ t b _ => return rebuild s #[← visit t, ← visit b]
      | .letE _ t v b _ => return rebuild s #[← visit t, ← visit v, ← visit b]
      | .mdata _ b | .proj _ _ b => return rebuild s #[← visit b]
      | _ => return s
  visit e

/-- [`mapM`] in the identity monad, with a fresh memo. -/
@[inline] def mapRec (f : (Expr → StateM (Memo Expr) Expr) → Expr →
    StateM (Memo Expr) (Option Expr)) (e : Expr) : Expr :=
  (mapM (m := Id) f e).run' {}

/-! ## Measures -/

/-- The number of distinct subterms of `e`: its size as a DAG. -/
partial def size (e : Expr) : Nat :=
  let rec go (s : Expr) : StateM (Std.HashSet Key) Unit := do
    if (← get).contains s then return
    modify fun t => t.insert s
    match s with
    | .app f a | .lam _ f a _ | .forallE _ f a _ => go f; go a
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b | .proj _ _ b => go b
    | _ => pure ()
  ((go e).run {}).2.size

/-- The size of `e` as a tree, computed on the DAG and saturating at `cap`:
`min cap (tree size)`.  Linear in the DAG however large the tree is. -/
partial def treeSizeCapped (e : Expr) (cap : Nat) : Nat :=
  let rec go (s : Expr) : StateM (Memo Nat) Nat :=
    memo s fun _ => do
      let n : Nat ← match s with
        | .app f a | .lam _ f a _ | .forallE _ f a _ => pure (1 + (← go f) + (← go a))
        | .letE _ t v b _ => pure (1 + (← go t) + (← go v) + (← go b))
        | .mdata _ b | .proj _ _ b => pure (1 + (← go b))
        | _ => pure 1
      return min cap n
  (go e).run' {}

end InductiveModels.Dag

namespace Lean.Expr

/-- [`InductiveModels.Dag.containsFVar`], for dot notation. -/
@[inline] def containsFVarDag (e : Expr) (fvarId : FVarId) : Bool :=
  InductiveModels.Dag.containsFVar e fvarId

/-- [`InductiveModels.Dag.hasAnyFVar`], for dot notation. -/
@[inline] def hasAnyFVarDag (e : Expr) (p : FVarId → Bool) : Bool :=
  InductiveModels.Dag.hasAnyFVar e p

end Lean.Expr
