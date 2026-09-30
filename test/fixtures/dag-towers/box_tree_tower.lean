/- **The recursive box in the tree arm: branching owners with a boxed arrow tower.**

   Each owner here stores, or binds under a recursive field, a value of type
   `bt 30`, where `bt 0 = α → γ` and `bt (k+1) = bt k → bt k`, the domain and
   the body being the *same* object: about 2^30 `Π` nodes as a tree and a few
   dozen as a DAG. With `α : Sort u`, `γ : Sort v` its level is an `imax`
   chain, so the tree arm stores it recursively boxed
   (`src/InductiveModels/Simple/Box.lean`), in the data tower or in a branch
   tower:

   * `BoxTree` — a boxed leaf field and a node with two recursive fields;
   * `BoxTreeLim` — a recursive field under a boxed binder, `(bt 30 → _) → _`;
   * `BoxTreeOne` — one constructor, so the model owes a selector for the boxed
     field, and its recursion is under a binder.

   Like `box_tower.lean` it gates a *construction*: every ι rule, the
   recursor and the selector rest on the box's round trips, which the kernel
   decides in time exponential in the tower's depth unless they are stated as
   lemmas (`docs/maintainers/DagSafety.md`).

   Regenerate with
   `FIXTURE_DIR=$PWD/test/fixtures/dag-towers LEAN_INDUCTIVE_MODELS_FILTER=0 scripts/export-fixture.sh box_tree_tower.lean`. -/
import Lean

open Lean Meta

--#export BoxTree BoxTreeLim BoxTreeOne

namespace DagTowers

def depth : Nat := 30

/-- The arrow tower over `A`: `at 0 A = A`, `at (k+1) A = at k A → at k A`. -/
def arrows (A : Expr) : Nat → Expr
  | 0 => A
  | k + 1 => let t := arrows A k; .forallE `x t t .default

/-- Add a two-parameter owner `n.{u,v} (α : Sort u) (γ : Sort v) : Type (max u v)`
whose constructors' fields are given as functions of `α`, `γ`, the tower and
the owner at those parameters. -/
def addOwner (n : Name) (ctors : List (Name × (Expr → Expr → Expr → Expr → MetaM (Array Expr)))) :
    MetaM Unit := do
  let u := Level.param `u
  let v := Level.param `v
  let ty ← withLocalDeclD `α (.sort u) fun α => withLocalDeclD `γ (.sort v) fun γ =>
    mkForallFVars #[α, γ] (.sort (mkLevelSucc (mkLevelMax u v)))
  let cs ← ctors.mapM fun (cn, fields) => do
    let t ← withLocalDeclD `α (.sort u) fun α => withLocalDeclD `γ (.sort v) fun γ => do
      let self := mkApp2 (.const n [u, v]) α γ
      let fs ← fields α γ (arrows (← mkArrow α γ) depth) self
      let body := fs.foldr (fun f acc => .forallE `f f acc .default) self
      mkForallFVars #[α, γ] body
    pure { name := n ++ cn, type := t : Constructor }
  addDecl (.inductDecl [`u, `v] 2 [{ name := n, type := ty, ctors := cs }] false)

run_meta addOwner `BoxTree [
  (`leaf, fun _ _ bt _ => pure #[bt]),
  (`node, fun _ _ _ self => pure #[self, self])]

run_meta addOwner `BoxTreeLim [
  (`base, fun _ _ _ _ => pure #[]),
  (`lim, fun _ _ bt self => return #[← mkArrow bt self])]

run_meta addOwner `BoxTreeOne [
  (`mk, fun α _ bt self => return #[bt, ← mkArrow α self])]

end DagTowers
