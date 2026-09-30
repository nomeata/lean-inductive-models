/- **A field that needs the recursive box, whose type is an arrow tower.**

   `TowerBox.{u, v} (α : Sort u) (γ : Sort v)` has one field of type
   `bt 60`, where `bt 0 = α → γ` and `bt (k+1) = bt k → bt k`, the domain and
   the body being the *same* object: about 2^60 `Π` nodes as a tree and a few
   dozen as a DAG. With `α : Sort u`, `γ : Sort v` the field's level is an
   `imax` chain, which no pad absorbs, so the Simple route stores the field
   recursively boxed (`src/InductiveModels/Simple/Box.lean`) and must build the
   coercions between `bt 60` and its box, in both directions.

   A coercion at a `Π` coerces the argument contravariantly and the result
   covariantly, so the coercion at `bt (k+1)` mentions the one at `bt k`
   twice. Inlined, it is as large as the tower's tree, and so is the kernel's
   check that unboxing undoes boxing; the box must share both. The fixture
   gates the *construction*, not a walk: it is the input that was exponential
   after every walk was made linear (see `docs/maintainers/DagSafety.md`).

   Regenerate with
   `FIXTURE_DIR=$PWD/test/fixtures/dag-towers LEAN_INDUCTIVE_MODELS_FILTER=0 scripts/export-fixture.sh box_tower.lean`. -/
import Lean

open Lean Meta

--#export TowerBox

namespace DagTowers

def depth : Nat := 60

/-- The arrow tower over `A`: `at 0 A = A`, `at (k+1) A = at k A → at k A`. -/
def arrows (A : Expr) : Nat → Expr
  | 0 => A
  | k + 1 => let t := arrows A k; .forallE `x t t .default

run_meta do
  let u := Level.param `u
  let v := Level.param `v
  let ty ← withLocalDeclD `α (.sort u) fun α => withLocalDeclD `γ (.sort v) fun γ =>
    mkForallFVars #[α, γ] (.sort (mkLevelMax 1 (mkLevelMax u v)))
  let mk ← withLocalDeclD `α (.sort u) fun α => withLocalDeclD `γ (.sort v) fun γ => do
    let base ← mkArrow α γ
    withLocalDeclD `f (arrows base depth) fun f =>
      mkForallFVars #[α, γ, f] (mkApp2 (.const `TowerBox [u, v]) α γ)
  addDecl (.inductDecl [`u, `v] 2
    [{ name := `TowerBox, type := ty,
       ctors := [{ name := `TowerBox.mk, type := mk }] }] false)

end DagTowers
