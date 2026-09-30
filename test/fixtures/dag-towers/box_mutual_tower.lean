/- **The recursive box in the mutual one-layer adapter.**

   `BoxMutA` and `BoxMutB` are one mutual block. `BoxMutA` has one
   constructor, with a field of type `bt 30` — `bt 0 = α → γ`,
   `bt (k+1) = bt k → bt k`, the domain and the body being the *same* object:
   about 2^30 `Π` nodes as a tree and a few dozen as a DAG — and a direct
   recursive field, so the mutual one-layer adapter publishes it as a
   constructor layer over the block's private family. With `α : Sort u`,
   `γ : Sort v` the field's level is an `imax` chain, so that layer stores it
   recursively boxed (`src/InductiveModels/Simple/Box.lean`). `BoxMutB`'s
   recursion is linear, so nothing else in the block branches.

   Like `box_tower.lean` it gates a *construction*: the layer's `roll`/`unroll`
   laws, its projection and its recursor rest on the box's round trips, which
   the kernel decides in time exponential in the tower's depth unless they are
   stated as lemmas (`docs/maintainers/DagSafety.md`).

   Regenerate with
   `FIXTURE_DIR=$PWD/test/fixtures/dag-towers LEAN_INDUCTIVE_MODELS_FILTER=0 scripts/export-fixture.sh box_mutual_tower.lean`. -/
import Lean

open Lean Meta

--#export BoxMutA BoxMutB

namespace DagTowers

def depth : Nat := 30

/-- The arrow tower over `A`: `at 0 A = A`, `at (k+1) A = at k A → at k A`. -/
def arrows (A : Expr) : Nat → Expr
  | 0 => A
  | k + 1 => let t := arrows A k; .forallE `x t t .default

run_meta do
  let u := Level.param `u
  let v := Level.param `v
  let ty ← withLocalDeclD `α (.sort u) fun α => withLocalDeclD `γ (.sort v) fun γ =>
    mkForallFVars #[α, γ] (.sort (mkLevelMax 1 (mkLevelMax u v)))
  let ctor (fields : Expr → Expr → Expr → Expr → Expr → MetaM (Array Expr)) (res : Name) :
      MetaM Expr :=
    withLocalDeclD `α (.sort u) fun α => withLocalDeclD `γ (.sort v) fun γ => do
      let a := mkApp2 (.const `BoxMutA [u, v]) α γ
      let b := mkApp2 (.const `BoxMutB [u, v]) α γ
      let fs ← fields α γ (arrows (← mkArrow α γ) depth) a b
      let body := fs.foldr (fun f acc => .forallE `f f acc .default)
        (mkApp2 (.const res [u, v]) α γ)
      mkForallFVars #[α, γ] body
  addDecl (.inductDecl [`u, `v] 2
    [{ name := `BoxMutA, type := ty,
       ctors := [{ name := `BoxMutA.mk, type := ← ctor (fun _ _ bt _ b => pure #[bt, b]) `BoxMutA }] },
     { name := `BoxMutB, type := ty,
       ctors := [{ name := `BoxMutB.nil, type := ← ctor (fun _ _ _ _ _ => pure #[]) `BoxMutB },
                 { name := `BoxMutB.cons, type := ← ctor (fun _ _ _ a _ => pure #[a]) `BoxMutB }] }]
    false)

end DagTowers
