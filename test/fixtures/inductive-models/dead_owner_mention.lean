/- **The βζ-dead owner mention, at every route that used to trip over it.**

   A constructor field may mention the type being declared in a position its
   own βζ reduction discards: `(fun _ : T => N) k` is `nonindexed_vanishing`'s
   spelling, and `let _u : Type := T; N` is this file's. Both are ordinary
   kernel-accepted plain inductives — Lean's positivity check reduces the
   field type first, so nothing here is nested, indexed or unsafe — and in
   both the field is *data*, not a recursive child.

   `let` rather than a β-redex on purpose: **Lean's own elaborator beta-reduces
   the redex away** before the exporter ever sees it, so a fixture written with
   `fun` cannot be regenerated from its source and the two that exist are
   pinned by hand. The `let` survives elaboration, so
   `test/scripts/export-inductive-models.sh` reproduces this file's raw export
   byte for byte. `InductiveModels.headNorm` discharges β and ζ in the same
   walk, so the two spellings are one question to every consumer.

   Every route below asked `mentionsAny` of the field domain **as written**,
   and each was wrong about this field in its own way. They are four
   dispositions, not four copies of one:

   * `DeadLabel` — **the tree arm's `labelFactored` gap**, and the shape the guard's
     own comment describes. The ζ-dead field `k` is *data*, and the infinitary
     child beside it binds `PFam k`; read as written, `k` is an earlier
     *recursive* field, which is precisely what the untagged label cannot
     reach, so the declaration was refused. It declined
     `.shapeUnsupported .incomplete` with `through the label: no`.

   * `DeadBranch` — **the tree arm's tower split**. `labelFactored` and `tagFactored`
     both say yes here, so the arm fired, and `wShapeOf` then put the ζ-dead
     field in the *branch* tower beside the two real children — a child whose
     type is `Q`. That was an internal tool error and not a decline: the arm
     was entered and could not finish.

   * `DeadStruct` — **not recursive at all.** One constructor, one data field,
     one ζ-dead field; `analysePrim`'s `isRec` said recursive, so the
     one-constructor nonrecursive routes were never reached and the
     since-withdrawn direct one-layer adapter's pointwise recursor walk
     aborted on a field that ends in `Q`.  It is an ordinary structure and
     models with both intrinsic projections, their literal ι rules, and the η
     rule that being structure-like earns — because the structure route reads
     recursion off what survives reduction as well, and not off the exported
     `isRec` flag, which is `true` here for a mention that means nothing.

   * `DeadProp` — the same shape as `DeadLabel` at `Prop`, so the **Church**
     route's `classifyCtor`/`pairArm` classification answers it rather than
     the tree arm's towers. It aborted on the nested-occurrence boundary message,
     naming a boundary this field is not on.

   `PFam` is `prim_w`'s: a family over a two-element type written through
   `P.rec`, because the equation compiler wants `PProd` and a `prelude`
   fixture has none. `DeadLabel` and `DeadProp` have a label-dependent child
   and are therefore the **untagged** instantiation of the tree arm's core, which is
   the `[propext, Classical.choice, Quot.sound]` column; `DeadBranch`'s
   branch type is a function of the tag alone and stays at
   `[propext, Quot.sound]`. -/
prelude
--#export Eq P Q PFam DeadLabel DeadBranch DeadStruct DeadProp

universe u

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive P : Type where
  | one : P
  | two : P

inductive Q : Type where
  | a : Q
  | b : Q
  | c : Q

/-- Written with `P.rec` rather than a `match`, exactly as `prim_w`'s is. -/
def PFam (k : P) : Type := @P.rec (fun _ => Type) P Q k

inductive DeadLabel : Type where
  | tip : DeadLabel
  | lim (k : (let _u : Type := DeadLabel; P)) : (PFam k → DeadLabel) → DeadLabel

inductive DeadBranch : Type where
  | tip : DeadBranch
  | fork (l : DeadBranch) (r : DeadBranch) (t : (let _u : Type := DeadBranch; Q)) :
      DeadBranch

inductive DeadStruct : Type where
  | mk (a : P) (dead : (let _u : Type := DeadStruct; Q)) : DeadStruct

inductive DeadProp : Prop where
  | tip : DeadProp
  | lim (k : (let _u : Prop := DeadProp; P)) : (PFam k → DeadProp) → DeadProp
