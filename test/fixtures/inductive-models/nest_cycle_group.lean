/- **Cyclic mimics, non-degenerately.** `nest_through_nested.lean` is the
   minimal cycle — `T.mk : Tree T → T`, and mimic 0 is the anchor whose
   container family covers the group, at the identity mapping. Two things it
   cannot distinguish, and this file does:

   * `U.mk : List (Tree U) → U`. Mimic 0 is `List (Tree U)`, whose container
     `List` is *not* nested, so it anchors nothing; the family has to be found
     from mimic **1**, `Tree U`. And `Tree`'s family is `Tree U` then `List
     (Tree U)`, so the mimic-to-family mapping is the **transposition** and not
     the identity — `pack_0` is `Tree.rec_1` and `pack_1` is `Tree.rec`.
   * `V.mk : Box (Tree V) → V`. Three mimics: `Box (Tree V)` alone, then the
     cycle `Tree V` / `List (Tree V)`. So the condensation is a genuine DAG and
     the cycle has to be emitted **before** the ordinary mimic that reads it —
     `pack_0` calls `pack_1`, and `pack_1` and `pack_2` are one recursion. -/
prelude

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

inductive Box (α : Type) : Type where
  | mk : α → Box α

--#export Eq N List Box Tree U V

inductive Tree (α : Type) : Type where
  | leaf : α → Tree α
  | node : List (Tree α) → Tree α

inductive U : Type where
  | mk : List (Tree U) → U
  | z : U

inductive V : Type where
  | mk : Box (Tree V) → V
  | z : V
