/- **The container the declaration nests into carries indices.** Lean supports
   it. `VTree.rec_1` comes back with `numIndices = 1` and a mimic motive
   `(a : N) → Vec VTree a → Sort u`: the occurrence is the container at its
   **parameters** and the index rides outside it, so a mimic is indexed even
   when the declaration is not.

   `WTree` nests into the *same* container at **two different indices**,
   `Vec WTree N.z` and `Vec WTree (N.s N.z)`. One mimic serves both, and a
   treatment that keyed a mimic on the whole application rather than on the
   container at its parameters would produce a block with a member Lean does
   not have — the same discrimination `nested_shapes`' `listOfN` decoy makes
   for the unindexed case.

   **`UTree` is the one that pins the index telescope rather than the fact of
   one.** A container with a *single* index at a *constant* value cannot
   distinguish a telescope that is threaded through `pack`, `unpack`, both
   round trips and `congrPack` from one that is dropped, nor an order that is
   preserved from one that is reversed. `Tab α : N → N → Type` has **two**
   indices; `UTree.node` sits at `Tab UTree N.z (N.s N.z)`, two *differing*
   values, so a swap is a type error; and `Tab`'s own recursion moves the
   indices one at a time — `wide` the first, `tall` the second — so a treatment
   that read one index where the other belongs is caught inside the container's
   own recursor as well as at the occurrence. -/
prelude

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

inductive Vec (α : Type) : N → Type where
  | vnil : Vec α N.z
  | vcons : α → (n : N) → Vec α n → Vec α (N.s n)

inductive Tab (α : Type) : N → N → Type where
  | leaf : α → Tab α N.z (N.s N.z)
  | wide : (a b : N) → Tab α a b → Tab α (N.s a) b
  | tall : (a b : N) → α → Tab α a b → Tab α a (N.s b)

--#export Eq N Vec Tab VTree WTree UTree

inductive VTree : Type where
  | leaf : VTree
  | node : Vec VTree (N.s N.z) → VTree

inductive WTree : Type where
  | leaf : WTree
  | one : Vec WTree N.z → WTree
  | two : Vec WTree (N.s N.z) → WTree

inductive UTree : Type where
  | leaf : UTree
  | node : Tab UTree N.z (N.s N.z) → UTree
