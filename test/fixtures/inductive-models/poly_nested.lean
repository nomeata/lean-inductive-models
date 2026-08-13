/- **The declaration carries universe parameters of its own.** Lean supports
   it; this file is the shape.

   Non-degeneracy is the whole point of the fixture. Three things are arranged
   so that a generator which confuses a *declared* level parameter with the
   level an occurrence is *instantiated* at cannot pass:

   * `List` and `Box` declare their parameter as `w`, and `PTree` declares `u`.
     A generator that wrote the container's declared parameter would leave `w`
     free in a declaration whose level parameters are `[u]`.
   * `QTree` has **two** level parameters and lands at `Type (max u v)`, so the
     occurrence's level is a *composite* and not a parameter at all. Two atoms
     cannot distinguish an ordering either: `QTree`'s parameters are at two
     different universes, so a generator that swapped them is visible.
   * `QTree` nests two deep, `List (Box (QTree α β))`, so both mimics carry the
     composite level. -/
prelude

universe u v w

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive List (α : Type w) : Type w where
  | nil : List α
  | cons : α → List α → List α

inductive Box (α : Type w) : Type w where
  | mk : α → Box α

--#export Eq List Box PTree QTree

inductive PTree (α : Type u) : Type u where
  | leaf : α → PTree α
  | node : List (PTree α) → PTree α

inductive QTree (α : Type u) (β : Type v) : Type (max u v) where
  | tip : α → β → QTree α β
  | node : List (Box (QTree α β)) → QTree α β
