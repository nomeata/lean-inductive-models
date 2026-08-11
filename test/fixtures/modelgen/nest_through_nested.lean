/- `T` nests into `Tree T`, and `Tree` was **itself** declared by nesting.
   Depth 2 through plain containers is covered by `nested_deep`; this is depth
   2 through a container that is a nested declaration, which nothing tests. -/
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

--#export Eq N List Tree T

inductive Tree (α : Type) : Type where
  | leaf : α → Tree α
  | node : List (Tree α) → Tree α

inductive T : Type where
  | mk : Tree T → T
  | z : T
