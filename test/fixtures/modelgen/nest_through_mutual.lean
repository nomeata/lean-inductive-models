/- A **mutual** block one of whose members nests. `mini/src/nested.rs` refuses
   this outright ("both a mutual block and nested; mini takes one or the
   other"); Lean accepts it. Nothing in the corpus has the shape. -/
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

--#export Eq N List A B

mutual
inductive A : Type where
  | mk : List B → A
  | leaf : A
inductive B : Type where
  | mk : A → B
end
