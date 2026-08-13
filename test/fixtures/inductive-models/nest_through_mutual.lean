/- A **mutual** block one of whose members nests. Lean accepts this combination,
   and the fixture ensures the generator handles the two features together. -/
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
