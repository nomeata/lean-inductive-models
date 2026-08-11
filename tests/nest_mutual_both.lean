/- A **mutual** block **both** of whose members nest, at **different**
   containers. `nest_through_mutual.lean` is the minimal shape and does not
   distinguish a per-member carrier from a single one: with only `A` nesting,
   a treatment that specialised `A` alone and passed `B` through would still
   look right at `A.rec`. Here `A` nests at `List B` and `B` at `Box A`, so
   there are four block members, two mimics at two distinct containers, and
   **four** recursors — `A.rec`, `B.rec`, `A.rec_1` (`List B`) and `A.rec_2`
   (`Box A`) — all over one shared motive and minor vector.

   The recursor family is the measurement: a nesting mutual block gets one
   recursor per **real member** in that member's own namespace, and one per
   mimic in the **first** member's, numbered from 1. -/
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

--#export Eq N List Box A B

mutual
inductive A : Type where
  | mk : List B → A
  | leaf : A
inductive B : Type where
  | mk : Box A → B
  | zb : B
end
