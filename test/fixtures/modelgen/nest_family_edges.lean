/- **Two edges of the family treatment that two-member fixtures cannot reach.**

   * `A1`/`A2`/`A3` is a mutual block of **three** members. Two of them cannot
     say where a mimic's recursor lives: with `A`/`B`, `A.rec_1` is equally
     "the first member's namespace" and "the previous member's". Here `A1` is
     the mimic of `List A2` and `A2` the mimic of `Box A3`, and Lean names both
     recursors `A1.rec_1` and `A1.rec_2` — **always the first member**,
     whichever member the occurrence came from. Five block members, five
     recursors, nine minors.
   * `X.mk : C X → X`, where `C` and `D` are a **mutually recursive pair of
     containers** rather than a nested one. The cycle `C X` / `D X` is answered
     by the same machinery, but through the other arm of the family lookup:
     `C`'s block has two real members and no nesting, where `Tree`'s has one
     real member and one nested occurrence. A family lookup that only knew how
     to count nested occurrences would find nothing here. -/
prelude

universe u

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

mutual
inductive C (α : Type) : Type where
  | c : D α → C α
  | cz : α → C α
inductive D (α : Type) : Type where
  | d : C α → D α
  | dz : D α
end

--#export Eq N List Box C D A1 A2 A3 X

mutual
inductive A1 : Type where
  | mk : List A2 → A1
  | z : A1
inductive A2 : Type where
  | mk : Box A3 → A2
  | z : A2
inductive A3 : Type where
  | mk : A1 → A3
  | z : A3
end

inductive X : Type where
  | mk : C X → X
  | z : X
