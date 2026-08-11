/- **The two family axes at once, and one of them under a universe
   parameter.** Each axis has its own fixture; nothing says they compose, and a
   treatment that special-cased either one would pass those and fail here.

   * `P`/`Q` is a **mutual** block that nests **through a nested container**.
     Five block members — `P`, `Q`, `Tree Q`, `List P`, `List (Tree Q)` — and
     five recursors `P.rec`, `Q.rec`, `P.rec_1`, `P.rec_2`, `P.rec_3` over one
     shared vector of five motives and ten minors. Two of the three mimics,
     `Tree Q` and `List (Tree Q)`, are a cycle and are one simultaneous
     recursion; `List P` is not and is emitted one at a time. So the block is
     mutual, the mimic graph has a non-trivial condensation, and the carriers
     are a family — all in one declaration.
   * `R`/`S` is a mutual nesting block **with a level parameter of its own**,
     at a polymorphic container. Every generated constant carries `w`; the
     recursors carry their motive universe in front of it. -/
prelude

universe u v w

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

inductive List (α : Type u) : Type u where
  | nil : List α
  | cons : α → List α → List α

inductive Tree (α : Type) : Type where
  | leaf : α → Tree α
  | node : List (Tree α) → Tree α

--#export Eq N List Tree P Q R S

mutual
inductive P : Type where
  | mk : Tree Q → P
  | z : P
inductive Q : Type where
  | mk : List P → Q
  | z : Q
end

mutual
inductive R (α : Type w) : Type w where
  | mk : List (S α) → R α
  | z : α → R α
inductive S (α : Type w) : Type w where
  | mk : R α → S α
  | z : S α
end
