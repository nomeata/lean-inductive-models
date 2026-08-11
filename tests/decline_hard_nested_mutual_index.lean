/- A mutual, nested, indexed declaration through a container block that is
   itself mutual, nested, and indexed.

   `C` and `D` recurse into each other under `Vec`; their two indices are
   deliberately swapped by `D.step`. The outer block has members with
   different index arities. `A.collapse` maps every pair `i, j` to the same
   result index and repeats `C` at the same container indices with distinct,
   fixed index pairs of the contained `B`. `B.diag` maps both result indices
   to the same value and repeats `D` with different fixed `A` indices. Thus
   neither the outer result indices nor the nested occurrence arguments can
   be recovered injectively from the result type.

   **Expected current result:** Lean accepts this declaration and exports 25
   recursors, all of which `modelgen --check-recursors` matches. The inner
   `C`/`D` block models successfully. The outer block exposes a separate bug:
   its generated recursor and iota statements do not match the export, so the
   statement oracle rejects the run and no output is written. -/
prelude

universe u

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

inductive Vec (α : Type) : N → Type where
  | nil : Vec α N.z
  | cons : {n : N} → α → Vec α n → Vec α (N.s n)

mutual
inductive C (α : Type) : N → N → Type where
  | base : α → C α N.z N.z
  | step : (i j : N) → Vec (D α N.z N.z) j → C α (N.s i) (N.s j)
inductive D (α : Type) : N → N → Type where
  | base : D α N.z N.z
  | step : (i j : N) → Vec (C α N.z N.z) i → D α (N.s j) (N.s i)
end

--#export Eq N Vec C D A B

mutual
inductive A : N → Type where
  | zero : A N.z
  | next : (i j : N) →
      C (B N.z N.z) i j → D (B N.z (N.s N.z)) j i → A i → A (N.s i)
  | collapse : (i j : N) →
      C (B N.z N.z) N.z N.z →
      C (B N.z (N.s N.z)) N.z N.z → A N.z
inductive B : N → N → Type where
  | zero : B N.z N.z
  | swap : (i j : N) → C (A N.z) j i → D (A (N.s N.z)) i j → B i j → B j i
  | diag : (i j : N) →
      D (A N.z) N.z N.z → D (A (N.s N.z)) N.z N.z →
      B i j → B (N.s i) (N.s i)
end
