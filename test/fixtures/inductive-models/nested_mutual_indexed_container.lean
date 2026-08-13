/- A mutual, indexed block that nests through an indexed container.

   The later field of each `step` constructor depends on the preceding index
   binder. The nested-model iota proof must therefore build its block-side
   field types in the export constructor's local context; opening the two
   constructor telescopes independently leaves the block index free.

   `C` and `D` also exchange their indices in `D.step`, while their recursive
   occurrences under `Vec` sit at fixed indices. This is the inner container
   block used by `hard_nested_mutual_index.lean`, isolated so a dependent-field
   regression stays small and identifies the inner block directly. -/
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

--#export Eq N Vec C D

mutual
inductive C (α : Type) : N → N → Type where
  | base : α → C α N.z N.z
  | step : (i j : N) → Vec (D α N.z N.z) j → C α (N.s i) (N.s j)
inductive D (α : Type) : N → N → Type where
  | base : D α N.z N.z
  | step : (i j : N) → Vec (C α N.z N.z) i → D α (N.s j) (N.s i)
end
