/- **The export declares no `Eq`.** The round trips are equations, so the model
   cannot be written without one — and `modelgen` splices Lean's own in rather
   than declining: `Tree`'s model is 15 declarations plus
   the `Eq`, `Eq.refl` and `Eq.rec` that come with it. The file is named for
   what its **input** lacks, not for what happens to it. -/
prelude
inductive N : Type where
  | z : N
  | s : N → N
inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

--#export N List Tree

inductive Tree : Type where
  | leaf : Tree
  | node : List Tree → Tree
