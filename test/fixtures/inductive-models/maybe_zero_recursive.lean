prelude

set_option bootstrap.inductiveCheckResultingUniverse false

/-!
The smallest inhabited recursive family at a maybe-zero sort.  Its recursor
is small: the motive is proposition-valued even when `u` is positive. `MRI`
crosses the same recursion with a changing index so the lifted pair projection
is checked at a nontrivial child fibre.
-/

universe u

inductive MR : Sort u where
  | nil : MR
  | step : MR → MR

inductive MRI (ι : Type) (i j : ι) : ι → Sort u where
  | base : MRI ι i j i
  | step : MRI ι i j i → MRI ι i j j

/- Relational Carve must thread one `Good` hypothesis under the binder and a
   second one beside it; this covers infinitary and branching recursion in the
   same indexed sometimes-`Prop` family. -/
inductive MRIWide (ι α : Type) (i j : ι) : ι → Sort u where
  | base : MRIWide ι α i j i
  | branch : (α → MRIWide ι α i j i) → MRIWide ι α i j j →
      MRIWide ι α i j j
