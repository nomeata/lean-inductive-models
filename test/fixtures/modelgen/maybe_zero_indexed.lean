prelude

set_option bootstrap.inductiveCheckResultingUniverse false

/-!
The smallest multi-constructor indexed family at a maybe-zero sort.  Its
recursor is small: the motive is proposition-valued even when `u` is positive.
-/

universe u

inductive MI (ι : Type) (i j : ι) : ι → Sort u where
  | left : MI ι i j i
  | right : MI ι i j j
