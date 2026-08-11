prelude

set_option bootstrap.inductiveCheckResultingUniverse false

/-!
The smallest inhabited recursive family at a maybe-zero sort.  Its recursor
is small: the motive is proposition-valued even when `u` is positive.
-/

universe u

inductive MR : Sort u where
  | nil : MR
  | step : MR → MR

