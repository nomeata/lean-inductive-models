prelude

set_option bootstrap.inductiveCheckResultingUniverse false

/-!
The indexed singleton corner of the maybe-zero route.  At `u = 0` the carrier
is a proposition; at positive `u` it is data, but its only constructor still
carries proof data alone.  Lean therefore gives `DG.rec` an unrestricted
motive universe.
-/

universe u

inductive I : Type where
  | a : I

inductive DG (P Q : Prop) : I → Sort u where
  | mk (hP : P) (hQ : Q) : DG P Q I.a

#check @DG.rec
