/-
The smallest direct-simple recursor telescope with an elaborated default
argument.  `DefaultCtor.synthetic` mirrors the relevant part of
`Lean.SourceInfo.synthetic`: the final constructor field is represented by an
`OptParam` domain in the exported constructor and recursor types.
-/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u

@[reducible] def optParam (alpha : Sort u) (default : alpha) : Sort u := alpha

inductive Eq : {alpha : Sort u} → alpha → alpha → Prop where
  | refl (value : alpha) : Eq value value

inductive Flag : Type where
  | false : Flag
  | true : Flag

inductive DefaultCtor : Type where
  | plain : DefaultCtor
  | synthetic (startPos endPos : Flag) (canonical := Flag.false) : DefaultCtor

--#export optParam Eq Flag DefaultCtor
