/- A proposition-valued field retained at a bare universe, with the input's
   own exact standard `PUnit` deliberately declared later.  This pins both
   parameter dependence and the simple-model basis wait. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive PFP (p : Prop) : Sort u where
  | mk : p → PFP p

inductive PUnit : Sort u where
  | unit : PUnit

--#export Eq PFP PUnit
