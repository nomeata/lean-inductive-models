/- Kernel unit-like positives and their nearest metadata misses. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

--#export Eq UnitType UnitProp MU MV WithField Indexed Recursive TwoCtor MR MS

inductive UnitType (α : Sort u) : Type where
  | mk : UnitType α

inductive UnitProp (α : Sort u) : Prop where
  | mk : UnitProp α

mutual
inductive MU (α : Sort u) : Type where
  | mk : MU α
inductive MV (α : Sort u) : Type where
  | mk : MV α
end

inductive WithField (α : Type u) : Type u where
  | mk (value : α) : WithField α

inductive Indexed (α : Type u) (f : α → α) : α → Type u where
  | mk (value : α) : Indexed α f (f value)

inductive Recursive : Type where
  | mk : Recursive → Recursive

inductive TwoCtor : Type where
  | left : TwoCtor
  | right : TwoCtor

mutual
inductive MR : Type where
  | mk : MS → MR
inductive MS : Type where
  | mk : MR → MS
end
