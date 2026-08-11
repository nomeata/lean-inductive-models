/- Focused arm-W storage cases at nested `imax` levels.

   `WData` branches, so it reaches arm W rather than the linear tuple tower;
   its leaf stores `((α → β) → β)`, whose inner function level survives a
   shallow codomain box.

   `WBind` is infinitary. Its recursive child's binder has the same nested
   function type, so the branch telescope must box and later unbox the binder
   before applying the original child. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive WData (α : Sort u) (β : Sort v) : Type (max u v) where
  | leaf : ((α → β) → β) → WData α β
  | fork : WData α β → WData α β → WData α β

inductive WBind (α : Sort u) (β : Sort v) : Type (max u v) where
  | leaf : WBind α β
  | lim : (((α → β) → β) → WBind α β) → WBind α β

--#export Eq WData WBind
