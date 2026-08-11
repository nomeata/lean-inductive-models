/- **The eliminating universe is an axis of its own.**

   Mode A leaves a recursor's motive universe standing and mode B folds it into
   the name; on a file where every recursor is used at one motive universe — or
   at none — the two modes emit the same number of declarations and the axis is
   the identity. `N.rec` here is used at **three** distinct motive universes, so
   mode B emits `N.rec._elim.0`, `N.rec._elim.1` and `N.rec._elim.2` where
   mode A emits one `N.rec`. Two would not distinguish an ordering. -/
prelude

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

--#export atElim0 atElim1 atElim2

def atElim0 (n : N) : Eq N.z N.z :=
  N.rec.{0} (motive := fun _ => Eq N.z N.z) (Eq.refl N.z) (fun _ ih => ih) n

noncomputable def atElim1 (n : N) : N :=
  N.rec.{1} (motive := fun _ => N) N.z (fun _ ih => ih) n

noncomputable def atElim2 (n : N) : Type :=
  N.rec.{2} (motive := fun _ => Type) N (fun _ ih => ih) n
