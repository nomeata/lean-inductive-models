prelude

/-!
An indexed recursive proposition with dependent proof fields.

All three constructor fields are kernel-projectable.  The second field depends
on the first, while the third forces the graph/strong-recursion implementation
rather than the nonrecursive direct structure route.
-/

universe u

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

@[reducible] def optParam (α : Sort u) (_default : α) : Sort u := α

inductive Ix : Type where
  | here
  | elsewhere

--#export Eq optParam Ix PropRecIdx

inductive PropRecIdx (a : Prop) (b : a → Prop) (defaultB : (ha : a) → b ha) :
    Ix → Prop where
  | mk (ha : a)
      (hb : Eq.rec (motive := fun _ _ => Prop) (b ha) (Eq.refl (b ha)) := defaultB ha)
      (tail : PropRecIdx a b defaultB Ix.here) :
      PropRecIdx a b defaultB Ix.here
