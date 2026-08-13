/- **An infinitary W child behind a transparent former alias.**

   Lean's recursive-argument check reduces `As AliasW` to `AliasW`, so this is
   a plain infinitary inductive, not a nested one. Model generation must use
   definitional equality only to recognize that fact: the public model
   constructor, recursor and iota theorem retain the literal `As` application,
   which the structural checker compares without unfolding.
-/
prelude

universe u

--#export Eq N As AliasW

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

def As (α : Sort u) : Sort u := α

inductive AliasW : Type where
  | leaf : AliasW
  | lim : (N → As AliasW) → AliasW
