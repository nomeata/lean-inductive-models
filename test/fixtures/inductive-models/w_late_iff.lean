/- A W-arm target before the exact shared `Iff` block and `propext`.

   The raw export roots are deliberately ordered with `LateW` first, although
   it mentions none of the shared logical interface. Raw-order generation must
   decline rather than move the later exact `Eq`, `Iff`, and `propext` support
   before the owner island or splice over their reserved names.

   The quotient and choice-side shared names are absent on purpose, so the W
   fragment may splice them. This isolates the Iff/propext prerequisite class
   from quotient/choice support. -/

prelude

universe u

inductive LateW : Type where
  | leaf : LateW
  | fork : LateW → LateW → LateW

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive Iff (a b : Prop) : Prop where
  | intro : (a → b) → (b → a) → Iff a b

axiom propext {a b : Prop} : Iff a b → Eq a b

--#export LateW Eq Iff propext
