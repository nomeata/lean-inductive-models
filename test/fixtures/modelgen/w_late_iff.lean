/- A W-arm target before the exact shared `Iff` block and `propext`.

   The export roots are deliberately ordered. `LateW` itself mentions none of
   the shared logical interface. Its model first waits for the later `Eq`
   basis; when that arrives, the W splice must notice that the file's own
   exact `Iff`, `Iff.intro`, `Iff.rec`, and `propext` are still coming and keep
   the whole job queued until all four have been replayed.

   The quotient and choice-side shared names are absent on purpose, so the W
   fragment may splice them. This isolates the Iff/propext readiness seam. -/

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
