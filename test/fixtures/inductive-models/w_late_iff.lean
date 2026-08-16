/- A W-arm target before the exact shared `Iff` block and `propext`.

   The raw export roots are deliberately ordered with `LateW` first, although
   it mentions none of the shared logical interface. `Eq`, `Iff` and `propext`
   below are Lean's own declarations exactly, so they are the declarations this
   tool would have written under those names and are installed before the
   stream is consumed: `LateW` models where it stands, nothing is spliced under
   a reserved name, and each of the three records is still emitted once, at its
   own position. An input whose `Iff` or `propext` is *not* Lean's keeps it,
   and then `LateW` declines on the Iff/propext readiness class instead.

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
  | intro (mp : a → b) (mpr : b → a) : Iff a b

axiom propext {a b : Prop} : Iff a b → Eq a b

--#export LateW Eq Iff propext
