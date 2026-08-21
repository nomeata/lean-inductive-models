/- A β-redex which reveals an infinitary recursive field.

   The kernel sees `Hidden.branch`'s field as the ordinary positive shape
   `N → Hidden N.z`. Lean's source exporter normalizes the displayed redex, so
   the adjacent raw fixture pins the unreduced, kernel-accepted constructor,
   recursor type and recursor rule. The public interface must retain that raw
   spelling while the carve arm's private erasure exposes the binder.

   This is not a nested inductive: after head normalization the recursive
   occurrence is headed by `Hidden` itself. A foreign head such as
   `List (Hidden N.z)` is marked `numNested > 0` by Lean and is routed through
   the nested pass before the simple pass.
-/
prelude

universe u

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

--#export Eq N Hidden

inductive Hidden : N → Type where
  | leaf : Hidden N.z
  | branch (n : N) : ((fun _ : N => N → Hidden n) N.z) → Hidden (N.s n)
