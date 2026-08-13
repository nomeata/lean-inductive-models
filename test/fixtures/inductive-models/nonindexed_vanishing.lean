/- A non-indexed specialization-shaped field whose owner mention vanishes.

   `Dead.step` has one real recursive field.  Its second field is written as
   `(fun _ : Dead => N) child`: the domain mentions `Dead`, but β reduction
   discards that binder annotation and leaves the non-recursive type `N`.  The
   simple Type route must therefore give the constructor one spine predecessor,
   not two.

   Lean's ordinary source export normalizes this spelling to `N`.  The adjacent
   raw fixture pins the kernel-accepted unreduced expression in the constructor,
   recursor type, and recursor rule so this exact exported-expression boundary
   remains covered.
-/
prelude

universe u

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

--#export Eq N Dead

inductive Dead : Type where
  | base : Dead
  | step (child : Dead) (payload : (fun _ : Dead => N) child) : Dead
