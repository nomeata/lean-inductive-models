/- **The nested declaration carries indices.** Lean supports it: `ITree.rec`
   comes back with `numIndices = 1` and a motive `(a : N) → ITree a → Sort u`,
   while the mimic's motive `List (ITree N.z) → Sort u` has none — so a block
   recursor here has a *different* index arity per member.

   `I2` carries **two** indices at distinct values, so a treatment that dropped
   an index, or applied the two in the wrong order, is visible; one index
   cannot distinguish either.

   `I3` is here because `ITree` and `I2` between them never make an index
   *vary*: every index vector in the model is read off a type in hand, and a
   treatment that read the major's where a field's belongs is invisible until
   the two differ. `I3.node : I3 N.z → List (I3 (N.s N.z)) → I3 (N.s (N.s N.z))`
   has three: the recursive field's, the occurrence's, and the result's.

   A nested occurrence whose container parameter mentions a **constructor
   field** — `node : (n : N) → List (ITree n) → ITree (N.s n)` — is *not* in
   this file, because Lean rejects it too: "nested inductive datatypes
   parameters cannot contain local variables".

   The same kernel gate covers the apparent residual W-label case. With an
   indexed `Box (α : Type) : α → Type`, the smallest candidate
   `U.node : (x : U) → Box U x → U` is rejected with that exact message: the
   later field cannot observe the earlier child through a dependent container
   while `U` is being declared. There is consequently no raw export of that
   source shape for the simple W arm; hand-specialising it produces a mutual
   block, which takes the mutual route instead. -/
prelude

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

--#export Eq N List ITree I2 I3

inductive ITree : N → Type where
  | leaf : ITree N.z
  | node : List (ITree N.z) → ITree (N.s N.z)

inductive I2 : N → N → Type where
  | leaf : I2 N.z (N.s N.z)
  | node : List (I2 (N.s N.z) N.z) → I2 N.z (N.s N.z)

inductive I3 : N → Type where
  | tip : I3 N.z
  | node : I3 N.z → List (I3 (N.s N.z)) → I3 (N.s (N.s N.z))
