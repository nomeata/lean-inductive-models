/- **Branching recursion at a positive universe with no syntactic predecessor.**

   `max 1 u` is never zero, so Lean accepts ordinary large elimination for
   `WMax`.  It is not definitionally a successor level, however: there is no
   level expression `v` for which `v + 1` normalizes to `max 1 u`.  The two
   recursive fields force the simple generator past its linear tuple route and
   make this the smallest probe of the tree arm's constrained exact-sort lift:
   a low W core paired by `PSigma'` with a canonical derived lift of `True`.
-/
prelude

universe u

--#export Eq WMax

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive WMax : Sort (max 1 u) where
  | leaf : WMax
  | node : WMax → WMax → WMax
