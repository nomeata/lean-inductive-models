/- **Branching recursion at a positive universe with no syntactic predecessor.**

   `max 1 u` is never zero, so Lean accepts ordinary large elimination for
   `WMax`.  It is not definitionally a successor level, however: there is no
   level expression `v` for which `v + 1` normalizes to `max 1 u`.  The two
   recursive fields force the simple generator past its linear tuple route and
   make this the smallest probe of the tree arm at such a sort. The W core
   lands at `Sort (max 1 w u)` and is run at the owner's own sort, so the
   carrier is the core itself; it used to be a `Type` core lifted into
   `Sort (max 1 u)` by a `PSigma'`, which `tree_sort_level.lean` showed cannot
   hold a field at `Sort u`.
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
