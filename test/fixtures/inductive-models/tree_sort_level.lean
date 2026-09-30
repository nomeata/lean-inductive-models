/- **Owners at a never-`Prop` sort with no syntactic predecessor, holding
   fields at their own parameter levels.**

   `Sort (max 1 u)` is never `Prop`, so Lean admits large elimination, but
   no level `ℓ` has `ℓ + 1` normalizing to it. A field at `Sort u` fits under
   it at every `u` — at `u = 0` it is a proposition in a `Type`, at `u = 5`
   it is at the owner's own sort — and the kernel accepts every declaration
   below.

   The tree arm (README entry 4) is the route this pins. A W core at
   `Type ℓ` has no `ℓ` for a carrier at `Sort (max 1 u)` holding `Sort u`
   data: `ℓ + 1` would have to be `1` at `u = 0` and `u` at `u = 5`. A core
   that lifted a `Type` tree into `Sort (max 1 u)` stopped every owner below
   with an internal error, and the core is now at `Sort (max 1 w u)` and run
   at the owner's own sort (`w_core.lean`). The owners cover the level
   shapes around it — `Sort (max 1 u)`, `Sort (max 1 u v)`,
   `Sort (max (u+1) v)` — with fields at `Sort u`, `Sort v`, `Prop`, an
   `imax` level (boxed) and a type field at `Sort u` itself, in the data
   tower and as a recursive field's binder, with one constructor and with
   several.

   The sibling routes are here on the same levels: the tuple tower
   (entry 9, linear recursion), the empty arm (entry 8) and the direct
   route (entry 10).

   `prelude`, so that Lean mints no `below`/`brecOn` for them: Lean 4.29.1's
   `TreeBindImax.below` is itself kernel-rejected (its motive's universe
   misses the `imax` of the binder), and the model does not need it. -/
prelude

universe u v

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | zero : N
  | succ : N → N

/-! ### The tree arm -/

/-- A field at `Sort u` in the data tower. -/
inductive TreeU (α : Sort u) : Sort (max 1 u) where
  | leaf : α → TreeU α
  | node : TreeU α → TreeU α → TreeU α

/-- Fields at `Sort u` and `Sort v`. -/
inductive TreeUV (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  | leaf : α → β → TreeUV α β
  | node : TreeUV α β → TreeUV α β → TreeUV α β

/-- A successor component and a bare one: `Sort u` and `Sort v` fields, and
a type field at `Sort (u+1)` itself. -/
inductive TreeSucc (α : Sort u) (β : Sort v) : Sort (max (u+1) v) where
  | leaf : α → β → TreeSucc α β
  | ty : Sort u → TreeSucc α β
  | node : TreeSucc α β → TreeSucc α β → TreeSucc α β

/-- A `Prop` field beside a `Sort u` one. -/
inductive TreeProp (p : Prop) (α : Sort u) : Sort (max 1 u) where
  | leaf : p → α → TreeProp p α
  | node : TreeProp p α → TreeProp p α → TreeProp p α

/-- An `imax` field, boxed, and a nested one. -/
inductive TreeImax (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  | fn : (α → β) → TreeImax α β
  | cont : ((α → β) → β) → TreeImax α β
  | node : TreeImax α β → TreeImax α β → TreeImax α β

/-- One constructor, infinitary, with a `Sort u` field: the projection
contract is owed. -/
inductive TreeOne (α : Sort u) : Sort (max 1 u) where
  | mk : α → (N → TreeOne α) → TreeOne α

/-- A recursive field under a binder at `Sort u`: the branch tower. -/
inductive TreeBind (α : Sort u) : Sort (max 1 u) where
  | leaf : TreeBind α
  | lim : (α → TreeBind α) → TreeBind α

/-- A recursive field under a boxed `imax` binder. -/
inductive TreeBindImax (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  | leaf : β → TreeBindImax α β
  | lim : ((α → β) → TreeBindImax α β) → TreeBindImax α β

/-! ### The tuple tower -/

inductive ListU (α : Sort u) : Sort (max 1 u) where
  | nil : ListU α
  | cons : α → ListU α → ListU α

inductive ListImax (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  | nil : ListImax α β
  | cons : (α → β) → ListImax α β → ListImax α β

inductive OptSucc (α : Sort u) (β : Sort v) : Sort (max (u+1) v) where
  | none : OptSucc α β
  | some : α → β → OptSucc α β
  | ty : Sort u → OptSucc α β

/-! ### The empty arm -/

inductive LoopU (α : Sort u) : Sort (max 1 u) where
  | mk : α → LoopU α → LoopU α

inductive LoopImax (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  | mk : (α → β) → LoopImax α β → LoopImax α β
  | two : α → LoopImax α β → LoopImax α β → LoopImax α β

/-! ### The direct route -/

structure PairU (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  fst : α
  snd : β

structure PairSucc (α : Sort u) (β : Sort v) : Sort (max (u+1) v) where
  ty : Sort u
  fst : α
  snd : β

structure FunImax (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  f : α → β

--#export Eq N TreeU TreeUV TreeSucc TreeProp TreeImax TreeOne TreeBind TreeBindImax ListU ListImax OptSucc LoopU LoopImax PairU PairSucc FunImax
