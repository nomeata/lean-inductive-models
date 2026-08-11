/- **A file that already spells the marker.**

   The naming scheme inserts a `_at` component followed by one `Name.num` per
   level, and the naming inversion works only when no input name already has
   one. Lean accepts `_at` as an identifier component — it mints
   such names itself for specialised code — so this is a **gap**: the pass
   refuses the whole file rather than emitting a name a consumer could not
   invert. -/
prelude

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

--#export wrapped foo._at.bar

def foo._at.bar : N := N.z

def wrapped (α : Sort u) : Sort u := α
