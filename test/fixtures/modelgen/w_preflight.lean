/- **Arm W's two residual preflight questions.**

   `AliasW.lim` is an infinitary recursive field whose result is definitionally,
   but not syntactically, the owner: `As AliasW`. It is not a nested inductive
   occurrence — `As` is a transparent definition, not an inductive container —
   and the kernel accepts it by reducing `As`. This is the smallest candidate
   for the old "nested rather than infinitary" guard.

   `OpaqueW.lim` has a genuinely atomic binder type at `Sort (imax u v)`.
   Recursive Π boxing can expose and box every binder in a function type, but
   there is no structure beneath `Atom α β` to recurse through: pairing an
   atomic value with a non-`Prop` pad still leaves the atomic `imax` in its
   level. This pins the checked boundary without changing the level normalizer
   or adding a basis primitive.
-/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

--#export Eq N As Atom AliasW OpaqueW

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

def As (α : Sort u) : Sort u := α

axiom Atom (α : Sort u) (β : Sort v) : Sort (imax u v)

inductive AliasW : Type where
  | leaf : AliasW
  | lim : (N → As AliasW) → AliasW

inductive OpaqueW (α : Sort u) (β : Sort v) : Type (max u v) where
  | leaf : OpaqueW α β
  | lim : (Atom α β → OpaqueW α β) → OpaqueW α β
