/-
# One nested constructor layer with intrinsic projections

This is the smallest source declaration on which a nested model can expose
literal projection computation.  `NestedLayer` has one real member and one
specialised `List` mimic.  The payload depends on the ordinary key, while the
nested field is independent of later fields; the latter is the exact boundary
at which the existing `pack`/`unpack` round trips can justify a literal field
right-hand side.
-/
prelude

--#export Eq N List Payload NestedLayer

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

inductive Eq : {alpha : Sort u} -> alpha -> alpha -> Prop where
  | refl (a : alpha) : Eq a a

inductive N : Type where
  | z : N
  | s : N -> N

inductive List (alpha : Type) : Type where
  | nil : List alpha
  | cons : alpha -> List alpha -> List alpha

inductive Payload : N -> Type where
  | at (key : N) : Payload key

inductive NestedLayer : Type where
  | mk (key : N) (payload : Payload key) (children : List NestedLayer) : NestedLayer
