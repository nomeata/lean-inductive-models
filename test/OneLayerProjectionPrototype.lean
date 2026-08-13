import Lean

/-!
# One-layer public carriers: a projection prototype

This is deliberately separate from the generator.  It tests the proposed API
shape on the smallest relevant signature: one ordinary field and one
infinitary recursive field.

`M` stands for the current recursive model and remains private.  `P A` is the
one-layer carrier `F (M A)`.  The public constructor converts its recursive
`P A` inputs with `roll`; the recursive projection converts the stored `M A`
values back with `unroll`.

The important result is the *statement* of `children_node`: its right-hand
side is literally the recursive argument supplied to `node`, and the
elaborated proposition contains no `Eq.rec`.  Its proof only needs the
section law pointwise and therefore need not be definitional equality in a
future generated version.
-/

namespace OneLayerProjectionPrototype

universe u

private inductive M (A : Type u) : Type u where
  | node (label : A) (children : Nat → M A) : M A

/-- The signature functor for the prototype, instantiated at `X = M A`. -/
private structure Layer (A X : Type u) : Type u where
  label : A
  children : Nat → X

/-- Public carrier: exactly one source-constructor layer over the private model. -/
def P (A : Type u) : Type u := Layer A (M A)

private def roll {A : Type u} : P A → M A
  | ⟨label, children⟩ => .node label children

private def unroll {A : Type u} : M A → P A
  | .node label children => ⟨label, children⟩

private theorem unroll_roll {A : Type u} (x : P A) : unroll (roll x) = x := by
  cases x
  rfl

private theorem roll_unroll {A : Type u} (x : M A) : roll (unroll x) = x := by
  cases x
  rfl

private structure ModelEquiv (A B : Type u) where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ x, toFun (invFun x) = x

/-- The proposed internal equivalence between the public layer and current model. -/
private def modelEquiv (A : Type u) : ModelEquiv (P A) (M A) where
  toFun := roll
  invFun := unroll
  left_inv := unroll_roll
  right_inv := roll_unroll

/-- Public constructor: roll only the recursive fields. -/
def node {A : Type u} (label : A) (children : Nat → P A) : P A :=
  ⟨label, fun i => roll (children i)⟩

/-- An ordinary projection reads the one-layer representation directly. -/
def label {A : Type u} (x : P A) : A :=
  x.1

/-- A recursive projection unrolls each stored private recursive value. -/
def children {A : Type u} (x : P A) : Nat → P A :=
  fun i => unroll (x.2 i)

theorem label_node {A : Type u} (a : A) (xs : Nat → P A) :
    label (node a xs) = a := rfl

/-- The desired public projection rule, with the literal original RHS `xs`. -/
theorem children_node {A : Type u} (a : A) (xs : Nat → P A) :
    children (node a xs) = xs := by
  funext i
  exact unroll_roll (xs i)

/-! Assert against the elaborated declaration, not only its pretty source. -/

open Lean Elab Command in
elab "#assert_type_omits_eq_rec " declaration:ident : command => do
  let some info := (← getEnv).find? declaration.getId
    | throwError "unknown declaration {declaration.getId}"
  if info.type.getUsedConstants.contains ``Eq.rec then
    throwError "{declaration.getId}'s type contains Eq.rec"

#assert_type_omits_eq_rec OneLayerProjectionPrototype.children_node

/-!
The positivity premise is true for a genuine dependency.  Here `Family` is
opaque, so the later field's type really depends on the earlier recursive
value; Lean rejects the occurrence.  A reducible family which erases its
argument can of course be accepted, but then the dependency is definitionally
irrelevant and cannot force a transport in an iota proposition.
-/

axiom Family : {A : Type u} → A → Type u

/--
error: (kernel) arg #2 of 'OneLayerProjectionPrototype.DependsOnRecursive.mk' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
inductive DependsOnRecursive : Type u where
  | mk (child : DependsOnRecursive) (later : Family child) : DependsOnRecursive

def ErasedFamily {A : Type u} (_ : A) : Type := Unit

/-- Accepted only because reduction erases the apparent dependency. -/
inductive ReduciblyErasedDependency : Type u where
  | mk (child : ReduciblyErasedDependency)
      (later : ErasedFamily child) : ReduciblyErasedDependency

end OneLayerProjectionPrototype
