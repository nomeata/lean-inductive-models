/-
# **Two packed positions in one constructor**, at a *mimic*'s own rule

`nested_iota.lean` carries every nesting shape that matters for `Lean.Syntax`
except one. This file is that one, at the smallest size that has it.

`DTree.node : List (List DTree) → DTree` specialises to two mimics of the **same**
container at two depths,

```text
M₀ ≅ List (List DTree)      M₀.cons : M₁ → M₀ → M₀
M₁ ≅ List DTree             M₁.cons : D  → M₁ → M₁
```

and `M₀.cons` is the point: **both** of its fields sit at a mimic, so the round
trip moves two arguments of one constructor application at once, and so does the
ι rule of `DTree.rec_1` on `List.cons`. Two positions is the first arity that can
distinguish a fold from a single transport.

**This file is not the only such witness, and the difference between the two is
the point of keeping both.** `nested_shapes.lean`'s
`BTree.node : Pair BTree → Pair BTree → BTree` has two packed positions in a
**root** constructor, and a root rule and a mimic rule use different transport
paths: the root folds over `pack` at each position, while a mimic transports
the whole constructor application once and folds *inside* the proof. Mutating
the fold to stop after the first position kills
`nested_deep/DTree`, `nested_shapes/DTree` **and** `nested_shapes/BTree`, and
those are one arm and the other.

This file was written when `nested_shapes.lean` declared no `Eq` and model
generation declined all four of its declarations before reaching the
interesting part, so at the time it really was the only occupant. It stopped
being the only one when that fixture grew an `Eq`, and this paragraph is that
correction rather than an appendix to it.

`Eq` is declared here for the reason `nested_shapes.lean` does not have it: the
round trips are equations, and the generator refuses to fabricate an `Eq` the
export never wrote. That refusal is what `nested_shapes` measures; this file
measures what happens past it.

`Nat` is avoided for the reason `infinitary_branching.lean` gives.
-/
prelude

--#export Eq N List DTree dtreeOfN

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

/-- Lean's own, restated: the file has no imports. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

/-- The payload, so a use site can exist without `Nat`. -/
inductive N : Type where
  | z : N
  | s : N → N

/-- The container, used at two depths. -/
inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

/-- `numNested = 2`, **one** container twice. The inner copy's `cons` is the
    constructor with two packed positions. -/
inductive DTree : Type where
  | leaf : N → DTree
  | node : List (List DTree) → DTree

/-- A closed inhabitant, so the file carries a pair and is not measuring an
    empty ledger. -/
def dtreeOfN : DTree := DTree.node (List.cons (List.cons (DTree.leaf N.z) List.nil) List.nil)
