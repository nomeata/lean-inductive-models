/-
# The keying, and the name that must not be trusted

`nested_shapes.lean` measures the declaration side of nesting and
`nested_iota.lean` the rules. This file measures the **join**: that `⟦Tree⟧` is
the generated model's carrier, and that it is that because a side table says so
and not because a name looked right.

Two nested declarations of the *same* shape stand side by side:

* `Tree` — nothing else in the file mentions the names its model wants, so
  `nested_ev::iso` builds one, `nested_splice::splice` puts it in the run and
  keys `⟦Tree⟧`, `⟦Tree.leaf⟧`, `⟦Tree.node⟧` to it. Its two `def`s certify.
* `UTree` — the file itself declares the legacy-looking name
  `UTree._model.self`, at a type that has nothing whatever to do with `UTree`.
  Exact declaration-local keying ignores it, and `UTree` must model normally.

The second is the whole point. A compatibility guard that still reserves the
old carrier spelling silently declines a valid model. The public type-former
model is now `UTree._model`, and the implementation block is rooted at
`UTree._model._impl.0`; this unrelated declaration must affect neither.

`UTree._model.self := N` is deliberately a *type* and deliberately inhabited,
so the test distinguishes exact-role keying from legacy suffix heuristics,
not merely well-formedness.

The declarations are otherwise as small as a nested inductive gets: one
container, depth one, no parameters. `nested_shapes.lean` and
`nested_iota.lean` carry the shape axes; this one carries the join, and it is
the fixture that is cheap enough to run in an inner loop.
-/
prelude

--#export Eq N List Tree UTree UTree._model.self
--#export treeTy treeNode utreeTy utreeNode

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

/-- Lean's own, restated: the file has no imports. The model's round trips and
    ι rules are equations, and `nested_ev::iso` declines a file that has no
    `Eq` to state them with. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

/-- The payload. -/
inductive N : Type where
  | z : N
  | s : N → N

/-- The container. -/
inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

/-- Nested, and modelled. -/
inductive Tree : Type where
  | leaf : Tree
  | node : List Tree → Tree

/-- Nested, and modelled despite the unrelated legacy-looking name below. -/
inductive UTree : Type where
  | uleaf : UTree
  | unode : List UTree → UTree

/-- The legacy squatter. Nothing about `UTree`; it is deliberately not one of
    the declaration-local contract names minted today. -/
def UTree._model.self : Type := N

def treeTy : Type := Tree
def treeNode (l : List Tree) : Tree := Tree.node l

def utreeTy : Type := UTree
def utreeNode (l : List UTree) : UTree := UTree.unode l
