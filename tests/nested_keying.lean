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
* `UTree` — the file itself declares `UTree._model.self`, at a type that has
  nothing whatever to do with `UTree`. `iso` answers `NameTaken`, no entry is
  keyed, and `⟦UTree⟧` must **decline**, naming that shape.

The second is the whole point. A keying spelled as a name rule — take the
declaration's name, append `_model.self`, look it up — answers `⟦UTree⟧ = ⟦N⟧`
here, silently, and every counter in the file reads as if the model worked.
That is the `_auxCarrier` failure at one level up, and this file is the input
that tells the two implementations apart: under the table, `utreeTy` and
`utreeNode` wait on `ind-spec(UTree: nested model name taken)`; under the name
rule they certify, against a model nobody built.

`UTree._model.self := N` is deliberately a *type* and deliberately inhabited,
so that a wrong keying produces a well-formed store entry rather than a crash —
a distinguishing input that only distinguishes by failing to typecheck would
not be measuring the keying.

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

/-- Nested, and **not** modelled: the name its carrier would take is already
    spoken for, immediately below. -/
inductive UTree : Type where
  | uleaf : UTree
  | unode : List UTree → UTree

/-- The squatter. Nothing about `UTree`; a perfectly ordinary definition that
    happens to have the name the model would have minted. -/
def UTree._model.self : Type := N

def treeTy : Type := Tree
def treeNode (l : List Tree) : Tree := Tree.node l

def utreeTy : Type := UTree
def utreeNode (l : List UTree) : UTree := UTree.unode l
