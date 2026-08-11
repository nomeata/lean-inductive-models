/-
# Nested inductives, on the axes they can be degenerate on

Mini declines a nested inductive at the parser, exit 2, and this file is the
before-picture — the way `mutual_*.lean`'s decline pins were, before the mutual
arc moved them. `nested_roundtrip.lean` is the measurement of *why* the mutual
encoding does not extend here; this one measures the declaration side.

Four declarations, chosen so that no single property is shared by all of them.
The last three rounds of this thread each lost a mutation to "the only fixture
exercising this had a degenerate shape", so the axes are separated on purpose:

| declaration | nesting depth | container parameterised | specialised copy recursive | container also used un-nested |
| --- | --- | --- | --- | --- |
| `Tree` | 1 | `List α` | **yes** (`List` is recursive) | yes, `listOfN` |
| `PTree` | 1 | `Pair α` | **no** (`Pair` is not recursive) | yes, `pairOfN` |
| `DTree` | **2** (`List (List DTree)`) | `List α` | yes | yes |
| `BTree` | 1 | `Pair α` at **two positions** | no | yes |

* **Depth.** `DTree.node : List (List DTree) → DTree` needs *two* auxiliary
  copies — `List` at `DTree` and `List` at that copy — so a compiler that
  specialises one level and stops is wrong here and right on `Tree`.
* **A non-recursive container.** `Pair`'s specialised copy has no recursive
  field of its own; it is in the block only because it mentions `PTree`. A
  block member with no self-recursion is the shape `mutual_one_recursive.lean`
  covers for mutual, and it is reachable here without writing a `mutual`.
* **The container used un-nested in the same file.** `listOfN : List N` and
  `pairOfN : Pair N` exist so that the *real* `List` and `Pair` have their own
  scheduled instantiations beside the nested ones. A treatment that quietly
  replaced `List` by its specialised copy would break these and nothing else.
* **Two nested positions in one constructor** (`BTree.node : Pair BTree →
  Pair BTree → BTree`) so that "one specialised copy per container" and "one
  per occurrence" are different answers.

`Nat` is avoided throughout: `N` is the same inductive without the literal
machinery, for the reason `infinitary_branching.lean` gives.

No constructor has a function-typed recursive argument, and nothing here is
indexed — which is itself a measurement, recorded in `mini/tests/mutual.rs`:
the specialised block of an unindexed nested declaration is an unindexed mutual
block, so `mutual_aux`'s index scope line is **not** what nesting is waiting on.
-/
prelude

--#export Eq List Pair N Tree PTree DTree BTree
--#export treeTy treeNode ptreeTy ptreeNode dtreeTy dtreeNode btreeTy btreeNode
--#export listOfN pairOfN

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

/-- Lean's own, restated: the file has no imports.

    **It is here so that the four declarations reach `mini::nested_ev`.** The
    nested model's two round trips are equations, and that module will not mint
    an `Eq` the export never wrote — so without this every declaration below
    declined as `nested model without Eq` before any of the axes the file exists
    to separate was reached. Nothing else in the file uses it. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

/-- The recursive container. -/
inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

/-- The non-recursive container. -/
inductive Pair (α : Type) : Type where
  | mk : α → α → Pair α

/-- A payload type, so that the containers are used un-nested as well. -/
inductive N : Type where
  | z : N
  | s : N → N

/-- Depth 1, recursive container. -/
inductive Tree : Type where
  | leaf : Tree
  | node : List Tree → Tree

/-- Depth 1, **non-recursive** container: the specialised copy of `Pair` has no
    recursive field of its own. -/
inductive PTree : Type where
  | leaf : PTree
  | node : Pair PTree → PTree

/-- Depth **2**: `List` at `DTree`, and `List` at that copy. -/
inductive DTree : Type where
  | leaf : DTree
  | node : List (List DTree) → DTree

/-- One container, **two** nested positions in one constructor. -/
inductive BTree : Type where
  | leaf : BTree
  | node : Pair BTree → Pair BTree → BTree

def treeTy : Type := Tree
def treeNode (l : List Tree) : Tree := Tree.node l
def ptreeTy : Type := PTree
def ptreeNode (p : Pair PTree) : PTree := PTree.node p
def dtreeTy : Type := DTree
def dtreeNode (l : List (List DTree)) : DTree := DTree.node l
def btreeTy : Type := BTree
def btreeNode (p q : Pair BTree) : BTree := BTree.node p q

/-- The containers, used un-nested, so the real ones have their own pairs. -/
def listOfN : List N := List.cons N.z List.nil
def pairOfN : Pair N := Pair.mk N.z (N.s N.z)
