/-
# The nested recursors, **made to compute**

`nested_shapes.lean` measures the declaration side of nesting and
`nested_roundtrip.lean` measures why the auxiliary encoding does not extend to
it. Neither of them ever applies a nested recursor, so neither would notice a
treatment that installed `Tree.rec` and `Tree.rec_1` with the right *types* and
rules that never fire. This file is that gap closed, and it is written the way
`mutual_iota_reduction.lean` is: every claim is a theorem proved by `rfl`, so
Lean's kernel checks it at export time and replay has to reduce the same redex
or reject the file.

# `Tree.rec_1` is the point

A nested `Tree` exports **two** recursors. `Tree.rec` is ordinary — it
eliminates `Tree` and ι-reduces on `Tree.leaf` and `Tree.node`. `Tree.rec_1`
eliminates **`List Tree`** and ι-reduces on **`List.nil` and `List.cons`**: a
recursor for one declaration computing on another declaration's constructors,
which is the unusual thing about nesting and the thing no encoding produces.
Both are stated below, at *variable* motives, minors and majors — the rules are
about a bound `a`, not about a closed term, and a closed term would reduce one
constructor at a time whatever the rule said.

The two cross-references are stated too:

* `Tree.rec`'s rule for `Tree.node` calls **`Tree.rec_1`** on the nested field,
  which is the induction hypothesis Lean 3's construction does not have;
* `Tree.rec_1`'s rule for `List.cons` calls **both** — `Tree.rec` on the head
  and `Tree.rec_1` on the tail.

A treatment that got the minor telescope right and the recursive call wrong
passes a type comparison and fails here.

# Two containers, not one container twice

`nested_shapes.lean`'s depth-2 case is `DTree.node : List (List DTree) → DTree`
— the *same* container at two depths. That is not the shape the real target
has: `Lean.Syntax`'s `numNested = 2` comes from `Array Syntax`, where `Array`
is a structure whose field is a `List`, so the two specialised copies are
copies of **different** containers. A treatment keyed on the container's name,
or one that memoises a single "the container" per declaration, passes `DTree`
and fails `Syntax`.

`BTree.node : Box BTree → BTree` is that shape at the smallest size that has
it: `Box` is a one-field structure over `List`, so `Box BTree` is one copy and
the `List BTree` inside `Box.mk` is a second copy of a *different* container.
Its three recursors' four rules are stated below.

`Box` is a `structure` for the same reason `Array` is one — so that the copy
sits behind a projection and a definitional η rule, and not only behind a
constructor.

# Why the motives land in `Type` and not in `Prop`

A `Prop`-valued motive would let proof irrelevance close the
equations without reducing anything, and every rule below would hold whether or
not it fired. `m1 : Tree → Type` and a payload of `N` is the cheapest motive
that cannot be collapsed that way.

`Nat` is avoided throughout, for the reason `infinitary_branching.lean` gives.
-/
prelude

--#export Eq N List Box Tree BTree PT
--#export treeIotaLeaf treeIotaNode treeIota1Nil treeIota1Cons
--#export btreeIotaLeaf btreeIotaTag btreeIotaNode btreeIota1Mk btreeIota2Nil btreeIota2Cons
--#export ptIotaLeaf ptIotaNode ptIota1Nil ptIota1Cons
--#export treeSize listOfN

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u

/-- Lean's own, restated: the file has no imports. -/
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

/-- The payload, so that a motive can land in `Type` without `Nat`. -/
inductive N : Type where
  | z : N
  | s : N → N

/-- The recursive container. -/
inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

/-- A **second, different** container, over the first. `Array` has this shape:
    a structure whose one field is a list. -/
structure Box (α : Type) : Type where
  unbox : List α

/-- Depth 1, one container. -/
inductive Tree : Type where
  | leaf : Tree
  | node : List Tree → Tree

/-- Depth 2, and the two copies are of **different** containers.

    `tag : List N → BTree` is the third constructor for the reason
    `Lean.Syntax.ident` exists: it carries a `List` at a type that has nothing
    to do with `BTree`, so a treatment that specialised *every* container
    application — rather than only the ones that mention the type being
    declared — would copy `List N` too and get a block with a member Lean does
    not have. `numNested` stays 2. -/
inductive BTree : Type where
  | leaf : BTree
  | tag : List N → BTree
  | node : Box BTree → BTree

/-- A nested declaration with **parameters of its own**.

    `Tree` and `BTree` have none, and a treatment that dropped the block's
    parameter telescope on the floor is the identity on both of them: the
    specialised copy of `List (PT α)` has to be declared as `∀ α, Type` and
    every reference to it inside the block has to be `copy α`, not `copy`.
    Restoring it has to put the parameter back. This is the fixture where those
    two are not the identity. -/
inductive PT (α : Type) : Type where
  | leaf : α → PT α
  | node : List (PT α) → PT α

/-- The container used un-nested, so the real `List` keeps its own pair. -/
def listOfN : List N := List.cons N.z List.nil

/-- A use of the nested recursor at a closed motive, so the file measures the
    evidence axis and not only the acceptance axis. -/
noncomputable def treeSize : Tree → N :=
  @Tree.rec (fun _ => N) (fun _ => N)
    N.z
    (fun _ ih => N.s ih)
    N.z
    (fun _ _ ih1 ih2 => N.s (N.s ih1))

section Tree

variable (m1 : Tree → Type) (m2 : List Tree → Type)
variable (lf : m1 Tree.leaf)
variable (nd : ∀ a : List Tree, m2 a → m1 (Tree.node a))
variable (nl : m2 (@List.nil Tree))
variable (cs : ∀ (a : Tree) (b : List Tree), m1 a → m2 b → m2 (@List.cons Tree a b))

theorem treeIotaLeaf : Eq (@Tree.rec m1 m2 lf nd nl cs Tree.leaf) lf :=
  Eq.refl _

theorem treeIotaNode (a : List Tree) :
    Eq (@Tree.rec m1 m2 lf nd nl cs (Tree.node a))
       (nd a (@Tree.rec_1 m1 m2 lf nd nl cs a)) :=
  Eq.refl _

theorem treeIota1Nil : Eq (@Tree.rec_1 m1 m2 lf nd nl cs (@List.nil Tree)) nl :=
  Eq.refl _

theorem treeIota1Cons (a : Tree) (b : List Tree) :
    Eq (@Tree.rec_1 m1 m2 lf nd nl cs (@List.cons Tree a b))
       (cs a b (@Tree.rec m1 m2 lf nd nl cs a) (@Tree.rec_1 m1 m2 lf nd nl cs b)) :=
  Eq.refl _

end Tree

section BTree

variable (p1 : BTree → Type) (p2 : Box BTree → Type) (p3 : List BTree → Type)
variable (blf : p1 BTree.leaf)
variable (btg : ∀ a : List N, p1 (BTree.tag a))
variable (bnd : ∀ a : Box BTree, p2 a → p1 (BTree.node a))
variable (bmk : ∀ a : List BTree, p3 a → p2 (@Box.mk BTree a))
variable (bnl : p3 (@List.nil BTree))
variable (bcs : ∀ (a : BTree) (b : List BTree), p1 a → p3 b → p3 (@List.cons BTree a b))

theorem btreeIotaLeaf : Eq (@BTree.rec p1 p2 p3 blf btg bnd bmk bnl bcs BTree.leaf) blf :=
  Eq.refl _

/-- The un-nested `List N` field gets **no** induction hypothesis, which is the
    other half of "only the containers that mention `BTree` are copied". -/
theorem btreeIotaTag (a : List N) :
    Eq (@BTree.rec p1 p2 p3 blf btg bnd bmk bnl bcs (BTree.tag a)) (btg a) :=
  Eq.refl _

theorem btreeIotaNode (a : Box BTree) :
    Eq (@BTree.rec p1 p2 p3 blf btg bnd bmk bnl bcs (BTree.node a))
       (bnd a (@BTree.rec_1 p1 p2 p3 blf btg bnd bmk bnl bcs a)) :=
  Eq.refl _

theorem btreeIota1Mk (a : List BTree) :
    Eq (@BTree.rec_1 p1 p2 p3 blf btg bnd bmk bnl bcs (@Box.mk BTree a))
       (bmk a (@BTree.rec_2 p1 p2 p3 blf btg bnd bmk bnl bcs a)) :=
  Eq.refl _

theorem btreeIota2Nil : Eq (@BTree.rec_2 p1 p2 p3 blf btg bnd bmk bnl bcs (@List.nil BTree)) bnl :=
  Eq.refl _

theorem btreeIota2Cons (a : BTree) (b : List BTree) :
    Eq (@BTree.rec_2 p1 p2 p3 blf btg bnd bmk bnl bcs (@List.cons BTree a b))
       (bcs a b (@BTree.rec p1 p2 p3 blf btg bnd bmk bnl bcs a)
                (@BTree.rec_2 p1 p2 p3 blf btg bnd bmk bnl bcs b)) :=
  Eq.refl _

end BTree

section PT

variable (α : Type)
variable (q1 : PT α → Type) (q2 : List (PT α) → Type)
variable (qlf : ∀ a : α, q1 (PT.leaf a))
variable (qnd : ∀ a : List (PT α), q2 a → q1 (PT.node a))
variable (qnl : q2 (@List.nil (PT α)))
variable (qcs : ∀ (a : PT α) (b : List (PT α)), q1 a → q2 b → q2 (@List.cons (PT α) a b))

theorem ptIotaLeaf (a : α) :
    Eq (@PT.rec α q1 q2 qlf qnd qnl qcs (PT.leaf a)) (qlf a) :=
  Eq.refl _

theorem ptIotaNode (a : List (PT α)) :
    Eq (@PT.rec α q1 q2 qlf qnd qnl qcs (PT.node a))
       (qnd a (@PT.rec_1 α q1 q2 qlf qnd qnl qcs a)) :=
  Eq.refl _

theorem ptIota1Nil : Eq (@PT.rec_1 α q1 q2 qlf qnd qnl qcs (@List.nil (PT α))) qnl :=
  Eq.refl _

theorem ptIota1Cons (a : PT α) (b : List (PT α)) :
    Eq (@PT.rec_1 α q1 q2 qlf qnd qnl qcs (@List.cons (PT α) a b))
       (qcs a b (@PT.rec α q1 q2 qlf qnd qnl qcs a) (@PT.rec_1 α q1 q2 qlf qnd qnl qcs b)) :=
  Eq.refl _

end PT
