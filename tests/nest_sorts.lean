/- **Two shapes about the *sort* the block lands in.**

   * `PTree : Prop` nesting `PL PTree`, where `PL (α : Prop) : Prop`. A block
     that eliminates only into `Prop` has **no motive universe at all**:
     `PTree.rec` carries the declaration's own level parameters and nothing in
     front of them, and so does the container's `PL.rec`. Every level list this
     module writes for a recursor therefore has to be read off the recursor and
     not assumed, and before it was, this file made the tool raise
     `incorrect number of universe levels PL.rec` — an uncaught exception
     rather than a decline, which is the worse of the two failures.

     `Eq` is the atom that says the guard is not simply "the sort is `Prop`":
     `Eq` *is* `Prop`-valued and *does* support large elimination, so it has a
     motive universe. The distinction is read off `levelParams`.

   * `STree.{u} : Type u` nesting `PolyL STree` at `PolyL (α : Sort u) :
     Sort (max 1 u)` — a container polymorphic over `Sort` rather than `Type`,
     where `poly_nested.lean`'s containers are all at `Type`. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive PUnit : Sort u where
  | unit : PUnit

structure PProd (α : Sort u) (β : Sort v) where
  fst : α
  snd : β

inductive PL (α : Prop) : Prop where
  | nil : PL α
  | cons : α → PL α → PL α

inductive PolyL (α : Sort u) : Sort (max 1 u) where
  | nil : PolyL α
  | cons : α → PolyL α → PolyL α

--#export Eq PUnit PProd PL PolyL PTree STree

inductive PTree : Prop where
  | mk : PL PTree → PTree

inductive STree : Type u where
  | mk : PolyL STree → STree
