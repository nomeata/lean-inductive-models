/- **The W arm** (`--prim-models`), `MODELGEN.md` §8.16 — the shapes the tuple
   tower cannot express and the tagged W construction can.

   `Wt` is `scripts/inductive-basis/WEmitted.lean`'s target, transcribed: six
   constructors chosen so that every shape the emitted scheme has to handle
   appears exactly once.

   * `leaf` — data, **no** children. The branch tower is empty at every index.
   * `one` — **no** data, one plain child. The data tower is the bare unit.
   * `two` — data **and two** plain children, which is where a dispatch that is
     right differs from one with its arms swapped.
   * `mix` — a plain child **and** an infinitary one **in the same
     constructor**, so the two towers are at different depths in one cascade.
   * `gap` — **data on both sides of a child**: the data tower and the branch
     tower index *different* subsequences of one telescope, and a generator
     that built the data from "the fields before the first recursive one"
     passes every other arm here.
   * `alt` — `leaf`'s shape at another tag. Two constructors of the same shape
     sharing a tag is **not** a type error, so this is the one mutation with no
     type error behind it, and the ι rule is what catches it.

   The other three targets are the parts `Wt` is monomorphic about:

   * `Tree` — a **parameter** and a **level parameter**, with the same
     branching. The towers are built at a parameter scope and the carrier is
     `Type u` for a variable `u`, which is what the terminating unit at exactly
     `Sort w` exists for.
   * `Br` — an infinitary child whose binder type is a **parameter** rather
     than a ground type, so the branch tower's own universe is variable too.
   * `Dep` — a non-recursive field whose type **depends on an earlier one**,
     beside a branching pair: the data tower is a dependent Σ-chain and this is
     what says so.

   **The last three are the untagged instantiation** (`MODELGEN.md` §8.16.6):
   the same core at `K := A` and `tg := id`, where the branch type sees the
   whole label and a child's binders may therefore mention the constructor's
   own non-recursive fields. `Modelgen.tagFactored` is false for each of them
   and `Modelgen.labelFactored` is true, which is the two-column split — these
   three model at `[propext, Classical.choice, Quot.sound]` where every target
   above stays at `[propext, Quot.sound]`.

   * `Bad` — one label-dependent child (`PFam k → Bad`) beside a plain one, and
     a base constructor. It was this file's decline until the untagged arm
     landed.
   * `Wty` — `WType` itself, which is what the corpus actually declines: a
     **parameter family** `β : α → Type u` at a level parameter, so the branch
     tower's own universe is variable and the label's data is a `α` rather than
     a ground type.
   * `Utd` — every remaining hazard at once. `mk` has **two** children whose
     binders read **different** fields of the same label, so the branch-index
     cascade and the data projections are exercised together and a dispatch
     that reads branch 1's tower out of field 0 is not the same term. `gap` has
     data **on both sides** of a label-dependent child, so the projection the
     binder needs is not at depth 1. `nil` is the base constructor.

   The boundary is now one field further out and `Utd` is not it: what neither
   instantiation reaches is a child whose binders mention an earlier
   **recursive** field, since the label carries no children for `Tel` to read
   one from. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive P : Type where
  | one : P
  | two : P

inductive Q : Type where
  | a : Q
  | b : Q
  | c : Q

/-- Written with `P.rec` rather than a `match`: the equation compiler wants
`PProd`, and a `prelude` fixture has none. -/
def PFam (k : P) : Type := @P.rec (fun _ => Type) P Q k

inductive Wt : Type where
  | leaf : P → Wt
  | one : Wt → Wt
  | two : Q → Wt → Wt → Wt
  | mix : Wt → (P → Wt) → Wt
  | gap : P → Wt → Q → Wt → Wt
  | alt : P → Wt

inductive Tree (α : Type u) : Type u where
  | tip : α → Tree α
  | bin : Tree α → Tree α → Tree α

inductive Br (α : Type u) : Type u where
  | z : Br α
  | lim : (α → Br α) → Br α

inductive Dep : Type where
  | nil : Dep
  | mk : (k : P) → PFam k → Dep → Dep → Dep

inductive Bad : Type where
  | tip : Bad
  | lim : (k : P) → (PFam k → Bad) → Bad → Bad

inductive Wty (α : Type u) (β : α → Type u) : Type u where
  | mk : (a : α) → (β a → Wty α β) → Wty α β

inductive Utd : Type where
  | nil : Utd
  | mk : (k : P) → (j : P) → (PFam k → Utd) → (PFam j → Utd) → Utd
  | gap : (k : P) → (PFam k → Utd) → Q → Utd → Utd
