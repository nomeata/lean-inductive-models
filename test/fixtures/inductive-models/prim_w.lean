/- **The W arm of simple-model generation** — the shapes the tuple
   tower cannot express and the tagged W construction can.

   `Wt` has six constructors chosen so that every shape the emitted scheme has to handle
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

   **The last three are the untagged instantiation**:
   the same core at `K := A` and `tg := id`, where the branch type sees the
   whole label and a child's binders may therefore mention the constructor's
   own non-recursive fields. `InductiveModels.tagFactored` is false for each of them
   and `InductiveModels.labelFactored` is true, which is the two-column split — these
   three model at `[propext, Classical.choice, Quot.sound]` where every target
   above stays at `[propext, Quot.sound]`.

   * `Bad` — one label-dependent child (`PFam k → Bad`) beside a plain one, and
     a base constructor. It was this file's decline until the untagged arm
     landed.
   * `Wty` — the general W-type shape: a
     **parameter family** `β : α → Type u` at a level parameter, so the branch
     tower's own universe is variable and the label's data is a `α` rather than
     a ground type.
   * `Utd` — every remaining hazard at once. `mk` has **two** children whose
     binders read **different** fields of the same label, so the branch-index
     cascade and the data projections are exercised together and a dispatch
     that reads branch 1's tower out of field 0 is not the same term. `gap` has
     data **on both sides** of a label-dependent child, so the projection the
     binder needs is not at depth 1. `nil` is the base constructor.

   A constructor-local child whose binder type mentions an earlier recursive
   field is rejected by Lean's nested-inductive compilation before this route;
   `Utd` therefore covers the far edge of the kernel-accepted direct W shapes,
   rather than sitting beside an unimplemented W case. -/
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

/- The phase-two one-layer boundary: every declaration below is still one
   constructor, unindexed and unnested, but its constructor has more than one
   recursive occurrence.  Their four shapes keep the proof fold honest:
   direct/direct, direct/infinitary, infinitary/infinitary, and a dependent
   *ordinary* prefix before the recursive suffix.

   **They are also all uninhabited, and six of them are no longer arm W's.**
   Each is a single constructor with no base, so every constructor has a bare
   recursive field, and arm E — which reaches that whole shape class rather
   than its linear corner — models `Twin`, `Mixed`, `Prefix`, `Triple`, `Quad`
   and `Trine` by the lift of `⊥`, exactly and with no axiom.  `TwinInf` has no
   bare occurrence and stays on W.  The one-layer public-carrier claim these
   were written for survives the move: the adapter is chosen on the
   declaration's shape and not on the arm, `runOne` still requires the complete
   private certificate for `Triple`, `Quad` and `Trine`, and
   [`InductiveModels.oneLayerNaryCompatibility`] is still the construction that
   proves their ι rules at three and four fields — reinstating an arity cap in
   it is red at `Triple` today.  **These six therefore stay as they are**: they
   are now this file's arm-E-past-the-linear-corner column, and a base
   constructor would cost more than it bought, because
   [`InductiveModels.phase1DirectTypeOneLayerEligible`] asks for *exactly one*
   constructor and a second one would drop them off the one-layer route
   altogether.

   What the move did lose is narrower and is restored by `TripleInf`,
   `QuadInf` and `TrineInf` below: **the one-layer adapter over an arm-W
   private model past two recursive fields**.  (Arm W itself still runs at
   three and four — `prim_carve`'s `Sm3`, `infinitary`'s `GTree` and
   `nest_fam_arg`'s `Both` and `Key` are its multi-constructor occupants — but
   every one of those is out of the one-layer route's reach.) -/
inductive Twin : Type where
  | mk : Twin → Twin → Twin

inductive Mixed (P : Type) : Type where
  | mk : Mixed P → P → (P → Mixed P) → Mixed P

inductive TwinInf (P Q : Type) : Type where
  | mk : (P → Q → TwinInf P Q) → (Q → P → TwinInf P Q) → TwinInf P Q

inductive Prefix (α : Type u) (β : α → Type u) : Type u where
  | mk : (a : α) → β a → Prefix α β → Prefix α β → Prefix α β

/- Past the binary boundary.  `Triple` and `Quad` are three and four bare
   recursive fields; `Trine` is three of them mixed — an ordinary field, a
   direct occurrence, an infinitary one and a direct one — at a parameter.
   Nothing in the compatibility construction may count, so these are the
   arities beyond the reach of any fixed-arity lemma. -/
inductive Triple : Type where
  | mk : Triple → Triple → Triple → Triple

inductive Quad : Type where
  | mk : Quad → Quad → Quad → Quad → Quad

inductive Trine (α : Type) : Type where
  | mk : α → Trine α → (α → Trine α) → Trine α → Trine α

/- **Arm W past two recursive fields, under the one-layer adapter**, which is
   the one combination the six above stopped covering when they became arm E's.

   There is exactly one way to be in it, and these three are it.  The one-layer
   route asks for a single constructor
   ([`InductiveModels.phase1DirectTypeOneLayerEligible`]), and a single
   constructor with a **bare** recursive field is empty and arm E's
   ([`InductiveModels.bareRecSlotOf`], `Simple/Site.lean`'s `emptySlots`).  So a
   one-constructor arm W has to put *every* recursive occurrence under a binder
   — which is what `TwinInf` already is at two fields.  `TripleInf` and
   `QuadInf` are that shape at three and four; `TrineInf` puts an ordinary
   field in front of three of them at a parameter, so the data tower is
   non-empty while the branch tower is three deep.

   Nothing here is a new *arm*: it is the composition — arm W's `roll`,
   `unroll`, `unroll_roll` and `WT.Wrec_iota`-proved private ι rule under the
   n-ary chain of [`InductiveModels.oneLayerNaryCompatibility`] — that no
   occupant of the corpus reached past `TwinInf`'s two. -/
inductive TripleInf (P Q : Type) : Type where
  | mk : (P → TripleInf P Q) → (Q → TripleInf P Q) → (P → Q → TripleInf P Q) →
      TripleInf P Q

inductive QuadInf (P Q : Type) : Type where
  | mk : (P → QuadInf P Q) → (Q → QuadInf P Q) → (P → Q → QuadInf P Q) →
      (Q → P → QuadInf P Q) → QuadInf P Q

inductive TrineInf (α : Type) : Type where
  | mk : α → (α → TrineInf α) → (P → TrineInf α) → (α → TrineInf α) → TrineInf α

inductive Utd : Type where
  | nil : Utd
  | mk : (k : P) → (j : P) → (PFam k → Utd) → (PFam j → Utd) → Utd
  | gap : (k : P) → (PFam k → Utd) → Q → Utd → Utd
