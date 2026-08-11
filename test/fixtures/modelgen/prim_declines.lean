/- **The simple-model construction's refusals**, one fixture per
   decline path of `src/Modelgen/Simple.lean`, each asserting the refusal and
   its printed reason:

   * `MixI` — an indexed subsingleton with a **pivot**: a fresh constructor
     argument that literally *is* one of the output's indices, with a proof
     field whose type mentions it. **No longer a refusal.** The packed-equation
     model substitutes the recursor's own index argument for such a field and
     equates only at the positions that are not pivots, so `MixI` is a model
     and `test/fixtures/modelgen/prim_idx.lean` is the grid that whole axis is measured on. What
     it still pins is the *promotion* fact its old header recorded: Lean's
     front end turns a leading bare-variable index into a parameter, so a pivot
     is only reachable behind a position that cannot be promoted, and here the
     fresh index sits after a constant one.
   * `Branch` — a **branching** recursive constructor (two recursive fields)
     and `Binder` — a recursive occurrence **under a binder** — are **no longer
     refusals**. They are the two shapes this file was built to refuse, the
     tuple tower's spine being one `Nat` and a constructor taking one
     predecessor; **arm W** models both, and they stay
     here as the positives at the boundary they used to mark. `Branch` is the
     first W target in the file, so it is the one that carries the spliced W
     core and the eighteen models of the fragment's own inductives that follow
     it; `Binder` behind it is its own dozen declarations.
     `test/fixtures/modelgen/prim_w.lean` is the arm's own fixture and carries the shapes these
     two do not — data on both sides of a child, a dependent data tower, a
     parameter and a level parameter, and the arm's own boundary (`Bad`, whose
     branch type does not factor through the tag).
   * `Inf.below` — the `below` Lean mints for the recursive proposition
     beside it. It is a recursive subsingleton too and reaches **arm G**, and
     is refused there: its index is `Inf.mk a` rather than one of the
     constructor's own data fields, so the graph route's inversion cannot be
     stated at an arbitrary index. `prim_graph.lean`'s `BadC` is the same
     refusal reached deliberately rather than by accident, and
     `prim_idx.lean`'s `Rxh` is this one written deliberately. **Arm F now
     models the same index shape and arm G does not**, which is the whole of
     what is left of this tranche's boundary.
   * `SvIx` — a carrier whose index telescope is **hidden behind a
     definition** *and* whose constructor's indices are its own fields.
     **Neither half is a refusal any more**: the shape check unfolds the
     telescope (`prim_shapes.lean`'s `Sv` is that positive) and the pivot split
     models the field-dependent indices, so this is now the cell where the two
     compose. It is kept for that: the unfolding and the pivot analysis are two
     different passes and this is the only occupant that runs the second on the
     first's output. Before the unfolding it declined as "does not land in a
     sort", which named the wrong obstruction rather than the composed shape.
   * `Idx` — an **indexed family** (`P` beside it is its index's type, and
     models — the guard is not refusing everything).
   * `BoxF` — a field whose level keeps an `imax` even boxed: the imax
     sits on a *domain* of the field's own telescope, where wrapping the
     codomain does not reach.

   `Inf` itself — `inductive Inf : Prop | mk : Inf → Inf` — is **no longer a
   refusal**: it is the degenerate shape of arm G, the graph route, and models
   with no `funext` at all because its recursive field has no binders.
   `prim_graph.lean` carries that arm's positives.

   The three variable-sort shapes this file used to carry — an empty
   carrier, a two-constructor carrier and a carrier whose constructor has a
   field — are **no longer refusals**: `PULiftP` reaches a bare `Sort u`
   with a carrier that can be empty, and they live in `prim_shapes.lean` as
   `PE`, `PM`, `PF`, `PT` and `PI`. `False` is no longer a refusal either;
   it is derived, and models.

   The basis-primitive **exemption** and the name guard are exercised by the
   aggregate fixture suite and `mutual_keying` respectively. The exemption is
   reported on its own row and is not counted a decline: it is what makes the
   construction well-founded rather than a shape it cannot reach.

   **Two of this file's refusals became models in the tranche that split the
   index axis** — `MixI` and `SvIx` above — and the paragraph each carries says
   so where a reader meets it rather than in an appendix. The decline path they
   used to occupy, arm F's "index-variable field", **no longer exists**: it was
   not a bound but a missing case. What replaces them as this file's
   subsingleton refusals is `Inf.below` alone, and `prim_idx.lean` carries the
   rest of the grid. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive Inf : Prop where
  | mk : Inf → Inf

inductive P : Type where
  | one : P
  | two : P

inductive Idx : P → Prop where
  | mk : Idx P.one

inductive MixI (q : P → Prop) : P → P → Prop where
  | mk (k : P) (h : q k) : MixI q P.one k

inductive Branch : Type where
  | leaf : Branch
  | node : Branch → Branch → Branch

inductive Binder : Type where
  | tip : Binder
  | lim : (P → Binder) → Binder

inductive BoxF (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  | mk : ((α → β) → β) → BoxF α β

def SvIxFam (x : P) : Type := P → P → Prop

inductive SvIx (x : P) : SvIxFam x where
  | mk (y z : P) : SvIx x y z
