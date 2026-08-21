/- **Former simple-model refusal boundaries**, retained as positive regression
   cases for the routes that replaced them:

   * `MixI` — an indexed subsingleton with a **pivot**: a fresh constructor
     argument that literally *is* one of the output's indices, with a proof
     field whose type mentions it. **No longer a refusal.** The packed-equation
     model substitutes the recursor's own index argument for such a field and
     equates only at the positions that are not pivots, so `MixI` is a model
     and `test/fixtures/inductive-models/prim_idx.lean` is the grid that whole axis is measured on. What
     it still pins is the *promotion* fact its old header recorded: Lean's
     front end turns a leading bare-variable index into a parameter, so a pivot
     is only reachable behind a position that cannot be promoted, and here the
     fresh index sits after a constant one.
   * `Branch` — a **branching** recursive constructor (two recursive fields)
     and `Binder` — a recursive occurrence **under a binder** — are **no longer
     refusals**. They are the two shapes this file was built to refuse, the
     tuple tower's spine being one `Nat` and a constructor taking one
     predecessor; **the tree arm** models both, and they stay
     here as the positives at the boundary they used to mark. `Branch` is the
     first W target in the file, so it is the one that carries the spliced W
     core and the eighteen models of the fragment's own inductives that follow
     it; `Binder` behind it is its own dozen declarations.
     `test/fixtures/inductive-models/prim_w.lean` is the arm's own fixture and carries
     the shapes these two do not — data on both sides of a child, a dependent
     data tower, a parameter and a level parameter, and the untagged `Bad`
     case whose branch type factors through the complete label rather than its
     constructor tag.
   * `Inf.below` — the `below` Lean mints for the recursive proposition beside
     it. It is a recursive subsingleton too and reaches **the graph arm**. Graph
     inversion now carries and transports the packed non-pivot index equality,
     so this generated declaration, `prim_graph.lean`'s `BadC`, and
     `prim_idx.lean`'s corresponding deliberate cases all model.
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
   * `BoxF` — a field whose `imax` sits recursively inside a domain of its own
     telescope.  Recursive boxing reaches that inner Π, so the field now has
     an exact `max 1 u v` representation and models with projection and eta.

   `Inf` itself — `inductive Inf : Prop | mk : Inf → Inf` — is **no longer a
   refusal**: it is the degenerate shape of the graph arm, the graph route, and models
   with no `funext` at all because its recursive field has no binders.
   `prim_graph.lean` carries that arm's positives.

   The three variable-sort shapes this file used to carry — an empty
   carrier, a two-constructor carrier and a carrier whose constructor has a
   field — are **no longer refusals**: the derived tight-pair/PUnit lift reaches a bare `Sort u`
   with a carrier that can be empty, and they live in `prim_shapes.lean` as
   `PE`, `PM`, `PF`, `PT` and `PI`. `False` is no longer a refusal either;
   it is derived, and models.

   The basis-primitive **exemption** and the name guard are exercised by the
   aggregate fixture suite and `mutual_keying` respectively. The exemption is
   reported on its own row and is not counted a decline: it is what makes the
   construction well-founded rather than a shape it cannot reach.

   The old recovery-arm "index-variable field" and graph-arm non-pivot refusal paths no
   longer exist: they were missing transport cases rather than semantic
   bounds. `prim_idx.lean` and `prim_graph.lean` carry the complete regression
   grids for those routes. -/
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
