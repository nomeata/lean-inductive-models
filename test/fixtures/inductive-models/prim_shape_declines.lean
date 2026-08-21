/- **Shapes that reach no generation arm**, and the shape that stopped being
   one.

   `prim_declines.lean` is the *former* refusal boundaries, kept as positives
   for the routes that replaced them. This file used to be the complement:
   four owners the simple construction does not model, each of which **aborted
   the run** until the route dispatcher learned to classify them. An abort is
   the wrong answer for all four — the output contract says an unsupported
   owner passes through unchanged and is reported, and exit `2` says so — and
   for a thirty-minute stream it is the difference between a decline row and a
   run that stops in the middle.

   **Two of the four now model**, and this file keeps them for the same reason
   `prim_declines.lean` keeps its own: a boundary that moved is worth pinning
   on the side it moved to.

   * **`Foreign` and `Foreign0` — the boundary that was not one.** Both write
     the owner mention as `idf (T … → Type) (fun _ => N) child`, which is dead
     — its reduct is `N` — but only after **δ**, and the route analysis used to
     reduce β and ζ and unfold no constant on purpose. What survived that
     normalization was an occurrence under a foreign type former, and no arm of
     any route can replace one, so both were declined `out of scope`: nesting
     is layer 1's business.

     They are not nested. Both are kernel-accepted with `numNested = 0` —
     Lean's own positivity check unfolds `idf` and finds no occurrence at all,
     so neither is routed to `Plan.plan` — and the recursor Lean minted for
     each binds an induction hypothesis for `child` and none for `tag`. The
     decline named a boundary that the declaration itself said was not there.

     A field is recursive exactly when an occurrence survives **full**
     reduction, and the constructor telescope is now normalised that far before
     any route is chosen, so `tag` arrives as the ordinary non-recursive field
     it is. The emitted constructor is still spelled from the source: `tag`'s
     type in `T.mk._model` is `idf (T._model … → Type) (fun _ => N) child`,
     unreduced, and the kernel's own conversion reconciles it with the term.
     `Foreign` is the indexed case and `Foreign0` the non-indexed one; both
     model, and `delta_dead_mention.lean` is the same question at the shapes
     that also project.

     Nothing declines in their place. The site that refused them is now a
     hard failure and its class is empty: an occurrence that really does
     survive reduction under a foreign type former is what Lean's positivity
     check rejects, so no export of one exists, and an input that claims
     `numNested = 0` of such a declaration is lying about its own metadata —
     which is `--type-check-input`'s business, not a shape to decline.

   * **`PadImax` and `PadImaxIdx` — out of scope, and it used to say
     incomplete.** A nonrecursive one-constructor owner at a **maybe-zero**
     sort is the field-preserving arm's, decided before any arm runs, and the
     Church fallback behind it would record only inhabitation and lose the
     field; the arm must therefore *store* the field at exactly `Sort w`.
     `PadOne` and `PadMany` used to stand here and said `incomplete`, because
     a field at `Sort u` under a carrier at `Sort (max u v)` was retained by
     neither exact one-field answer and the tower had no pad. **They model**
     now — the tower ends at [`InductiveModels.unitAt`] `w` and lands at
     `Sort (max ℓ⃗ w)` — and `maybe_zero_pad.lean` is that whole family.

     What is left here is not the same shape. `PadImax`'s field is a Π, so its
     level is `imax u v`, and `max (imax u v) (max u v)` is not `max u v` in
     normal form however the pad is placed: Lean's conversion on levels is
     normal-form equality (`level.cpp:518-520`) and admits no absorption of an
     `imax` into a `max`, even though `is_geq` proved the bound by splitting
     the `imax` into a stronger `max`-shaped one. The recursive box that
     removes an exposed `imax` for the never-zero tuple tower
     ([`InductiveModels.boxTyOf`]) is unavailable here for a reason that is
     also a statement: every boxed level carries a `max 1 ·` floor and no
     `max 1 ·` is ever a maybe-zero `w`, since at `w := 0` the carrier is
     `Prop` and a boxed field is not a proof. There is no third pad to build —
     one that cleared the `imax` would miss `Prop`, one that reached `Prop`
     would not clear the `imax` — so this is a boundary the construction
     states, not an arm anyone can finish. `PadImaxIdx` is the indexed half,
     which reaches the same question through the indexed case's own guard.

   `N` is the control: an ordinary owner in the same file that models, so a
   run which declined everything could not pass this row.

   The **third** hole the audit named — the tree arm's `labelFactored` guard refusing
   a shape at a never-zero non-indexed sort — has no occupant here, and not
   for want of trying. It needs a recursive field one of whose *binder types*
   depends on an earlier recursive field, and the kernel rejects an owner
   mention in a binder type as a non-positive occurrence whatever hides it
   (β-redex, `let`, or a definition), while a dependence without a mention
   would need a constant of type `T → Sort` that does not exist while `T` is
   being declared. The dispatcher classifies it anyway; see
   `InductiveModels.primIso`. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive N : Type where
  | z : N
  | s : N → N

/-- The identity, as an ordinary definition. It is what makes the owner mention
dead without making it disappear: `idf (T → Type) (fun _ => N) child` mentions
`T`, reduces to `N`, and needs δ to get there. -/
def idf (α : Sort u) (a : α) : α := a

--#export Eq N idf Foreign Foreign0 PadImax PadImaxIdx

inductive Foreign : N → Type where
  | base : Foreign N.z
  | step (n : N) (child : Foreign n)
      (tag : idf (Foreign n → Type) (fun _ => N) child) : Foreign (N.s n)

inductive Foreign0 : Type where
  | base : Foreign0
  | step (child : Foreign0) (tag : idf (Foreign0 → Type) (fun _ => N) child) : Foreign0

inductive PadImax (α : Sort u) (β : Sort v) : Sort (max u v) where
  | mk : (α → β) → PadImax α β

inductive PadImaxIdx (α : Sort u) (β : Sort v) (n : N) : N → Sort (max u v) where
  | mk : (α → β) → PadImaxIdx α β n n
