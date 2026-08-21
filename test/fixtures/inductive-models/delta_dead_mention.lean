/- **The owner mention that only δ discards, at the shapes that project.**

   `dead_owner_mention.lean` is this file's βζ sibling: a field written
   `(fun _ : T => N) k` or `let _u := T; N` mentions the owner and reduces to a
   domain that does not, and the reduction needed to see that is available to a
   pure function. A field written `cst T N` or
   `idf (T → Type) (fun _ => N) child` is the same fact one reduction further
   on — the mention is dead, and **unfolding a definition** is what discards
   it. Both spellings are ordinary kernel-accepted plain inductives: Lean's
   positivity check reduces the field type first, finds no occurrence, and
   marks the owner `numNested = 0`, and the exported recursor's minor premise
   binds no induction hypothesis for the field.

   `prim_shape_declines.lean` carries the two owners this used to refuse
   outright. What is here is the half of the question that file cannot ask,
   because both of its owners have two constructors and neither projects:

   * `ProjDead` — **one constructor, so the field is a projection.** Its `tag`
     is `cst ProjDead N`, a dead mention that names no field. The projection's
     codomain is stated at the field's type *as written*, with the owner's name
     replaced by the model's — `cst ProjDead._model N` — and not at its `N`
     reduct, because the emitted statement is source syntax and the kernel's
     own conversion is what reconciles it with the term. Its ι rule is the
     literal equation at that same type.

   * `ProjDeadDep` — the same, with the dead mention **naming an earlier
     recursive field**. `tag`'s type is
     `idf (ProjDeadDep → Type) (fun _ => N) child`, so `tag` depends on `child`
     as written and does not depend on it at all after reduction. The
     projection for `tag` therefore has the codomain
     `idf (ProjDeadDep._model → Type) (fun _ => N) (ProjDeadDep._model.proj_0
     self)`: a codomain stated at an earlier projection, which is the shape the
     projection contract has to admit, and which reduces to `N` for the kernel.
     This is the row that would fail if the field were stored at its reduct, or
     if the dependence on a recursive field were read as a real one.

   * `Plain` — the control. It is `ProjDead` with the dead mention spelled `N`,
     and it must model with the same two projections and the same two ι rules,
     so a run that declined everything cannot pass this row.

     **It models with the same η rule too, and that agreement is the row.**
     Lean's exported `isRec` flag is syntactic: it is `true` for `ProjDead`,
     whose only mention is dead, while the recursor Lean minted beside it binds
     no induction hypothesis at all. One question — is this declaration
     recursive? — gets one answer here, and the answer is the recursor's: a
     field is recursive exactly when an owner occurrence survives full
     reduction. So `ProjDead` is *structure-like* by the same reading the
     construction already used to build its carrier, and `README.md`'s η
     contract applies to it exactly as it applies to `Plain`.
     `ProjDeadDep` is the control on the other side and gets **no** η rule: its
     `child` is an occurrence that survives, so the block really is recursive
     and the recursor really does bind an induction hypothesis for it.

   `idf` and `cst` are the two ways a definition can swallow a mention: the
   identity applied at a function type whose *domain* is the owner, and a
   constant function whose *discarded* argument is the owner. Neither is
   special-cased anywhere; what decides the field is whether an occurrence
   survives full reduction. Which arm then builds the model is not this file's
   question — the reduction happens once, on the shared telescope, before any
   route is chosen ([`InductiveModels.mkPrimSite`]). -/
prelude

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive N : Type where
  | z : N
  | s : N → N

/-- The identity, as an ordinary definition. `idf (T → Type) (fun _ => N) child`
mentions `T`, reduces to `N`, and needs δ to get there. -/
def idf (α : Sort u) (a : α) : α := a

/-- The constant function on sorts. `cst T N` mentions `T` in the argument it
throws away. -/
def cst (α : Sort u) (β : Sort v) : Sort v := β

--#export Eq N idf cst Plain ProjDead ProjDeadDep

inductive Plain : Type where
  | mk (k : N) (tag : N) : Plain

inductive ProjDead : Type where
  | mk (k : N) (tag : cst ProjDead N) : ProjDead

inductive ProjDeadDep : Type where
  | mk (child : ProjDeadDep) (tag : idf (ProjDeadDep → Type) (fun _ => N) child) :
      ProjDeadDep
