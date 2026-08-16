/- **A dependent ordinary field on the legacy W route.**

   The intrinsic projection ι contract is literal: `T._model.proj_j` applied to
   the modeled constructor equals constructor field `j` itself, with no
   transport. For a *dependent* field — one whose type names an earlier field —
   the left-hand side's type is the field type with each earlier field replaced
   by its own modeled projection, so the equation is a proposition **only if
   each of those projections selects its field definitionally**. Where it does
   not, the two sides live in different types and there is nothing to state.

   `WDep` is that shape at the one route which reconstructs a field
   propositionally rather than definitionally:

   * **one constructor with a dependent ordinary field.** `Vec a` names the
     data field `a`, so `WDep._model.proj_1`'s codomain is
     `Vec (WDep._model.proj_0 self)`.
   * **the untagged W arm.** The child's binder type `Vec a` reads the label's
     own data, so `InductiveModels.tagFactored` is false and the arm runs the
     core at `K := A` with `WT.decEqAll = Classical.propDecidable`. The
     modeled selector is then `WT.Wrec`, whose ι rule is `WT.Wrec_iota` — a
     *theorem*.
   * **off the phase-1 one-layer adapter.** `HiddenType` is a reducible result
     former, so the owner's serialized type does not end in a literal sort and
     `InductiveModels.phase1DirectTypeOneLayerEligible` declines it. This is
     the same idiom `HiddenIndexed` uses in `indexed_fibre_boundary.lean` to
     stay structurally legacy, and it is what leaves this owner on the legacy
     arm rather than on the adapter that supplies reflexive selectors.

   Before the guard this file is why: generation emitted
   `WDep._model.proj_1.iota` at `Eq (Vec (WDep._model.proj_0 (WDep.mk._model …)))`
   with the constructor's own `Vec a` binder on the right, and Lean's kernel
   rejected the declaration with an application type mismatch. Nothing in the
   suite read that verdict.

   `WPlain` is the control and must keep modelling: the same reducible result
   former, the same legacy W arm, the same three projected fields — and no
   field type that names an earlier one. So what stops `WDep` is the
   *dependency*, not the route.

   There is no untagged control, and that is a fact about the arm rather than
   an omission: untagged-ness *is* a child binder that names an earlier field,
   so an untagged one-constructor owner always has a dependent projected field.
   `WDep`'s field 2 is that field and its field 1 is an ordinary one, so the
   file carries both spellings of the same defect.
-/
prelude

universe u

--#export Eq HiddenType WDep WPlain

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

inductive Vec : N → Type where
  | vnil : Vec N.z
  | vcons : (n : N) → Vec n → Vec (N.s n)

/-- Reducible result former, hidden in the serialized owner type. -/
def HiddenType := Type

/-- Dependent ordinary field: `Vec a` names the data field `a`. -/
inductive WDep : HiddenType where
  | mk : (a : N) → Vec a → (Vec a → WDep) → WDep

/-- The control: same route, same three projected fields, no dependent one. -/
inductive WPlain : HiddenType where
  | mk : (a : N) → Vec N.z → (Vec N.z → WPlain) → WPlain
