/- **A dependent ordinary field on the empty-carrier route**, and the one
   occupant that keeps `InductiveModels.Decline.projectionCodomain` a live
   verdict rather than dead code.

   The intrinsic projection ι contract is literal: `T._model.proj_j` at the
   modeled constructor *is* constructor field `j`, with no transport. For a
   field whose type names an earlier field the left-hand side's type is that
   field type with each earlier field replaced by its own modeled projection,
   so the equation is a proposition only if each of those projections
   **selects** — reduces to — its field on the modeled constructor.

   `w_dependent_field.lean` used to be that owner and no longer is: arm W
   selects its stored fields through `_wcore.WT.root` and the data tower. What
   is left is a different construction with a statable reason of its own.

   `EDep.mk`'s third field is a **bare** recursive occurrence, so every
   constructor of `EDep` has one and arm E's property holds: no constructor can
   ever be applied and `EDep._model.self` δ-reduces to
   [`InductiveModels.emptyAt`]. Arm E answers a projection by *eliminating* the
   major rather than by selecting out of it — which is total, and which the
   route states as an [`InductiveModels.Iso.emptyCarriers`] entry rather than
   as a projection override, precisely because it is a fact about the carrier
   and not a selector. An elimination is not a selector: `EDep._model.proj_0`
   applied to `EDep.mk._model a v t` is `emptyAt`'s eliminator at the major,
   which δβ-reduces to the bare field `t` — a variable — and stops. So field
   1's codomain `Vec (EDep._model.proj_0 (EDep.mk._model …))` is not the
   field's own `Vec a`, the two sides are terms of different types, and there
   is no proposition to state at all.

   This is a property of storing nothing, not a gap in an implementation: an
   empty carrier has no field to select, so no construction over it can supply
   a definitional selector for one. The owner therefore declines rather than
   emitting an equation the kernel refuses.

   `HiddenType` keeps the owner off the phase-1 one-layer adapter — the same
   idiom `HiddenIndexed` uses in `indexed_fibre_boundary.lean` — so the legacy
   arm is what builds the model.
-/
prelude

universe u

--#export Eq HiddenType EDep

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

/-- Every constructor has a bare recursive field, so the carrier is empty; and
field 1's type names field 0. -/
inductive EDep : HiddenType where
  | mk : (a : N) → Vec a → EDep → EDep
