/- **A declaration every one of whose constructors has a bare recursive field
   is empty, and that — not linearity — is the shape class arm E models.**

   Arm E is the exact model of this shape: the carrier is the derived lift of
   `⊥` at the declaration's own sort, each constructor returns its own
   recursive field, and the recursor eliminates that empty value
   (`Simple/ArmE.lean:38-70`).  It costs `Nat`, the lift, and no axiom.

   Its guard is `route .type && ni == 0 && isRec` with every constructor's
   bare recursive slot found (`Simple/Site.lean`'s `emptySlots`, over
   `InductiveModels.bareRecSlotOf`).  It used to ask `recSlotOf` instead, which
   is the *tuple tower's* question — one recursive field per constructor, that
   occurrence bare — and so reached only the **linear** corner of a class
   linearity has nothing to do with.

   * `NbLin` is that corner, and the control.
   * `NbBr` has two recursive fields instead of one.  It is just as empty, and
     just as exactly modelled by the lift of `⊥`.  It used to be handed to arm
     W, which built a W-type with no leaves: a spliced `_wcore` fragment, and
     `Classical.choice` beside it, for a carrier that is `⊥`.  It is arm E's
     now, at 8 declarations against the whole fragment `NbInf` still pays for
     below.
   * `NbInf` recurses under a binder whose domain is **inhabited**.  Still
     empty, and still arm W's, because a recursive occurrence under a binder
     carries no inhabitant of the owner to return.  It is what pays for the
     fragment in this file now that `NbBr` does not.
   * `NbVac` is the boundary, and the reason the statement is not "no base
     constructor".  Its only constructor recurses under a binder whose domain
     `E0` is **empty**, so `E0 → NbVac` is inhabited vacuously and `NbVac` is
     **inhabited**.  An arm E generalised to "no base constructor" would model
     an inhabited type by `⊥`.  Emptiness of a binder domain is not a question
     the route analysis can ask, so the class stops at occurrences that carry
     an inhabitant of the owner directly: `NbBr` is in, `NbVac` is out.

   Nothing here is red.  The counts below are the whole of the evidence that
   the guard reaches the class and stops at its boundary. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u

inductive Eq : {a : Sort u} → a → a → Prop where
  | refl (x : a) : Eq x x

inductive Nt : Type where
  | z : Nt
  | s : Nt → Nt

inductive E0 : Type where

inductive NbLin : Type where
  | s : NbLin → NbLin

inductive NbBr : Type where
  | s : NbBr → NbBr → NbBr

inductive NbInf : Type where
  | s : (Nt → NbInf) → NbInf

inductive NbVac : Type where
  | s : (E0 → NbVac) → NbVac
