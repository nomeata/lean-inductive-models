/- **A recursive declaration with no base constructor is empty, and only the
   linear one is modelled as empty.**

   Arm E is the exact model of this shape: the carrier is the derived lift of
   `⊥` at the declaration's own sort, each constructor returns its own
   recursive field, and the recursor eliminates that empty value
   (`Simple/ArmE.lean:38-70`).  It costs `Nat`, the lift, and no axiom.

   Its guard is `route .type && ni == 0 && isRec && erasureLinear`, with every
   constructor's slot found (`Simple/Site.lean:446-456`).  `erasureLinear` is
   the tuple tower's own linearity — one recursive field per constructor, and
   that occurrence a bare `T p⃗` — so arm E reaches only the **linear** corner
   of a shape class that is not about linearity at all.

   * `NbLin` is that corner, and the control.
   * `NbBr` has two recursive fields instead of one.  It is just as empty, and
     just as exactly modelled by the lift of `⊥`.  `erasureLinear` is false, so
     arm E declines to look and the dispatcher hands it to arm W, which builds
     a W-type that happens to have no leaves: a spliced `_wcore` fragment, and
     `Classical.choice` beside it, for a carrier that is `⊥`.  The declaration
     counts below are the evidence and the whole of it.
   * `NbInf` recurses under a binder whose domain is **inhabited**.  Still
     empty, still on arm W.
   * `NbVac` is the boundary, and the reason the general statement is not "no
     base constructor".  Its only constructor recurses under a binder whose
     domain `E0` is **empty**, so `E0 → NbVac` is inhabited vacuously and
     `NbVac` is **inhabited**.  An arm E generalised to "no base constructor"
     would model an inhabited type by `⊥`.  The generalisation that is sound is
     "every constructor has at least one recursive field whose occurrence is a
     **bare** `T p⃗`" — which `recSlotOf` already computes, and which admits
     `NbBr` and excludes `NbVac`.

   Nothing here is red.  This file is the count that has to move when arm E's
   guard is decided: today `NbBr` and `NbInf` pay a two-hundred-declaration
   fragment and an axiom for the empty type, and `NbLin` beside them does not. -/
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
