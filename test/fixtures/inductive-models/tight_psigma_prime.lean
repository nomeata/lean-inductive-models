prelude

/- A kernel-level universe-polymorphic pair and two source families which
   require it for field-preserving models.  `prelude` suppresses elaborator
   convenience declarations: this fixture is about the inductive records,
   their primitive projections, recursors, and reduction metadata only. -/

universe u v

set_option genSizeOf false

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PSigma' {α : Sort u} (β : α → Sort v) : Sort (max u v) where
  | mk (fst : α) (snd : β fst) : PSigma' β

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PI2 (α β : Sort u) : Sort u where
  | mk (fst : α) (snd : β) : PI2 α β

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PIDep (α : Sort u) (β : α → Sort u) : Sort u where
  | mk (fst : α) (snd : β fst) : PIDep α β

--#export PSigma' PI2 PIDep
