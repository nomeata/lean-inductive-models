/- The exact tight-pair support bundle and its two smallest consumers.

   `PI2` fixes two independent fields at the tight `max u v` carrier.
   `PIDep` makes the second field depend on the first.  Both have intrinsic
   primitive projections and a small kernel recursor at the maybe-Prop
   specialization; their models use the projection-derived `PSigma'.rec'`. -/

set_option bootstrap.inductiveCheckResultingUniverse false in
set_option genSizeOf false in
set_option genInjectivity false in
inductive PSigma' {α : Sort u} (β : α → Sort v) : Sort (max u v) where
  | mk (fst : α) (snd : β fst) : PSigma' β

def PSigma'.fst {α : Sort u} {β : α → Sort v} (self : PSigma' β) : α := self.1

def PSigma'.snd {α : Sort u} {β : α → Sort v} (self : PSigma' β) : β self.fst := self.2

theorem PSigma'.fst_mk {α : Sort u} {β : α → Sort v}
    (fst : α) (snd : β fst) : (PSigma'.mk fst snd).fst = fst := rfl

theorem PSigma'.snd_mk {α : Sort u} {β : α → Sort v}
    (fst : α) (snd : β fst) : (PSigma'.mk fst snd).snd = snd := rfl

def PSigma'.rec'.{u,v,w} :
    ∀ {α : Sort u} {β : α → Sort v} {motive : PSigma' β → Sort w},
      (∀ fst snd, motive (.mk fst snd)) → ∀ t, motive t :=
  fun h t => h t.fst t.snd

theorem PSigma'.rec'_mk {α : Sort u} {β : α → Sort v}
    {motive : PSigma' β → Sort w} (h : ∀ fst snd, motive (.mk fst snd))
    (fst : α) (snd : β fst) :
    PSigma'.rec' h (.mk fst snd) = h fst snd := rfl

set_option bootstrap.inductiveCheckResultingUniverse false in
set_option genSizeOf false in
inductive PI2 (α : Sort u) (β : Sort v) : Sort (max u v) where
  | mk (fst : α) (snd : β) : PI2 α β

set_option bootstrap.inductiveCheckResultingUniverse false in
set_option genSizeOf false in
inductive PIDep (α : Sort u) (β : α → Sort v) : Sort (max u v) where
  | mk (fst : α) (snd : β fst) : PIDep α β

--#export Eq PSigma' PI2 PIDep
