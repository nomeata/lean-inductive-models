/- **A basis primitive the input declares *after* the block whose model needs
   it**, so the composition's third step has to wait for it.

   `MODELGEN.md` §1.6 is the rule for a mutual model and the input's own `Eq`,
   and [`Modelgen.runFilter`]'s `waitingPrim` is the same rule for the third
   construction and the input's own `Eq`, `False`, `Nat` and `PSigma`: a model
   that would have to *splice* a constant the file itself declares later is
   held back and generated after that declaration, because a splice may not
   take a name the input is going to use.

   **What this file adds is that the rule reaches the composition.** The queue
   belongs to `runFilter`, and [`Modelgen.primCompose`] — the third step, over
   the `_model.tag` and `_model.aux` a mutual model just emitted — is called
   from inside `genMutual` and from the nested arm, neither of which could
   reach it. So it passed `canWait := false` and every one of its models
   declined `prim model name taken (PSigma)` at a primitive that was merely
   *late*. `Lean.Syntax` is that shape in Mathlib — replayed at line 9,948 of
   the export against `PSigma` at line 95,424 — and it was two of the eleven
   declines the full run reported. `MODELGEN.md` §8.16.5.

   The layout is the whole fixture:

   * `MA`/`MB`/`MC` is a plain **mutual** block, so `Modelgen/Mutual.lean`
     emits `MA._model.tag` and `MA._model.aux` for it, and those two are what
     the third step then models. Three members and unequal constructor counts,
     for the reason `mutual_shapes.lean` gives: two members cannot distinguish
     an ordering.
   * `PSigma` is declared **after** it, at Lean's own shape, so
     [`Modelgen.primReady`] is false at the block and true at the drain.
     `Modelgen.checkPSigma` runs on it, so a declaration that is not Lean's
     would be refused here rather than used.
   * `Nd` is a **nested** declaration, also before `PSigma`, because the third
     step has two callers and a repair at one of them would leave the other
     declining. Its `_model.aux` is indexed and takes arm C.
   * `Pre` is the control: a simple inductive **before** `PSigma` whose own
     model is an input declaration's, not the composition's. It waits on the
     queue that already existed, so a regression that broke *that* wait while
     fixing this one is caught in the same file.

   `Eq` is declared first and `Nat` is not declared at all — the model splices
   Lean's `Nat`, which is the case the queue must *not* fire on, and the report
   says so with a splice line rather than a wait. -/
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

inductive L (α : Type) : Type where
  | nil : L α
  | cons : α → L α → L α

/-- The control: its model is an input declaration's, held by the queue that
already existed. -/
inductive Pre : Type where
  | p0 : Pre
  | p1 : N → Pre

mutual
inductive MA : Type where
  | a0 : MA
  | a1 : MB → MA
inductive MB : Type where
  | b0 : MB
  | b1 : MC → MB
  | b2 : MA → MB
inductive MC : Type where
  | c0 : N → MC
end

inductive Nd : Type where
  | leaf : Nd
  | node : L Nd → Nd

--#export Eq N L Pre MA MB MC Nd PSigma

structure PSigma {α : Sort u} (β : α → Sort v) where
  mk ::
  fst : α
  snd : β fst
