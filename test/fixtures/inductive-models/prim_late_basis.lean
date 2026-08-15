/- **An ordinary declaration physically follows unrelated model owners in the
   raw export.**

   [`InductiveModels.runFilter`] consumes the source in its physical order.
   `Eq`, `Nat`, `PSigma'`, and `PUnit` are fixed support; ordinary `PSigma` is
   not, and therefore remains an ordinary modelled owner at its source position.

   **What this file adds is that available fixed support reaches composition.**
   [`InductiveModels.primCompose`] is the third step over the `_model._impl.tag` and
   `_model._impl.aux` a mutual model just emitted. It runs inside the same
   disposable island as `genMutual` or the nested arm, with the exact
   fixed support already installed in the persistent prefix.

   The layout is the whole fixture:

   * `MA`/`MB`/`MC` is a plain **mutual** block, so `src/InductiveModels/Mutual.lean`
     emits `MA._model._impl.tag` and `MA._model._impl.aux` for it, and those two are what
     the third step then models. Three members and unequal constructor counts,
     for the reason `mutual_shapes.lean` gives: two members cannot distinguish
     an ordering.
   * `PSigma` is declared **after** it, at Lean's own shape. The earlier models
     use tight `PSigma'`; this source block stays put and models in its own turn.
   * `Nd` is a **nested** declaration, also before `PSigma`, because the third
     step has two callers and a repair at one of them would leave the other
     declining. Its `_model._impl.aux` is indexed and takes arm C.
   * `Pre` is the control: a direct simple inductive **before** `PSigma` in the
   raw export. It uses the same fixed support prefix as composed models.

   `Eq` is declared first and `Nat` is not declared at all — the model splices
   Lean's `Nat`, and the report distinguishes that splice from the later
   ordinary `PSigma` model. -/
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

/-- The direct-simple control, using the same available support prefix. -/
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
