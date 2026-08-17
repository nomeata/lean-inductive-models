/- **Records whose fields nothing later names.**

   A constructor's field telescope splits in two, and the split is a property
   of the telescope rather than of any storage decision: field `i` is on the
   *spine* when some later field's type (or the constructor's own result)
   mentions it, and in the *block* when nothing does.  A block field's type may
   name spine variables freely — the block sits inside the spine's scope — and
   it can never name another block field, because a named field is by
   definition on the spine.

   These families are the four positions that split can be in, on the
   never-zero `Type` route (the `Nat`-tagged tuple tower):

   * `WFlat` — **all block**: twelve independent fields at two different
     parameters' levels, so the storage is one balanced tree and the spine is
     empty.  Twelve rather than two, because a balanced tree over two leaves is
     also the right-nested one and says nothing about the shape.
   * `WMixed` — **interleaved**: two fields named later and five not, in an
     order where a block field sits before, between and after the spine ones,
     and where every block field's type names a spine variable.  A treatment
     that reordered the public interface, or that built the block outside the
     spine's scope, fails here and at nothing above.
   * `WChain` — **all spine but the last**, four deep: the shape every chain
     had before a block existed, kept as the control that the spine is still
     built the way it was.
   * `WBox` — four independent fields whose levels carry an `imax`, so every
     leaf of the block is stored through `boxTyOf` and read back through
     `unbox`.  Boxing is a per-field decision and the block has to keep it one.

   `BFlat`, `BMixed` and `BChain` are the same three shapes at a **bare,
   maybe-zero** carrier, which is a different construction (the tight tower and
   its reflexive projection overrides) over the same partition. -/
prelude

set_option genSizeOf false
set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

inductive Vec (α : Type u) : N → Type u where
  | nil : Vec α N.z
  | cons : α → (n : N) → Vec α n → Vec α (N.s n)

inductive WFlat (α : Type u) (β : Type v) : Type (max u v) where
  | mk (a0 : α) (a1 : β) (a2 : α) (a3 : β) (a4 : α) (a5 : β)
       (a6 : α) (a7 : β) (a8 : α) (a9 : β) (a10 : α) (a11 : β) : WFlat α β

inductive WMixed (α : Type u) : Type u where
  | mk (x0 : α) (n : N) (v0 : Vec α n) (x1 : α) (m : N) (v1 : Vec α m) (x2 : α) :
      WMixed α

inductive WChain (α : Type u) (β : α → Type u) : Type u where
  | mk (c0 : α) (c1 : β c0) (c2 : Eq c1 c1) (c3 : Eq c2 c2) (c4 : Eq c3 c3) :
      WChain α β

inductive WBox (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  | mk : ((α → β) → β) → ((α → β) → β) → ((α → β) → β) → ((α → β) → β) → WBox α β

inductive BFlat (α : Sort u) (β : Sort u) : Sort u where
  | mk : α → β → α → β → α → β → α → β → BFlat α β

inductive BMixed (α : Sort u) (P : α → Sort u) : Sort u where
  | mk : (k : α) → P k → α → (j : α) → P j → P k → BMixed α P

inductive BChain (α : Sort u) (P : α → Sort u) : Sort u where
  | mk : (b0 : α) → (b1 : P b0) → (b2 : Eq b1 b1) → (b3 : Eq b2 b2) → BChain α P

--#export Eq N Vec WFlat WMixed WChain WBox BFlat BMixed BChain
