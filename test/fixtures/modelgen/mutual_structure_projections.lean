/-
Two kernel structure-like members in one non-recursive mutual block.

This is the route-separation fixture: neither member is a single-member simple
declaration, but each independently has the kernel shape used for structure
projections.  `MRight.payload` depends on its earlier `key` field, so the
mutual route also has to install projection models incrementally.
-/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

mutual
  structure MLeft (α : Type u) (β : α → Type v) : Type (max u v) where
    value : α

  structure MRight (α : Type u) (β : α → Type v) : Type (max u v) where
    key : α
    payload : β key
end

-- Deliberately later than the structure block. Projection generation needs
-- this basis lift for unrelated mutual motives and must wait instead of
-- declining or shadow-splicing it.
inductive PULiftP.{w} (p : Prop) : Sort w where
  | up : p → PULiftP p

def leftValue (α : Type u) (β : α → Type v) (x : MLeft α β) : α := x.value

def rightPayload (α : Type u) (β : α → Type v) (x : MRight α β) : β x.key :=
  x.payload

--#export Eq MLeft MLeft.value MRight MRight.key MRight.payload PULiftP
--#export leftValue rightPayload
