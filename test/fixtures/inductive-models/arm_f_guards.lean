/- The two residual recovery-arm guard boundaries, at their smallest source shapes.

   `LostData` is kernel accepted, but its `payload : Nat` is not recoverable
   from the conclusion index.  The kernel therefore gives it only a
   Prop-valued recursor.  Simple sees `large = false` and never enters the
   recovery-arm/graph-arm classifier which defensively rejects this shape in an
   inconsistent unchecked export.

   `MovingPivot` is the smallest large-eliminating shape which reaches the
   dependent-pivot scan: index 1 is supplied by `payload`, and its declared
   type is index 0.  Recording a pivot therefore necessarily records that
   supplying field at the same time; there is no kernel declaration, or even
   classifier state, in which this pivot has no constructor data field. -/

--#export LostData MovingPivot

inductive LostData : Nat → Prop where
  | mk (payload : Nat) : LostData Nat.zero

inductive MovingPivot : (α : Type) → α → Prop where
  | mk (payload : Nat) : MovingPivot Nat payload
