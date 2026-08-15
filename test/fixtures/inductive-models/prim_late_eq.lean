/- **A modelable declaration in front of the input's own basis records.**

   The raw export puts `Cnt` first and only then the `Nat` and `Eq` its
   neighbour needs, because `Use` is the first root that mentions either. So
   this file is the minimal shape of the late-basis regression: the record
   which *provides* the fixed basis stands at a positive ordinal, and a
   perfectly ordinary owner stands in front of it.

   `Cnt` needs the same `Eq` every prim model is written at, and the tool would
   otherwise have to write one — into a name the input itself binds four
   records later. The two declarations are the same declaration, so the splice
   proceeds and the input's own record replays as a no-op; `Nat` and `Eq` stay
   at their source positions in the output and are reported as the basis
   exemption, exactly as they are when they come first.

   `Use` is the control on the far side of the boundary: with the basis
   physically in front of it, it models the way it always has. A regression
   which only restores owners *behind* the basis record leaves `Cnt` declining
   and is caught here. -/

--#export Cnt Use

inductive Cnt : Type where
  | zero : Cnt
  | succ : Cnt → Cnt

inductive Use : Nat → Prop where
  | mk (x : Nat) (h : x = x) : Use x
