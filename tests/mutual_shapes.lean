/- **A plain mutual block, on every axis that is not about indices.**

   `Modelgen/Mutual.lean` is a second construction and not a specialisation of
   the nested one, so it needs its own coverage rather than a corner of
   somebody else's. This file is the axes that a *type*-valued block has;
   `mutual_index.lean` is the indices and `mutual_prop.lean` is `Prop`.

   Every block here has **three** members, deliberately. Two cannot distinguish
   an ordering from a permutation of it, and the encoding has three orderings
   to get right at once: which member is which tag constructor, whose
   constructors come first in the flattened `T._model.ctor_j`, and which ι
   theorem belongs to which recursor.

   * `A`/`B`/`C` — a three-way cycle with **2, 1 and 3 constructors**. Equal
     constructor counts would let a generator that flattened the members in the
     wrong order still land every minor on a minor of the right *arity*; unequal
     counts do not. `C.cf : (N → A) → C` is an **infinitary** field, so a
     minor's induction hypothesis is a function and the ι rule has to write
     `fun n => rec_0 … (f n)` at it.

   * `PA`/`PB`/`PC` — **two parameters**, used by different members and by no
     constructor of `PC`, so a parameter telescope that is threaded through
     every member is told apart from one that is threaded where it is needed.
   * `UA`/`UB`/`UC` — **two level parameters** at `Type (max u v)`. Every
     generated constant carries the block's own levels and a recursor carries
     its motive universe in front of them; the tag lives at `Sort 1` here
     regardless, because none of these blocks has an index.

   **Every member of every block here recurses**, so that `nanoda_bin` can load
   the result: a member that recurses into nothing trips an upstream `isRec`
   assert that has nothing to do with this tool, and `mutual_nonrec.lean` is
   that axis, held apart for exactly that reason. -/
prelude

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

--#export Eq N A B C PA PB PC UA UB UC
--#export aOfB cOfA cFun paNode pbWrap ucMore

mutual
/-- Two constructors. -/
inductive A : Type where
  | a0 : A
  | aB : B → A
/-- One. -/
inductive B : Type where
  | bC : C → B
/-- Three, and the last is infinitary. -/
inductive C : Type where
  | c0 : C
  | cA : A → C
  | cf : (N → A) → C
end

mutual
/-- Two parameters, both mentioned. -/
inductive PA (α : Type) (β : Type) : Type where
  | leaf : α → PA α β
  | node : PB α β → PA α β
/-- Only the second. -/
inductive PB (α : Type) (β : Type) : Type where
  | wrap : β → PC α β → PB α β
/-- Neither. -/
inductive PC (α : Type) (β : Type) : Type where
  | done : PC α β
  | back : PA α β → PC α β
end

mutual
/-- `max u v`, so a level list written at the wrong parameter is caught. -/
inductive UA (α : Type u) (β : Type v) : Type (max u v) where
  | mk : α → UB α β → UA α β
inductive UB (α : Type u) (β : Type v) : Type (max u v) where
  | mk : β → UC α β → UB α β
inductive UC (α : Type u) (β : Type v) : Type (max u v) where
  | done : UC α β
  | more : UA α β → UC α β
end

def aOfB (b : B) : A := A.aB b
def cOfA (a : A) : C := C.cA a
def cFun (f : N → A) : C := C.cf f
def paNode (α β : Type) (b : PB α β) : PA α β := PA.node b
def pbWrap (α β : Type) (b : β) (c : PC α β) : PB α β := PB.wrap b c
def ucMore (α : Type u) (β : Type v) (a : UA α β) : UC α β := UC.more a
