/- **A `Prop`-valued mutual block, and the two elimination questions it asks.**

   A block of several members never supports large elimination, so its
   recursors carry **no motive universe at all** and every level list the model
   writes is the declaration's own. That is one question. The other is about
   the *auxiliary* inductive: the encoding replaces `r` members by **one**
   inductive, and one `Prop`-valued inductive may support large elimination
   where the block it came from could not. So the level list handed to
   `T._model.aux.rec` is read off that recursor rather than off the block's, and
   these three blocks are what makes the two answers differ.

   * `Even`/`Odd` — the ordinary indexed `Prop` family. `Even.rec` and
     `Odd.rec` have one level parameter list between them and it is empty.
   * `M0`/`M1`/`M2` — the same at three members, so the motive vector is not a
     pair.
   * `Sa`/`Sb` — **unindexed** `Prop`s, where `Sa` has a single constructor
     whose only field is a proof. On its own `Sa` is exactly the shape
     `elimToSort` gives large elimination to; being in a block is the only
     reason it does not get it. The auxiliary inductive has three constructors
     and so does not get it either, which is the case where block and aux agree
     by accident.

   `Ka`/`Kb`, the **K-rule** shape, is in `mutual_nonrec.lean` and not here:
   `Ka.mk : Ka` recurses into nothing, which is the axis that file is about. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive PUnit : Sort u where
  | unit : PUnit

structure PProd (α : Sort u) (β : Sort v) where
  fst : α
  snd : β

--#export Eq N Even Odd M0 M1 M2 Sa Sb
--#export evenSucc oddSucc m0Succ saMk sbMk1

mutual
inductive Even : N → Prop where
  | zero : Even N.z
  | succ : (n : N) → Odd n → Even (N.s n)
inductive Odd : N → Prop where
  | succ : (n : N) → Even n → Odd (N.s n)
end

mutual
inductive M0 : N → Prop where
  | zero : M0 N.z
  | succ : (n : N) → M2 n → M0 (N.s n)
inductive M1 : N → Prop where
  | succ : (n : N) → M0 n → M1 (N.s n)
inductive M2 : N → Prop where
  | succ : (n : N) → M1 n → M2 (N.s n)
end

mutual
/-- One constructor, one field, and that field is a proof. -/
inductive Sa : Prop where
  | mk : Sb → Sa
inductive Sb : Prop where
  | mk0 : Sb
  | mk1 : Sa → Sb
end

def evenSucc (n : N) (h : Odd n) : Even (N.s n) := Even.succ n h
def oddSucc (n : N) (h : Even n) : Odd (N.s n) := Odd.succ n h
def m0Succ (n : N) (h : M2 n) : M0 (N.s n) := M0.succ n h
def saMk (b : Sb) : Sa := Sa.mk b
def sbMk1 (a : Sa) : Sb := Sb.mk1 a
