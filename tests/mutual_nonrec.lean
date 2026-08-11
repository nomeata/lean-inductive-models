/- **A mutual block with a member that recurses into nothing**, which is three
   different things at once and one upstream wrinkle.

   `isRec` is a property of the **block** and Lean sets it for the whole block,
   so a member none of whose constructors mentions a member in a binder type is
   still part of a recursive block. Everything in this file has one.

   * `OA`/`OB`/`OC` — **only one member is recursive**. `OB` has two nullary
     constructors and `OC` mentions `OB` and nothing else; only `OA` recurses.
     Two members cannot separate a per-member treatment from a shared one here,
     because with `OA`/`OB` the non-recursive member is also the only other
     member; `OC` is the third that makes "some members, not all" visible.
     `mini/tests/fixtures/mutual_one_recursive.lean` is the same shape.
   * `EA`/`EB`/`EC` — a member with **no constructors at all**. The tag then has
     a constructor no `aux` constructor ever mentions, `EB.rec` has no rules,
     and `EB._model.self` is the carrier of an empty type. A generator that
     indexed the ι theorems off the flattened constructor list rather than off
     each recursor's *own* rules gets the wrong ones here.
   * `Ka`/`Kb` — `Ka : Prop | mk : Ka` is the shape Lean gives a **K-rule** to
     when it stands alone; being in a block is the only reason it does not get
     one. The auxiliary inductive does not get one either, and for a different
     reason: `T._model.aux` always carries the tag as an *index*, and an indexed
     inductive is never K-like. So a generator that copied the block's `k` flag
     onto the aux recursor would be wrong here and nowhere else in the tree.

   **`nanoda_bin` will not load this file, and that is upstream's and not this
   tool's.** `checker/src/inductive.rs:30` recomputes `isRec` **per member** by
   scanning that member's constructors for a binder type mentioning any name in
   the block, where Lean sets it for the whole block — so `OB`, `EB`, `EC` and
   `Ka` each make the assert fire. It fires on the **input** too, before this
   tool has written anything: `MODELGEN.md` §4 names the four fixtures in
   `mini/tests/fixtures` with the same property. This file is deliberately the
   one that carries the shape, so that the three fixtures beside it stay
   loadable. -/
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

--#export Eq N OA OB OC EA EB EC Ka Kb
--#export oaSelf oaFromB ocFromB eaOfC kbMk

mutual
/-- The only recursive member. -/
inductive OA : Type where
  | fromB : OB → OA
  | self : OA → OA
/-- No constructor of this one mentions a member of the block. -/
inductive OB : Type where
  | b0 : OB
  | b1 : OB
/-- Mentions `OB`, so it is not recursive either. -/
inductive OC : Type where
  | fromB : OB → OC
end

mutual
/-- Recursive, through a member that has no values. -/
inductive EA : Type where
  | a0 : EA
  | ofC : EC → EA
/-- **No constructors.** -/
inductive EB : Type where
/-- One, and it does not mention `EB`. -/
inductive EC : Type where
  | c0 : EC
end

mutual
/-- Nullary, so on its own it would get a K-rule. -/
inductive Ka : Prop where
  | mk : Ka
inductive Kb : Prop where
  | mk : Ka → Kb
end

def oaSelf (a : OA) : OA := OA.self a
def oaFromB (b : OB) : OA := OA.fromB b
def ocFromB (b : OB) : OC := OC.fromB b
def eaOfC (c : EC) : EA := EA.ofC c
def kbMk (a : Ka) : Kb := Kb.mk a
