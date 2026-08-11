/- **`Expr.proj` carries the structure's name but not its level arguments.**

   Lean's own `inferProjType` rejects a projection whose name is not the head of
   the projected term's inferred type, so the name has to move to the right
   copy — and *which* copy is only recoverable by inferring that type. On a file
   where every projected structure has one copy the axis is the identity, which
   is why `P.{u,v}` is projected at **three** instantiations here, two of them
   the same two atoms in opposite orders. -/
prelude

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

structure P (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  fst : α
  snd : β

--#export useA useB useC

def useA (p : P.{1,1} N N) : N := p.fst
def useB (p : P.{1,2} N Type) : N := p.fst
noncomputable def useC (p : P.{2,1} Type N) : N := p.snd
