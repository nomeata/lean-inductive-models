/- **The DAG is over groups, not declarations.**

   A mutual inductive block's members, constructors and recursors mention one
   another cyclically, and a mutual `def` block's `all` field names records that
   have to keep pointing at each other. Both are one node of the walk and are
   emitted whole, at one shared instantiation. Used at **two** instantiations
   here, so "one copy per instantiation" and "rename" are not the same map, and
   `Fst`/`Snd` are asymmetric so a pass that mixed the two members up is
   visible. -/
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

mutual
inductive Fst (α : Type u) : Type u where
  | mk : α → Snd α → Fst α
inductive Snd (α : Type u) : Type u where
  | nil : Snd α
  | cons : Fst α → Snd α
end

--#export fstAt0 fstAt1 sndAt0

def fstAt0 (x : Fst.{0} N) : Fst.{0} N := x
def fstAt1 (x : Fst.{1} Type) : Fst.{1} Type := x
def sndAt0 (x : Snd.{0} N) : Snd.{0} N := x
