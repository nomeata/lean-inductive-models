prelude

set_option bootstrap.inductiveCheckResultingUniverse false

/-!
Exact-syntax controls just outside the first Prop literal-projection tranche.

`NestedProp` nests through a proposition-valued container. `MutualPropA` and
`MutualPropB` form a plain recursive mutual block. Their dependent field
domains retain a head beta-redex and default wrapper, so treating an installed
constructor telescope as exact source syntax is observably wrong.
-/

universe u

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

@[reducible] def optParam (α : Sort u) (_default : α) : Sort u := α

inductive PUnit : Sort u where
  | unit : PUnit

inductive PBox (α : Prop) : Prop where
  | mk : α → PBox α

inductive NestedProp (a : Prop) (b : a → Prop) (defaultB : (ha : a) → b ha) :
    Prop where
  | mk (ha : a) (hb : (fun proof => b proof) ha := defaultB ha)
      (tail : PBox (NestedProp a b defaultB)) : NestedProp a b defaultB

mutual
inductive MutualPropA (a : Prop) (b : a → Prop) (defaultB : (ha : a) → b ha) :
    Prop where
  | mk (ha : a) (hb : (fun proof => b proof) ha := defaultB ha)
      (tail : MutualPropB a b defaultB) : MutualPropA a b defaultB
inductive MutualPropB (a : Prop) (b : a → Prop) (defaultB : (ha : a) → b ha) :
    Prop where
  | mk (tail : MutualPropA a b defaultB) : MutualPropB a b defaultB
end

--#export Eq optParam PUnit PBox NestedProp MutualPropA MutualPropB
