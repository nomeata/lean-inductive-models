/-
The smallest plain-mutual SCC that separates a partial one-layer family from
the existing all-members mutual carrier.

`MutualLayerA` has one constructor and therefore three intrinsic projections.
Its recursive field crosses to `MutualLayerB`; its final payload depends only
on the ordinary key. `MutualLayerB.back` closes the SCC, while its `stop`
constructor makes that sibling deliberately multi-constructor and therefore
projection-ineligible. A partial family adapter should change only `A`'s
carrier and treat `B` as an identity member without changing `B`'s public
constructor/recursor family.
-/
prelude

universe u v

inductive Eq : {alpha : Sort u} -> alpha -> alpha -> Prop where
  | refl (a : alpha) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

mutual
inductive MutualLayerA (alpha : Type u) (beta : alpha -> Type v) : Type (max u v) where
  | mk (key : alpha) (child : MutualLayerB alpha beta)
      (payload : (fun selected => beta selected) key) : MutualLayerA alpha beta
inductive MutualLayerB (alpha : Type u) (beta : alpha -> Type v) : Type (max u v) where
  | stop : MutualLayerB alpha beta
  | back (parent : MutualLayerA alpha beta) : MutualLayerB alpha beta
end

--#export Eq MutualLayerA MutualLayerB
