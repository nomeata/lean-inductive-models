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
      (payload : Eq.rec (motive := fun _ _ => Type v)
        (beta key) (Eq.refl (beta key))) : MutualLayerA alpha beta
inductive MutualLayerB (alpha : Type u) (beta : alpha -> Type v) : Type (max u v) where
  | stop : MutualLayerB alpha beta
  | back (parent : MutualLayerA alpha beta) : MutualLayerB alpha beta
end

/-
The same boundary at more than one recursive field per constructor.
`MutualBranchA.mk` crosses to the sibling twice and recurses into itself once,
so its ι rule needs three independent equality eliminations while the sibling
needs one.

**This pair does not pin the arity of that construction, and the claim that it
does was never true.**  `InductiveModels.oneLayerNaryCompatibility` is reached
here at three fields — but the mutual adapter requires its `roll` to agree with
the private constructor *definitionally*
(`MutualOneLayer.lean`'s "roll compatibility is not definitional"), so every
field step in the chain collapses and a chain capped at two fields still checks.
What used to go red at such a cap was `prim_w`, whose owners rolled through a
real private carrier under the direct one-layer adapter.  That adapter has been
withdrawn and the mutual one is now the chain's only caller, with the same
definitional collapse at every owner it takes, so **an arity cap in the chain is
red nowhere in the corpus** — capping the chain's loop at two field steps leaves
`test/scripts/run-correctness.sh` entirely green.  What this pair pins is
the *adapter* past one recursive field per constructor — the member certificate,
the checker's independent agreement — and not the compatibility proof's arity.
That is a gap in this fixture rather than in the construction, and it is
unrelated to `MutualBranchA`'s erasure skeleton having moved from arm W to arm E
(the same cap is accepted with arm E disabled).
-/
mutual
inductive MutualBranchA : Type where
  | mk (left : MutualBranchB) (mid : MutualBranchA) (right : MutualBranchB) :
      MutualBranchA
inductive MutualBranchB : Type where
  | wrap (inner : MutualBranchA) : MutualBranchB
end

--#export Eq MutualLayerA MutualLayerB MutualBranchA MutualBranchB
