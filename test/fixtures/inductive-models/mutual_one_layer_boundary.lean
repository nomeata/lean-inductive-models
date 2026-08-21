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
here at three fields — but no field step it takes can fail to collapse, and the
reason is not the one recorded here before.  It is not the `roll`/private
constructor agreement the adapter checks for the *major*
(`MutualOneLayer.lean`'s "roll compatibility is not definitional"): that guard
says nothing about a *field*.  A field step eliminates that field's own
`unroll_roll`, and this adapter installs `unroll_roll` for every member as a
declaration of type `unroll (roll value) = value` whose value is the private
family's ι rule — which `Mutual.lean` emits as `Eq.refl` for every member of
every family it builds.  That declaration is part of the emitted model and is
checked at its kernel gate, which it can pass only where `unroll (roll value)`
is already definitionally `value`, so a member whose round trip is merely
propositional cannot survive in a family this adapter publishes; `Eq` is a
`Prop`, so proof irrelevance then identifies every path in the chain with
`Eq.refl` and every transport along one vanishes.  What used to go
red at such a cap was `prim_w`, whose owners rolled through a real private
carrier under the direct one-layer adapter.  That adapter has been withdrawn and
the mutual one is now the chain's only caller, so **an arity cap in the chain is
red nowhere in the corpus** — capping the chain's loop at two field steps leaves
`test/scripts/run-correctness.sh` entirely green, and so does dropping the chain
*and* the bridge outright and publishing `Eq.refl` for every ι rule this adapter
emits (measured over `fixtures`, `kernelcheck`, `mutualonelayerdiagnostic`,
`projectiontransportcensus`, `check` and the 182-declaration arena corpus, at
3.01G to 2.34G retired instructions on `mutualonelayerdiagnostic`, -22.3%).  No fixture closes
that gap, because it is the adapter's own `unroll_roll` that forbids the
non-collapsing input.  So what this pair pins is the *adapter* past one
recursive field per constructor — the member certificate, the checker's
independent agreement — and not the compatibility proof's arity.  That is a gap
in the construction's justification rather than in this fixture, and it is
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
