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
so its rule reaches three round trips at three different fields while the
sibling's reaches one.

**This pair does not pin the arity of any proof, and the claim that it did was
never true.**  `MutualBranchA.mk`'s rule is `Eq.refl`, and so is the sibling's,
and so is a rule at six recursive fields: the adapter's `unroll_roll` is the
private family's ι rule — an `Eq.refl` — at the public tower's projections, so
`unroll (roll pᵢ)` is definitionally `pᵢ` for every member it publishes, and
proof irrelevance collapses every path any of these rules could transport
along.  There used to be an n-ary compatibility construction here, folding one
equality elimination per recursive field, and this pair was said to pin its
arity; capping that fold at two fields left the whole suite green, because no
step it took was ever between distinct endpoints.  The construction has been
withdrawn and the rules state their reflexivity directly, guarded by the
`isDefEq` that refuses the rule by name, `is not definitional`, if a round trip
ever stops being one.

What this pair pins is the *adapter* past one recursive field per constructor:
the member certificate, the minor layout read off the public minor's own
binders, the checker's independent agreement, and — now — that the reflexivity
guard holds at three fields with two of them crossing to a sibling.  It is
unrelated to `MutualBranchA`'s erasure skeleton having moved from arm W to arm
E.
-/
mutual
inductive MutualBranchA : Type where
  | mk (left : MutualBranchB) (mid : MutualBranchA) (right : MutualBranchB) :
      MutualBranchA
inductive MutualBranchB : Type where
  | wrap (inner : MutualBranchA) : MutualBranchB
end

--#export Eq MutualLayerA MutualLayerB MutualBranchA MutualBranchB
