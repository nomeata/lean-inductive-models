/-
The plain-mutual one-layer boundary at a carrier level that is **never zero
without being a successor**.

`mutual_one_layer_boundary`'s owners are at `Type`, so their carriers sit at a
`succ`; this pair sits at `max 1 u` instead, which is the same never-zero
tranche and no successor at all.  Everything the adapter builds here is
level-generic — the tower, both maps, the certificate's two laws — and the ι
rules it publishes are `Eq.refl`, exactly as at `Type`.

That is the point of the fixture.  The rules used to be assembled by an n-ary
compatibility construction whose lemmas were *stated* at `{M P : Type u}`, so
this shape did not reach a decline: it reached those lemmas and failed to
apply, and the tool refused the whole export with an application type mismatch.
The construction has been withdrawn — every step it took was between
definitionally equal endpoints — and a rule that states its own reflexivity
carries no universe of its own to disagree about.  So this pair pins reach and
not only shape: it is a family the adapter could not publish before and can
now, and it is the corpus's only mutual one-layer owner off `Type`.
-/
prelude

universe u

inductive Eq : {alpha : Sort u} -> alpha -> alpha -> Prop where
  | refl (a : alpha) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

mutual
inductive LevelLayerA (alpha : Sort (max 1 u)) : Sort (max 1 u) where
  | mk (left : LevelLayerB alpha) (mid : LevelLayerA alpha) : LevelLayerA alpha
inductive LevelLayerB (alpha : Sort (max 1 u)) : Sort (max 1 u) where
  | wrap (inner : LevelLayerA alpha) (payload : alpha) : LevelLayerB alpha
end

--#export Eq LevelLayerA LevelLayerB
