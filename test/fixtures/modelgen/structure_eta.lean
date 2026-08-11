/-
Focused kernel structure-eta shapes.

`EtaDependent` supplies the ordinary named-projection contract, while
`EtaBare` is structure-like without any elaborator-generated projection
declarations.  The two independent members in the mutual block pin the fact
that structure-likeness and eta are per member, not properties of a group.

The final four declarations are the nearest misses for the kernel predicate.
In particular, a proposition-valued one-constructor family is deliberately a
miss: proof irrelevance handles it before the kernel's structure-eta path, and
Lean's constructor eta expansion explicitly skips propositions.
-/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {alpha : Sort u} → alpha → alpha → Prop where
  | refl (value : alpha) : Eq value value

/-- Zero fields, no source projection declarations. -/
inductive EtaZero : Type where
  | mk : EtaZero

/-- Named projections with a dependency on the preceding field. -/
structure EtaDependent (alpha : Type u) (family : alpha → Type v) :
    Type (max u v) where
  key : alpha
  payload : family key
  witness : Eq payload payload

/-- Kernel structure-like, but declared as an inductive and hence without P names. -/
inductive EtaBare (alpha : Type u) : Type u where
  | mk (value : alpha) (witness : Eq value value) : EtaBare alpha

/-- Independent mutual structures: both members have kernel eta. -/
mutual
structure EtaMutualLeft (alpha : Type u) : Type u where
  value : alpha
structure EtaMutualRight (alpha : Type u) : Type u where
  value : alpha
  witness : Eq value value
end

/-- Proof irrelevance, rather than the structure-eta reduction path. -/
structure EtaProposition (proposition : Prop) : Prop where
  proof : proposition

/-- One constructor, but an index excludes structure eta. -/
inductive EtaIndexed (alpha : Type u) : alpha → Type u where
  | mk (value : alpha) : EtaIndexed alpha value

/-- One constructor and no indices, but recursive. -/
inductive EtaRecursive : Type where
  | mk (next : EtaRecursive) : EtaRecursive

/-- Non-recursive and index-free, but not single-constructor. -/
inductive EtaTwo : Type where
  | left : EtaTwo
  | right : EtaTwo

--#export Eq EtaZero EtaDependent EtaDependent.key EtaDependent.payload
--#export EtaDependent.witness EtaBare
--#export EtaMutualLeft EtaMutualLeft.value EtaMutualRight EtaMutualRight.value
--#export EtaMutualRight.witness EtaProposition EtaProposition.proof
--#export EtaIndexed EtaRecursive EtaTwo
