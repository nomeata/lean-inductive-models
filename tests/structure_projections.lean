/-
Focused structure-projection shapes.

`Dep.payload` depends on `Dep.key`, and `Dep.witness` depends on both earlier
fields.  This pins the literal projection substitution in the generated types:
the latter two model declarations must name the earlier projection models,
not the source projections and not the model carrier's representation.

The focused Lean test also rewrites this block to deterministic raw private
names.  Doing that after parsing avoids putting lean4export's scratch-path
component into the checked-in fixture.
-/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

structure Dep (α : Type u) (β : α → Type v) : Type (max u v) where
  key : α
  payload : β key
  witness : (x : β key) → Eq x payload

/-- Universe-inference probes for projection rules: a sort-valued field, a
function-valued field, a dependent field whose type contains a preceding
projection, and a result written through a `let`. -/
structure SortFields (α : Type u) : Type (max (u + 1) (v + 1)) where
  carrier : Type v
  family : α → Type v
  element : carrier
  letCarrier : (let X := Type v; X)

/-- Raw kernel projections also support indexed one-constructor families. -/
inductive Indexed (α : Type u) : α → Type u where
  | mk (index payload : α) : Indexed α index

/-- Raw kernel projections also support recursive one-constructor families. -/
inductive Recursive (α : Type u) : Type u where
  | roll (head : α) (tail : Recursive α) : Recursive α

/-- Neither field is kernel-projectable: the selected data field is not a
proposition, and the later proof field depends on that data field. -/
inductive PropDependent (α : Type u) : Prop where
  | mk (data : α) (proof : Eq data data) : PropDependent α

/-- More than one constructor rules out every raw kernel projection. -/
inductive Multi (α : Type u) : Type u where
  | left (value : α)
  | right (value : α)

def depKey (α : Type u) (β : α → Type v) (x : Dep α β) : α := x.key

def depPayload (α : Type u) (β : α → Type v) (x : Dep α β) : β x.key :=
  x.payload

def depWitness (α : Type u) (β : α → Type v) (x : Dep α β) :
    (y : β x.key) → Eq y x.payload :=
  x.witness

-- Keep the projection declarations themselves in the filtered export.  The
-- use sites above retain the owners and make accidental projection erasure
-- visible as a dependency-order failure.
--#export Eq Dep Dep.key Dep.payload Dep.witness SortFields SortFields.carrier
--#export SortFields.family SortFields.element SortFields.letCarrier
--#export depKey depPayload depWitness
--#export Indexed Recursive PropDependent Multi
