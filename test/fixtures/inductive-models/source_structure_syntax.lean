/-
A source-owned structure whose exact export syntax crosses all of the simple
structure adapters: an inherited projection occurs in dependent field types,
and the final field carries a default.  The model generator must preserve the
raw owner, constructor, recursor, intrinsic projection, and projection-iota
statements even though the kernel stores normalized metadata for the block.
-/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

def id (alpha : Sort u) (value : alpha) : alpha := value

@[reducible] def optParam (alpha : Sort u) (default : alpha) : Sort u := alpha

@[reducible] def Wrapped (alpha : Sort u) : Sort u := alpha

inductive Eq : {alpha : Sort u} → alpha → alpha → Prop where
  | refl (value : alpha) : Eq value value

structure SourceParent (alpha : Wrapped (Type u)) where
  key : alpha

structure SourceStructure (alpha : Wrapped (Type u))
    (family : (fun domain => domain) (alpha → Type v))
    extends SourceParent alpha where
  betaField : (fun X : Type u => X) alpha
  payload : family toSourceParent.key
  witness : optParam (Eq payload payload) (Eq.refl payload)

--#export lcErased lcAny lcVoid id optParam Wrapped Eq SourceParent SourceParent.key SourceStructure
--#export SourceStructure.toSourceParent SourceStructure.payload SourceStructure.witness
