/-
One-constructor indexed `Type` boundaries for the one-layer fibre adapter.

`IndexedDep` in `structure_projections.lean` is the positive target.  This
fixture isolates the fail-closed edge: a proposed result index syntactically
mentions a recursive constructor field, although reduction erases that
dependency.  Lean rejects that return type before export.  The accepted
control immediately below keeps the result index independent of the moved
field; an adapter classifier must preserve this boundary rather than invent a
meaning for the rejected declaration.
-/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {alpha : Sort u} -> alpha -> alpha -> Prop where
  | refl (a : alpha) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive FibreIx : Type where
  | here
  | elsewhere

inductive FibreKey : Type where
  | key

inductive FibrePayload : FibreKey -> Type where
  | at (key : FibreKey) : FibrePayload key

axiom RecursiveWitness {alpha : Type u} (_ : alpha) : Type u

/-- Transparent application former used to keep a recursive occurrence
syntactically non-bare while remaining kernel-positive. -/
def TransparentOwnerAlias (owner : FibreIx -> Type u) (index : FibreIx) : Type u :=
  owner index

/-- Zero-field indexed `Type`: its malformed certificate must be diagnosed at
the family boundary even though there is no intrinsic projection loop. -/
inductive IndexedUnit : FibreIx -> Type where
  | mk : IndexedUnit FibreIx.here

/-- Reducible result former intentionally hidden in serialized syntax.  The
generator and checker must both leave this owner on the legacy route. -/
def HiddenIndexedResult (index : FibreIx) := Type

inductive HiddenIndexed : (index : FibreIx) -> HiddenIndexedResult index where
  | mk : HiddenIndexed FibreIx.here

/-- This reducible function makes the source declaration kernel-valid while
retaining the recursive field in the exported result-index syntax. -/
def erasedResultIndex {alpha : Sort u} (_ : alpha) : FibreIx :=
  FibreIx.here

/- The companion `IndexedFibreDiagnosticTest` compile-checks the rejected
declaration under `#guard_msgs`; prelude-only exporter fixtures deliberately
do not import that test command. -/

/-- Nearest exportable control: the recursive field is moved by a one-layer
adapter, but the constructor result is visibly independent of that field. -/
inductive FixedRecursiveResult : FibreIx -> Type where
  | mk (child : FixedRecursiveResult FibreIx.here) :
      FixedRecursiveResult FibreIx.here

/-- Positive recursive fibre boundary.  The dependent ordinary field exposes
whether the adapter makes an earlier projection reduce definitionally; the
single recursive child has a fixed, source-visible result index. -/
inductive IndexedRecursiveLayer : FibreIx -> Type where
  | mk (key : FibreKey)
      (payload : Eq.rec (motive := fun _ _ => Type)
        (FibrePayload key) (Eq.refl (FibrePayload key)))
      (child : IndexedRecursiveLayer FibreIx.here) (tail : FibreKey) :
      IndexedRecursiveLayer FibreIx.here

/-- The same boundary with parameters and distinct source universes. -/
inductive ParametricRecursiveLayer (alpha : Type u) (beta : alpha -> Type v) :
    FibreIx -> Type (max u v) where
  | mk (key : alpha) (payload : beta key)
      (child : ParametricRecursiveLayer alpha beta FibreIx.here) (tail : alpha) :
      ParametricRecursiveLayer alpha beta FibreIx.here

/-- Two direct fixed-fibre children form the next bounded certificate tranche. -/
inductive TwoRecursiveResults : FibreIx -> Type where
  | mk (left right : TwoRecursiveResults FibreIx.here) :
      TwoRecursiveResults FibreIx.here

/-- Two fixed recursive children beside the same dependent ordinary prefix as
`IndexedRecursiveLayer`.  This makes the two-child certificate observable:
the payload rule must retain the source-authored transport but acquire no
additional projection transport. -/
inductive TwoRecursiveDependentResults : FibreIx -> Type where
  | mk (key : FibreKey)
      (payload : Eq.rec (motive := fun _ _ => Type)
        (FibrePayload key) (Eq.refl (FibrePayload key)))
      (left right : TwoRecursiveDependentResults FibreIx.here) (tail : FibreKey) :
      TwoRecursiveDependentResults FibreIx.here

/-- Three otherwise identical direct children.  `roll`/`unroll` are the
identity and their laws are reflexivity, so each child's rule is settled on its
own and the certificate never counts them; this is the occupant that would
notice a count reappearing. -/
inductive ThreeRecursiveResults : FibreIx -> Type where
  | mk (first second third : ThreeRecursiveResults FibreIx.here) :
      ThreeRecursiveResults FibreIx.here

/-- Recursion below a function former remains outside the direct-field
tranche even though the constructor result index is fixed. -/
inductive InfinitaryRecursiveResult : FibreIx -> Type where
  | mk (children : FibreIx -> InfinitaryRecursiveResult FibreIx.here) :
      InfinitaryRecursiveResult FibreIx.here

/-- A recursive occurrence indexed by an ordinary constructor field.  The
child's index reads field 0, whose selector is reflexive, so the child's own
projection rule is still the literal field.  Only a field depending on a
*recursive* field would need transport, and Lean has no spelling for that. -/
inductive FieldIndexedRecursiveResult : FibreIx -> Type where
  | mk (index : FibreIx) (child : FieldIndexedRecursiveResult index) :
      FieldIndexedRecursiveResult FibreIx.here

/-- A transparent former around the owner is not a bare recursive field in
the serialized contract and therefore remains legacy. -/
inductive TransparentRecursiveResult : FibreIx -> Type where
  | mk (child : TransparentOwnerAlias TransparentRecursiveResult FibreIx.here) :
      TransparentRecursiveResult FibreIx.here

--#export Eq FibreIx FibreKey FibrePayload RecursiveWitness TransparentOwnerAlias
--#export IndexedUnit HiddenIndexedResult HiddenIndexed erasedResultIndex
--#export FixedRecursiveResult IndexedRecursiveLayer ParametricRecursiveLayer
--#export TwoRecursiveResults TwoRecursiveDependentResults
--#export ThreeRecursiveResults
--#export InfinitaryRecursiveResult FieldIndexedRecursiveResult
--#export TransparentRecursiveResult
