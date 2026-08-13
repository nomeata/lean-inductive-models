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

universe u

inductive Eq : {alpha : Sort u} -> alpha -> alpha -> Prop where
  | refl (a : alpha) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive FibreIx : Type where
  | here
  | elsewhere

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

--#export Eq FibreIx erasedResultIndex FixedRecursiveResult
