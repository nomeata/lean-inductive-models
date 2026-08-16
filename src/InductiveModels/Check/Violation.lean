import InductiveModels.Naming

/-!
# The structural checker's diagnostic vocabulary

The violation alphabet, the export-level declaration kinds it names, and the
two report shapes the checker returns.  Nothing here inspects an export: this
module is the floor every other `Check` part reports against, and it therefore
depends only on [`InductiveModels.Naming`] for the metadata slot kinds.
-/

open Lean

namespace InductiveModels.Check

/-- The export-level declaration kind relevant to the public model contract. -/
inductive DeclarationKind where
  | axiom
  | defn
  | thm
  | opaq
  | quotient
  | induct
  | ctor
  | recursor
  deriving Inhabited, Repr, BEq

/-- A structural model-contract violation. -/
inductive Violation where
  /-- A model declaration is at or after its owner's inductive record. -/
  | modelNotBefore (owner declaration : Name) (modelDecl ownerDecl : Nat)
  /-- The owner's inductive record refers back to a declaration of its model. -/
  | ownerBackreference (owner target : Name)
  /-- An expected public declaration or reduction theorem is absent. -/
  | missingPublic (owner expected : Name)
  /-- A required public declaration or reduction theorem occurs more than once. -/
  | duplicatePublic (owner expected : Name) (count : Nat)
  /-- Legacy diagnostic retained for API compatibility.  Exact declaration-local
  naming has no syntactic "extra constructor slot" class. -/
  | extraConstructor (owner declaration : Name)
  /-- A direct intrinsic projection slot has no kernel-valid field index. -/
  | extraProjection (owner declaration : Name)
  /-- A direct `R._model.iota_j` theorem has no exported rule `j` of `R`. -/
  | extraRule (owner declaration : Name)
  /-- A direct metadata theorem is present although its owner lacks the kernel
  feature named by the theorem slot. -/
  | extraMetadata (owner declaration : Name) (kind : Naming.MetadataKind)
  /-- The two declarations do not carry equally many positional universes. -/
  | universeArity (owner declaration : Name) (ownerArity modelArity : Nat)
  /-- The exported declaration types differ after the exact permitted rewrite. -/
  | declarationType (owner declaration : Name)
  /-- A public model slot uses the wrong export-level declaration kind. -/
  | declarationKind (owner declaration : Name) (expected actual : DeclarationKind)
  /-- A public implementation definition is not marked exactly `safe`. -/
  | declarationSafety (owner declaration : Name) (actual : String)
  deriving Repr, BEq

/-- Stable text for a structural violation, shared by the CLI and the
generation-time syntactic oracle. -/
def Violation.message : Violation → String
  | .modelNotBefore owner declaration modelDecl ownerDecl =>
      s!"model declaration {declaration} at record {modelDecl} is not before \
        {owner} at record {ownerDecl}"
  | .ownerBackreference owner target =>
      s!"modeled inductive {owner} refers back to {target}"
  | .missingPublic owner expected =>
      s!"model of {owner} is missing {expected}"
  | .duplicatePublic owner expected count =>
      s!"model of {owner} declares {expected} {count} times"
  | .extraConstructor owner declaration =>
      s!"model of {owner} has an unexpected constructor declaration {declaration}"
  | .extraProjection owner declaration =>
      s!"model of {owner} has an unexpected intrinsic projection declaration {declaration}"
  | .extraRule owner declaration =>
      s!"model recursor {owner} has an unexpected reduction theorem {declaration}"
  | .extraMetadata owner declaration kind =>
      s!"model of {owner} has unexpected {repr kind} metadata {declaration}"
  | .universeArity owner declaration ownerArity modelArity =>
      s!"{declaration}, modeling {owner}, has {modelArity} universe parameters; \
        expected {ownerArity}"
  | .declarationType owner declaration =>
      s!"type of {declaration} does not literally model the type of {owner}"
  | .declarationKind owner declaration expected actual =>
      s!"{declaration}, modeling {owner}, is a {repr actual}; expected a {repr expected}"
  | .declarationSafety owner declaration actual =>
      s!"{declaration}, modeling {owner}, has safety {actual}; expected safe"

/-- The owner named by a diagnostic, for callers checking one family in a
larger export. -/
def Violation.familyOwner : Violation → Name
  | .modelNotBefore owner .. | .ownerBackreference owner .. |
      .missingPublic owner .. | .duplicatePublic owner .. |
      .extraConstructor owner .. | .extraProjection owner .. |
      .extraRule owner .. | .extraMetadata owner .. |
      .universeArity owner .. |
      .declarationType owner .. | .declarationKind owner .. |
      .declarationSafety owner .. => owner

/-- The observable result of one complete structural check.  `familiesChecked`
counts the exact public model families discovered in the checked export; it is
reported separately from violations so successful command-line checks can
show that they inspected a nonempty serialized model interface. -/
structure Report where
  familiesChecked : Nat
  violations : Array Violation
  deriving Inhabited, Repr, BEq

/-- Exact public-interface comparison without an environment or an ordering
assumption.  This is the generation oracle: all expected declarations and
theorems are reconstructed from the serialized owner records.  The separate
ordering checker remains responsible for model-before-owner and owner
backreference invariants. -/
structure StatementReport where
  statementsChecked : Nat
  violations : Array Violation
  deriving Inhabited, Repr, BEq

end InductiveModels.Check
