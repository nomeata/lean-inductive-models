import InductiveModels.Check.Index

/-!
# The generation-time statement oracle

Exact public-interface comparison without an environment or an ordering
assumption.  The separate ordering checker remains responsible for
model-before-owner and owner-backreference invariants.
-/

open Lean

namespace InductiveModels.Check

/-- Check one already-discovered family against reusable syntax tables.  This
is the island-sized form needed by compact generation: family-local interface
checks do not rebuild the source declaration, constructor, and rule indexes.
Global extra-slot diagnostics are retained only when they belong to this
family's exact source declarations. -/
def checkFamilyStatementsWithIndex (x : Export) (index : SyntaxIndex)
    (family : Family) : StatementReport :=
  let diagnosticOwners := family.correspondence.diagnosticOwners.foldl
    (fun result owner => result.insert owner) ({} : Std.HashSet Name)
  let global := index.globalExtras.filter fun violation =>
    diagnosticOwners.contains violation.familyOwner
  { statementsChecked := family.correspondence.statementCount
    violations := checkFamilyWithIndex x index family false ++ global }

/-- Batch only family-local statement diagnostics. Compact generation uses
this form for each island and leaves the whole-export unexpected-slot sweep to
the final aggregate pass, preserving its historical order and multiplicity. -/
def checkStatementFamiliesLocalWithIndex (x : Export) (index : SyntaxIndex)
    (families : Array Family) : StatementReport :=
  { statementsChecked := families.foldl
      (fun count family => count + family.correspondence.statementCount) 0
    violations := families.foldl (fun violations family =>
      violations ++ checkFamilyWithIndex x index family false) #[] }

/-- Batch a selected set of discovered families through one reusable index.
Unlike concatenating single-family reports, the global unexpected-slot sweep
runs once, retaining aggregate diagnostic order and multiplicity exactly. -/
def checkStatementFamiliesWithIndex (x : Export) (index : SyntaxIndex)
    (families : Array Family) : StatementReport :=
  let diagnosticOwners := families.foldl
    (fun result family => family.correspondence.diagnosticOwners.foldl
      (fun result owner => result.insert owner) result)
    ({} : Std.HashSet Name)
  let localReport := checkStatementFamiliesLocalWithIndex x index families
  let global := index.globalExtras.filter fun violation =>
    diagnosticOwners.contains violation.familyOwner
  { localReport with violations := localReport.violations ++ global }

def checkStatements (x : Export) : StatementReport :=
  let index := SyntaxIndex.ofExport x
  let families := discoverWithIndex x index
  { statementsChecked := families.foldl
      (fun count family => count + family.correspondence.statementCount) 0
    violations := checkFamiliesWithIndex x index families false }

/-- Generation-time view restricted to the families emitted by this run.
Pre-existing models in an already-filtered input remain available as exact
declaration dependencies, but do not inflate the run's work count or errors. -/
def checkStatementsFor (x : Export) (owners : Std.HashSet Name) : StatementReport :=
  let index := SyntaxIndex.ofExport x
  let families := statementFamiliesForWithIndex x index owners
  checkStatementFamiliesWithIndex x index families

/-- Compatibility view of [`checkReport`] for callers interested only in
violations. -/
def check (x : Export) : Array Violation :=
  (checkReport x).violations

end InductiveModels.Check
