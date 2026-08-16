import InductiveModels.Format

/-!
# Binder and record tables shared by the structural checks

The exact `forall` telescope kit and the two whole-export record views every
later part reuses.  `openForalls`/`closeForalls` open a telescope onto free
variables tagged by declaration name, so the same binder can be recognized
after substitution without asking Lean for anything.

These names are the internal interface between the `Check` parts rather than
the checker's public API; they were file-private while the checker was one
file and are module-visible now for exactly the same reason.
-/

open Lean

namespace InductiveModels.Check

structure OpenBinder where
  name : Name
  type : Expr
  info : BinderInfo
  value : Expr

partial def openForalls (tag : Name) (expression : Expr) : Array OpenBinder × Expr :=
  let rec loop (expression : Expr) (binders : Array OpenBinder) :=
    match expression with
    | .forallE name type body info =>
      let value := mkFVar (FVarId.mk (tag.mkNum binders.size))
      loop (body.instantiate1 value) (binders.push { name, type, info, value })
    | body => (binders, body)
  loop expression #[]

def closeForalls (binders : Array OpenBinder) (body : Expr) : Expr :=
  binders.reverse.foldl (fun body binder =>
    .forallE binder.name binder.type (body.abstract #[binder.value]) binder.info) body

abbrev Constructors := Lean.PersistentHashMap Name ECtor

abbrev StructureOwners := Lean.PersistentHashMap Name (EIndType × List ECtor)

def constructorRecords (x : Export) : Constructors := Id.run do
  let mut result : Constructors := {}
  for declaration in x.decls do
    if let .induct _ constructors _ := declaration then
      for constructor in constructors do result := result.insert constructor.name constructor
  return result

def structureOwners (x : Export) : StructureOwners := Id.run do
  let mut result : StructureOwners := {}
  for declaration in x.decls do
    if let .induct types constructors _ := declaration then
      for type in types do result := result.insert type.name (type, constructors)
  return result

end InductiveModels.Check
