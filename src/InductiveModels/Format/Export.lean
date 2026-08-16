import InductiveModels.Format.Types
/-!
# The whole-export record and its primitive-projection view

`Export` itself, its declaration-name validator, and the syntactic recovery of
Lean's primitive structure projections from exported values.
-/
open Lean

namespace InductiveModels

/-- A whole export: the `meta` line verbatim, then the declarations in order. -/
structure Export where
  metaLine : Json
  decls : Array EDecl
  deriving Inhabited

/-- Declaration names are semantic export identities. The library parsers use
this validator by default; the CLI may defer it until after syntactic parsing
so a collision is reported as a rejected export rather than a parser crash. -/
def Export.validateUniqueDeclarationNames (x : Export) : Except String Unit := do
  let mut names : Std.HashSet Name := {}
  for declaration in x.decls do
    for name in declaration.names do
      if names.contains name then throw s!"duplicate declaration {name}"
      names := names.insert name

/-! ## Recovering primitive structure projections

The export format has no record for Lean's projection-function or structure
environment extensions.  What survives is the kernel object itself: a
projection declaration is an ordinary definition (or theorem/opaque
declaration for proof/unsafe fields) whose value is a lambda telescope ending
in `Expr.proj owner fieldIndex self`.

The view below retains exact raw names.  In particular, a private projection's
leading `_private` components are data, not a namespace convention to erase.
-/

/-- A primitive projection declaration recovered from its exported value. -/
structure EProjection where
  name : Name
  levelParams : List Name
  type : Expr
  value : Expr
  owner : Name
  fieldIndex : Nat
  /-- Number of lambdas in the exported projection value, including `self`. -/
  numArguments : Nat
  /-- The declaration-record position, retained for ordering tests/checks. -/
  declIndex : Nat
  deriving Inhabited, BEq

private partial def stripProjectionMData : Expr → Expr
  | .mdata _ body => stripProjectionMData body
  | expression => expression

private partial def projectionBody? (value : Expr) : Option (Name × Nat × Nat) :=
  let rec visit (expression : Expr) (numArguments : Nat) :=
    match stripProjectionMData expression with
    | .lam _ _ body _ => visit body (numArguments + 1)
    | .proj owner fieldIndex struct =>
      if stripProjectionMData struct == .bvar 0 && numArguments > 0 then
        some (owner, fieldIndex, numArguments)
      else
        none
    | _ => none
  visit value 0

/-- View one ordinary export record as a primitive projection declaration.

This intentionally recognizes the kernel expression, not a generated-name
suffix.  A declaration that is observationally the same primitive projection
has the same view; the export has discarded the elaborator extension that
could distinguish two such definitions. -/
def EDecl.projection? (declIndex : Nat) : EDecl → Option EProjection
  | .defn name levelParams type value .. |
    .thm name levelParams type value .. |
    .opaq name levelParams type value .. => do
      let (owner, fieldIndex, numArguments) ← projectionBody? value
      return { name, levelParams, type, value, owner, fieldIndex, numArguments, declIndex }
  | _ => none

/-- Whole-export projection prepass, in source declaration order. -/
def Export.projections (x : Export) : Array EProjection := Id.run do
  let mut projections := #[]
  for index in [0:x.decls.size] do
    if let some projection := x.decls[index]!.projection? index then
      projections := projections.push projection
  return projections

/-- Exact primitive projections whose kernel projection names `owner`. -/
def Export.projectionsFor (x : Export) (owner : Name) : Array EProjection :=
  x.projections.filter (·.owner == owner)

end InductiveModels
