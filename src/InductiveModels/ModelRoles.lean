import InductiveModels.Format
import InductiveModels.Naming

/-!
# Exact generated model roles

This module recovers the declaration-local public model role attached to an
exact exported name.  It is part of model inspection and structural testing;
it does not transform declarations or universe levels.
-/

open Lean

namespace InductiveModels.ModelRoles

/-- The exact public role of a generated model declaration. -/
inductive Role where
  | typeFormer
  | constructor
  | recursor
  | iota
  | unitlike
  | eta
  | ruleK
  | projection
  | projectionIota
  deriving BEq, Inhabited

/-- A generated public declaration and the original inductive record that owns
it. `owner` is read from that record, never recovered by splitting a generated
name. -/
structure Entry where
  owner : Name
  ownerDecl : Nat
  role : Role
  deriving Inhabited

abbrev Table := Std.HashMap Name Entry

private inductive SiteKind where
  | value
  | theorem
  | inductive
  | other
  deriving BEq

private structure Site where
  kind : SiteKind

private def siteKind : EDecl → SiteKind
  | .defn .. => .value
  | .thm .. => .theorem
  | .induct .. => .inductive
  | _ => .other

/-- Build the model relation from exact source roles.

A candidate counts only when the export contains a declaration of the
generated role's expected kind. Ambiguous candidates are omitted rather than
guessed. This distinguishes an original inductive literally named
`Foo._model` from the carrier model of `Foo`, and treats raw private names as
ordinary exact keys. -/
def table (x : Export) : Table := Id.run do
  let normalizer := x.exactNormalizationEnv
  let mut sites : Std.HashMap Name Site := {}
  for declaration in x.decls do
    for name in declaration.names do
      sites := sites.insert name { kind := siteKind declaration }
  let mut result : Table := {}
  let mut ambiguous : Std.HashSet Name := {}
  let add := fun (result : Table) (ambiguous : Std.HashSet Name)
      (name : Name) (want : SiteKind) (entry : Entry) =>
    match sites[name]? with
    | some site =>
      if site.kind != want then (result, ambiguous)
      else if ambiguous.contains name then (result, ambiguous)
      else if result.contains name then (result.erase name, ambiguous.insert name)
      else (result.insert name entry, ambiguous)
    | none => (result, ambiguous)
  for ownerDecl in [:x.decls.size] do
    let .induct types constructors recursors := x.decls[ownerDecl]! | continue
    let some ownerType := types.head? | continue
    let entry := fun role =>
      { owner := ownerType.name, ownerDecl, role }
    for type in types do
      (result, ambiguous) := add result ambiguous (Naming.modelName type.name) .value
        (entry .typeFormer)
    for constructor in constructors do
      (result, ambiguous) := add result ambiguous
        (Naming.modelName constructor.name) .value (entry .constructor)
    for recursor in recursors do
      (result, ambiguous) := add result ambiguous
        (Naming.modelName recursor.name) .value (entry .recursor)
      for ruleIndex in [:recursor.rules.length] do
        (result, ambiguous) := add result ambiguous
          (Naming.iotaName recursor.name ruleIndex) .theorem (entry .iota)
      if recursor.k then
        (result, ambiguous) := add result ambiguous
          (Naming.ruleKName recursor.name) .theorem (entry .ruleK)
    for type in types do
      if type.isKernelUnitlike constructors normalizer then
        (result, ambiguous) := add result ambiguous
          (Naming.unitlikeName type.name) .theorem (entry .unitlike)
      if type.isKernelStructureLike constructors normalizer then
        (result, ambiguous) := add result ambiguous
          (Naming.etaName type.name) .theorem (entry .eta)
      for fieldIndex in x.intrinsicProjectionFieldsFor type constructors do
        (result, ambiguous) := add result ambiguous
          (Naming.projectionName type.name fieldIndex) .value (entry .projection)
        (result, ambiguous) := add result ambiguous
          (Naming.projectionIotaName type.name fieldIndex) .theorem
          (entry .projectionIota)
  return result

end InductiveModels.ModelRoles
