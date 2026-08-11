import Modelgen.Format

/-!
# Structural checks for exported inductive models

This module is the format-only foundation of the model checker.  It discovers
public model families by the declaration of their conventional carrier
`T._model.self`; an arbitrary name containing `_model` is not enough.  The
owner must be a public inductive type declared in the same export.

Once a carrier establishes a family, every declaration record introducing a
name under the same *innermost* `T._model` prefix belongs to that family.  This
deliberately includes support declarations such as `T._model.funext`: helpers
are part of the emitted model's dependency-ordered declaration slice, not
independent model families.  A second-layer name such as
`T._model.0._model.self` is instead keyed to `T._model.0`.

Only two invariants live here for now:

* every declaration record in the model family precedes the inductive record
  containing its owner; and
* the complete owner inductive record does not refer to any name introduced by
  its model family.

The second walk covers both names held directly in export records and names in
expressions.  In expressions it treats both `Expr.const` and the `typeName`
field of `Expr.proj` as references.  It intentionally performs no type, term,
constructor, recursor, or reduction-rule comparison yet.
-/

open Lean

namespace Modelgen.Check

/-- The innermost `_model` component in a name, including that component. -/
def modelPrefix : Name → Option Name
  | .anonymous => none
  | n@(.str p s) => if s == "_model" then some n else modelPrefix p
  | .num p _ => modelPrefix p

/-- The name modeled by declarations under the innermost model prefix. -/
def modelOwner (name : Name) : Option Name :=
  match modelPrefix name with
  | some (.str owner "_model") => some owner
  | _ => none

/-- A public model family discovered in an export.

`decls` are declaration-record indices, not individual kernel declarations.
If one record introduces several names (notably an inductive block), all of
them are included in `names`, because ordering and dependency are atomic at the
export-record boundary. -/
structure Family where
  owner : Name
  modelRoot : Name
  carrier : Name
  ownerDecl : Nat
  decls : Array Nat
  names : Array Name
  deriving Repr, BEq

/-- A structural model-contract violation. -/
inductive Violation where
  /-- A model declaration is at or after its owner's inductive record. -/
  | modelNotBefore (owner declaration : Name) (modelDecl ownerDecl : Nat)
  /-- The owner's inductive record refers back to a declaration of its model. -/
  | ownerBackreference (owner target : Name)
  deriving Repr, BEq

private def appendUnique (names : Array Name) (more : List Name) : Array Name :=
  more.foldl (fun out name => if out.contains name then out else out.push name) names

/-- Discover public model families.  A carrier and a public inductive owner in
the same export are both required, so unrelated namespaces called `_model`
are ignored. -/
def discover (x : Export) : Array Family := Id.run do
  let mut owners : Std.HashMap Name Nat := {}
  for i in [0 : x.decls.size] do
    if let .induct types _ _ := x.decls[i]! then
      for inductiveType in types do
        owners := owners.insert inductiveType.name i

  let mut seeds : Array (Name × Name × Name × Nat) := #[]
  for declaration in x.decls do
    for name in declaration.names do
      let some modelRoot := modelPrefix name | continue
      let carrier := Name.str modelRoot "self"
      unless name == carrier do continue
      let some owner := modelOwner name | continue
      if isPrivateName owner then continue
      let some ownerDecl := owners[owner]? | continue
      unless seeds.any (fun seed => seed.1 == owner) do
        seeds := seeds.push (owner, modelRoot, carrier, ownerDecl)

  let mut families : Array Family := #[]
  for (owner, modelRoot, carrier, ownerDecl) in seeds do
    let mut decls : Array Nat := #[]
    let mut names : Array Name := #[]
    for i in [0 : x.decls.size] do
      let declaration := x.decls[i]!
      if declaration.names.any (fun name => modelPrefix name == some modelRoot) then
        decls := decls.push i
        names := appendUnique names declaration.names
    families := families.push { owner, modelRoot, carrier, ownerDecl, decls, names }
  return families

private partial def expressionReference? (targets : Std.HashSet Name) : Expr → Option Name
  | .const name _ => if targets.contains name then some name else none
  | .proj typeName _ struct =>
      if targets.contains typeName then some typeName else expressionReference? targets struct
  | .app fn arg => expressionReference? targets fn <|> expressionReference? targets arg
  | .lam _ type body _ | .forallE _ type body _ =>
      expressionReference? targets type <|> expressionReference? targets body
  | .letE _ type value body _ =>
      expressionReference? targets type <|> expressionReference? targets value <|>
        expressionReference? targets body
  | .mdata _ body => expressionReference? targets body
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => none

private def nameReference? (targets : Std.HashSet Name) (names : List Name) : Option Name :=
  names.find? targets.contains

private def typeReference? (targets : Std.HashSet Name) (type : EIndType) : Option Name :=
  nameReference? targets type.all <|>
    nameReference? targets type.ctors <|>
    expressionReference? targets type.type

private def ctorReference? (targets : Std.HashSet Name) (ctor : ECtor) : Option Name :=
  (if targets.contains ctor.induct then some ctor.induct else none) <|>
    expressionReference? targets ctor.type

private def ruleReference? (targets : Std.HashSet Name) (rule : ERecRule) : Option Name :=
  (if targets.contains rule.ctor then some rule.ctor else none) <|>
    expressionReference? targets rule.rhs

private def recReference? (targets : Std.HashSet Name) (recursor : ERec) : Option Name :=
  nameReference? targets recursor.all <|>
    expressionReference? targets recursor.type <|>
    recursor.rules.findSome? (ruleReference? targets)

private def ownerReference? (targets : Std.HashSet Name) : EDecl → Option Name
  | .induct types ctors recursors =>
      types.findSome? (typeReference? targets) <|>
        ctors.findSome? (ctorReference? targets) <|>
        recursors.findSome? (recReference? targets)
  | _ => none

/-- Check the currently implemented structural part of the model contract.
An empty result means only that these two invariants hold; it does not yet say
that the model's declarations correspond syntactically to the owner. -/
def check (x : Export) : Array Violation := Id.run do
  let mut violations : Array Violation := #[]
  for family in discover x do
    for modelDecl in family.decls do
      unless modelDecl < family.ownerDecl do
        let declaration := x.decls[modelDecl]!
        let name := declaration.names.head?.getD family.modelRoot
        violations := violations.push
          (.modelNotBefore family.owner name modelDecl family.ownerDecl)
    let targets := family.names.foldl (fun set name => set.insert name) ({} : Std.HashSet Name)
    if let some target := ownerReference? targets x.decls[family.ownerDecl]! then
      violations := violations.push (.ownerBackreference family.owner target)
  return violations

end Modelgen.Check
