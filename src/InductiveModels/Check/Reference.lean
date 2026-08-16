import InductiveModels.Format

/-!
# Owner-reference traversal and its name-only certificate

The independence invariant walks an inductive record for references to its own
model.  [`ownerReference?`] is the direct form; the certificate below records
the same ordered traversal as `(referring, referenced)` name pairs so a compact
run can reproduce it after the record's expressions have been released.
-/

open Lean

namespace InductiveModels.Check

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

private def typeReference? (targets : Std.HashSet Name) (type : EIndType) : Option (Name × Name) :=
  (nameReference? targets type.all <|>
    nameReference? targets type.ctors <|>
    expressionReference? targets type.type).map (type.name, ·)

private def ctorReference? (targets : Std.HashSet Name) (ctor : ECtor) : Option (Name × Name) :=
  ((if targets.contains ctor.induct then some ctor.induct else none) <|>
    expressionReference? targets ctor.type).map (ctor.name, ·)

private def ruleReference? (targets : Std.HashSet Name) (rule : ERecRule) : Option Name :=
  (if targets.contains rule.ctor then some rule.ctor else none) <|>
    expressionReference? targets rule.rhs

private def recReference? (targets : Std.HashSet Name) (recursor : ERec) : Option (Name × Name) :=
  (nameReference? targets recursor.all <|>
    expressionReference? targets recursor.type <|>
    recursor.rules.findSome? (ruleReference? targets)).map (recursor.name, ·)

def ownerReference? (targets : Std.HashSet Name) : EDecl → Option (Name × Name)
  | .induct types ctors recursors =>
      types.findSome? (typeReference? targets) <|>
        ctors.findSome? (ctorReference? targets) <|>
        recursors.findSome? (recReference? targets)
  | _ => none

/-! ## Name-only owner-reference certificates

The compact structural checker does not retain an inductive record's
expressions when final model-family discovery runs.  Capture the exact ordered
reference traversal while that record is live, so intersecting this array with
one discovered family's names later reproduces [`ownerReference?`] without an
`EDecl` or `Expr` root. -/

private partial def appendExpressionReferences (references : Array (Name × Name))
    (owner : Name) : Expr → Array (Name × Name)
  | .const name _ => references.push (owner, name)
  | .proj typeName _ struct =>
      appendExpressionReferences (references.push (owner, typeName)) owner struct
  | .app fn arg =>
      appendExpressionReferences (appendExpressionReferences references owner fn) owner arg
  | .lam _ type body _ | .forallE _ type body _ =>
      appendExpressionReferences (appendExpressionReferences references owner type) owner body
  | .letE _ type value body _ =>
      appendExpressionReferences
        (appendExpressionReferences (appendExpressionReferences references owner type) owner value)
        owner body
  | .mdata _ body => appendExpressionReferences references owner body
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => references

private def appendNameReferences (references : Array (Name × Name)) (owner : Name)
    (names : List Name) : Array (Name × Name) :=
  names.foldl (fun references name => references.push (owner, name)) references

/-- Ordered `(referring declaration, referenced declaration)` pairs from one
inductive export record.  The order deliberately mirrors [`ownerReference?`]:
types, constructors, and recursors in record order, and every direct-name field
before the expression field which follows it.  Duplicates remain observable. -/
def ownerReferenceCertificate : EDecl → Array (Name × Name)
  | .induct types constructors recursors => Id.run do
      let mut references : Array (Name × Name) := #[]
      for type in types do
        references := appendNameReferences references type.name type.all
        references := appendNameReferences references type.name type.ctors
        references := appendExpressionReferences references type.name type.type
      for constructor in constructors do
        references := references.push (constructor.name, constructor.induct)
        references := appendExpressionReferences references constructor.name constructor.type
      for recursor in recursors do
        references := appendNameReferences references recursor.name recursor.all
        references := appendExpressionReferences references recursor.name recursor.type
        for rule in recursor.rules do
          references := references.push (recursor.name, rule.ctor)
          references := appendExpressionReferences references recursor.name rule.rhs
      return references
  | _ => #[]

/-- First owner backreference selected by the same traversal as the full
checker, using only a retained name certificate and the final model-family
record names. -/
def ownerBackreferenceFromCertificate? (references : Array (Name × Name))
    (familyNames : Array Name) : Option (Name × Name) :=
  let targets := familyNames.foldl (fun targets name => targets.insert name)
    ({} : Std.HashSet Name)
  references.find? (fun reference => targets.contains reference.2)

end InductiveModels.Check
