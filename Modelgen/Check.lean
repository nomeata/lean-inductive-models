import Modelgen.Format
import Modelgen.Naming

/-!
# Structural checks for exported inductive models

This module is the format-only foundation of the model checker.  It discovers
public model families solely from the declarations in an original inductive
record.  If that record declares type former `T`, constructor `C`, recursor `R`
and rule `j`, their public names are respectively `T._model`, `C._model`,
`R._model` and `R._model.iota_j`, constructed by [`Modelgen.Naming`].  No name
is split at `_model`, so private names and originals which themselves contain
an `_model` component retain their exact identity.

Declaration records remain atomic for ordering.  A record which introduces at
least one exact public name belongs to the corresponding family in its entirety;
ordinary dependency edges order any non-contract implementation helpers on
which it depends.

The implemented invariants are:

* every declaration record in the model family precedes the inductive record
  containing its owner; and
* the complete owner inductive record does not refer to any name introduced by
  its model family;
* there is exactly one public type-former and constructor declaration for every
  corresponding original declaration; and
* type-former and constructor types are syntactically equal after the one public
  constant substitution and positional alignment of declaration universes.

The second walk covers both names held directly in export records and names in
expressions.  In expressions it treats both `Expr.const` and the `typeName`
field of `Expr.proj` as references.  Recursor and reduction-rule names are part
of discovery and correspondence, but this tranche intentionally does not
validate their statements yet.  It never unfolds or asks for definitional
equality.
-/

open Lean

namespace Modelgen.Check

/-- One entry in the simultaneous public constant substitution. -/
structure ConstantPair where
  owner : Name
  model : Name
  deriving Inhabited, Repr, BEq

/-- The public correspondence table for one modeled inductive record.

Recursors are already present so every comparison tranche uses the same table,
but this module does not validate their declarations yet. -/
structure Correspondence where
  typeFormers : Array ConstantPair
  constructors : Array ConstantPair
  recursors : Array ConstantPair
  iotas : Array Naming.Iota
  deriving Inhabited, Repr, BEq

def Correspondence.entries (table : Correspondence) : Array ConstantPair :=
  table.typeFormers ++ table.constructors ++ table.recursors

/-- Exact public declarations which can establish this correspondence in an
export.  Recursors and iota theorems participate in discovery even though their
statements are validated by a later checker tranche. -/
def Correspondence.publicNames (table : Correspondence) : Array Name :=
  table.entries.map (·.model) ++ table.iotas.map (·.name)

/-- The exact original declaration owning one public name in the table. -/
def Correspondence.originalOfPublic? (table : Correspondence) (name : Name) : Option Name :=
  (table.entries.find? (·.model == name)).map (·.owner) <|>
    (table.iotas.find? (·.name == name)).map (·.recursor)

/-- Apply the table simultaneously.  Projection type-name fields are constants
for this purpose just as they are for the backreference invariant. -/
def Correspondence.substitute (table : Correspondence) (expression : Expr) : Expr :=
  let replacements := table.entries.foldl
    (fun map pair => map.insert pair.owner pair.model) ({} : Std.HashMap Name Name)
  mapConstsE (fun name => replacements[name]?) expression

/-- Align the owner's declaration universes with the model declaration's by
position and then apply the simultaneous public constant substitution.  A
length mismatch is rejected by the caller rather than truncated here. -/
def Correspondence.expectedType (table : Correspondence) (ownerParams modelParams : List Name)
    (type : Expr) : Expr :=
  table.substitute (type.instantiateLevelParams ownerParams (modelParams.map Level.param))

/-- The correspondence table determined by an inductive record, independent
of whether any model declarations are present. -/
def correspondenceAt? (x : Export) (ownerDecl : Nat) : Option Correspondence := do
  let .induct types ctors recursors ← x.decls[ownerDecl]?
    | none
  let typeFormers := types.toArray.map fun type =>
    { owner := type.name, model := Naming.modelName type.name }
  let constructors := ctors.toArray.map fun ctor =>
    { owner := ctor.name, model := Naming.modelName ctor.name }
  let recursorRecords := recursors.toArray
  let recursors := recursorRecords.map fun recursor =>
    { owner := recursor.name, model := Naming.modelName recursor.name }
  let iotas := recursorRecords.flatMap fun recursor =>
    (Array.range recursor.rules.length).map (Naming.Iota.ofRecursor recursor.name)
  return { typeFormers, constructors, recursors, iotas }

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
  correspondence : Correspondence
  decls : Array Nat
  names : Array Name
  deriving Inhabited, Repr, BEq

/-- A structural model-contract violation. -/
inductive Violation where
  /-- A model declaration is at or after its owner's inductive record. -/
  | modelNotBefore (owner declaration : Name) (modelDecl ownerDecl : Nat)
  /-- The owner's inductive record refers back to a declaration of its model. -/
  | ownerBackreference (owner target : Name)
  /-- An expected public type-former or constructor declaration is absent. -/
  | missingPublic (owner expected : Name)
  /-- A public type-former or constructor declaration occurs more than once. -/
  | duplicatePublic (owner expected : Name) (count : Nat)
  /-- Legacy diagnostic retained for API compatibility.  Exact declaration-local
  naming has no syntactic "extra constructor slot" class. -/
  | extraConstructor (owner declaration : Name)
  /-- The two declarations do not carry equally many positional universes. -/
  | universeArity (owner declaration : Name) (ownerArity modelArity : Nat)
  /-- The exported declaration types differ after the exact permitted rewrite. -/
  | declarationType (owner declaration : Name)
  deriving Repr, BEq

private def appendUnique (names : Array Name) (more : List Name) : Array Name :=
  more.foldl (fun out name => if out.contains name then out else out.push name) names

/-- Discover public model families from exact names computed from each original
inductive record.  One family covers the whole atomic record, but every public
slot in its correspondence remains attached to its exact original declaration.
Names merely containing an `_model` component have no special meaning. -/
def discover (x : Export) : Array Family := Id.run do
  let mut declarations : Std.HashMap Name (Array Nat) := {}
  for i in [0:x.decls.size] do
    for name in x.decls[i]!.names do
      declarations := declarations.insert name ((declarations.getD name #[]).push i)

  let mut families : Array Family := #[]
  for ownerDecl in [0:x.decls.size] do
    let .induct types _ _ := x.decls[ownerDecl]! | continue
    let some root := types.head?.map (·.name) | continue
    let some correspondence := correspondenceAt? x ownerDecl | continue
    let publicNames := correspondence.publicNames
    unless publicNames.any (fun name => !(declarations.getD name #[]).isEmpty) do continue
    let mut modelDecls : Array Nat := #[]
    for name in publicNames do
      for i in declarations.getD name #[] do
        unless modelDecls.contains i do modelDecls := modelDecls.push i
    modelDecls := modelDecls.qsort (· < ·)
    let modelNames := modelDecls.foldl
      (fun names i => appendUnique names x.decls[i]!.names) #[]
    let modelRoot := Naming.modelName root
    families := families.push
      { owner := root, modelRoot, carrier := modelRoot, ownerDecl, correspondence,
        decls := modelDecls, names := modelNames }
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

private def ownerReference? (targets : Std.HashSet Name) : EDecl → Option (Name × Name)
  | .induct types ctors recursors =>
      types.findSome? (typeReference? targets) <|>
        ctors.findSome? (ctorReference? targets) <|>
        recursors.findSome? (recReference? targets)
  | _ => none

/-- The type-bearing view of one public constant introduced by an export
record.  Values are intentionally absent: this tranche checks the interface,
not how a model implements it. -/
private structure DeclType where
  name : Name
  levelParams : List Name
  type : Expr
  deriving Inhabited

private def declTypes : EDecl → Array DeclType
  | .ax name levelParams type _ | .quot name levelParams type _ =>
      #[{ name, levelParams, type }]
  | .defn name levelParams type .. | .thm name levelParams type .. |
      .opaq name levelParams type .. =>
      #[{ name, levelParams, type }]
  | .induct types ctors recursors =>
      types.toArray.map (fun type =>
        { name := type.name, levelParams := type.levelParams, type := type.type }) ++
      ctors.toArray.map (fun ctor =>
        { name := ctor.name, levelParams := ctor.levelParams, type := ctor.type }) ++
      recursors.toArray.map (fun recursor =>
        { name := recursor.name, levelParams := recursor.levelParams, type := recursor.type })

private abbrev DeclarationTypes := Std.HashMap Name (Array DeclType)

private def declarationTypes (x : Export) : DeclarationTypes := Id.run do
  let mut declarations : DeclarationTypes := {}
  for declaration in x.decls do
    for info in declTypes declaration do
      declarations := declarations.insert info.name
        ((declarations.getD info.name #[]).push info)
  return declarations

private def checkPair (table : Correspondence) (declarations : DeclarationTypes)
    (pair : ConstantPair) : Array Violation := Id.run do
  let mut violations : Array Violation := #[]
  let models := declarations.getD pair.model #[]
  if models.isEmpty then
    return #[.missingPublic pair.owner pair.model]
  if models.size != 1 then
    return #[.duplicatePublic pair.owner pair.model models.size]
  let some ownerDecl := (declarations.getD pair.owner #[])[0]?
    | return #[.declarationType pair.owner pair.model]
  let modelDecl := models[0]!
  if ownerDecl.levelParams.length != modelDecl.levelParams.length then
    violations := violations.push (.universeArity pair.owner pair.model
      ownerDecl.levelParams.length modelDecl.levelParams.length)
  else
    let expected := table.expectedType
      ownerDecl.levelParams modelDecl.levelParams ownerDecl.type
    unless expected == modelDecl.type do
      violations := violations.push (.declarationType pair.owner pair.model)
  return violations

/-- The owner named by a diagnostic, for callers checking one family in a
larger export. -/
def Violation.familyOwner : Violation → Name
  | .modelNotBefore owner .. | .ownerBackreference owner .. |
      .missingPublic owner .. | .duplicatePublic owner .. |
      .extraConstructor owner .. | .universeArity owner .. |
      .declarationType owner .. => owner

/-- Check the currently implemented part of the model contract.  An empty
result establishes order, independence, and exact type-former/constructor slots
and types.  Recursor and reduction-rule slots establish discovery and ordering,
but their presence and statements are validated by a later tranche. -/
def check (x : Export) : Array Violation := Id.run do
  let mut violations : Array Violation := #[]
  let declarations := declarationTypes x
  for family in discover x do
    for modelDecl in family.decls do
      unless modelDecl < family.ownerDecl do
        let declaration := x.decls[modelDecl]!
        for name in declaration.names do
          if let some owner := family.correspondence.originalOfPublic? name then
            violations := violations.push
              (.modelNotBefore owner name modelDecl family.ownerDecl)
    let targets := family.names.foldl (fun set name => set.insert name) ({} : Std.HashSet Name)
    if let some (owner, target) := ownerReference? targets x.decls[family.ownerDecl]! then
      violations := violations.push (.ownerBackreference owner target)
    for pair in family.correspondence.typeFormers do
      violations := violations ++ checkPair family.correspondence declarations pair
    for pair in family.correspondence.constructors do
      violations := violations ++ checkPair family.correspondence declarations pair
  return violations

end Modelgen.Check
