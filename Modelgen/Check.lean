import Modelgen.Format

/-!
# Structural checks for exported inductive models

This module is the format-only foundation of the model checker.  It discovers
public model families through a conventional public slot: a carrier
`R._model.self` or a numbered root constructor `T._model.ctor_j`.  An arbitrary
name containing `_model` is not enough, and the owner must be a public
inductive type declared in the same export.

Once a conventional slot establishes a family, every declaration record
introducing a name under the same *innermost* `T._model` prefix belongs to that
family.  This deliberately includes support declarations such as
`T._model.funext`: helpers are part of the emitted model's dependency-ordered
declaration slice, not independent model families.  A second-layer name such as
`T._model.0._model.self` is instead keyed to `T._model.0`.

The implemented invariants are:

* every declaration record in the model family precedes the inductive record
  containing its owner; and
* the complete owner inductive record does not refer to any name introduced by
  its model family;
* there is exactly one public carrier and constructor declaration for every
  corresponding owner declaration, and no extra numbered constructor slot;
  and
* carrier and constructor types are syntactically equal after the one public
  constant substitution and positional alignment of declaration universes.

The second walk covers both names held directly in export records and names in
expressions.  In expressions it treats both `Expr.const` and the `typeName`
field of `Expr.proj` as references.  It intentionally performs no recursor or
reduction-rule comparison yet, and never unfolds or asks for definitional
equality.
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
  deriving Inhabited, Repr, BEq

def Correspondence.entries (table : Correspondence) : Array ConstantPair :=
  table.typeFormers ++ table.constructors ++ table.recursors

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
  let root ← types.head?.map (·.name)
  let modelRoot := Name.str root "_model"
  let typeFormers := types.toArray.filterMap fun type =>
    if isPrivateName type.name then none else
      some { owner := type.name, model := Name.str (Name.str type.name "_model") "self" }
  let ctorArray := ctors.toArray
  let constructors := (Array.range ctorArray.size).filterMap fun index =>
    let ctor := ctorArray[index]!
    if isPrivateName ctor.name then none else
      some { owner := ctor.name, model := Name.str modelRoot s!"ctor_{index}" }
  let recArray := recursors.toArray
  let recursors := (Array.range recArray.size).filterMap fun index =>
    let recursor := recArray[index]!
    if isPrivateName recursor.name then none else
      some { owner := recursor.name, model := Name.str modelRoot s!"rec_{index}" }
  return { typeFormers, constructors, recursors }

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
  /-- An expected public carrier or constructor slot is absent. -/
  | missingPublic (owner expected : Name)
  /-- A public carrier or constructor slot is declared more than once. -/
  | duplicatePublic (owner expected : Name) (count : Nat)
  /-- A numbered public constructor slot has no owner constructor. -/
  | extraConstructor (owner declaration : Name)
  /-- The two declarations do not carry equally many positional universes. -/
  | universeArity (owner declaration : Name) (ownerArity modelArity : Nat)
  /-- The exported declaration types differ after the exact permitted rewrite. -/
  | declarationType (owner declaration : Name)
  deriving Repr, BEq

private def appendUnique (names : Array Name) (more : List Name) : Array Name :=
  more.foldl (fun out name => if out.contains name then out else out.push name) names

/-- A direct `T._model.ctor_j` slot, with its root and index. -/
def constructorSlot? : Name → Option (Name × Nat)
  | .str (.str root "_model") suffix => do
      unless suffix.startsWith "ctor_" do none
      let index ← (suffix.drop 5).toNat?
      return (root, index)
  | _ => none

/-- Discover public model families.  A conventional public slot and a public
inductive owner in the same export are both required, so unrelated namespaces
called `_model` are ignored.  One family covers the whole inductive record,
including a mutual block's member-specific carrier roots. -/
def discover (x : Export) : Array Family := Id.run do
  let mut owners : Std.HashMap Name Nat := {}
  let mut roots : Std.HashMap Name Nat := {}
  for i in [0 : x.decls.size] do
    if let .induct types _ _ := x.decls[i]! then
      if let root :: _ := types then
        unless isPrivateName root.name do roots := roots.insert root.name i
      for inductiveType in types do
        unless isPrivateName inductiveType.name do
          owners := owners.insert inductiveType.name i

  let mut seeds : Array Nat := #[]
  for declaration in x.decls do
    for name in declaration.names do
      let mut ownerDecl? : Option Nat := none
      if let some owner := modelOwner name then
        if name == Name.str (Name.str owner "_model") "self" then
          ownerDecl? := owners[owner]?
      if ownerDecl?.isNone then
        if let some (root, _) := constructorSlot? name then ownerDecl? := roots[root]?
      if let some ownerDecl := ownerDecl? then
        unless seeds.contains ownerDecl do seeds := seeds.push ownerDecl

  let mut families : Array Family := #[]
  let mut familyOfOwner : Std.HashMap Name Nat := {}
  for ownerDecl in seeds do
    let .induct types _ _ := x.decls[ownerDecl]! | continue
    let some root := types.head?.map (·.name) | continue
    let some correspondence := correspondenceAt? x ownerDecl | continue
    let modelRoot := Name.str root "_model"
    let carrier := Name.str modelRoot "self"
    let familyIndex := families.size
    for pair in correspondence.typeFormers do
      familyOfOwner := familyOfOwner.insert pair.owner familyIndex
    families := families.push
      { owner := root, modelRoot, carrier, ownerDecl, correspondence, decls := #[], names := #[] }

  -- Assign every declaration record once.  Looking at the innermost owner is
  -- what keeps a model of `T._model.0` out of `T`'s own family.
  for i in [0 : x.decls.size] do
    let declaration := x.decls[i]!
    let mut familyIndices : Array Nat := #[]
    for name in declaration.names do
      if let some owner := modelOwner name then
        if let some familyIndex := familyOfOwner[owner]? then
          unless familyIndices.contains familyIndex do
            familyIndices := familyIndices.push familyIndex
    for familyIndex in familyIndices do
      let family := families[familyIndex]!
      families := families.set! familyIndex
        { family with decls := family.decls.push i, names := appendUnique family.names declaration.names }
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

private def checkPair (family : Family) (declarations : DeclarationTypes)
    (pair : ConstantPair) : Array Violation := Id.run do
  let mut violations : Array Violation := #[]
  let models := declarations.getD pair.model #[]
  if models.isEmpty then
    return #[.missingPublic family.owner pair.model]
  if models.size != 1 then
    return #[.duplicatePublic family.owner pair.model models.size]
  let some ownerDecl := (declarations.getD pair.owner #[])[0]?
    | return #[.declarationType family.owner pair.model]
  let modelDecl := models[0]!
  if ownerDecl.levelParams.length != modelDecl.levelParams.length then
    violations := violations.push (.universeArity family.owner pair.model
      ownerDecl.levelParams.length modelDecl.levelParams.length)
  else
    let expected := family.correspondence.expectedType
      ownerDecl.levelParams modelDecl.levelParams ownerDecl.type
    unless expected == modelDecl.type do
      violations := violations.push (.declarationType family.owner pair.model)
  return violations

/-- The owner named by a diagnostic, for callers checking one family in a
larger export. -/
def Violation.familyOwner : Violation → Name
  | .modelNotBefore owner .. | .ownerBackreference owner .. |
      .missingPublic owner .. | .duplicatePublic owner .. |
      .extraConstructor owner .. | .universeArity owner .. |
      .declarationType owner .. => owner

/-- Check the currently implemented part of the model contract.  An empty
result establishes order, independence, and exact carrier/constructor slots
and types.  It says nothing yet about recursor or reduction-rule slots. -/
def check (x : Export) : Array Violation := Id.run do
  let mut violations : Array Violation := #[]
  let declarations := declarationTypes x
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
    for pair in family.correspondence.typeFormers do
      violations := violations ++ checkPair family declarations pair
    for pair in family.correspondence.constructors do
      violations := violations ++ checkPair family declarations pair
    for name in family.names do
      if let some (root, _) := constructorSlot? name then
        if root == family.owner &&
            !family.correspondence.constructors.any (·.model == name) then
          violations := violations.push (.extraConstructor family.owner name)
  return violations

end Modelgen.Check
