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
* there is exactly one public type-former, constructor and recursor declaration,
  and one theorem for every exported recursor rule; and
* all declaration types, including the exact equality proposition synthesized
  for each rule, are syntactically equal after the one public
  constant substitution and positional alignment of declaration universes.

The second walk covers both names held directly in export records and names in
expressions.  In expressions it treats both `Expr.const` and the `typeName`
field of `Expr.proj` as references.  It never unfolds or asks for definitional
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

Recursors and their ordered reduction theorems share this table with type
formers and constructors, so every comparison uses one simultaneous rewrite. -/
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

/-- Align and rewrite an iota proposition while retaining its outer ambient
`Eq`.  This distinction matters when the modeled inductive is itself `Eq`: its
arguments and rule use `Eq._model`, but the theorem relating both sides still
uses the export's equality type. -/
def Correspondence.expectedIotaType (table : Correspondence)
    (ownerParams modelParams : List Name) (type : Expr) : Expr :=
  let aligned := type.instantiateLevelParams ownerParams (modelParams.map Level.param)
  let rec rewrite : Expr → Expr
    | .forallE name domain body info =>
      .forallE name (table.substitute domain) (rewrite body) info
    | body =>
      match body.getAppFn with
      | .const ``Eq levels => mkAppN (.const ``Eq levels) (body.getAppArgs.map table.substitute)
      | _ => table.substitute body
  rewrite aligned

private structure OpenBinder where
  name : Name
  type : Expr
  info : BinderInfo
  value : Expr

private partial def openForalls (tag : Name) (expression : Expr) : Array OpenBinder × Expr :=
  let rec loop (expression : Expr) (binders : Array OpenBinder) :=
    match expression with
    | .forallE name type body info =>
      let value := mkFVar (FVarId.mk (tag.mkNum binders.size))
      loop (body.instantiate1 value) (binders.push { name, type, info, value })
    | body => (binders, body)
  loop expression #[]

private partial def applyLambdasAux (arguments : Array Expr) (expression : Expr)
    (index : Nat) : Option Expr :=
  match arguments[index]? with
  | none => some expression
  | some argument => match expression with
    | .lam _ _ body _ => applyLambdasAux arguments (body.instantiate1 argument) (index + 1)
    | _ => none

private def applyLambdas (expression : Expr) (arguments : Array Expr) : Option Expr :=
  applyLambdasAux arguments expression 0

private def closeForalls (binders : Array OpenBinder) (body : Expr) : Expr :=
  binders.reverse.foldl (fun body binder =>
    .forallE binder.name binder.type (body.abstract #[binder.value]) binder.info) body

private abbrev Constructors := Std.HashMap Name ECtor

private def constructorRecords (x : Export) : Constructors := Id.run do
  let mut result : Constructors := {}
  for declaration in x.decls do
    if let .induct _ constructors _ := declaration then
      for constructor in constructors do result := result.insert constructor.name constructor
  return result

/-- The literal equality proposition exported for rule `ruleIndex` of
`recursorName`, before the simultaneous model-name substitution.  Its left-hand
side already names `recursorName._model`, as the proposition necessarily does;
all types, constructors and right-hand-side recursor calls still use originals.

The recursor's own minor premise supplies the motive application, constructor
levels, parameters, indices and field telescope.  The exported rule supplies
the right-hand side.  Nothing is inferred, unfolded or compared definitionally.
The returned level parameters are those of the original recursor. -/
private def iotaPropositionWith? (x : Export) (constructors : Constructors)
    (ownerDecl : Nat) (recursorName : Name) (ruleIndex : Nat) : Option (List Name × Expr) := do
  let .induct types _ recursors ← x.decls[ownerDecl]? | none
  let recursor ← recursors.find? (·.name == recursorName)
  let rule ← recursor.rules[ruleIndex]?
  let constructor ← constructors[rule.ctor]?
  unless constructor.numFields == rule.nfields do none
  let nb := recursor.numParams + recursor.numMotives + recursor.numMinors
  let (recBinders, _) := openForalls ((`_check.rec).append recursorName) recursor.type
  unless recBinders.size >= nb + recursor.numIndices + 1 do none
  let preBinders := recBinders.extract 0 nb
  let pre := preBinders.map (·.value)
  let minorBinders := recBinders.extract
    (recursor.numParams + recursor.numMotives) nb

  let mut selected? : Option (Array OpenBinder × Expr × Array Expr) := none
  for minor in minorBinders do
    let (fieldsAndIhs, motiveResult) :=
      openForalls ((`_check.minor).append rule.ctor) minor.type
    let motiveArgs := motiveResult.getAppArgs
    let some major := motiveArgs.back? | continue
    let .const ctorName _ := major.getAppFn | continue
    unless ctorName == rule.ctor do continue
    let majorArgs := major.getAppArgs
    unless majorArgs.size >= rule.nfields do continue
    let fieldValues := majorArgs.extract (majorArgs.size - rule.nfields) majorArgs.size
    let mut fields : Array OpenBinder := #[]
    for value in fieldValues do
      let some binder := fieldsAndIhs.find? (·.value == value) | fields := #[]; break
      fields := fields.push binder
    unless fields.size == rule.nfields do continue
    selected? := some (fields, motiveResult, motiveArgs.extract 0 (motiveArgs.size - 1))
    break
  let some (fieldBinders, motiveResult, indices) := selected? | none
  let fields := fieldBinders.map (·.value)
  let rhs ← applyLambdas rule.rhs (pre ++ fields)
  let majorArgs := motiveResult.getAppArgs
  let some major := majorArgs.back? | none
  let recLevels := recursor.levelParams.map Level.param
  let lhs := mkAppN (.const (Naming.modelName recursor.name) recLevels)
    ((pre ++ indices).push major)
  let blockLevelCount := types.head?.map (·.levelParams.length) |>.getD 0
  let eqLevel := if recursor.levelParams.length == blockLevelCount + 1 then
      recursor.levelParams.head?.map Level.param |>.getD .zero
    else .zero
  let originalBody := mkAppN (.const `Eq [eqLevel]) #[motiveResult, lhs, rhs]
  return (recursor.levelParams, closeForalls (preBinders ++ fieldBinders) originalBody)

def iotaProposition? (x : Export) (ownerDecl : Nat) (recursorName : Name)
    (ruleIndex : Nat) : Option (List Name × Expr) :=
  iotaPropositionWith? x (constructorRecords x) ownerDecl recursorName ruleIndex

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
  /-- An expected public declaration or reduction theorem is absent. -/
  | missingPublic (owner expected : Name)
  /-- A required public declaration or reduction theorem occurs more than once. -/
  | duplicatePublic (owner expected : Name) (count : Nat)
  /-- Legacy diagnostic retained for API compatibility.  Exact declaration-local
  naming has no syntactic "extra constructor slot" class. -/
  | extraConstructor (owner declaration : Name)
  /-- A direct `R._model.iota_j` theorem has no exported rule `j` of `R`. -/
  | extraRule (owner declaration : Name)
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

private def checkIota (x : Export) (constructors : Constructors) (family : Family)
    (declarations : DeclarationTypes) (iota : Naming.Iota) : Array Violation := Id.run do
  let models := declarations.getD iota.name #[]
  if models.isEmpty then
    return #[.missingPublic iota.recursor iota.name]
  if models.size != 1 then
    return #[.duplicatePublic iota.recursor iota.name models.size]
  let some (ownerParams, ownerType) :=
      iotaPropositionWith? x constructors family.ownerDecl iota.recursor iota.ruleIndex
    | return #[.declarationType iota.recursor iota.name]
  let model := models[0]!
  if ownerParams.length != model.levelParams.length then
    return #[.universeArity iota.recursor iota.name ownerParams.length model.levelParams.length]
  let expected := family.correspondence.expectedIotaType ownerParams model.levelParams ownerType
  if model.type == expected then #[] else #[.declarationType iota.recursor iota.name]

private def iotaSlot? (name : Name) : Option (Name × Nat) := do
  let .str parent suffix := name | none
  unless suffix.startsWith "iota_" do none
  return (parent, ← (suffix.drop 5).toNat?)

private abbrev IotaSlots := Std.HashMap Name (Array (Name × Nat))

private def iotaSlots (x : Export) : IotaSlots := Id.run do
  let mut slots : IotaSlots := {}
  for declaration in x.decls do
    for name in declaration.names do
      if let some (parent, index) := iotaSlot? name then
        slots := slots.insert parent ((slots.getD parent #[]).push (name, index))
  return slots

/-- The owner named by a diagnostic, for callers checking one family in a
larger export. -/
def Violation.familyOwner : Violation → Name
  | .modelNotBefore owner .. | .ownerBackreference owner .. |
      .missingPublic owner .. | .duplicatePublic owner .. |
      .extraConstructor owner .. | .extraRule owner .. | .universeArity owner .. |
      .declarationType owner .. => owner

/-- Check order, independence, and every exact public declaration and statement.
All comparisons are literal after positional universe alignment and the one
simultaneous declaration-name substitution. -/
def check (x : Export) : Array Violation := Id.run do
  let mut violations : Array Violation := #[]
  let declarations := declarationTypes x
  let constructors := constructorRecords x
  let ruleSlots := iotaSlots x
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
    for pair in family.correspondence.recursors do
      violations := violations ++ checkPair family.correspondence declarations pair
    for iota in family.correspondence.iotas do
      violations := violations ++ checkIota x constructors family declarations iota
    for pair in family.correspondence.recursors do
      let numRules := (family.correspondence.iotas.filter (·.recursor == pair.owner)).size
      for (name, ruleIndex) in ruleSlots.getD pair.model #[] do
        if ruleIndex >= numRules || name != Naming.iotaName pair.owner ruleIndex then
          violations := violations.push (.extraRule pair.owner name)
  return violations

end Modelgen.Check
