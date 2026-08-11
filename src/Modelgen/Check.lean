import Modelgen.Format
import Modelgen.Naming
import Modelgen.Projection

/-!
# Structural checks for exported inductive models

This module is the format-only foundation of the model checker.  It discovers
public model families solely from the declarations in an original inductive
record.  If that record declares type former `T`, constructor `C`, recursor `R`
and rule `j`, their public names are respectively `T._model`, `C._model`,
`R._model` and `R._model.iota_j`, constructed by [`Modelgen.Naming`].  A
recursor whose literal `k` flag is true additionally owns `R._model.ruleK`.  No
name is split at `_model`, so private names and originals which themselves
contain an `_model` component retain their exact identity.

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
* all declaration types, including the exact equality propositions synthesized
  for each ordinary rule and K reduction, are syntactically equal after the one public
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
  projections : Array Naming.Projection
  iotas : Array Naming.Iota
  metadata : Array Naming.Metadata
  deriving Inhabited, Repr, BEq

def Correspondence.entries (table : Correspondence) : Array ConstantPair :=
  table.typeFormers ++ table.constructors ++ table.recursors

/-- Exact public declarations which can establish this correspondence in an
export.  Recursors and iota theorems participate in discovery even though their
statements are validated by a later checker tranche. -/
def Correspondence.publicNames (table : Correspondence) : Array Name :=
  table.entries.map (·.model) ++ table.iotas.map (·.name) ++
    table.projections.flatMap (fun projection => #[projection.name, projection.iota]) ++
    table.metadata.map (·.name)

/-- The exact original declaration owning one public name in the table. -/
def Correspondence.originalOfPublic? (table : Correspondence) (name : Name) : Option Name :=
  (table.entries.find? (·.model == name)).map (·.owner) <|>
    (table.iotas.find? (·.name == name)).map (·.recursor) <|>
    (table.projections.find? fun projection =>
      projection.name == name || projection.iota == name).map (·.owner) <|>
    (table.metadata.find? (·.name == name)).map (·.owner)

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
  let (recBinders, recResult) :=
    openForalls ((`_check.rec).append recursorName) recursor.type
  unless recBinders.size >= nb + recursor.numIndices + 1 do none
  let preBinders := recBinders.extract 0 nb
  let pre := preBinders.map (·.value)
  -- Nested declarations can contribute several motives whose minor premises
  -- use the same container constructor (for example two distinct `Vec.cons`
  -- premises).  The recursor result identifies which motive this particular
  -- recursor eliminates; constructor spelling alone cannot select its minor.
  let targetMotive := recResult.getAppFn
  let minorBinders := recBinders.extract
    (recursor.numParams + recursor.numMotives) nb

  let mut selected? : Option (Array OpenBinder × Expr × Array Expr) := none
  for minor in minorBinders do
    let (fieldsAndIhs, motiveResult) :=
      openForalls ((`_check.minor).append rule.ctor) minor.type
    unless motiveResult.getAppFn == targetMotive do continue
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
  -- Use the same beta-reduction operation as the generator's statement
  -- oracle.  Merely peeling the outer lambdas leaves internal redexes in the
  -- auxiliary recursors which Lean exports for nested occurrences, so a
  -- syntactically correct theorem was previously reported as different on the
  -- hard nested/mutual fixtures.
  let rhs := rule.rhs.beta (pre ++ fields)
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

/-- The literal unit-like proposition for one exported member.  The carrier is
still named by the original here; [`Correspondence.expectedIotaType`] performs
the same simultaneous, ambient-`Eq`-preserving rewrite as it does for recursor
rules. -/
def unitlikeProposition? (x : Export) (ownerDecl : Nat) (owner : Name) :
    Option (List Name × Expr) := do
  let .induct types constructors _ ← x.decls[ownerDecl]? | none
  let type ← types.find? (·.name == owner)
  unless type.isKernelUnitlike constructors do none
  let (allBinders, result) := openForalls ((`_check.unitlike).append owner) type.type
  unless allBinders.size == type.numParams do none
  let .sort _ := result | none
  let params := allBinders.map (·.value)
  let carrier := mkAppN (.const owner (type.levelParams.map Level.param)) params
  let xBinder : OpenBinder :=
    { name := `x, type := carrier, info := .default
      value := mkFVar (FVarId.mk ((`_check.unitlike.x).append owner)) }
  let yBinder : OpenBinder :=
    { name := `y, type := carrier, info := .default
      value := mkFVar (FVarId.mk ((`_check.unitlike.y).append owner)) }
  let level := match result with | .sort level => level | _ => .zero
  let equality := mkAppN (.const ``Eq [level])
    #[carrier, xBinder.value, yBinder.value]
  return (type.levelParams, closeForalls (allBinders ++ #[xBinder, yBinder]) equality)

/-- The literal equality proposition for the K-like reduction of `recursorName`.
It is the first iota proposition with its constructor major replaced by an
arbitrary inhabitant of that constructor-result fiber.  Consequently indexed
families retain the constructor's result indices rather than quantifying over
arbitrary indices. -/
def ruleKProposition? (x : Export) (ownerDecl : Nat) (recursorName : Name) :
    Option (List Name × Expr) := do
  let .induct _ _ recursors ← x.decls[ownerDecl]? | none
  let recursor ← recursors.find? (·.name == recursorName)
  unless recursor.k && recursor.rules.length == 1 do none
  let rule := recursor.rules.head!
  unless rule.nfields == 0 do none
  let nb := recursor.numParams + recursor.numMotives + recursor.numMinors
  let (levelParams, iotaType) ← iotaProposition? x ownerDecl recursorName 0
  let (pre, body) := openForalls ((`_check.ruleK).append recursorName) iotaType
  unless pre.size == nb do none
  let eqArgs := body.getAppArgs
  unless body.getAppFn.isConstOf `Eq && eqArgs.size == 3 do none
  let lhs := eqArgs[1]!
  let major ← lhs.getAppArgs.back?
  let .const ctorName ctorLevels := major.getAppFn | none
  let constructor ← (constructorRecords x)[ctorName]?
  let mut majorType := constructor.type.instantiateLevelParams constructor.levelParams ctorLevels
  for argument in major.getAppArgs do
    let .forallE _ _ rest _ := majorType | none
    majorType := rest.instantiate1 argument
  let arbitrary := mkFVar (FVarId.mk ((`_check.ruleK.major).append recursorName))
  let replaceMajor := fun expression => expression.replace fun sub =>
    if sub == major then some arbitrary else none
  let result := mkAppN body.getAppFn
    #[replaceMajor eqArgs[0]!, replaceMajor lhs, eqArgs[2]!]
  let majorBinder : OpenBinder :=
    { name := `major, type := majorType, info := .default, value := arbitrary }
  return (levelParams, closeForalls (pre.push majorBinder) result)

/- Reduce only transparent exported former aliases.  This is the syntactic
counterpart of the kernel's Prop test on a structure-like member. -/
private partial def formerWhnf (x : Export) (expression : Expr)
    (seen : Std.HashSet Name := {}) : Expr :=
  match expression with
  | .mdata _ body => formerWhnf x body seen
  | .letE _ _ value body _ => formerWhnf x (body.instantiate1 value) seen
  | .app .. =>
    let reduced := expression.headBeta
    if reduced != expression then formerWhnf x reduced seen
    else match expression.getAppFn with
      | .const name levels =>
        if seen.contains name then expression
        else
          let value? := x.decls.findSome? fun declaration => match declaration with
            | .defn n levelParams _ value .. =>
              if n == name && levelParams.length == levels.length then
                some (value.instantiateLevelParams levelParams levels)
              else none
            | _ => none
          match value? with
          | some value => formerWhnf x (mkAppN value expression.getAppArgs) (seen.insert name)
          | none => expression
      | _ => expression
  | .const name levels =>
    if seen.contains name then expression
    else
      let value? := x.decls.findSome? fun declaration => match declaration with
        | .defn n levelParams _ value .. =>
          if n == name && levelParams.length == levels.length then
            some (value.instantiateLevelParams levelParams levels)
          else none
        | _ => none
      match value? with
      | some value => formerWhnf x value (seen.insert name)
      | none => expression
  | _ => expression

private partial def isPropositionFormer (x : Export) (type : Expr) : Bool :=
  match formerWhnf x type with
  | .forallE _ _ body _ => isPropositionFormer x body
  | .sort .zero => true
  | _ => false

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
  let unitlikeMetadata := types.toArray.filterMap fun type =>
    if type.isKernelUnitlike ctors then some (Naming.Metadata.ofOwner .unitlike type.name)
    else none
  let ruleKMetadata := recursorRecords.filterMap fun recursor =>
    if recursor.k then some (Naming.Metadata.ofOwner .ruleK recursor.name) else none
  let etaMetadata := types.toArray.filterMap fun type =>
    if type.isKernelStructureLike ctors && !isPropositionFormer x type.type then
      some (Naming.Metadata.ofOwner .eta type.name)
    else none
  let mut projections : Array Naming.Projection := #[]
  for type in types do
    for fieldIndex in x.intrinsicProjectionFieldsFor type ctors do
      projections := projections.push (.ofField type.name fieldIndex)
  let metadata := unitlikeMetadata ++ etaMetadata ++ ruleKMetadata
  return { typeFormers, constructors, recursors, projections, iotas, metadata }

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
  kind : DeclarationKind
  safety? : Option String := none
  deriving Inhabited

private def declTypes : EDecl → Array DeclType
  | .ax name levelParams type _ =>
      #[{ name, levelParams, type, kind := .axiom }]
  | .defn name levelParams type _ _ safety _ =>
      #[{ name, levelParams, type, kind := .defn, safety? := some safety }]
  | .thm name levelParams type .. =>
      #[{ name, levelParams, type, kind := .thm }]
  | .opaq name levelParams type .. =>
      #[{ name, levelParams, type, kind := .opaq }]
  | .quot name levelParams type _ =>
      #[{ name, levelParams, type, kind := .quotient }]
  | .induct types ctors recursors =>
      types.toArray.map (fun type =>
        { name := type.name, levelParams := type.levelParams, type := type.type,
          kind := .induct }) ++
      ctors.toArray.map (fun ctor =>
        { name := ctor.name, levelParams := ctor.levelParams, type := ctor.type,
          kind := .ctor }) ++
      recursors.toArray.map (fun recursor =>
        { name := recursor.name, levelParams := recursor.levelParams, type := recursor.type,
          kind := .recursor })

private abbrev DeclarationTypes := Std.HashMap Name (Array DeclType)

private def declarationTypes (x : Export) : DeclarationTypes := Id.run do
  let mut declarations : DeclarationTypes := {}
  for declaration in x.decls do
    for info in declTypes declaration do
      declarations := declarations.insert info.name
        ((declarations.getD info.name #[]).push info)
  return declarations

private def checkImplementationDecl (owner : Name) (declaration : DeclType) : Array Violation :=
  if declaration.kind != .defn then
    #[.declarationKind owner declaration.name .defn declaration.kind]
  else if declaration.safety? != some "safe" then
    #[.declarationSafety owner declaration.name (declaration.safety?.getD "<missing>")]
  else
    #[]

private def checkTheoremDecl (owner : Name) (declaration : DeclType) : Array Violation :=
  if declaration.kind == .thm then #[]
  else #[.declarationKind owner declaration.name .thm declaration.kind]

/-- Kind-check a proof slot without duplicating its missing/duplicate diagnostics,
which remain the responsibility of the slot's exact statement checker. -/
private def checkTheoremSlot (declarations : DeclarationTypes) (owner name : Name) :
    Array Violation :=
  match declarations.getD name #[] with
  | #[declaration] => checkTheoremDecl owner declaration
  | _ => #[]

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
  violations := violations ++ checkImplementationDecl pair.owner modelDecl
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
  let mut violations := checkTheoremDecl iota.recursor model
  if ownerParams.length != model.levelParams.length then
    return violations.push
      (.universeArity iota.recursor iota.name ownerParams.length model.levelParams.length)
  let expected := family.correspondence.expectedIotaType ownerParams model.levelParams ownerType
  if model.type != expected then
    violations := violations.push (.declarationType iota.recursor iota.name)
  return violations

private def checkUnitlike (x : Export) (family : Family)
    (declarations : DeclarationTypes) (metadata : Naming.Metadata) : Array Violation := Id.run do
  let models := declarations.getD metadata.name #[]
  if models.isEmpty then return #[.missingPublic metadata.owner metadata.name]
  if models.size != 1 then
    return #[.duplicatePublic metadata.owner metadata.name models.size]
  let some (ownerParams, ownerType) :=
      unitlikeProposition? x family.ownerDecl metadata.owner
    | return #[.declarationType metadata.owner metadata.name]
  let model := models[0]!
  let mut violations : Array Violation := #[]
  if ownerParams.length != model.levelParams.length then
    return violations.push (.universeArity metadata.owner metadata.name
      ownerParams.length model.levelParams.length)
  let expected := family.correspondence.expectedIotaType
    ownerParams model.levelParams ownerType
  if model.type != expected then
    violations := violations.push (.declarationType metadata.owner metadata.name)
  return violations

private def checkRuleK (x : Export) (family : Family) (declarations : DeclarationTypes)
    (metadata : Naming.Metadata) : Array Violation := Id.run do
  let models := declarations.getD metadata.name #[]
  if models.isEmpty then return #[.missingPublic metadata.owner metadata.name]
  if models.size != 1 then
    return #[.duplicatePublic metadata.owner metadata.name models.size]
  let some (ownerParams, ownerType) := ruleKProposition? x family.ownerDecl metadata.owner
    | return #[.declarationType metadata.owner metadata.name]
  let model := models[0]!
  let mut violations : Array Violation := #[]
  if ownerParams.length != model.levelParams.length then
    return violations.push (.universeArity metadata.owner metadata.name
      ownerParams.length model.levelParams.length)
  let expected := family.correspondence.expectedIotaType ownerParams model.levelParams ownerType
  if model.type != expected then
    violations := violations.push (.declarationType metadata.owner metadata.name)
  return violations

private partial def instantiateForallsExact (expression : Expr) (arguments : Array Expr)
    (index : Nat := 0) : Option Expr :=
  match arguments[index]? with
  | none => some expression
  | some argument => match expression with
    | .forallE _ _ body _ => instantiateForallsExact (body.instantiate1 argument) arguments (index + 1)
    | _ => none

/-- Check the exact non-Prop structure-eta statement.  Reconstruction is
through the intrinsic projection slots for the owner's fields, in constructor
telescope order; exported projection wrapper declarations are irrelevant. -/
private def checkEta (x : Export) (family : Family) (declarations : DeclarationTypes)
    (metadata : Naming.Metadata) : Array Violation := Id.run do
  let models := declarations.getD metadata.name #[]
  if models.isEmpty then return #[.missingPublic metadata.owner metadata.name]
  if models.size != 1 then
    return #[.duplicatePublic metadata.owner metadata.name models.size]
  let model := models[0]!
  let .induct ownerTypes constructors _ := x.decls[family.ownerDecl]!
    | return #[.declarationType metadata.owner metadata.name]
  let some ownerType := ownerTypes.find? (fun type => type.name == metadata.owner)
    | return #[.declarationType metadata.owner metadata.name]
  let [constructorName] := ownerType.ctors
    | return #[.declarationType metadata.owner metadata.name]
  let some constructor := constructors.find? fun candidate =>
      candidate.name == constructorName && candidate.induct == metadata.owner
    | return #[.declarationType metadata.owner metadata.name]
  unless ownerType.isKernelStructureLike constructors &&
      !isPropositionFormer x ownerType.type do
    return #[.declarationType metadata.owner metadata.name]
  if ownerType.levelParams.length != model.levelParams.length then
    return #[.universeArity metadata.owner metadata.name
      ownerType.levelParams.length model.levelParams.length]
  let some typePair := family.correspondence.typeFormers.find?
      (·.owner == metadata.owner)
    | return #[.declarationType metadata.owner metadata.name]
  let some constructorPair := family.correspondence.constructors.find?
      (·.owner == constructorName)
    | return #[.declarationType metadata.owner metadata.name]
  let levels := model.levelParams.map Level.param
  let mappedOwnerType := family.correspondence.expectedType
    ownerType.levelParams model.levelParams ownerType.type
  let (parameterBinders, ownerResult) : Array OpenBinder × Expr := openForalls
    ((`_check.structureEtaOwner).append metadata.owner) mappedOwnerType
  unless parameterBinders.size == ownerType.numParams && ownerType.numIndices == 0 do
    return #[.declarationType metadata.owner metadata.name]
  let params := parameterBinders.map fun binder => binder.value
  let .sort carrierLevel := formerWhnf x ownerResult
    | return #[.declarationType metadata.owner metadata.name]
  let carrier := mkAppN (.const typePair.model levels) params
  let selfValue := mkFVar (FVarId.mk
    ((`_check.structureEtaSelf).append metadata.owner))
  let selfBinder : OpenBinder :=
    { name := `x, type := carrier, info := .default, value := selfValue }
  let mappedConstructorType := family.correspondence.expectedType
    constructor.levelParams model.levelParams constructor.type
  let some constructorTail := instantiateForallsExact mappedConstructorType params
    | return #[.declarationType metadata.owner metadata.name]
  let (fieldBinders, _) : Array OpenBinder × Expr := openForalls
    ((`_check.structureEtaFields).append metadata.owner) constructorTail
  unless fieldBinders.size == constructor.numFields do
    return #[.declarationType metadata.owner metadata.name]
  let mut fields : Array Expr := #[]
  for fieldIndex in [0:constructor.numFields] do
    let some projection := family.correspondence.projections.find? fun projection =>
        projection.owner == metadata.owner && projection.fieldIndex == fieldIndex
      | return #[.declarationType metadata.owner metadata.name]
    fields := fields.push <| mkAppN (.const projection.name levels) (params.push selfValue)
  let reconstruction := mkAppN (.const constructorPair.model levels) (params ++ fields)
  let expectedBody := mkAppN (.const ``Eq [carrierLevel])
    #[carrier, selfValue, reconstruction]
  let expected := closeForalls (parameterBinders.push selfBinder) expectedBody
  if model.type != expected then
    return #[.declarationType metadata.owner metadata.name]
  return #[]

private abbrev ExactLocals := Array (FVarId × Expr)

private def ExactLocals.typeOf? (locals : ExactLocals) (id : FVarId) : Option Expr :=
  (locals.find? (·.1 == id)).map (·.2)

private partial def exactWhnf : Expr → Expr
  | .mdata _ body => exactWhnf body
  | .letE _ _ value body _ => exactWhnf (body.instantiate1 value)
  | expression => expression

private def structureOwner? (x : Export) (owner : Name) : Option (EIndType × List ECtor) :=
  x.decls.findSome? fun declaration => match declaration with
    | .induct types constructors _ =>
      (types.find? (·.name == owner)).map fun type => (type, constructors)
    | _ => none

mutual

/-- A deliberately small, exact type synthesizer for the result of an
exported projection declaration.  It never unfolds a definition: declaration
types and local binder types suffice to expose the result sort, while the
projection case follows the exact recovered primitive projection interface. -/
private partial def inferExactType? (x : Export) (declarations : DeclarationTypes)
    (locals : ExactLocals) : Expr → Option Expr
  | .sort level => some (.sort (.succ level))
  | .fvar id => locals.typeOf? id
  | .const name levels => do
      let declaration ← (declarations.getD name #[])[0]?
      if declaration.levelParams.length != levels.length then none
      return declaration.type.instantiateLevelParams declaration.levelParams levels
  | .app function argument => do
      let functionType := exactWhnf (← inferExactType? x declarations locals function)
      let .forallE _ _ body _ := functionType | none
      return body.instantiate1 argument
  | .lam name domain body info => do
      let value := mkFVar (FVarId.mk ((`_check.exactLam).mkNum locals.size))
      let bodyType ← inferExactType? x declarations
        (locals.push (value.fvarId!, domain)) (body.instantiate1 value)
      return .forallE name domain (bodyType.abstract #[value]) info
  | .forallE name domain body info => do
      let domainLevel ← inferExactSortLevel? x declarations locals domain
      let value := mkFVar (FVarId.mk ((`_check.exactPi).mkNum locals.size))
      let bodyLevel ← inferExactSortLevel? x declarations
        (locals.push (value.fvarId!, domain)) (body.instantiate1 value)
      let _ := name
      let _ := info
      return .sort (Level.imax domainLevel bodyLevel).normalize
  | .letE _ _ value body _ =>
      inferExactType? x declarations locals (body.instantiate1 value)
  | .mdata _ body => inferExactType? x declarations locals body
  | .proj owner fieldIndex struct => do
      let structType := exactWhnf (← inferExactType? x declarations locals struct)
      let .const structOwner levels := structType.getAppFn | none
      unless structOwner == owner do none
      let (type, constructors) ← structureOwner? x owner
      let constructorName ← type.ctors.head?
      let constructor ← constructors.find? fun constructor =>
        constructor.name == constructorName && constructor.induct == owner
      unless type.ctors == [constructorName] do none
      unless (x.intrinsicProjectionFieldsFor type constructors).contains fieldIndex do none
      unless constructor.levelParams.length == levels.length do none
      let ownerArguments := structType.getAppArgs
      unless ownerArguments.size == type.numParams + type.numIndices do none
      let params := ownerArguments.extract 0 type.numParams
      let mut current ← instantiateForallsExact
        (constructor.type.instantiateLevelParams constructor.levelParams levels) params
      for earlier in [0:fieldIndex + 1] do
        let .forallE _ fieldType rest _ := current | none
        if earlier == fieldIndex then return fieldType
        current := rest.instantiate1 (.proj owner earlier struct)
      none
  | .lit (.natVal _) => some (.const ``Nat [])
  | .lit (.strVal _) => some (.const ``String [])
  | .bvar _ | .mvar _ => none

private partial def inferExactSortLevel? (x : Export) (declarations : DeclarationTypes)
    (locals : ExactLocals) (expression : Expr) : Option Level := do
  let .sort level := exactWhnf (← inferExactType? x declarations locals expression) | none
  return level

end

/-- Check one intrinsic projection and its literal constructor rule.

There is no source projection declaration to rewrite.  Both types are
synthesized from the unique constructor telescope.  References to earlier
fields in a dependent result become applications of the corresponding earlier
intrinsic projections. -/
private def checkProjection (x : Export) (family : Family) (declarations : DeclarationTypes)
    (projection : Naming.Projection) : Array Violation := Id.run do
  let projectionModels := declarations.getD projection.name #[]
  if projectionModels.isEmpty then
    return #[.missingPublic projection.owner projection.name]
  if projectionModels.size != 1 then
    return #[.duplicatePublic projection.owner projection.name projectionModels.size]
  let ruleModels := declarations.getD projection.iota #[]
  if ruleModels.isEmpty then return #[.missingPublic projection.owner projection.iota]
  if ruleModels.size != 1 then
    return #[.duplicatePublic projection.owner projection.iota ruleModels.size]
  let .induct _ ownerConstructors _ := x.decls[family.ownerDecl]!
    | return #[.declarationType projection.owner projection.name]
  let some constructor := ownerConstructors.find? (·.induct == projection.owner)
    | return #[.declarationType projection.owner projection.name]
  let some constructorPair := family.correspondence.constructors.find?
      (·.owner == constructor.name)
    | return #[.declarationType projection.owner projection.name]
  let ownerTypes : List EIndType := match x.decls[family.ownerDecl]! with
    | .induct types _ _ => types
    | _ => []
  let some ownerType := ownerTypes.find? (fun (type : EIndType) => type.name == projection.owner)
    | return #[.declarationType projection.owner projection.name]
  let model := projectionModels[0]!
  let ruleModel := ruleModels[0]!
  if ownerType.levelParams.length != model.levelParams.length then
    return #[.universeArity projection.owner projection.name
      ownerType.levelParams.length model.levelParams.length]
  if ownerType.levelParams.length != ruleModel.levelParams.length then
    return #[.universeArity projection.owner projection.iota
      ownerType.levelParams.length ruleModel.levelParams.length]
  let mappedConstructorType := family.correspondence.expectedType
    constructor.levelParams model.levelParams constructor.type
  let (constructorBinders, constructorResult) : Array OpenBinder × Expr := openForalls
    ((`_check.intrinsicProjectionCtor).append projection.name) mappedConstructorType
  unless constructorBinders.size == constructor.numParams + constructor.numFields do
    return #[.declarationType projection.owner projection.name]
  let constructorArgs := constructorBinders.map fun (binder : OpenBinder) => binder.value
  let params := constructorArgs.extract 0 constructor.numParams
  let fields := constructorArgs.extract constructor.numParams constructorArgs.size
  let levels := model.levelParams.map Level.param
  let some typePair := family.correspondence.typeFormers.find? (·.owner == projection.owner)
    | return #[.declarationType projection.owner projection.name]
  let mappedOwnerType := family.correspondence.expectedType
    ownerType.levelParams model.levelParams ownerType.type
  let (ownerBinders, _) : Array OpenBinder × Expr := openForalls
    ((`_check.intrinsicProjectionOwner).append projection.name) mappedOwnerType
  let ownerArity := ownerType.numParams + ownerType.numIndices
  unless ownerBinders.size == ownerArity do
    return #[.declarationType projection.owner projection.name]
  let ownerArgs := ownerBinders.map fun (binder : OpenBinder) => binder.value
  let ownerParams := ownerArgs.extract 0 ownerType.numParams
  let some projectionFieldsType := instantiateForallsExact mappedConstructorType ownerParams
    | return #[.declarationType projection.owner projection.name]
  let (projectionFieldBinders, _) : Array OpenBinder × Expr := openForalls
    ((`_check.intrinsicProjectionFields).append projection.name) projectionFieldsType
  let some selectedBinder := projectionFieldBinders[projection.fieldIndex]?
    | return #[.declarationType projection.owner projection.name]
  let selfValue := mkFVar (FVarId.mk
    ((`_check.intrinsicProjectionSelf).append projection.name))
  let selfBinder : OpenBinder :=
    { name := `self, type := mkAppN (.const typePair.model levels) ownerArgs,
      info := .default, value := selfValue }
  let projectionFieldArgs := projectionFieldBinders.map fun (binder : OpenBinder) => binder.value
  let mut projectionResult := selectedBinder.type
  for earlier in [:projection.fieldIndex] do
    let earlierField := projectionFieldArgs[earlier]!
    let earlierProjection := mkAppN
      (.const (Naming.projectionName projection.owner earlier) levels) (ownerArgs.push selfValue)
    projectionResult := projectionResult.replace fun subexpression =>
      if subexpression == earlierField then some earlierProjection else none
  let expectedProjectionType := closeForalls
    (ownerBinders.push selfBinder) projectionResult
  let mut violations := checkImplementationDecl projection.owner model
  violations := violations ++ checkTheoremDecl projection.owner ruleModel
  unless model.type == expectedProjectionType do
    violations := violations.push (.declarationType projection.owner projection.name)

  let major := mkAppN (.const constructorPair.model levels) constructorArgs
  let constructorIndices := constructorResult.getAppArgs.extract constructor.numParams ownerArity
  unless constructorIndices.size == ownerType.numIndices do
    return violations.push (.declarationType projection.owner projection.iota)
  let some alpha := instantiateForallsExact expectedProjectionType
      (params ++ constructorIndices ++ #[major])
    | return violations.push (.declarationType projection.owner projection.iota)
  let lhs := mkAppN (.const projection.name levels) (params ++ constructorIndices ++ #[major])

  let sourceConstructorType := constructor.type
  let (sourceBinders, _) : Array OpenBinder × Expr := openForalls
    ((`_check.intrinsicProjectionSource).append projection.name) sourceConstructorType
  let some sourceField := sourceBinders[constructor.numParams + projection.fieldIndex]?
    | return violations.push (.declarationType projection.owner projection.iota)
  let sourceLocals := sourceBinders.map fun (binder : OpenBinder) =>
    (binder.value.fvarId!, binder.type)
  let mut normalizedFields : Array ProjectionField := #[]
  for index in [:fields.size] do
    let some mappedField := constructorBinders[constructor.numParams + index]?
      | return violations.push (.declarationType projection.owner projection.iota)
    let some sourceFieldAtIndex := sourceBinders[constructor.numParams + index]?
      | return violations.push (.declarationType projection.owner projection.iota)
    let some sourceLevel := inferExactSortLevel? x declarations sourceLocals
        sourceFieldAtIndex.type
      | return violations.push (.declarationType projection.owner projection.iota)
    let level := sourceLevel.instantiateParams constructor.levelParams
      (model.levelParams.map Level.param)
    let projected := mkAppN
      (.const (Naming.projectionName projection.owner index) levels)
      (params ++ constructorIndices ++ #[major])
    let iota? := if index < projection.fieldIndex then
      some (mkAppN (.const (Naming.projectionIotaName projection.owner index) levels)
        constructorArgs)
    else none
    normalizedFields := normalizedFields.push
      { name := Name.mkSimple s!"field_{index}", info := .default,
        value := fields[index]!, type := mappedField.type, level, projected, iota? }
  let eqi : EqInfo := { eqN := ``Eq, reflN := ``Eq.refl, recN := ``Eq.rec }
  let .ok rhs := ProjectionField.normalizeProjectionField eqi projection.name
      normalizedFields projection.fieldIndex
    | return violations.push (.declarationType projection.owner projection.iota)
  let some sourceEqLevel := inferExactSortLevel? x declarations sourceLocals sourceField.type
    | return violations.push (.declarationType projection.owner projection.iota)
  let eqLevel := sourceEqLevel.instantiateParams constructor.levelParams
    (model.levelParams.map Level.param)
  let expectedBody := mkAppN (.const ``Eq [eqLevel]) #[alpha, lhs, rhs]
  let expected := closeForalls constructorBinders expectedBody
  unless ruleModel.type == expected do
    violations := violations.push (.declarationType projection.owner projection.iota)
  return violations

private def iotaSlot? (name : Name) : Option (Name × Nat) := do
  let .str parent suffix := name | none
  unless suffix.startsWith "iota_" do none
  return (parent, ← (suffix.drop 5).toNat?)

private def projectionSlot? (owner name : Name) : Option Nat := do
  let modelRoot := Naming.modelName owner
  match name with
  | .str parent suffix =>
    if parent == modelRoot && suffix.startsWith "proj_" then
      (suffix.drop 5).toNat?
    else if suffix == "iota" then
      let .str grandParent projectionSuffix := parent | none
      unless grandParent == modelRoot && projectionSuffix.startsWith "proj_" do none
      (projectionSuffix.drop 5).toNat?
    else none
  | _ => none

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
      .extraConstructor owner .. | .extraProjection owner .. |
      .extraRule owner .. | .extraMetadata owner .. |
      .universeArity owner .. |
      .declarationType owner .. | .declarationKind owner .. |
      .declarationSafety owner .. => owner

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
    for projection in family.correspondence.projections do
      violations := violations ++ checkProjection x family declarations projection
    for iota in family.correspondence.iotas do
      violations := violations ++ checkIota x constructors family declarations iota
    for metadata in family.correspondence.metadata do
      violations := violations ++ checkTheoremSlot declarations metadata.owner metadata.name
      if metadata.kind == .unitlike then
        violations := violations ++ checkUnitlike x family declarations metadata
      else if metadata.kind == .eta then
        violations := violations ++ checkEta x family declarations metadata
      else if metadata.kind == .ruleK then
        violations := violations ++ checkRuleK x family declarations metadata
    for pair in family.correspondence.recursors do
      let numRules := (family.correspondence.iotas.filter (·.recursor == pair.owner)).size
      for (name, ruleIndex) in ruleSlots.getD pair.model #[] do
        if ruleIndex >= numRules || name != Naming.iotaName pair.owner ruleIndex then
          violations := violations.push (.extraRule pair.owner name)
  -- An extra metadata-looking theorem is invalid even when no carrier or
  -- other public slot exists to make the declaration a discoverable model
  -- family.  The exact owner record, not suffix parsing, determines the slot.
  for ownerDecl in [0:x.decls.size] do
    let .induct types constructors recursors := x.decls[ownerDecl]! | continue
    for type in types do
      let validFields := x.intrinsicProjectionFieldsFor type constructors
      for declaration in x.decls do
        for name in declaration.names do
          if let some fieldIndex := projectionSlot? type.name name then
            unless validFields.contains fieldIndex do
              violations := violations.push (.extraProjection type.name name)
      unless type.isKernelUnitlike constructors do
        let name := Naming.unitlikeName type.name
        unless (declarations.getD name #[]).isEmpty do
          violations := violations.push (.extraMetadata type.name name .unitlike)
      unless type.isKernelStructureLike constructors &&
          !isPropositionFormer x type.type do
        let name := Naming.etaName type.name
        unless (declarations.getD name #[]).isEmpty do
          violations := violations.push (.extraMetadata type.name name .eta)
    for recursor in recursors do
      unless recursor.k do
        let name := Naming.ruleKName recursor.name
        unless (declarations.getD name #[]).isEmpty do
          violations := violations.push (.extraMetadata recursor.name name .ruleK)
  return violations

end Modelgen.Check
