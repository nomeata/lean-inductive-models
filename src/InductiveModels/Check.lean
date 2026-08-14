import InductiveModels.Format
import InductiveModels.Naming
import InductiveModels.Projection

/-!
# Structural checks for exported inductive models

This module is the format-only foundation of the model checker.  It discovers
public model families solely from the declarations in an original inductive
record.  If that record declares type former `T`, constructor `C`, recursor `R`
and rule `j`, their public names are respectively `T._model`, `C._model`,
`R._model` and `R._model.iota_j`, constructed by [`InductiveModels.Naming`].  A
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
field of `Expr.proj` as references. Literal comparisons never ask for
definitional equality; the few kernel-visible sort observations use only the
bounded export-syntax normalizer from `InductiveModels.Format`.
-/

open Lean

namespace InductiveModels.Check

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

/-- The historical driver statement metric: one comparison for each modeled
recursor type and ordinary iota, two for each intrinsic projection (definition
and iota), and one for each rule-K theorem.  Type formers, constructors,
unit-like witnesses and eta are checked by the same structural pass, but were
never included in the CLI's `statements:` count. -/
def Correspondence.statementCount (table : Correspondence) : Nat :=
  table.recursors.size + table.iotas.size + 2 * table.projections.size +
    (table.metadata.filter (·.kind == .ruleK)).size

/-- Every exact source declaration to which a structural diagnostic for this
correspondence may be attributed.  A generated mutual or nested family is
reported under its root, but its violations remain attached to the particular
member, constructor, or recursor whose public slot is wrong. -/
def Correspondence.diagnosticOwners (table : Correspondence) : Array Name :=
  table.entries.foldl
    (fun owners pair => if owners.contains pair.owner then owners else owners.push pair.owner) #[]

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

/-- Rename universe parameters without normalizing the exported level syntax.

`Level.instantiateParams` deliberately canonicalizes expressions such as
`max 1 (u+1)`.  That is useful to the kernel, but it is the wrong operation at
the literal public-interface boundary: lean4export records that redundant
`max`, and a generated declaration which retained it must be compared with the
same tree. -/
private partial def renameLevelParamsExact (renames : Std.HashMap Name Name) : Level → Level
  | .zero => .zero
  | .succ level => .succ (renameLevelParamsExact renames level)
  | .max left right =>
    .max (renameLevelParamsExact renames left) (renameLevelParamsExact renames right)
  | .imax left right =>
    .imax (renameLevelParamsExact renames left) (renameLevelParamsExact renames right)
  | .param name => .param (renames[name]?.getD name)
  | .mvar id => .mvar id

/-- The expression analogue of [`renameLevelParamsExact`].  Rebuild only nodes
which can carry levels; ordinary expression syntax and sharing are otherwise
left to `Expr.replace`. -/
private def renameExprLevelParamsExact (ownerParams modelParams : List Name)
    (expression : Expr) : Expr :=
  let renames := (ownerParams.zip modelParams).foldl
    (fun map pair => map.insert pair.1 pair.2) ({} : Std.HashMap Name Name)
  expression.replace fun subexpression => match subexpression with
    | .sort level => some (.sort (renameLevelParamsExact renames level))
    | .const name levels =>
      some (.const name (levels.map (renameLevelParamsExact renames)))
    | _ => none

private def renameLevelParamNamesExact (ownerParams modelParams : List Name)
    (level : Level) : Level :=
  let renames := (ownerParams.zip modelParams).foldl
    (fun map pair => map.insert pair.1 pair.2) ({} : Std.HashMap Name Name)
  renameLevelParamsExact renames level

/-- Align the owner's declaration universes with the model declaration's by
position and then apply the simultaneous public constant substitution.  A
length mismatch is rejected by the caller rather than truncated here. -/
def Correspondence.expectedType (table : Correspondence) (ownerParams modelParams : List Name)
    (type : Expr) : Expr :=
  table.substitute (renameExprLevelParamsExact ownerParams modelParams type)

/-- Align and rewrite an iota proposition while retaining its outer ambient
`Eq`.  This distinction matters when the modeled inductive is itself `Eq`: its
arguments and rule use `Eq._model`, but the theorem relating both sides still
uses the export's equality type. -/
def Correspondence.expectedIotaType (table : Correspondence)
    (ownerParams modelParams : List Name) (type : Expr) : Expr :=
  let aligned := renameExprLevelParamsExact ownerParams modelParams type
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

private abbrev Constructors := Lean.PersistentHashMap Name ECtor

private abbrev StructureOwners := Lean.PersistentHashMap Name (EIndType × List ECtor)

private def constructorRecords (x : Export) : Constructors := Id.run do
  let mut result : Constructors := {}
  for declaration in x.decls do
    if let .induct _ constructors _ := declaration then
      for constructor in constructors do result := result.insert constructor.name constructor
  return result

private def structureOwners (x : Export) : StructureOwners := Id.run do
  let mut result : StructureOwners := {}
  for declaration in x.decls do
    if let .induct types constructors _ := declaration then
      for type in types do result := result.insert type.name (type, constructors)
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
  let constructor ← constructors.find? rule.ctor
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
  let constructor ← (constructorRecords x).find? ctorName
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

/-- The correspondence table determined by one inductive record and its exact
syntax context, independent of whether any model declarations are present. -/
private def correspondenceFor? (normalizer : ExactNormalizationEnv)
    (projectionFields : EIndType → List ECtor → Array Nat)
    (declaration : EDecl) : Option Correspondence := do
  let .induct types ctors recursors := declaration | none
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
    if type.isKernelStructureLike ctors &&
        !normalizer.isPropositionFormer type.type then
      some (Naming.Metadata.ofOwner .eta type.name)
    else none
  let mut projections : Array Naming.Projection := #[]
  for type in types do
    for fieldIndex in projectionFields type ctors do
      projections := projections.push (.ofField type.name fieldIndex)
  let metadata := unitlikeMetadata ++ etaMetadata ++ ruleKMetadata
  return { typeFormers, constructors, recursors, projections, iotas, metadata }

/-- The correspondence table determined by an inductive record, independent
of whether any model declarations are present. -/
def correspondenceAt? (x : Export) (ownerDecl : Nat) : Option Correspondence := do
  let declaration ← x.decls[ownerDecl]?
  correspondenceFor? x.exactNormalizationEnv x.intrinsicProjectionFieldsFor declaration

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

/-- Stable text for a structural violation, shared by the CLI and the
generation-time syntactic oracle. -/
def Violation.message : Violation → String
  | .modelNotBefore owner declaration modelDecl ownerDecl =>
      s!"model declaration {declaration} at record {modelDecl} is not before \
        {owner} at record {ownerDecl}"
  | .ownerBackreference owner target =>
      s!"modeled inductive {owner} refers back to {target}"
  | .missingPublic owner expected =>
      s!"model of {owner} is missing {expected}"
  | .duplicatePublic owner expected count =>
      s!"model of {owner} declares {expected} {count} times"
  | .extraConstructor owner declaration =>
      s!"model of {owner} has an unexpected constructor declaration {declaration}"
  | .extraProjection owner declaration =>
      s!"model of {owner} has an unexpected intrinsic projection declaration {declaration}"
  | .extraRule owner declaration =>
      s!"model recursor {owner} has an unexpected reduction theorem {declaration}"
  | .extraMetadata owner declaration kind =>
      s!"model of {owner} has unexpected {repr kind} metadata {declaration}"
  | .universeArity owner declaration ownerArity modelArity =>
      s!"{declaration}, modeling {owner}, has {modelArity} universe parameters; \
        expected {ownerArity}"
  | .declarationType owner declaration =>
      s!"type of {declaration} does not literally model the type of {owner}"
  | .declarationKind owner declaration expected actual =>
      s!"{declaration}, modeling {owner}, is a {repr actual}; expected a {repr expected}"
  | .declarationSafety owner declaration actual =>
      s!"{declaration}, modeling {owner}, has safety {actual}; expected safe"

private def appendUnique (names : Array Name) (more : List Name) : Array Name :=
  more.foldl (fun out name => if out.contains name then out else out.push name) names

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

/-! ## Name-only owner-reference certificates

The compact whole-output checker no longer retains an inductive record's
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

private abbrev DeclarationTypes := Lean.PersistentHashMap Name (Array DeclType)

private def declarationTypes (x : Export) : DeclarationTypes := Id.run do
  let mut declarations : DeclarationTypes := {}
  for declaration in x.decls do
    for info in declTypes declaration do
      declarations := declarations.insert info.name
        ((declarations.findD info.name #[]).push info)
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
  match declarations.findD name #[] with
  | #[declaration] => checkTheoremDecl owner declaration
  | _ => #[]

private inductive Phase1OneLayerCertificate where
  | absent
  | valid
  | malformed (slot : Name)

private def rewriteCertificateNames (mapping : Array (Name × Name)) (type : Expr) : Expr :=
  type.replace fun expression => match expression with
    | .const name levels => mapping.findSome? fun (source, target) =>
        if name == source then some (.const target levels) else none
    | _ => none

/-- Recognize the complete first-tranche private/public interface from the
serialized declarations.  Names alone do not select the new contract: every
private public-facing type, both directions of the equivalence, and both laws
must be uniquely present and exact.  A partial prefix is malformed rather
than a request to reinterpret the family as legacy output. -/
private def phase1OneLayerCertificate (declarations : DeclarationTypes)
    (ownerType : EIndType) (constructors : Array ECtor) (recursors : Array ERec)
    (family : Family) :
    Phase1OneLayerCertificate := Id.run do
  let publicCarrierName := Naming.modelName ownerType.name
  let impl := Name.str publicCarrierName "_impl"
  let privateCarrierName := Name.str impl "self"
  let privateConstructorName := Name.str impl "ctor_0"
  let privateRecursorName := Name.str impl "rec"
  let privateIotaName := Name.str impl "rec_iota_0"
  let rollName := Name.str impl "roll"
  let unrollName := Name.str impl "unroll"
  let unrollRollName := Name.str impl "unroll_roll"
  let rollUnrollName := Name.str impl "roll_unroll"
  let certificateNames := #[privateCarrierName, privateConstructorName,
    privateRecursorName, privateIotaName, rollName, unrollName,
    unrollRollName, rollUnrollName]
  unless certificateNames.any declarations.contains do return .absent
  let some sourceConstructor := constructors.find? fun constructor =>
      constructor.induct == ownerType.name && ownerType.ctors.contains constructor.name
    | return .malformed privateConstructorName
  let some sourceRecursor := recursors.find? fun recursor =>
      recursor.all.contains ownerType.name &&
        recursor.rules.any (·.ctor == sourceConstructor.name)
    | return .malformed privateRecursorName
  unless oneLayerProjectionFamily #[ownerType] ownerType ||
      indexedFibreOneLayerProjectionFamily #[ownerType] ownerType sourceConstructor
        sourceRecursor do
    return .malformed privateCarrierName
  let some constructorPair := family.correspondence.constructors[0]?
    | return .malformed privateConstructorName
  let some recursorPair := family.correspondence.recursors[0]?
    | return .malformed privateRecursorName
  let some iota := family.correspondence.iotas[0]?
    | return .malformed privateIotaName
  let unique := fun name => match declarations.findD name #[] with
    | #[declaration] => some declaration
    | _ => none
  let some publicCarrier := unique publicCarrierName | return .malformed publicCarrierName
  let some publicConstructor := unique constructorPair.model
    | return .malformed constructorPair.model
  let some publicRecursor := unique recursorPair.model
    | return .malformed recursorPair.model
  let some publicIota := unique iota.name | return .malformed iota.name
  let some privateCarrier := unique privateCarrierName | return .malformed privateCarrierName
  let some privateConstructor := unique privateConstructorName
    | return .malformed privateConstructorName
  let some privateRecursor := unique privateRecursorName | return .malformed privateRecursorName
  let some privateIota := unique privateIotaName | return .malformed privateIotaName
  let some roll := unique rollName | return .malformed rollName
  let some unroll := unique unrollName | return .malformed unrollName
  let some unrollRoll := unique unrollRollName | return .malformed unrollRollName
  let some rollUnroll := unique rollUnrollName | return .malformed rollUnrollName
  unless publicCarrier.name == publicCarrierName do return .malformed publicCarrierName
  unless privateCarrier.kind == .defn && privateCarrier.safety? == some "safe" do
    return .malformed privateCarrierName
  unless privateConstructor.kind == .defn && privateConstructor.safety? == some "safe" do
    return .malformed privateConstructorName
  unless privateRecursor.kind == .defn && privateRecursor.safety? == some "safe" do
    return .malformed privateRecursorName
  unless privateIota.kind == .thm do return .malformed privateIotaName
  unless roll.kind == .defn && roll.safety? == some "safe" do return .malformed rollName
  unless unroll.kind == .defn && unroll.safety? == some "safe" do return .malformed unrollName
  unless unrollRoll.kind == .thm do return .malformed unrollRollName
  unless rollUnroll.kind == .thm do return .malformed rollUnrollName
  unless #[privateCarrier, privateConstructor, roll, unroll, unrollRoll, rollUnroll].all
      (·.levelParams == publicCarrier.levelParams) &&
      privateRecursor.levelParams == publicRecursor.levelParams &&
      privateIota.levelParams == publicIota.levelParams do
    return .malformed (Name.str privateCarrierName "levels")
  let mapping := #[(publicCarrierName, privateCarrierName),
    (constructorPair.model, privateConstructorName),
    (recursorPair.model, privateRecursorName), (iota.name, privateIotaName)]
  unless privateCarrier.type == publicCarrier.type do
    return .malformed (Name.str privateCarrierName "type")
  unless privateConstructor.type == rewriteCertificateNames mapping publicConstructor.type do
    return .malformed privateConstructorName
  unless privateRecursor.type == rewriteCertificateNames mapping publicRecursor.type do
    return .malformed privateRecursorName
  unless privateIota.type == rewriteCertificateNames mapping publicIota.type do
    return .malformed privateIotaName
  let (parameters, result) := openForalls
    ((`_check.oneLayerCertificate).append ownerType.name) publicCarrier.type
  unless parameters.size == ownerType.numParams + ownerType.numIndices do
    return .malformed publicCarrierName
  let .sort carrierLevel := result | return .malformed publicCarrierName
  let levels := publicCarrier.levelParams.map Level.param
  let parameterValues := parameters.map (fun binder => binder.value)
  let publicCarrierType := mkAppN (.const publicCarrierName levels) parameterValues
  let privateCarrierType := mkAppN (.const privateCarrierName levels) parameterValues
  let publicValue : OpenBinder :=
    { name := `public, type := publicCarrierType, info := .default
      value := mkFVar (FVarId.mk ((`_check.oneLayerPublic).append ownerType.name)) }
  let privateValue : OpenBinder :=
    { name := `private, type := privateCarrierType, info := .default
      value := mkFVar (FVarId.mk ((`_check.oneLayerPrivate).append ownerType.name)) }
  let expectedRoll := closeForalls (parameters.push publicValue) privateCarrierType
  let expectedUnroll := closeForalls (parameters.push privateValue) publicCarrierType
  unless roll.type == expectedRoll do return .malformed rollName
  unless unroll.type == expectedUnroll do return .malformed unrollName
  let rollApp := mkAppN (.const rollName levels) (parameterValues.push publicValue.value)
  let unrollRollApp := mkAppN (.const unrollName levels) (parameterValues.push rollApp)
  let unrollRollBody := mkAppN (.const ``Eq [carrierLevel])
    #[publicCarrierType, unrollRollApp, publicValue.value]
  unless unrollRoll.type == closeForalls (parameters.push publicValue) unrollRollBody do
    return .malformed unrollRollName
  let unrollApp := mkAppN (.const unrollName levels) (parameterValues.push privateValue.value)
  let rollUnrollApp := mkAppN (.const rollName levels) (parameterValues.push unrollApp)
  let rollUnrollBody := mkAppN (.const ``Eq [carrierLevel])
    #[privateCarrierType, rollUnrollApp, privateValue.value]
  unless rollUnroll.type == closeForalls (parameters.push privateValue) rollUnrollBody do
    return .malformed rollUnrollName
  return .valid

/-- Recognize the complete serialized simultaneous family boundary.  The
family root comes from the first source owner, but every member, constructor,
and rule slot is recovered by its source owner/key.  Seeing any prefix commits
the checker to validating the whole certificate; a partial family is never
interpreted as legacy mutual output. -/
private def phase1MutualOneLayerCertificate (declarations : DeclarationTypes)
    (ownerTypes : Array EIndType) (constructors : Array ECtor) (recursors : Array ERec)
    (normalizer : ExactNormalizationEnv) (family : Family) : Phase1OneLayerCertificate := Id.run do
  let some first := ownerTypes[0]? | return .absent
  let root := Name.str (Naming.modelName first.name) "_impl"
  let support := #[Name.str root "tag", Name.str root "aux"]
  let memberRoot := fun owner => Name.str root (lastStr owner)
  let privateSelf := fun owner => Name.str (memberRoot owner) "self"
  let privateRecursor := fun owner => Name.str (memberRoot owner) "rec"
  let privateConstructor := fun owner constructor =>
    Name.str (Name.str (memberRoot owner) "ctor") (lastStr constructor)
  let privateIota := fun owner constructor =>
    Name.str (Name.str (memberRoot owner) "rec_iota") (lastStr constructor)
  let privateRule := fun owner constructor =>
    Name.str (Name.str (memberRoot owner) "rule") (lastStr constructor)
  let roll := fun owner => Name.str (memberRoot owner) "roll"
  let unroll := fun owner => Name.str (memberRoot owner) "unroll"
  let unrollRoll := fun owner => Name.str (memberRoot owner) "unroll_roll"
  let rollUnroll := fun owner => Name.str (memberRoot owner) "roll_unroll"
  -- `tag` and `aux` are shared with every legacy mutual encoding.  Only a
  -- member-local adapter slot commits the stream to this new certificate.
  let mut certificateNames : Array Name := #[]
  for ownerType in ownerTypes do
    certificateNames := certificateNames ++ #[privateSelf ownerType.name,
      privateRecursor ownerType.name, roll ownerType.name, unroll ownerType.name,
      unrollRoll ownerType.name, rollUnroll ownerType.name]
    for constructor in constructors do
      if constructor.induct == ownerType.name then
        certificateNames := certificateNames.push
          (privateConstructor ownerType.name constructor.name)
    if let some recursor := recursors.find? fun recursor =>
        recursor.name == Name.str ownerType.name "rec" then
      for rule in recursor.rules do
        certificateNames := certificateNames ++ #[privateIota ownerType.name rule.ctor,
          privateRule ownerType.name rule.ctor]
  unless certificateNames.any declarations.contains do return .absent
  unless ownerTypes.size ≥ 2 do return .malformed root
  let all := ownerTypes.map (·.name)
  unless ownerTypes.all fun ownerType =>
      ownerType.all.toArray == all && ownerType.numIndices == 0 && ownerType.numNested == 0 &&
        ownerType.isRec && !ownerType.isUnsafe && ownerType.numParams == first.numParams do
    return .malformed root
  let mut anyChanged := false
  let mut edges : Array (Name × Name) := #[]
  for ownerType in ownerTypes do
    let (_, carrierResult) := openForalls
      ((`_check.mutualOneLayerShape).append ownerType.name) ownerType.type
    let .sort carrierLevel := carrierResult | return .malformed (privateSelf ownerType.name)
    unless carrierLevel.normalize.isNeverZero do
      return .malformed (privateSelf ownerType.name)
    let ownerConstructors := constructors.filter (·.induct == ownerType.name)
    unless ownerConstructors.size == ownerType.ctors.length do
      return .malformed (privateSelf ownerType.name)
    let mut changed := false
    for constructor in ownerConstructors do
      let (binders, _) := openForalls
        ((`_check.mutualOneLayerFields).append constructor.name) constructor.type
      unless binders.size == constructor.numParams + constructor.numFields do
        return .malformed (privateConstructor ownerType.name constructor.name)
      let fields := binders.extract constructor.numParams binders.size
      let fieldTypes := fields.map (·.type)
      let fieldValues := fields.map (·.value)
      let mut recursiveFields := 0
      for fieldIndex in [:fields.size] do
        let normalized := normalizer.whnf fieldTypes[fieldIndex]!
        let target? := all.find? fun candidate =>
          normalized.getAppFn.constName? == some candidate &&
            normalized.getAppArgs.size == first.numParams
        if target?.isNone && all.any (fieldTypes[fieldIndex]!.getUsedConstants.contains ·) then
          return .malformed (privateConstructor ownerType.name constructor.name)
        if target?.isSome then
          recursiveFields := recursiveFields + 1
          edges := edges.push (ownerType.name, target?.get!)
          let fieldId := fieldValues[fieldIndex]!.fvarId!
          for later in [fieldIndex + 1:fields.size] do
            if fieldTypes[later]!.containsFVar fieldId then
              return .malformed (privateConstructor ownerType.name constructor.name)
          changed := true
      unless recursiveFields ≤ 1 do
        return .malformed (privateConstructor ownerType.name constructor.name)
    anyChanged := anyChanged || (ownerType.ctors.length == 1 && changed)
  unless anyChanged do return .malformed root
  for source in all do
    let mut reached : Std.HashSet Name := { source }
    let mut progress := true
    while progress do
      progress := false
      for edge in edges do
        if reached.contains edge.1 && !reached.contains edge.2 then
          reached := reached.insert edge.2
          progress := true
    unless all.all reached.contains do return .malformed root
  let unique := fun name => match declarations.findD name #[] with
    | #[declaration] => some declaration
    | _ => none
  for name in support do
    let some declaration := unique name | return .malformed name
    unless declaration.kind == .induct do return .malformed name
  for memberIndex in [:ownerTypes.size] do
    let ownerType := ownerTypes[memberIndex]!
    let owner := ownerType.name
    let publicCarrierName := Naming.modelName owner
    let some publicCarrier := unique publicCarrierName
      | return .malformed publicCarrierName
    let some privateCarrier := unique (privateSelf owner)
      | return .malformed (privateSelf owner)
    let some privateRec := unique (privateRecursor owner)
      | return .malformed (privateRecursor owner)
    let some rollDecl := unique (roll owner) | return .malformed (roll owner)
    let some unrollDecl := unique (unroll owner) | return .malformed (unroll owner)
    let some sectionDecl := unique (unrollRoll owner)
      | return .malformed (unrollRoll owner)
    let some retractionDecl := unique (rollUnroll owner)
      | return .malformed (rollUnroll owner)
    unless privateCarrier.kind == .defn && privateCarrier.safety? == some "safe" &&
        privateRec.kind == .defn && privateRec.safety? == some "safe" &&
        rollDecl.kind == .defn && rollDecl.safety? == some "safe" &&
        unrollDecl.kind == .defn && unrollDecl.safety? == some "safe" &&
        sectionDecl.kind == .thm && retractionDecl.kind == .thm do
      return .malformed (privateSelf owner)
    unless privateCarrier.levelParams == publicCarrier.levelParams &&
        privateCarrier.type == publicCarrier.type do
      return .malformed (privateSelf owner)
    let some publicRecPair := family.correspondence.recursors.find? fun pair =>
        pair.owner == Name.str owner "rec"
      | return .malformed (privateRecursor owner)
    let some publicRec := unique publicRecPair.model
      | return .malformed publicRecPair.model
    unless privateRec.levelParams == publicRec.levelParams do
      return .malformed (privateRecursor owner)
    let ownerConstructors := constructors.filter (·.induct == owner)
    unless ownerConstructors.size == ownerType.ctors.length do
      return .malformed (privateSelf owner)
    for constructor in ownerConstructors do
      let privateName := privateConstructor owner constructor.name
      let some privateCtor := unique privateName | return .malformed privateName
      let some publicCtorPair := family.correspondence.constructors.find? fun pair =>
          pair.owner == constructor.name
        | return .malformed privateName
      let some publicCtor := unique publicCtorPair.model | return .malformed publicCtorPair.model
      unless privateCtor.kind == .defn && privateCtor.safety? == some "safe" &&
          privateCtor.levelParams == publicCtor.levelParams do
        return .malformed privateName
    let some sourceRec := recursors.find? fun recursor =>
        recursor.name == Name.str owner "rec"
      | return .malformed (privateRecursor owner)
    for ruleIndex in [0:sourceRec.rules.length] do
      let sourceRule := sourceRec.rules[ruleIndex]!
      let iotaName := privateIota owner sourceRule.ctor
      let ruleName := privateRule owner sourceRule.ctor
      let some iotaDecl := unique iotaName | return .malformed iotaName
      let some ruleDecl := unique ruleName | return .malformed ruleName
      let some publicIota := family.correspondence.iotas.find? fun iota =>
          iota.recursor == sourceRec.name && iota.ruleIndex == ruleIndex
        | return .malformed iotaName
      let some publicIotaDecl := unique publicIota.name | return .malformed publicIota.name
      unless iotaDecl.kind == .thm && ruleDecl.kind == .thm &&
          iotaDecl.levelParams == publicIotaDecl.levelParams &&
          ruleDecl.levelParams == iotaDecl.levelParams && ruleDecl.type == iotaDecl.type do
        return .malformed ruleName
    let (parameters, result) := openForalls
      ((`_check.mutualOneLayerCertificate).append owner) publicCarrier.type
    unless parameters.size == ownerType.numParams do return .malformed publicCarrierName
    let .sort carrierLevel := result | return .malformed publicCarrierName
    let levels := publicCarrier.levelParams.map Level.param
    let parameterValues := parameters.map (·.value)
    let publicCarrierType := mkAppN (.const publicCarrierName levels) parameterValues
    let privateCarrierType := mkAppN (.const (privateSelf owner) levels) parameterValues
    let publicValue : OpenBinder :=
      { name := `public, type := publicCarrierType, info := .default
        value := mkFVar (FVarId.mk ((`_check.mutualPublic).append owner)) }
    let privateValue : OpenBinder :=
      { name := `private, type := privateCarrierType, info := .default
        value := mkFVar (FVarId.mk ((`_check.mutualPrivate).append owner)) }
    let expectedRoll := closeForalls (parameters.push publicValue) privateCarrierType
    let expectedUnroll := closeForalls (parameters.push privateValue) publicCarrierType
    unless rollDecl.type == expectedRoll do return .malformed (roll owner)
    unless unrollDecl.type == expectedUnroll do return .malformed (unroll owner)
    let rollApp := mkAppN (.const (roll owner) levels) (parameterValues.push publicValue.value)
    let unrollRollApp := mkAppN (.const (unroll owner) levels)
      (parameterValues.push rollApp)
    let sectionBody := mkAppN (.const ``Eq [carrierLevel])
      #[publicCarrierType, unrollRollApp, publicValue.value]
    unless sectionDecl.type == closeForalls (parameters.push publicValue) sectionBody do
      return .malformed (unrollRoll owner)
    let unrollApp := mkAppN (.const (unroll owner) levels)
      (parameterValues.push privateValue.value)
    let rollUnrollApp := mkAppN (.const (roll owner) levels)
      (parameterValues.push unrollApp)
    let retractionBody := mkAppN (.const ``Eq [carrierLevel])
      #[privateCarrierType, rollUnrollApp, privateValue.value]
    unless retractionDecl.type == closeForalls (parameters.push privateValue) retractionBody do
      return .malformed (rollUnroll owner)
  return .valid

private def checkPair (table : Correspondence) (declarations : DeclarationTypes)
    (pair : ConstantPair) : Array Violation := Id.run do
  let mut violations : Array Violation := #[]
  let models := declarations.findD pair.model #[]
  if models.isEmpty then
    return #[.missingPublic pair.owner pair.model]
  if models.size != 1 then
    return #[.duplicatePublic pair.owner pair.model models.size]
  let some ownerDecl := (declarations.findD pair.owner #[])[0]?
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
  let models := declarations.findD iota.name #[]
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
  let models := declarations.findD metadata.name #[]
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
  let models := declarations.findD metadata.name #[]
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
private def checkEta (x : Export) (normalizer : ExactNormalizationEnv) (family : Family)
    (declarations : DeclarationTypes) (metadata : Naming.Metadata) : Array Violation := Id.run do
  let models := declarations.findD metadata.name #[]
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
      !normalizer.isPropositionFormer ownerType.type do
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
  let .sort carrierLevel := normalizer.whnf ownerResult
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

mutual

/-- A deliberately small, exact type synthesizer for the result of an
exported projection declaration. Declaration and local binder types suffice;
when their head is hidden, it unfolds only transparent definitions in the
export syntax. The projection case follows the exact recovered primitive
projection interface. -/
private partial def inferExactType? (structures : StructureOwners)
    (normalizer : ExactNormalizationEnv)
    (declarations : DeclarationTypes)
    (locals : ExactLocals) : Expr → Option Expr
  | .sort level => some (.sort (.succ level))
  | .fvar id => locals.typeOf? id
  | .const name levels => do
      let declaration ← (declarations.findD name #[])[0]?
      if declaration.levelParams.length != levels.length then none
      return declaration.type.instantiateLevelParams declaration.levelParams levels
  | .app function argument => do
      let functionType := normalizer.whnf
        (← inferExactType? structures normalizer declarations locals function)
      let .forallE _ _ body _ := functionType | none
      return body.instantiate1 argument
  | .lam name domain body info => do
      let value := mkFVar (FVarId.mk ((`_check.exactLam).mkNum locals.size))
      let bodyType ← inferExactType? structures normalizer declarations
        (locals.push (value.fvarId!, domain)) (body.instantiate1 value)
      return .forallE name domain (bodyType.abstract #[value]) info
  | .forallE name domain body info => do
      let domainLevel ← inferExactSortLevel? structures normalizer declarations locals domain
      let value := mkFVar (FVarId.mk ((`_check.exactPi).mkNum locals.size))
      let bodyLevel ← inferExactSortLevel? structures normalizer declarations
        (locals.push (value.fvarId!, domain)) (body.instantiate1 value)
      let _ := name
      let _ := info
      return .sort (Level.imax domainLevel bodyLevel).normalize
  | .letE _ _ value body _ =>
      inferExactType? structures normalizer declarations locals (body.instantiate1 value)
  | .mdata _ body => inferExactType? structures normalizer declarations locals body
  | .proj owner fieldIndex struct => do
      let structType := normalizer.whnf
        (← inferExactType? structures normalizer declarations locals struct)
      let .const structOwner levels := structType.getAppFn | none
      unless structOwner == owner do none
      let (type, constructors) ← structures.find? owner
      let constructorName ← type.ctors.head?
      let constructor ← constructors.find? fun constructor =>
        constructor.name == constructorName && constructor.induct == owner
      unless type.ctors == [constructorName] do none
      unless constructor.levelParams.length == levels.length do none
      let ownerArguments := structType.getAppArgs
      unless ownerArguments.size == type.numParams + type.numIndices do none
      let params := ownerArguments.extract 0 type.numParams
      let mut current := constructor.type.instantiateLevelParams constructor.levelParams levels
      for param in params do
        let .forallE _ _ body _ := normalizer.whnf current | none
        current := body.instantiate1 param
      let ownerIsProp := normalizer.isPropositionFormer type.type
      for earlier in [0:fieldIndex + 1] do
        let .forallE _ fieldType rest _ := normalizer.whnf current | none
        let fieldIsProp :=
          inferExactSortLevel? structures normalizer declarations locals fieldType == some .zero
        if earlier == fieldIndex then
          if ownerIsProp && !fieldIsProp then none else return fieldType
        if ownerIsProp && rest.hasLooseBVars && !fieldIsProp then none
        current := rest.instantiate1 (.proj owner earlier struct)
      none
  | .lit (.natVal _) => some (.const ``Nat [])
  | .lit (.strVal _) => some (.const ``String [])
  | .bvar _ | .mvar _ => none

private partial def inferExactSortLevel? (structures : StructureOwners)
    (normalizer : ExactNormalizationEnv)
    (declarations : DeclarationTypes)
    (locals : ExactLocals) (expression : Expr) : Option Level := do
  let .sort level := normalizer.whnf
    (← inferExactType? structures normalizer declarations locals expression) | none
  return level

end

/-- Check one intrinsic projection and its literal constructor rule.

There is no source projection declaration to rewrite.  Both types are
synthesized from the unique constructor telescope.  References to earlier
fields in a dependent result become applications of the corresponding earlier
intrinsic projections. -/
private def checkProjection (x : Export) (structures : StructureOwners)
    (normalizer : ExactNormalizationEnv) (family : Family)
    (declarations : DeclarationTypes) (oneLayerCertificate : Phase1OneLayerCertificate)
    (projection : Naming.Projection) : Array Violation := Id.run do
  let projectionModels := declarations.findD projection.name #[]
  if projectionModels.isEmpty then
    return #[.missingPublic projection.owner projection.name]
  if projectionModels.size != 1 then
    return #[.duplicatePublic projection.owner projection.name projectionModels.size]
  let ruleModels := declarations.findD projection.iota #[]
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
  if let .malformed slot := oneLayerCertificate then
    return #[.declarationType projection.owner slot]
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
  -- Kernel insertion β-normalizes a head application in a constructor-local
  -- binder type. Mirror exactly that step for the theorem's outer binders, but
  -- retain written `let`s and named model constants so the public statement
  -- remains literal. The unnormalized binders below still drive the RHS.
  let propositionLiteral := propositionProjectionIotaUsesLiteralField ownerType
  let theoremBinders := if oneLayerCertificate matches .valid || propositionLiteral then
      constructorBinders
    else constructorBinders.map fun binder =>
      { binder with type := normalizer.beta binder.type }
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
    let some sourceLevel := inferExactSortLevel? structures normalizer declarations sourceLocals
        sourceFieldAtIndex.type
      | return violations.push (.declarationType projection.owner projection.iota)
    let level := renameLevelParamNamesExact constructor.levelParams model.levelParams sourceLevel
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
  let rhs? := if projectionIotaUsesLiteralField ownerTypes.toArray ownerType ||
      propositionLiteral || oneLayerCertificate matches .valid then
      fields[projection.fieldIndex]?
    else
      let eqi : EqInfo := { eqN := ``Eq, reflN := ``Eq.refl, recN := ``Eq.rec }
      match ProjectionField.normalizeProjectionField eqi projection.name
          normalizedFields projection.fieldIndex with
        | .ok rhs => some rhs
        | .error _ => none
  let some rhs := rhs?
    | return violations.push (.declarationType projection.owner projection.iota)
  let some sourceEqLevel :=
      inferExactSortLevel? structures normalizer declarations sourceLocals sourceField.type
    | return violations.push (.declarationType projection.owner projection.iota)
  let eqLevel := renameLevelParamNamesExact
    constructor.levelParams model.levelParams sourceEqLevel
  let expectedBody := mkAppN (.const ``Eq [eqLevel]) #[alpha, lhs, rhs]
  let expected := closeForalls theoremBinders expectedBody
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

private abbrev IotaSlots := Lean.PersistentHashMap Name (Array (Name × Nat))

private def iotaSlots (x : Export) : IotaSlots := Id.run do
  let mut slots : IotaSlots := {}
  for declaration in x.decls do
    for name in declaration.names do
      if let some (parent, index) := iotaSlot? name then
        slots := slots.insert parent ((slots.findD parent #[]).push (name, index))
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

/-- The observable result of one complete structural check.  `familiesChecked`
counts the exact public model families discovered in the checked export; it is
reported separately from violations so successful command-line checks can
show that they inspected a nonempty serialized model interface. -/
structure Report where
  familiesChecked : Nat
  violations : Array Violation
  deriving Inhabited, Repr, BEq

/-- Reusable declaration-facing syntax tables for checking several model
families from the same source snapshot.  The expression graph is shared with
the export; constructing an index does not copy declaration bodies. -/
structure SyntaxIndex where
  private declarations : DeclarationTypes
  private constructors : Constructors
  private structures : StructureOwners
  private ruleSlots : IotaSlots
  private normalizer : ExactNormalizationEnv
  /-- Exact declaration-record occurrences in source order.  Keeping this in
  the shared index prevents family discovery from rebuilding a whole-export
  name table for every consumer. -/
  private records : Std.HashMap Name (Array Nat)
  /-- Sparse occurrences introduced in front of `records` by island overlays.
  Base occurrences are interpreted after `recordOffset`; keeping both axes
  separate avoids copying the whole source map whenever support is prepended. -/
  private recordPrefix : Std.HashMap Name (Array Nat) := {}
  private recordOffset : Nat := 0
  private globalExtras : Array Violation := #[]
  private sourceFamilies : Std.HashMap Name (Array Family) := {}
  private names : Lean.PersistentHashSet Name := {}

/-- Mutable construction state for an immutable [`SyntaxIndex`].  The builder
is fed in declaration order.  It retains only exact declaration-facing syntax
tables plus inductive owner records until `freeze`; ordinary declaration
values are not accumulated. -/
structure SyntaxIndex.Builder where
  private declarations : DeclarationTypes := {}
  private constructors : Constructors := {}
  private structures : StructureOwners := {}
  private ruleSlots : IotaSlots := {}
  private definitions : Std.HashMap Name ExactNormalizationDef := {}
  private records : Std.HashMap Name (Array Nat) := {}
  private names : Lean.PersistentHashSet Name := {}
  private owners : Array (Nat × EDecl) := #[]
  private nextOrdinal : Nat := 0

/-- Add one exact export record to a syntax-index builder.  Duplicate handling
matches the historical whole-export prepasses: declaration types and record
occurrences append, constructor/structure tables keep the last occurrence,
and transparent normalization keeps the first definition. -/
def SyntaxIndex.Builder.push (builder : SyntaxIndex.Builder)
    (declaration : EDecl) : SyntaxIndex.Builder := Id.run do
  let ordinal := builder.nextOrdinal
  let mut declarations := builder.declarations
  for info in declTypes declaration do
    declarations := declarations.insert info.name
      ((declarations.findD info.name #[]).push info)
  let mut constructors := builder.constructors
  let mut structures := builder.structures
  let mut owners := builder.owners
  if let .induct types ctors _ := declaration then
    for ctor in ctors do constructors := constructors.insert ctor.name ctor
    for type in types do structures := structures.insert type.name (type, ctors)
    owners := owners.push (ordinal, declaration)
  let mut ruleSlots := builder.ruleSlots
  let mut records := builder.records
  let mut names := builder.names
  for name in declaration.names do
    if let some (parent, index) := iotaSlot? name then
      ruleSlots := ruleSlots.insert parent
        ((ruleSlots.findD parent #[]).push (name, index))
    records := records.insert name ((records.getD name #[]).push ordinal)
    names := names.insert name
  let mut definitions := builder.definitions
  if let .defn name levelParams _ value .. := declaration then
    unless definitions.contains name do
      definitions := definitions.insert name { levelParams, value }
  let builder := { builder with declarations := declarations }
  let builder := { builder with constructors := constructors }
  let builder := { builder with structures := structures }
  let builder := { builder with ruleSlots := ruleSlots }
  let builder := { builder with definitions := definitions }
  let builder := { builder with records := records }
  let builder := { builder with names := names }
  let builder := { builder with owners := owners }
  return { builder with nextOrdinal := ordinal + 1 }

/-- The exact syntax normalizer already retained by this index.  The returned
value structurally shares its definition table; consumers must reuse it rather
than rebuilding a second whole-export map. -/
def SyntaxIndex.exactNormalizer (index : SyntaxIndex) : ExactNormalizationEnv :=
  index.normalizer

/-- Replace the declaration-facing portion of a syntax index with an explicit
collision-free replay view while retaining exact source occurrence/family
certificates.

Only records which mention a moved source name need appear in `exactRecords` /
`replayRecords`.  The two arrays are positional pairs.  Updating persistent
hash maps here avoids rebuilding a second whole-source index for the rare
flattened-export normalized-name collision. -/
def SyntaxIndex.withReplayRecords (source : SyntaxIndex)
    (exactRecords replayRecords : Array EDecl) : Except String SyntaxIndex := do
  unless exactRecords.size == replayRecords.size do
    throw "replay syntax replacement arrays have different sizes"
  let mut declarations := source.declarations
  let mut constructors := source.constructors
  let mut structures := source.structures
  let mut normalizer := source.normalizer
  let mut names := source.names
  for ordinal in [:exactRecords.size] do
    let exact := exactRecords[ordinal]!
    let replay := replayRecords[ordinal]!
    unless exact.names.length == replay.names.length do
      throw s!"replay syntax replacement {ordinal} changed declaration arity"
    if exact matches .quot .. then
      unless replay matches .quot .. do
        throw s!"replay syntax replacement {ordinal} changed a quotient record's kind"
      unless exact.names == replay.names do
        throw s!"replay syntax replacement {ordinal} moved an atomic quotient role"
    for name in exact.names do
      declarations := declarations.erase name
      normalizer := normalizer.eraseDefinition name
    if let .induct types ctors _ := exact then
      for type in types do structures := structures.erase type.name
      for ctor in ctors do constructors := constructors.erase ctor.name
    for info in declTypes replay do
      declarations := declarations.insert info.name #[info]
      names := names.insert info.name
    if let .induct types ctors _ := replay then
      for ctor in ctors do constructors := constructors.insert ctor.name ctor
      for type in types do structures := structures.insert type.name (type, ctors)
    if let .defn name levelParams _ value .. := replay then
      normalizer := normalizer.insertDefinition name { levelParams, value }
  return { source with
    declarations, constructors, structures,
    normalizer, names }

private def declarationRecords (x : Export) : Std.HashMap Name (Array Nat) := Id.run do
  let mut records : Std.HashMap Name (Array Nat) := {}
  for i in [0:x.decls.size] do
    for name in x.decls[i]!.names do
      records := records.insert name ((records.getD name #[]).push i)
  return records

private def SyntaxIndex.coreOfExport (x : Export) : SyntaxIndex :=
  { declarations := declarationTypes x, constructors := constructorRecords x,
    structures := structureOwners x, ruleSlots := iotaSlots x,
    normalizer := x.exactNormalizationEnv, records := declarationRecords x,
    names := x.decls.foldl (fun names declaration =>
      declaration.names.foldl (·.insert ·) names) {} }

private def checkFamilyWithIndex (x : Export) (index : SyntaxIndex)
    (family : Family) (checkOrder : Bool) : Array Violation := Id.run do
  let mut violations : Array Violation := #[]
  if checkOrder then
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
    violations := violations ++ checkPair family.correspondence index.declarations pair
  for pair in family.correspondence.constructors do
    violations := violations ++ checkPair family.correspondence index.declarations pair
  for pair in family.correspondence.recursors do
    violations := violations ++ checkPair family.correspondence index.declarations pair
  let ownerTypes : Array EIndType := match x.decls[family.ownerDecl]! with
    | .induct types _ _ => types.toArray
    | _ => #[]
  let ownerConstructors : Array ECtor := match x.decls[family.ownerDecl]! with
    | .induct _ constructors _ => constructors.toArray
    | _ => #[]
  let ownerRecursors : Array ERec := match x.decls[family.ownerDecl]! with
    | .induct _ _ recursors => recursors.toArray
    | _ => #[]
  let mutualCertificate := phase1MutualOneLayerCertificate index.declarations
    ownerTypes ownerConstructors ownerRecursors index.normalizer family
  let certificates := ownerTypes.map fun ownerType =>
    let singleton := phase1OneLayerCertificate index.declarations ownerType
      ownerConstructors ownerRecursors family
    (ownerType.name, if singleton matches .absent then mutualCertificate else singleton)
  for (owner, certificate) in certificates do
    if let .malformed slot := certificate then
      violations := violations.push (.declarationType owner slot)
  for projection in family.correspondence.projections do
    let certificate := match certificates.find? fun entry => entry.1 == projection.owner with
      | some (_, .malformed _) => .absent
      | some (_, certificate) => certificate
      | none => .malformed projection.owner
    violations := violations ++ checkProjection
      x index.structures index.normalizer family index.declarations certificate projection
  for iota in family.correspondence.iotas do
    violations := violations ++ checkIota x index.constructors family index.declarations iota
  for metadata in family.correspondence.metadata do
    violations := violations ++ checkTheoremSlot
      index.declarations metadata.owner metadata.name
    if metadata.kind == .unitlike then
      violations := violations ++ checkUnitlike x family index.declarations metadata
    else if metadata.kind == .eta then
      violations := violations ++ checkEta
        x index.normalizer family index.declarations metadata
    else if metadata.kind == .ruleK then
      violations := violations ++ checkRuleK x family index.declarations metadata
  for pair in family.correspondence.recursors do
    let numRules := (family.correspondence.iotas.filter (·.recursor == pair.owner)).size
    for (name, ruleIndex) in index.ruleSlots.findD pair.model #[] do
      if ruleIndex >= numRules || name != Naming.iotaName pair.owner ruleIndex then
        violations := violations.push (.extraRule pair.owner name)
  return violations

/-- Overlay an island in front of a persistent source index without rescanning
the source export. Any name collision fails closed before first/last-map
semantics could hide it. Declaration and rule arrays are prefixed, generated
transparent definitions win, and generated constructor/owner records extend
the source maps. Global extras remain a final-export concern and are
intentionally not recomputed here. -/
def SyntaxIndex.prependRecords (source : SyntaxIndex) (records : Array EDecl) :
    Except String SyntaxIndex := Id.run do
  let mut names := source.names
  for declaration in records do
    for name in declaration.names do
      if names.contains name then
        return .error s!"island overlay redeclares {name}"
      names := names.insert name
  let mut declarations := source.declarations
  let mut ruleSlots := source.ruleSlots
  for declaration in records.reverse do
    for info in (declTypes declaration).reverse do
      declarations := declarations.insert info.name
        (#[info] ++ declarations.findD info.name #[])
    for name in declaration.names.reverse do
      if let some (parent, index) := iotaSlot? name then
        ruleSlots := ruleSlots.insert parent
          (#[((name, index))] ++ ruleSlots.findD parent #[])
  let mut constructors := source.constructors
  let mut structures := source.structures
  for declaration in records do
    if let .induct types ctors _ := declaration then
      for constructor in ctors do
        unless source.constructors.contains constructor.name do
          constructors := constructors.insert constructor.name constructor
      for type in types do
        unless source.structures.contains type.name do
          structures := structures.insert type.name (type, ctors)
  let mut normalizer := source.normalizer
  for declaration in records.reverse do
    if let .defn name levelParams _ value .. := declaration then
      normalizer := normalizer.insertDefinition name { levelParams, value }
  -- `discoverWithIndex` may consume the resulting index together with the
  -- literal combined view `records ++ source`. Shift only the sparse existing
  -- overlay; base source occurrences retain their map and acquire one offset.
  -- Collision rejection above guarantees new prefix entries cannot hide one.
  let mut recordPrefix : Std.HashMap Name (Array Nat) := {}
  for (name, occurrences) in source.recordPrefix do
    recordPrefix := recordPrefix.insert name
      (occurrences.map fun ordinal => records.size + ordinal)
  for ordinal in [0:records.size] do
    for name in records[ordinal]!.names do
      recordPrefix := recordPrefix.insert name #[ordinal]
  return .ok {
    declarations := declarations
    constructors := constructors
    structures := structures
    ruleSlots := ruleSlots
    normalizer := normalizer
    records := source.records
    recordPrefix := recordPrefix
    recordOffset := source.recordOffset + records.size
    globalExtras := source.globalExtras
    sourceFamilies := source.sourceFamilies
    names := names }

/-- Fail-closed family templates for one owner from the persistent source
snapshot.  They are built once with the source `SyntaxIndex`; island checks do
not rediscover them by scanning the complete input. -/
def SyntaxIndex.sourceStatementFamilies (index : SyntaxIndex) (owner : Name) : Array Family :=
  index.sourceFamilies.getD owner #[]

private partial def projectionFieldEligibleWithIndex (index : SyntaxIndex)
    (ownerIsProp : Bool) (fieldIndex : Nat) (current : Expr)
    (locals : ExactLocals) : Option Bool := do
  let .forallE _ fieldType body _ := index.normalizer.whnf current | none
  let fieldIsProp := inferExactSortLevel? index.structures index.normalizer
    index.declarations locals fieldType == some .zero
  if fieldIndex == 0 then return !ownerIsProp || fieldIsProp
  if ownerIsProp && body.hasLooseBVars && !fieldIsProp then return false
  let value := mkFVar (FVarId.mk ((`_check.projectionField).mkNum locals.size))
  projectionFieldEligibleWithIndex index ownerIsProp (fieldIndex - 1)
    (body.instantiate1 value) (locals.push (value.fvarId!, fieldType))

private def intrinsicProjectionFieldsWithIndex (index : SyntaxIndex)
    (type : EIndType) (constructors : List ECtor) : Array Nat := Id.run do
  let [constructorName] := type.ctors | return #[]
  let some constructor := constructors.find? fun constructor =>
      constructor.name == constructorName && constructor.induct == type.name
    | return #[]
  let mut ownerType := type.type
  while ownerType.isForall do ownerType := ownerType.bindingBody!
  let ownerIsProp := index.normalizer.isPropositionFormer ownerType
  let mut current := constructor.type
  let mut locals : ExactLocals := #[]
  for parameterIndex in [:type.numParams] do
    let .forallE _ parameterType body _ := index.normalizer.whnf current | return #[]
    let value := mkFVar (FVarId.mk ((`_check.projectionParam).mkNum parameterIndex))
    locals := locals.push (value.fvarId!, parameterType)
    current := body.instantiate1 value
  let mut fields : Array Nat := #[]
  for fieldIndex in [:constructor.numFields] do
    if projectionFieldEligibleWithIndex index ownerIsProp fieldIndex current locals == some true then
      fields := fields.push fieldIndex
  return fields

/-- Kernel-valid intrinsic projection field indices using the syntax tables
already built for this export. Driver readiness checks use this query to avoid
reconstructing whole-export declaration and normalization maps per owner. -/
def SyntaxIndex.intrinsicProjectionFields (index : SyntaxIndex)
    (type : EIndType) (constructors : List ECtor) : Array Nat :=
  intrinsicProjectionFieldsWithIndex index type constructors

private def SyntaxIndex.recordOccurrences (index : SyntaxIndex) (name : Name) : Array Nat :=
  index.recordPrefix.getD name #[] ++
    (index.records.getD name #[]).map fun ordinal => index.recordOffset + ordinal

/-! ## Indexed family discovery

The historical discovery helper rebuilt the complete transparent-definition
and declaration-type tables once per inductive owner.  On a flattened export
that is quadratic in the number of records.  Discovery below consumes the one
shared syntax index instead: all whole-export tables are built once and each
owner performs only its local correspondence walk. -/

/-- Indexed core of family discovery. `includeEmpty root` retains an expected
family even when none of its public slots is declared. -/
private def discoverWithIndexWhere (x : Export) (index : SyntaxIndex)
    (includeEmpty : Name → Bool) : Array Family := Id.run do
  let mut families : Array Family := #[]
  for ownerDecl in [0:x.decls.size] do
    let declaration := x.decls[ownerDecl]!
    let .induct types _ _ := declaration | continue
    let some root := types.head?.map (·.name) | continue
    let some correspondence := correspondenceFor? index.normalizer
        (intrinsicProjectionFieldsWithIndex index) declaration
      | continue
    let publicNames := correspondence.publicNames
    unless includeEmpty root ||
        publicNames.any (fun name => !(index.recordOccurrences name).isEmpty) do continue
    let mut modelDecls : Array Nat := #[]
    for name in publicNames do
      for i in index.recordOccurrences name do
        unless modelDecls.contains i do modelDecls := modelDecls.push i
    modelDecls := modelDecls.qsort (· < ·)
    let modelNames := modelDecls.foldl
      (fun names i => appendUnique names x.decls[i]!.names) #[]
    let modelRoot := Naming.modelName root
    families := families.push
      { owner := root, modelRoot, carrier := modelRoot, ownerDecl, correspondence,
        decls := modelDecls, names := modelNames }
  return families

/-- Discover public model families using syntax tables already built for the
same export. This is the reusable production entry point for passes which need
both an index and family discovery. -/
def discoverWithIndex (x : Export) (index : SyntaxIndex) : Array Family :=
  discoverWithIndexWhere x index fun _ => false

/-- Discover public model families from exact names computed from each original
inductive record. One family covers each atomic owner record; a declaration
record introducing any exact public slot belongs to that family in its
entirety. -/
def discover (x : Export) : Array Family :=
  discoverWithIndex x (SyntaxIndex.coreOfExport x)

/-- Discover the exact generated-family view, retaining a requested owner even
when every public model slot is absent. -/
def statementFamiliesForWithIndex (x : Export) (index : SyntaxIndex)
    (owners : Std.HashSet Name) : Array Family :=
  (discoverWithIndexWhere x index owners.contains).filter fun family =>
    owners.contains family.owner

def statementFamiliesFor (x : Export) (owners : Std.HashSet Name) : Array Family :=
  statementFamiliesForWithIndex x (SyntaxIndex.coreOfExport x) owners

private def sourceFamilyTable (families : Array Family) : Std.HashMap Name (Array Family) :=
  families.foldl (init := {}) fun table family =>
    let template := { family with decls := #[], names := #[] }
    table.insert family.owner ((table.getD family.owner #[]).push template)

/-- Freeze declaration callbacks into one immutable source syntax index.
Owner templates are computed directly from the retained inductive records;
they do not require a second whole-export discovery/index construction. -/
def SyntaxIndex.Builder.freeze (builder : SyntaxIndex.Builder) : SyntaxIndex := Id.run do
  let index : SyntaxIndex :=
    { declarations := builder.declarations
      constructors := builder.constructors
      structures := builder.structures
      ruleSlots := builder.ruleSlots
      normalizer := { definitions := builder.definitions }
      records := builder.records
      names := builder.names }
  let mut families : Array Family := #[]
  for (ownerDecl, declaration) in builder.owners do
    let .induct types _ _ := declaration | continue
    let some root := types.head?.map (·.name) | continue
    let some correspondence := correspondenceFor? index.normalizer
        (intrinsicProjectionFieldsWithIndex index) declaration
      | continue
    let modelRoot := Naming.modelName root
    families := families.push
      { owner := root, modelRoot, carrier := modelRoot, ownerDecl, correspondence
        decls := #[], names := #[] }
  return { index with sourceFamilies := sourceFamilyTable families }

/-- Incremental source-index construction.  This is intentionally separate
from `ofSource` during the migration so property tests retain the old
whole-export implementation as an independent reference. -/
def SyntaxIndex.ofSourceIncremental (x : Export) : SyntaxIndex :=
  (x.decls.foldl (fun builder declaration => builder.push declaration)
    ({} : SyntaxIndex.Builder)).freeze

/-- Build persistent generation-time source tables without the whole-output
unexpected-slot sweep. Every owner template is attached after indexed
discovery, breaking the former per-owner whole-export reconstruction. -/
def SyntaxIndex.ofSource (x : Export) : SyntaxIndex :=
  let index := SyntaxIndex.coreOfExport x
  let families := discoverWithIndexWhere x index fun _ => true
  { index with sourceFamilies := sourceFamilyTable families }

/-! ## Value-free global-extra summaries

The whole-export unexpected-slot sweep historically revisits every owner
record after generation. Compact no-output modes cannot retain generated
`EDecl`s just for that pass, so record the eligibility decisions while each
owner is live.
These summaries contain names, field indices, and booleans only; in
particular, they cannot retain an island's expression graph.

The outer array returned by `globalExtraRecordsWithIndex` remains aligned with
its input records, including non-inductive records. Each element binds the
introduced names to its templates so a caller cannot reorder one axis without
the other. A compact final ordering may therefore permute these records with
the same locators it uses for declaration records. -/

/-- One owner-local decision needed by the unexpected public-slot sweep. -/
inductive GlobalExtraTemplate where
  | type (owner : Name) (validProjectionFields : Array Nat)
      (allowsUnitlike allowsEta : Bool)
  | recursor (owner : Name) (allowsRuleK : Bool)
  deriving Inhabited, Repr, BEq

/-- Names and owner decisions captured atomically for one export record. -/
structure GlobalExtraRecord where
  names : Array Name
  templates : Array GlobalExtraTemplate
  deriving Inhabited, Repr, BEq

def GlobalExtraTemplate.owner : GlobalExtraTemplate → Name
  | .type owner .. | .recursor owner .. => owner

/-- Capture unexpected-slot eligibility for each record without retaining an
`Expr`.  Projection eligibility and proposition-former tests use the supplied
overlay index, so generated owners may depend on transparent source aliases.
Duplicate owner declarations must be rejected by compact ordering before
capture; the index's owner table is not a
substitute for that collision check. -/
def globalExtraRecordsWithIndex (index : SyntaxIndex)
    (records : Array EDecl) : Array GlobalExtraRecord :=
  records.map fun declaration => match declaration with
    | .induct types constructors recursors =>
      { names := declaration.names.toArray
        templates := types.toArray.map (fun type =>
          .type type.name (intrinsicProjectionFieldsWithIndex index type constructors)
            (type.isKernelUnitlike constructors)
            (type.isKernelStructureLike constructors &&
              !index.normalizer.isPropositionFormer type.type)) ++
        recursors.toArray.map fun recursor => .recursor recursor.name recursor.k }
    | _ => { names := declaration.names.toArray, templates := #[] }

/-- Recover the modeled-type root and field index from either spelling counted
by [`projectionSlot?`].  Indexing by the already-modeled root avoids repeating
the full declaration-name scan for every inductive type while retaining each
name's original position and multiplicity. -/
private def projectionSlotRoot? (name : Name) : Option (Name × Nat) := do
  match name with
  | .str parent suffix =>
    if suffix.startsWith "proj_" then
      return (parent, ← (suffix.drop 5).toNat?)
    else if suffix == "iota" then
      let .str grandParent projectionSuffix := parent | none
      unless projectionSuffix.startsWith "proj_" do none
      return (grandParent, ← (projectionSuffix.drop 5).toNat?)
    else
      none
  | _ => none

/-- Reproduce the historical global-extra diagnostic order from value-free
records in final order. The flattened names deliberately remain an array:
repeated slot names retain projection-diagnostic order and multiplicity, while
a local set answers metadata presence queries. -/
def globalExtrasFromRecords (records : Array GlobalExtraRecord) : Array Violation := Id.run do
  let orderedNames := records.flatMap (·.names)
  let declared := orderedNames.foldl (fun names name => names.insert name)
    ({} : Std.HashSet Name)
  let projectionSlots := orderedNames.foldl (init :=
      ({} : Std.HashMap Name (Array (Name × Nat)))) fun slots name =>
    match projectionSlotRoot? name with
    | none => slots
    | some (root, fieldIndex) =>
      slots.insert root ((slots.getD root #[]).push (name, fieldIndex))
  let mut violations : Array Violation := #[]
  for record in records do
    for template in record.templates do
      match template with
      | .type owner validFields allowsUnitlike allowsEta =>
        for (name, fieldIndex) in projectionSlots.getD (Naming.modelName owner) #[] do
          unless validFields.contains fieldIndex do
            violations := violations.push (.extraProjection owner name)
        unless allowsUnitlike do
          let name := Naming.unitlikeName owner
          if declared.contains name then
            violations := violations.push (.extraMetadata owner name .unitlike)
        unless allowsEta do
          let name := Naming.etaName owner
          if declared.contains name then
            violations := violations.push (.extraMetadata owner name .eta)
      | .recursor owner allowsRuleK =>
        unless allowsRuleK do
          let name := Naming.ruleKName owner
          if declared.contains name then
            violations := violations.push (.extraMetadata owner name .ruleK)
  return violations

/-- Build all reusable syntax tables, including the whole-export unexpected
slot sweep. Family discovery and projection eligibility share the same index;
the global sweep uses the linear name index above rather than rescanning the
complete declaration stream for every inductive owner. -/
def SyntaxIndex.ofExport (x : Export) : SyntaxIndex :=
  let index := SyntaxIndex.ofSource x
  { index with globalExtras :=
      globalExtrasFromRecords (globalExtraRecordsWithIndex index x.decls) }

/-- Attach the whole-export unexpected-slot sweep to an already complete
overlay. The caller is responsible for having overlaid every declaration not
present in the source snapshot. -/
def SyntaxIndex.withGlobalExtras (x : Export) (index : SyntaxIndex) : SyntaxIndex :=
  { index with globalExtras :=
      globalExtrasFromRecords (globalExtraRecordsWithIndex index x.decls) }

/-- Restrict the expensive unexpected-slot sweep to selected diagnostic
owners before any template scans the complete final name array. Names from
unselected records remain visible because a selected owner's unexpected public
slot may be introduced anywhere in the final stream. This is exactly the
historical late violation filter, but avoids work for unrelated owners. -/
def globalExtrasFromRecordsFor (records : Array GlobalExtraRecord)
    (owners : Std.HashSet Name) : Array Violation :=
  globalExtrasFromRecords <| records.map fun record =>
    { record with templates := record.templates.filter fun template =>
        owners.contains template.owner }

/-- Convenience form for an in-memory export. Compact callers instead retain
the bound per-record summaries and reorder them with compact declaration
locators before calling `globalExtrasFromRecords`. -/
def compactGlobalExtrasWithIndex (index : SyntaxIndex) (records : Array EDecl) :
    Array Violation :=
  globalExtrasFromRecords (globalExtraRecordsWithIndex index records)

/-- Discover selected families whose owner records belong to one generated
island, using its overlay for transparent aliases and projection eligibility.
Declaration indices are island-local; statement checking never interprets
them as positions in the source export. -/
def statementFamiliesForRecordsWithIndex (island : Export) (index : SyntaxIndex)
    (owners : Std.HashSet Name) : Array Family := Id.run do
  let mut families : Array Family := #[]
  for ownerDecl in [0:island.decls.size] do
    let .induct types _ _ := island.decls[ownerDecl]! | continue
    let some root := types.head?.map (·.name) | continue
    unless owners.contains root do continue
    let some correspondence := correspondenceFor? index.normalizer
        (intrinsicProjectionFieldsWithIndex index) island.decls[ownerDecl]!
      | continue
    families := families.push
      { owner := root, modelRoot := Naming.modelName root,
        carrier := Naming.modelName root, ownerDecl, correspondence,
        decls := #[], names := #[] }
  return families

private def checkFamiliesWithIndex (x : Export) (index : SyntaxIndex)
    (families : Array Family) (checkOrder : Bool) : Array Violation :=
  families.foldl (fun violations family =>
      violations ++ checkFamilyWithIndex x index family checkOrder) #[] ++
    index.globalExtras

private def checkFamilies (x : Export) (families : Array Family)
    (checkOrder : Bool) : Array Violation :=
  checkFamiliesWithIndex x (.ofExport x) families checkOrder

/-- Check order, independence, and every exact public declaration and statement,
and report the exact number of model families inspected.  All comparisons are
literal after positional universe alignment and the one simultaneous
declaration-name substitution. -/
def checkReport (x : Export) : Report :=
  let index := SyntaxIndex.ofExport x
  let families := discoverWithIndex x index
  { familiesChecked := families.size,
    violations := checkFamiliesWithIndex x index families true }

/-! ## Compact whole-output certificates

Once compact ordering succeeds, model records precede their owners. An owner
reference to a model name reinforces that order rather than forming a cycle,
so the exact ordered owner-reference trace is retained as well. The remaining
whole-output check can therefore release declarations and expression graphs.
-/

/-- Name-only whole-output certificate captured while one family's source and
model declarations are live. `localViolations` excludes order/backreference
checks and the final whole-stream extra-rule census. -/
structure CompactFamilyCertificate where
  owner : Name
  publicNames : Array Name
  ownerReferences : Array (Name × Name)
  captureIsland? : Option Nat := none
  localViolations : Array Violation
  recursors : Array (Name × Name × Nat)
  deriving Inhabited, Repr, BEq

/-- Mark a family whose syntax was checked with the declarations available in
one generated island. `none` denotes the complete parsed source snapshot. -/
def CompactFamilyCertificate.inIsland
    (certificate : CompactFamilyCertificate) (island : Nat) : CompactFamilyCertificate :=
  { certificate with captureIsland? := some island }

private def notExtraRule : Violation → Bool
  | .extraRule .. => false
  | _ => true

/-- Capture one family through the exact syntax index used for its local
structural check. The recursor tuples are `(owner, model, validRuleCount)`. -/
def compactFamilyCertificateWithIndex (x : Export) (index : SyntaxIndex)
    (family : Family) : CompactFamilyCertificate :=
  { owner := family.owner
    publicNames := family.correspondence.publicNames
    ownerReferences := ownerReferenceCertificate x.decls[family.ownerDecl]!
    localViolations :=
      (checkFamilyWithIndex x index family false).filter notExtraRule
    recursors := family.correspondence.recursors.map fun pair =>
      (pair.owner, pair.model,
        (family.correspondence.iotas.filter (·.recursor == pair.owner)).size) }

/-- Bind selected family certificates to their owner records. Empty rows are
retained so this array can be permuted with declaration summaries and byte
locators without a separate owner/name lookup. -/
def compactFamilyCertificateRecordsWithIndex (x : Export) (index : SyntaxIndex)
    (families : Array Family) : Array (Array CompactFamilyCertificate) := Id.run do
  let mut records := Array.replicate x.decls.size #[]
  for family in families do
    if family.ownerDecl < records.size then
      records := records.modify family.ownerDecl (·.push
        (compactFamilyCertificateWithIndex x index family))
  return records

/-- Capture the frozen source-family template while its exact owner record is
live.  The singleton *record view* still contains the complete mutual block;
all declaration types, constructors, public-slot occurrences, transparent
definitions, and rule slots come from `index`. Rebasing only the record ordinal
therefore avoids retaining unrelated `EDecl` values without synthesizing or
splitting the owner. -/
def SyntaxIndex.sourceFamilyCertificatesForRecord (index : SyntaxIndex)
    (template : Export) (owner : EDecl) : Array CompactFamilyCertificate :=
  let root? := match owner with
    | .induct (type :: _) _ _ => some type.name
    | _ => none
  root?.elim #[] fun root =>
    let view := { template with decls := #[owner] }
    (index.sourceStatementFamilies root).filterMap fun family =>
      -- Match indexed discovery exactly: an expected family becomes an input
      -- family only when at least one exact public slot occurs in the source.
      if family.correspondence.publicNames.any index.names.contains then
        some (compactFamilyCertificateWithIndex view index { family with ownerDecl := 0 })
      else none

/-- Capture every currently discoverable family in owner-record order. This is
the full-export convenience form; compact generation captures source and island
families separately through `compactFamilyCertificateWithIndex`. -/
def compactFamilyCertificates (x : Export) : Array CompactFamilyCertificate :=
  let index := SyntaxIndex.ofSource x
  (discoverWithIndex x index).map (compactFamilyCertificateWithIndex x index)

/-- One final record's global-extra template and family certificates. Keeping
the fields bound makes it possible to reject a certificate attached to a row
other than its exact owner record. -/
structure CompactCheckRecord where
  owner : Option Name := none
  modelSlots : Array Name := #[]
  globalExtra : GlobalExtraRecord
  families : Array CompactFamilyCertificate := #[]
  deriving Inhabited, Repr, BEq

/-- Finish the structural report from final ordered names and family-local
certificates. The caller must already have proved compact dependency/model
ordering; that proof excludes the two order-only violation classes omitted by
the certificates. -/
def compactOrderedReport (records : Array CompactCheckRecord) : Except String Report := do
  let orderedGlobals := records.map (·.globalExtra)
  let orderedNames := orderedGlobals.flatMap (·.names)
  let mut declared : Std.HashSet Name := {}
  let mut declaringRecord : Std.HashMap Name (Array Name) := {}
  for record in records do
    for name in record.globalExtra.names do
      if declared.contains name then
        throw s!"duplicate compact declaration name {name}"
      declared := declared.insert name
      declaringRecord := declaringRecord.insert name record.globalExtra.names
  let ruleSlots := orderedNames.foldl (init :=
      ({} : Std.HashMap Name (Array (Name × Nat)))) fun slots name =>
    match iotaSlot? name with
    | none => slots
    | some (parent, ruleIndex) =>
      slots.insert parent ((slots.getD parent #[]).push (name, ruleIndex))
  let mut familiesChecked := 0
  let mut violations : Array Violation := #[]
  let mut certifiedOwners : Std.HashSet Name := {}
  for record in records do
    if record.families.size > 1 then
      throw s!"compact owner record {record.owner} carries {record.families.size} family certificates"
    for family in record.families do
      unless record.owner == some family.owner do
        throw s!"compact family certificate for {family.owner} is not bound to its owner record"
      if certifiedOwners.contains family.owner then
        throw s!"duplicate compact family certificate for {family.owner}"
      certifiedOwners := certifiedOwners.insert family.owner
      unless family.publicNames.any declared.contains do continue
      familiesChecked := familiesChecked + 1
      let familyNames := family.publicNames.foldl (init := #[]) fun names publicName =>
        appendUnique names (declaringRecord.getD publicName #[]).toList
      if let some (owner, target) :=
          ownerBackreferenceFromCertificate? family.ownerReferences familyNames then
        violations := violations.push (.ownerBackreference owner target)
      violations := violations ++ family.localViolations
      for (owner, model, validRules) in family.recursors do
        for (name, ruleIndex) in ruleSlots.getD model #[] do
          if ruleIndex >= validRules || name != Naming.iotaName owner ruleIndex then
            violations := violations.push (.extraRule owner name)
    if record.modelSlots.any declared.contains && record.families.isEmpty then
      throw s!"compact owner record {record.owner} has declared model slots but no family certificate"
  violations := violations ++ globalExtrasFromRecords orderedGlobals
  return { familiesChecked, violations }

/-- In-memory equivalence oracle for an already ordered export. -/
def compactOrderedCheckReport (x : Export) : Except String Report :=
  let index := SyntaxIndex.ofSource x
  let families := discoverWithIndex x index
  let familyRecords := compactFamilyCertificateRecordsWithIndex x index families
  let modelSlotRecords := families.foldl (init := Array.replicate x.decls.size #[])
    fun records family => records.set! family.ownerDecl family.correspondence.publicNames
  compactOrderedReport <| (globalExtraRecordsWithIndex index x.decls).mapIdx fun i globalExtra =>
    { owner := match x.decls[i]! with
        | .induct (type :: _) _ _ => some type.name
        | _ => none
      modelSlots := modelSlotRecords[i]!
      globalExtra, families := familyRecords[i]! }

/-- Exact public-interface comparison without an environment or an ordering
assumption.  This is the generation oracle: all expected declarations and
theorems are reconstructed from the serialized owner records.  The separate
ordering checker remains responsible for model-before-owner and owner
backreference invariants. -/
structure StatementReport where
  statementsChecked : Nat
  violations : Array Violation
  deriving Inhabited, Repr, BEq

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
