import InductiveModels.Check.Kit
import InductiveModels.Check.Correspondence

/-!
# Reconstructed statements and the discovered family record

The literal propositions the checker expects a model to prove — recursor
rules, unit-like witnesses and K reductions — reconstructed from the owner's
own export records, plus the correspondence table each inductive record
determines and the discovered-family record built on it.  Nothing is inferred,
unfolded, or compared definitionally.
-/

open Lean

namespace InductiveModels.Check

/-- The literal equality proposition exported for rule `ruleIndex` of
`recursorName`, before the simultaneous model-name substitution.  Its left-hand
side already names `recursorName._model`, as the proposition necessarily does;
all types, constructors and right-hand-side recursor calls still use originals.

The recursor's own minor premise supplies the motive application, constructor
levels, parameters, indices and field telescope.  The exported rule supplies
the right-hand side.  Nothing is inferred, unfolded or compared definitionally.
The returned level parameters are those of the original recursor. -/
def iotaPropositionWith? (x : Export) (constructors : Constructors)
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
  unless type.isKernelUnitlike constructors x.exactNormalizationEnv do none
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

private structure CorrespondenceRecursorSeed where
  name : Name
  ruleCount : Nat
  k : Bool

/-- Compact owner facts retained by declaration-wise source indexing. Type and
constructor syntax is required by exact projection/eta reconstruction after
the complete normalizer exists; recursor types and rule RHS graphs are not. -/
structure SourceFamilySeed where
  ownerDecl : Nat
  root : Name
  types : List EIndType
  ctors : List ECtor
  recursors : Array CorrespondenceRecursorSeed

def SourceFamilySeed.ofDeclaration? (ownerDecl : Nat) :
    EDecl → Option SourceFamilySeed
  | .induct types ctors recursors => do
    let root ← types.head?.map (·.name)
    return {
      ownerDecl, root, types, ctors
      recursors := recursors.toArray.map fun recursor =>
        { name := recursor.name, ruleCount := recursor.rules.length, k := recursor.k } }
  | _ => none

def correspondenceForParts (normalizer : ExactNormalizationEnv)
    (projectionFields : EIndType → List ECtor → Array Nat)
    (types : List EIndType) (ctors : List ECtor)
    (recursorRecords : Array CorrespondenceRecursorSeed) : Correspondence := Id.run do
  let typeFormers := types.toArray.map fun type =>
    { owner := type.name, model := Naming.modelName type.name }
  let constructors := ctors.toArray.map fun ctor =>
    { owner := ctor.name, model := Naming.modelName ctor.name }
  let recursors := recursorRecords.map fun recursor =>
    { owner := recursor.name, model := Naming.modelName recursor.name }
  let iotas := recursorRecords.flatMap fun recursor =>
    (Array.range recursor.ruleCount).map (Naming.Iota.ofRecursor recursor.name)
  let unitlikeMetadata := types.toArray.filterMap fun type =>
    if type.isKernelUnitlike ctors normalizer then
      some (Naming.Metadata.ofOwner .unitlike type.name)
    else none
  let ruleKMetadata := recursorRecords.filterMap fun recursor =>
    if recursor.k then some (Naming.Metadata.ofOwner .ruleK recursor.name) else none
  let etaMetadata := types.toArray.filterMap fun type =>
    if type.isKernelStructureLike ctors normalizer &&
        !normalizer.isPropositionFormer type.type then
      some (Naming.Metadata.ofOwner .eta type.name)
    else none
  let mut projections : Array Naming.Projection := #[]
  for type in types do
    for fieldIndex in projectionFields type ctors do
      projections := projections.push (.ofField type.name fieldIndex)
  let metadata := unitlikeMetadata ++ etaMetadata ++ ruleKMetadata
  return { typeFormers, constructors, recursors, projections, iotas, metadata }

/-- The correspondence table determined by one inductive record and its exact
syntax context, independent of whether any model declarations are present. -/
def correspondenceFor? (normalizer : ExactNormalizationEnv)
    (projectionFields : EIndType → List ECtor → Array Nat)
    (declaration : EDecl) : Option Correspondence := do
  let .induct types ctors recursors := declaration | none
  return correspondenceForParts normalizer projectionFields types ctors <|
    recursors.toArray.map fun recursor =>
      { name := recursor.name, ruleCount := recursor.rules.length, k := recursor.k }

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

end InductiveModels.Check
