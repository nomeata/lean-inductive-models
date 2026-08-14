import InductiveModels.Driver
import InductiveModels.Check
import InductiveModels.ModelRoles
import InductiveModels.Order

set_option maxRecDepth 2048

open Lean Meta InductiveModels

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def projectionGeneration : Cli.Config :=
  { nested := true, mutualModels := true, simple := true, basic := true }

def readExport (path : String) : IO Export := do
  let .ok x := parse (← IO.FS.readFile path)
    | throw <| IO.userError s!"cannot parse {path}"
  return x

def runExport (x : Export) : IO (Array EDecl × Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<projection-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Core.CoreM.toIO
    (MetaM.run' (runFilter x false projectionGeneration)) context { env }
  return result

def outputExport (input : Export) (declarations : Array EDecl) : Export :=
  { input with decls := declarations }

/-- No declaration-local public model root, iota, projection, or private
implementation descendant of the complete source block survived a declined
owner transition. -/
def noModeledBlockDescendants (input : Export) (declarations : Array EDecl)
    (owner : Name) : Bool :=
  (input.decls.find? (·.names.contains owner)).any fun sourceBlock =>
    let modelRoots := sourceBlock.names.toArray.map Naming.modelName
    declarations.all fun declaration => declaration.names.all fun name =>
      modelRoots.all fun root => !root.isPrefixOf name

def declarationIndex? (x : Export) (name : Name) : Option Nat :=
  x.decls.findIdx? (·.names.contains name)

/-- Test-only source variant: move one complete declaration record before an
owner while preserving the relative order of every other source record.  This
does not model production scheduling; it makes the prerequisite-first contract
of positive generation fixtures explicit. -/
def withCompletePrerequisiteBefore (x : Export) (prerequisite owner : Name) : IO Export := do
  let prerequisiteIndices := (Array.range x.decls.size).filter fun index =>
    x.decls[index]!.names.contains prerequisite
  let ownerIndices := (Array.range x.decls.size).filter fun index =>
    x.decls[index]!.names.contains owner
  unless prerequisiteIndices.size == 1 do
    throw <| IO.userError s!"expected one complete {prerequisite} record, got {prerequisiteIndices}"
  unless ownerIndices.size == 1 do
    throw <| IO.userError s!"expected one complete {owner} record, got {ownerIndices}"
  let prerequisiteIndex := prerequisiteIndices[0]!
  let ownerIndex := ownerIndices[0]!
  if prerequisiteIndex < ownerIndex then return x
  let prerequisiteRecord := x.decls[prerequisiteIndex]!
  return { x with decls :=
    x.decls.extract 0 ownerIndex ++ #[prerequisiteRecord] ++
      x.decls.extract ownerIndex prerequisiteIndex ++
      x.decls.extract (prerequisiteIndex + 1) x.decls.size }

def declaration? (x : Export) (name : Name) : Option EDecl :=
  x.decls.find? (·.names.contains name)

def declarationType? (x : Export) (name : Name) : Option Expr := do
  let declaration ← declaration? x name
  match declaration with
  | .ax got _ type _ | .quot got _ type _ => if got == name then some type else none
  | .defn got _ type .. | .thm got _ type .. | .opaq got _ type .. =>
      if got == name then some type else none
  | .induct types constructors recursors =>
      (types.find? (·.name == name)).map (·.type) <|>
      (constructors.find? (·.name == name)).map (·.type) <|>
      (recursors.find? (·.name == name)).map (·.type)

def definitionValue? (x : Export) (name : Name) : Option Expr := do
  let .defn got _ _ value .. ← declaration? x name | none
  if got == name then some value else none

def theoremValue? (x : Export) (name : Name) : Option Expr := do
  let .thm got _ _ value _ ← declaration? x name | none
  if got == name then some value else none

def ownerAndRecursor? (x : Export) (owner : Name) : Option (EIndType × ERec) :=
  x.decls.findSome? fun declaration => match declaration with
    | .induct types _ recursors => do
      let type ← types.find? (·.name == owner)
      let recursor ← recursors.find? (·.name == Name.str owner "rec")
      return (type, recursor)
    | _ => none

partial def containsConst (target : Name) : Expr → Bool
  | .const name _ => name == target
  | .proj _ _ struct => containsConst target struct
  | .app fn argument => containsConst target fn || containsConst target argument
  | .lam _ type body _ | .forallE _ type body _ =>
      containsConst target type || containsConst target body
  | .letE _ type value body _ =>
      containsConst target type || containsConst target value || containsConst target body
  | .mdata _ body => containsConst target body
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => false

partial def containsRedundantZeroMaxLevel : Level → Bool
  | .max _ .zero | .max .zero _ => true
  | .succ level => containsRedundantZeroMaxLevel level
  | .max left right | .imax left right =>
      containsRedundantZeroMaxLevel left || containsRedundantZeroMaxLevel right
  | .zero | .param _ | .mvar _ => false

partial def containsRedundantZeroMax : Expr → Bool
  | .sort level => containsRedundantZeroMaxLevel level
  | .const _ levels => levels.any containsRedundantZeroMaxLevel
  | .proj _ _ struct => containsRedundantZeroMax struct
  | .app fn argument => containsRedundantZeroMax fn || containsRedundantZeroMax argument
  | .lam _ type body _ | .forallE _ type body _ =>
      containsRedundantZeroMax type || containsRedundantZeroMax body
  | .letE _ type value body _ =>
      containsRedundantZeroMax type || containsRedundantZeroMax value ||
        containsRedundantZeroMax body
  | .mdata _ body => containsRedundantZeroMax body
  | .bvar _ | .fvar _ | .mvar _ | .lit _ => false

partial def outerEqualityRhs? : Expr → Option Expr
  | .forallE _ _ body _ => outerEqualityRhs? body
  | body => body.getAppArgs[2]?

partial def lambdaBodyIsEqRefl : Expr → Bool
  | .lam _ _ body _ => lambdaBodyIsEqRefl body
  | body => match body.getAppFn with
    | .const ``Eq.refl _ => true
    | _ => false

/-- A test-only defeq-redundant level spelling.  The raw constructor is
intentional: normalization would destroy the syntax this regression pins. -/
def redundantSourceLevels (expression : Expr) : Expr :=
  expression.replace fun
    | .sort level => some (.sort (.max level .zero))
    | .const `Wty.rec (motiveLevel :: ownerLevels) =>
        some (.const `Wty.rec (.max motiveLevel .zero :: ownerLevels))
    | _ => none

/-- `Eq.rec` returning `Sort level` along reflexivity, hence definitionally
equal to the original sort but observably source-authored syntax. -/
def authoredSortTransport (level : Level) : Expr :=
  let α := Expr.sort (.succ level)
  let value := Expr.sort level
  let equalityLevel := .succ (.succ level)
  let motive := Expr.lam `target α
    (Expr.lam `equality
      (mkAppN (.const ``Eq [equalityLevel]) #[α, value, .bvar 0])
      (Expr.sort (.succ level)) .default) .default
  let equality := mkAppN (.const ``Eq.refl [equalityLevel]) #[α, value]
  mkAppN (.const ``Eq.rec [equalityLevel, equalityLevel])
    #[α, value, motive, value, value, equality]

/-- Add one source-authored, definitionally trivial transport to the outer
parameter domain of every exact face in an exported inductive record. -/
def authoredOuterSortTransport : Expr → Expr
  | .forallE name (.sort level) body info =>
      .forallE name (authoredSortTransport level) body info
  | .lam name (.sort level) body info =>
      .lam name (authoredSortTransport level) body info
  | expression => expression

def mapOwnerSyntax (x : Export) (owner : Name) (map : Expr → Expr) : Export :=
  { x with decls := x.decls.map fun declaration =>
      if declaration.names.contains owner then EDecl.mapNames id map declaration
      else declaration }

def mapRecursorSyntax (x : Export) (recursor : Name) (map : Expr → Expr) : Export :=
  { x with decls := x.decls.map fun declaration => match declaration with
    | .induct types constructors recursors => .induct types constructors <|
        recursors.map fun value => if value.name == recursor then
          { value with
            type := map value.type
            rules := value.rules.map fun rule => { rule with rhs := map rule.rhs } }
        else value
    | _ => declaration }

partial def containsProjection : Expr → Bool
  | .proj .. => true
  | .app fn argument => containsProjection fn || containsProjection argument
  | .lam _ type body _ | .forallE _ type body _ =>
      containsProjection type || containsProjection body
  | .letE _ type value body _ =>
      containsProjection type || containsProjection value || containsProjection body
  | .mdata _ body => containsProjection body
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => false

def declarationNames : EDecl → Array Name
  | .ax name _ type _ | .quot name _ type _ =>
      #[name] ++ type.getUsedConstants
  | .defn name _ type value _ _ all |
    .thm name _ type value all |
    .opaq name _ type value _ all =>
      #[name] ++ all.toArray ++ type.getUsedConstants ++ value.getUsedConstants
  | .induct types constructors recursors =>
      (types.toArray.flatMap fun type =>
        #[type.name] ++ type.all.toArray ++ type.ctors.toArray ++ type.type.getUsedConstants) ++
      (constructors.toArray.flatMap fun constructor =>
        #[constructor.name, constructor.induct] ++ constructor.type.getUsedConstants) ++
      (recursors.toArray.flatMap fun recursor =>
        #[recursor.name] ++ recursor.all.toArray ++ recursor.type.getUsedConstants ++
          recursor.rules.toArray.flatMap fun rule =>
            #[rule.ctor] ++ rule.rhs.getUsedConstants)

def insertCollision (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.push (.ax name [] (.sort (.succ .zero)) false) }

def withoutDeclaration (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.filter (!·.names.contains name) }

def intrinsicFieldsFor (x : Export) (owner : Name) : Array Nat :=
  x.decls.findSome? (fun declaration => match declaration with
    | .induct types constructors _ =>
      (types.find? (·.name == owner)).map fun type =>
        x.intrinsicProjectionFieldsFor type constructors
    | _ => none) |>.getD #[]

def indexedIntrinsicFieldsAgree (x : Export) : Bool :=
  let index := Check.SyntaxIndex.ofSource x
  x.decls.all fun declaration => match declaration with
    | .induct types constructors _ =>
      types.all fun type =>
        index.intrinsicProjectionFields type constructors ==
          x.intrinsicProjectionFieldsFor type constructors
    | _ => true

private structure ProjectionPropertyDecl where
  key : Nat
  ordinal : Nat
  declaration : EDecl

private def projectionPropertyMix (seed index : Nat) : Nat :=
  (seed * 1664525 + index * 1013904223 + index * index * 31) % 2147483647

def permuteProjectionExport (x : Export) (seed : Nat) : Export :=
  let keyed := x.decls.mapIdx fun ordinal declaration =>
    { key := projectionPropertyMix seed ordinal, ordinal, declaration : ProjectionPropertyDecl }
  let ordered := keyed.qsort fun left right =>
    left.key < right.key || (left.key == right.key && left.ordinal < right.ordinal)
  { x with decls := ordered.map (·.declaration) }

def replaceDeclarationType (x : Export) (name : Name) (type : Expr) : Export :=
  { x with decls := x.decls.map fun declaration => match declaration with
    | .ax got params _ isUnsafe =>
        if got == name then .ax got params type isUnsafe else declaration
    | .defn got params _ value hints safety all =>
        if got == name then .defn got params type value hints safety all else declaration
    | .thm got params _ value all =>
        if got == name then .thm got params type value all else declaration
    | .opaq got params _ value isUnsafe all =>
        if got == name then .opaq got params type value isUnsafe all else declaration
    | _ => declaration }

def replaceDefinitionSafety (x : Export) (name : Name) (safety : String) : Export :=
  { x with decls := x.decls.map fun declaration => match declaration with
    | .defn got params type value hints _ all =>
        if got == name then .defn got params type value hints safety all else declaration
    | _ => declaration }

def replaceImplementationWithAxiom (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.map fun declaration => match declaration with
    | .defn got params type _ _ _ _ =>
        if got == name then .ax got params type false else declaration
    | _ => declaration }

def replaceTheoremWithDefinition (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.map fun declaration => match declaration with
    | .thm got params type value all =>
        if got == name then .defn got params type value .opaque "safe" all else declaration
    | _ => declaration }

def replaceConst (type : Expr) (target replacement : Name) : Expr :=
  type.replace fun
    | .const name levels =>
        if name == target then some (.const replacement levels) else none
    | _ => none

/-- Raise only the universe argument of a theorem's outer equality, retaining
the complete binder telescope and all three equality arguments literally. -/
partial def raiseOuterEqLevel? : Expr → Option Expr
  | .forallE name domain body info =>
      return .forallE name domain (← raiseOuterEqLevel? body) info
  | body => do
      let .const ``Eq [level] := body.getAppFn | none
      some (mkAppN (.const ``Eq [.succ level]) body.getAppArgs)

def hasTypeViolation (owner declaration : Name) : Check.Violation → Bool
  | .declarationType gotOwner gotDeclaration =>
      gotOwner == owner && gotDeclaration == declaration
  | _ => false

def hasMissingViolation (owner declaration : Name) : Check.Violation → Bool
  | .missingPublic gotOwner gotDeclaration =>
      gotOwner == owner && gotDeclaration == declaration
  | _ => false

def hasExtraProjectionViolation (owner declaration : Name) : Check.Violation → Bool
  | .extraProjection gotOwner gotDeclaration =>
      gotOwner == owner && gotDeclaration == declaration
  | _ => false

def hasKindViolation (owner declaration : Name)
    (expected actual : Check.DeclarationKind) : Check.Violation → Bool
  | .declarationKind gotOwner gotDeclaration gotExpected gotActual =>
      gotOwner == owner && gotDeclaration == declaration &&
        gotExpected == expected && gotActual == actual
  | _ => false

def hasSafetyViolation (owner declaration : Name) (actual : String) :
    Check.Violation → Bool
  | .declarationSafety gotOwner gotDeclaration gotActual =>
      gotOwner == owner && gotDeclaration == declaration && gotActual == actual
  | _ => false

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let wrapperRaw ← readExport "test/fixtures/inductive-models/structure_projections.ndjson"
  let raw := #[`Dep.key, `Dep.payload, `Dep.witness, `SortFields.carrier,
    `SortFields.family, `SortFields.element, `SortFields.letCarrier,
    `depKey, `depPayload, `depWitness].foldl withoutDeclaration wrapperRaw
  let (declarations, report) ← runExport raw
  let generated := outputExport raw declarations
  let names := declarations.flatMap (·.names.toArray)
  let keyModel := Naming.projectionName `Dep 0
  let payloadModel := Naming.projectionName `Dep 1
  let witnessModel := Naming.projectionName `Dep 2
  let keyRule := Naming.projectionIotaName `Dep 0
  let payloadRule := Naming.projectionIotaName `Dep 1
  let witnessRule := Naming.projectionIotaName `Dep 2
  let projectionNames := #[keyModel, payloadModel, witnessModel]
  let projectionRules := #[keyRule, payloadRule, witnessRule]
  let sortFieldProjections := (Array.range 4).flatMap fun fieldIndex =>
    #[Naming.projectionName `SortFields fieldIndex,
      Naming.projectionIotaName `SortFields fieldIndex]
  let mut state : TestState := {}
  state := state.check "indexed intrinsic fields equal the whole-export helper" <|
    indexedIntrinsicFieldsAgree wrapperRaw && indexedIntrinsicFieldsAgree raw
  state := state.check "indexed intrinsic fields survive focused permutations" <|
    (Array.range 64).all fun seed =>
      indexedIntrinsicFieldsAgree (permuteProjectionExport wrapperRaw seed)

  -- A maybe-zero singleton cannot use the ordinary Church carrier: it forgets
  -- which payload constructed it, while an intrinsic projection retains that
  -- payload at positive instantiations.  `PI` uses its exact-sort field as the
  -- carrier; `PF` lifts its exactly proposition-valued field with the derived
  -- tight-pair/PUnit construction.
  let primRaw ← readExport "test/fixtures/inductive-models/prim_shapes.ndjson"
  let (primDeclarations, primReport) ← runExport primRaw
  let primGenerated := outputExport primRaw primDeclarations
  let primLateEqOwners := #[`Tri, `TagS4, `TagS3, `Weave, `Opt, `IdxP, `Le3,
    `Le3.below, `PM, `Emp, `Conj3, `PU, `Sv, `PE, `MNm, `IdxS]
  let primSupportRaw ← withCompletePrerequisiteBefore primRaw `Eq `Tri
  let (primSupportDeclarations, primSupportReport) ← runExport primSupportRaw
  let primSupportGenerated := outputExport primSupportRaw primSupportDeclarations
  let pfProjection := Naming.projectionName `PF 0
  let pfRule := Naming.projectionIotaName `PF 0
  let pfSlots := #[Naming.modelName `PF, Naming.modelName `PF.mk,
    Naming.modelName `PF.rec, Naming.iotaName `PF.rec 0, pfProjection, pfRule]
  let piProjection := Naming.projectionName `PI 0
  let piRule := Naming.projectionIotaName `PI 0
  let piDefinitions := #[Naming.modelName `PI, Naming.modelName `PI.mk,
    Naming.modelName `PI.rec, piProjection]
  let primNames := primDeclarations.flatMap (·.names.toArray)
  state := state.check "proposition-field singleton emits its six exact slots" <|
    primReport.generated.any (·.1 == `PF) &&
      !primReport.declined.any (·.1 == `PF) && pfSlots.all primNames.contains
  state := state.check "proposition-field singleton interface is exact" <|
    (Check.check primGenerated).all (·.familyOwner != `PF)
  state := state.check "proposition-field model uses only the derived exact-sort lift" <|
    (definitionValue? primGenerated (Naming.modelName `PF)).any (containsConst `PSigma') &&
    (definitionValue? primGenerated (Naming.modelName `PF)).any (containsConst `PUnit) &&
    (definitionValue? primGenerated (Naming.modelName `PF.mk)).any
      (containsConst `PSigma'.mk) &&
    (definitionValue? primGenerated (Naming.modelName `PF.mk)).any
      (containsConst `PUnit.unit) &&
    (definitionValue? primGenerated (Naming.modelName `PF.rec)).any
      (containsConst `PSigma'.rec') &&
    (definitionValue? primGenerated pfProjection).any (containsConst `PSigma'.fst) &&
    pfSlots.all fun name => (declaration? primGenerated name).all fun declaration =>
      let used := declarationNames declaration
      !used.contains `PULiftP && !used.contains `PULiftP.up && !used.contains `PULiftP.rec
  state := state.check "proposition-field projection iota is literal and uncast" <|
    (declarationType? primGenerated pfRule).any fun type => !containsConst ``Eq.rec type
  state := state.check "raw-order prim owners before Eq decline without partial models" <|
    primReport.declined == primLateEqOwners.map (·, "prim model name taken (Eq)") &&
      primLateEqOwners.all fun owner =>
        noModeledBlockDescendants primRaw primDeclarations owner
  let propStructureRules :=
    (Array.range 2).map (Naming.projectionIotaName `Conj) ++
      (Array.range 3).map (Naming.projectionIotaName `Conj3)
  state := state.check "prerequisite-first Prop-structure dependent iotas are literal reflexivity" <|
    primSupportReport.generated.any (·.1 == `Conj3) &&
    propStructureRules.all fun rule =>
      (declarationType? primSupportGenerated rule).any (!containsConst ``Eq.rec ·) &&
        (theoremValue? primSupportGenerated rule).any (containsConst ``Eq.refl)
  state := state.check "variable-sort singleton retains its intrinsic field" <|
    primReport.generated.any (·.1 == `PI) &&
      !primReport.declined.any (·.1 == `PI) &&
      primNames.contains piProjection && primNames.contains piRule
  state := state.check "variable-sort singleton projection is exact" <|
    (Check.check primGenerated).all (·.familyOwner != `PI)
  state := state.check "variable-sort singleton selector avoids its small recursor" <|
    (definitionValue? primGenerated piProjection).any fun value =>
      !containsConst `PI.rec._model value
  state := state.check "exact-sort singleton remains the identity route" <|
    piDefinitions.all fun name => (definitionValue? primGenerated name).any fun value =>
      !containsConst `PSigma' value && !containsConst `PUnit value &&
        !containsConst `PULiftP value

  -- A genuine proposition has a stronger projection contract than an
  -- arbitrary maybe-zero carrier. Every kernel-projectable field is itself a
  -- proof, so proof irrelevance identifies both an earlier projected proof
  -- with its constructor local and the selected proof with the projection
  -- result. `PropRecIdx` is recursive and indexed, ensuring this does not pass
  -- merely because a direct nonrecursive selector reduces.
  let propRaw ← readExport
    "test/fixtures/inductive-models/prop_recursive_projections.ndjson"
  let (propDeclarations, propReport) ← runExport propRaw
  let propGenerated := outputExport propRaw propDeclarations
  let propProjectionNames := (Array.range 3).map (Naming.projectionName `PropRecIdx)
  let propProjectionRules := (Array.range 3).map (Naming.projectionIotaName `PropRecIdx)
  state := state.check "recursive indexed Prop exposes every proof field" <|
    intrinsicFieldsFor propRaw `PropRecIdx == #[0, 1, 2] &&
      propReport.generated.any (fun row => row.1 == `PropRecIdx) &&
      !propReport.declined.any (fun row => row.1 == `PropRecIdx) &&
      (propProjectionNames ++ propProjectionRules).all fun name =>
        (declaration? propGenerated name).isSome
  state := state.check "recursive indexed Prop projection iotas have literal fields" <|
    (Array.range 3).all fun fieldIndex =>
      let rule := propProjectionRules[fieldIndex]!
      (declarationType? propGenerated rule).bind outerEqualityRhs? ==
          some (.bvar (2 - fieldIndex)) &&
        (theoremValue? propGenerated rule).any lambdaBodyIsEqRefl
  state := state.check "dependent Prop projection retains the source default wrapper" <|
    (declarationType? propGenerated propProjectionRules[1]!).any
      (containsConst `optParam)
  state := state.check "recursive indexed Prop projections use the nontrivial recursor path" <|
    propProjectionNames.all fun projection =>
      (definitionValue? propGenerated projection).any
        (containsConst (Naming.modelName `PropRecIdx.rec))
  state := state.check "checker accepts recursive indexed Prop literal projection rules" <|
    propReport.stmtErrors.isEmpty &&
      (Check.check propGenerated).all (fun violation => violation.familyOwner != `PropRecIdx)
  state := state.check "maybe-zero formers do not enter the Prop literal contract" <|
    (ownerAndRecursor? primRaw `PI).any fun (type, _) =>
      !propositionProjectionIotaUsesLiteralField type

  -- Literal means source-literal, not transport-free. The fixture writes a
  -- definitionally trivial Eq.rec in the dependent proof field's domain. It
  -- must remain in that projection's exact public type and iota telescope;
  -- only the generator's former dependency transport is absent.
  state := state.check "source-authored Eq.rec survives dependent Prop faces" <|
    (declarationType? propGenerated propProjectionNames[1]!).any
        (containsConst ``Eq.rec) &&
      (declarationType? propGenerated propProjectionRules[1]!).any
        (containsConst ``Eq.rec)

  -- Nested and plain-mutual builders still use installed constructor
  -- telescopes. Their head-beta wrapper is therefore pinned to the existing
  -- normalized/transported projection contract until those routes receive an
  -- exact raw-source adapter of their own.
  let propBoundaryRaw ← readExport
    "test/fixtures/inductive-models/prop_projection_boundaries.ndjson"
  let (propBoundaryDeclarations, propBoundaryReport) ← runExport propBoundaryRaw
  let propBoundaryGenerated := outputExport propBoundaryRaw propBoundaryDeclarations
  let nestedBoundaryRule := Naming.projectionIotaName `NestedProp 1
  let mutualBoundaryRule := Naming.projectionIotaName `MutualPropA 1
  state := state.check "nested and mutual Prop owners remain outside the literal tranche" <|
    (ownerAndRecursor? propBoundaryRaw `NestedProp).all fun (type, _) =>
      !propositionProjectionIotaUsesLiteralField type &&
    (ownerAndRecursor? propBoundaryRaw `MutualPropA).all fun (type, _) =>
      !propositionProjectionIotaUsesLiteralField type
  state := state.check "nested and mutual Prop controls expose dependent proof fields" <|
    intrinsicFieldsFor propBoundaryRaw `NestedProp == #[0, 1, 2] &&
      intrinsicFieldsFor propBoundaryRaw `MutualPropA == #[0, 1, 2] &&
      intrinsicFieldsFor propBoundaryRaw `MutualPropB == #[0]
  state := state.check "nested Prop control is generated rather than declined" <|
    propBoundaryReport.generated.any (fun row => row.1 == `NestedProp) &&
      !propBoundaryReport.declined.any (fun row => row.1 == `NestedProp)
  state := state.check "nested and mutual Prop controls retain their legacy rule contracts" <|
    (declarationType? propBoundaryGenerated nestedBoundaryRule).any fun type =>
      (outerEqualityRhs? type).any fun rhs =>
        rhs != .bvar 1 && containsConst ``Eq.rec rhs &&
      (declarationType? propBoundaryGenerated mutualBoundaryRule).bind outerEqualityRhs? ==
        some (.bvar 1) &&
      (declarationType? propBoundaryGenerated mutualBoundaryRule).any (containsConst `optParam)
  state := state.check "nested and mutual Prop controls remain exactly checked" <|
    propBoundaryReport.stmtErrors.isEmpty &&
      (Check.check propBoundaryGenerated).all fun violation =>
        !#[`NestedProp, `MutualPropA, `MutualPropB].contains violation.familyOwner

  -- A recursive Type with no base constructor is empty, including when arm C
  -- obtains it as the erasure skeleton of an indexed family.  `NoBase` checks
  -- both layers: each exact eight-slot public interface (including its two
  -- intrinsic projection pairs) must close. First-use foundation records are
  -- charged to the island that splices them, not to either public slot set.
  let noBaseRaw ← readExport "test/fixtures/inductive-models/prim_carve.ndjson"
  let (noBaseDeclarations, noBaseReport) ← runExport noBaseRaw
  let noBaseGenerated := outputExport noBaseRaw noBaseDeclarations
  let noBaseOrdered ← match Order.reorder noBaseGenerated with
    | .ok output => pure output
    | .error error => throw <| IO.userError s!"cannot order no-base fixture: {repr error}"
  let noBaseSkel := `NoBase._model._impl.skel
  let noBaseSlots := #[Naming.modelName `NoBase, Naming.modelName `NoBase.mk,
    Naming.modelName `NoBase.rec, Naming.iotaName `NoBase.rec 0,
    Naming.projectionName `NoBase 0, Naming.projectionIotaName `NoBase 0,
    Naming.projectionName `NoBase 1, Naming.projectionIotaName `NoBase 1]
  let noBaseSkelSlots := #[Naming.modelName noBaseSkel,
    Naming.modelName (Name.str noBaseSkel "c_0"),
    Naming.modelName (Name.str noBaseSkel "rec"),
    Naming.iotaName (Name.str noBaseSkel "rec") 0,
    Naming.projectionName noBaseSkel 0, Naming.projectionIotaName noBaseSkel 0,
    Naming.projectionName noBaseSkel 1, Naming.projectionIotaName noBaseSkel 1]
  state := state.check "no-base indexed family and its empty skeleton both model" <|
    noBaseReport.generated.any (·.1 == `NoBase) &&
      noBaseReport.generated.any (·.1 == noBaseSkel) &&
      !noBaseReport.declined.any fun (owner, _) => owner == `NoBase || owner == noBaseSkel
  state := state.check "no-base and skeleton expose exactly their required public slots" <|
    noBaseSlots.all (fun slot => (noBaseDeclarations.filter (·.names.contains slot)).size == 1) &&
      noBaseSkelSlots.all fun slot =>
        (noBaseDeclarations.filter (·.names.contains slot)).size == 1
  state := state.check "no-base first-use support is charged to its generating islands" <|
    (noBaseReport.spliced.filter (·.1 == `NoBase)).size == 1 &&
    (noBaseReport.spliced.filter (·.1 == noBaseSkel)).size == 1 &&
    noBaseReport.spliced.find? (·.1 == `NoBase) == some (`NoBase,
      #[`PSigma', `PSigma'.rec, `PSigma'.mk, `PSigma'.fst, `PSigma'.snd,
        `PSigma'.rec', `PSigma'.fst_mk, `PSigma'.snd_mk, `PSigma'.rec'_mk, noBaseSkel]) &&
    noBaseReport.spliced.find? (·.1 == noBaseSkel) == some (noBaseSkel,
      #[`Nat, `Nat.rec, `Nat.zero, `Nat.succ, `PUnit, `PUnit.rec, `PUnit.unit])
  state := state.check "no-base interfaces satisfy the exact public checker" <|
    (Check.check noBaseOrdered).all fun violation =>
      violation.familyOwner != `NoBase && violation.familyOwner != noBaseSkel
  state := state.check "no-base skeleton uses the derived exact empty carrier" <|
    (definitionValue? noBaseGenerated (Naming.modelName noBaseSkel)).any fun value =>
      containsConst `PSigma' value && containsConst `PUnit value && !containsConst `PULiftP value
  state := state.check "no-base recursor projects and eliminates Church false" <|
    (definitionValue? noBaseGenerated (Naming.modelName (Name.str noBaseSkel "rec"))).any
      fun value =>
        containsConst `PSigma'.fst value && containsConst `Nat.rec value &&
          containsConst `Eq.rec value && !containsConst `PULiftP.rec value

  -- `Fmid` and the original `FChain` keep the one-pivot path pinned in the
  -- broad index-axis fixture.
  let fmidRaw ← readExport "test/fixtures/inductive-models/prim_idx.ndjson"
  let (fmidRawDeclarations, fmidRawReport) ← runExport fmidRaw
  let fmidLateEqOwners := #[`N, `Rv, `Rvx, `Inf, `Rxh, `Rxh.below, `FChain,
    `Rgd, `Rgd.below, `Fam, `Inf.below, `Fg, `Rv.below, `Fall3, `Fxh, `Fmid]
  let fmidSupportRaw ← withCompletePrerequisiteBefore fmidRaw `Eq `N
  let (fmidDeclarations, fmidReport) ← runExport fmidSupportRaw
  let fmidGenerated := outputExport fmidSupportRaw fmidDeclarations
  let fmidOrdered ← match Order.reorder fmidGenerated with
    | .ok output => pure output
    | .error error => throw <| IO.userError s!"cannot order dependent-pivot fixture: {repr error}"
  let fmidOwners := #[`Fmid, `FChain]
  state := state.check "raw-order dependent-pivot owners before Eq decline without partial models" <|
    fmidRawReport.declined == fmidLateEqOwners.map (·, "prim model name taken (Eq)") &&
      fmidLateEqOwners.all fun owner =>
        noModeledBlockDescendants fmidRaw fmidRawDeclarations owner
  state := state.check "one-pivot arm-F owners retain their exact interfaces" <|
    #[(`Fmid, 4), (`FChain, 4)].all fmidReport.generated.contains &&
      !fmidReport.declined.any fun (owner, _) => fmidOwners.contains owner &&
      (Check.check fmidOrdered).all fun violation => !fmidOwners.contains violation.familyOwner

  -- The two apparent guards at the dependent-pivot classifier have different
  -- status. `LostData` is accepted by the kernel, but because its `Nat`
  -- payload is absent from the conclusion index the kernel gives it only a
  -- small recursor: route selection stops before arm F. `MovingPivot` has a
  -- large recursor and reaches the dependent-pivot scan. Its pivot and the
  -- supplying constructor field are one recorded classifier entry, so the
  -- old "pivot has no data field" state is unrepresentable.
  let guardRaw ← readExport "test/fixtures/inductive-models/arm_f_guards.ndjson"
  let (guardDeclarations, guardReport) ← runExport guardRaw
  let guardGenerated := outputExport guardRaw guardDeclarations
  let guardOrdered ← match Order.reorder guardGenerated with
    | .ok output => pure output
    | .error error => throw <| IO.userError s!"cannot order arm-F guard fixture: {repr error}"
  let guardOwners := #[`LostData, `MovingPivot]
  let lostRoute := ownerAndRecursor? guardRaw `LostData
  let movingRoute := ownerAndRecursor? guardRaw `MovingPivot
  state := state.check "unrecoverable data receives a small recursor before arm F" <|
    lostRoute.any fun (type, recursor) =>
      recursor.levelParams.length == type.levelParams.length
  state := state.check "a dependent pivot receives the large arm-F recursor" <|
    movingRoute.any fun (type, recursor) =>
      recursor.levelParams.length == type.levelParams.length + 1
  state := state.check "arm-F guard boundaries model at exact interface sizes" <|
    #[(`LostData, 5), (`MovingPivot, 11)].all guardReport.generated.contains &&
      !guardReport.declined.any fun (owner, _) => guardOwners.contains owner
  state := state.check "arm-F guard boundary output satisfies the exact checker" <|
    (Check.check guardOrdered).all fun violation => !guardOwners.contains violation.familyOwner
  state := state.check "the dependent-pivot boundary takes the zipper transport" <|
    (definitionValue? guardGenerated (Naming.modelName `MovingPivot.rec)).any
      (containsConst ``Eq.rec)

  -- The focused zipper fixture adds two pivots, a proof after a pivot, and a
  -- final non-pivot endpoint depending on the recovered value.
  let zipRaw ← readExport "test/fixtures/inductive-models/arm_f_zip.ndjson"
  let (zipRawDeclarations, zipRawReport) ← runExport zipRaw
  let zipSupportRaw ← withCompletePrerequisiteBefore zipRaw `Eq `FTwo
  let (zipDeclarations, zipReport) ← runExport zipSupportRaw
  let zipGenerated := outputExport zipSupportRaw zipDeclarations
  let zipOrdered ← match Order.reorder zipGenerated with
    | .ok output => pure output
    | .error error => throw <| IO.userError s!"cannot order arm-F zipper fixture: {repr error}"
  let zipOwners := #[`FTwo, `FProof, `FChain, `FEndpoint]
  let zipSupport := #[`PSigma', `PSigma'.rec, `PSigma'.mk, `PSigma'.fst,
    `PSigma'.snd, `PSigma'.rec', `PSigma'.fst_mk, `PSigma'.snd_mk, `PSigma'.rec'_mk]
  state := state.check "arm-F fixture declares a basis-exempt owner before Eq" <|
    (declarationIndex? zipRaw `Nat).any fun natIndex =>
      (declarationIndex? zipRaw `Eq).any fun eqIndex => natIndex < eqIndex
  state := state.check "raw-order arm-F owner before Eq declines without a partial model" <|
    zipRawReport.declined == #[(`FTwo, "prim model name taken (Eq)")] &&
      noModeledBlockDescendants zipRaw zipRawDeclarations `FTwo
  state := state.check "arm-F shared support persists once ahead of every owner" <|
    zipSupport.all fun support =>
      (zipDeclarations.filter (·.names.contains support)).size == 1 &&
        (declarationIndex? zipGenerated support).any fun supportIndex =>
          zipOwners.all fun owner =>
            (declarationIndex? zipGenerated owner).any fun ownerIndex => supportIndex < ownerIndex
  state := state.check "arm-F zipper owners model at exact interface sizes" <|
    zipOwners.all (fun owner => zipReport.generated.any (·.1 == owner)) &&
      !zipReport.declined.any fun (owner, _) => zipOwners.contains owner
  state := state.check "arm-F zipper input satisfies the exact public checker" <|
    (Check.check zipRaw).all fun violation => !zipOwners.contains violation.familyOwner
  state := state.check "arm-F zipper output satisfies the exact public checker" <|
    (Check.check zipOrdered).all fun violation => !zipOwners.contains violation.familyOwner
  state := state.check "arm-F zipper emits every checked iota slot" <|
    zipOwners.all fun owner =>
      (declaration? zipGenerated (Naming.iotaName (Name.str owner "rec") 0)).isSome
  state := state.check "arm-F zipper recursors perform equality transport" <|
    #[`FTwo.rec, `FProof.rec, `FChain.rec, `FEndpoint.rec].all fun recursor =>
      (definitionValue? zipGenerated (Naming.modelName recursor)).any (containsConst ``Eq.rec)

  -- The parameter-dependent proposition field takes the same route.  Its
  -- source owner precedes the input's own `PUnit` declaration, so the original
  -- stream declines it.  A separate prerequisite-first variant retains the
  -- positive exact-interface oracle without introducing production scheduling.
  let pfpRaw ← readExport "test/fixtures/inductive-models/tight_prop_field_late.ndjson"
  let (pfpRawDeclarations, pfpRawReport) ← runExport pfpRaw
  let pfpSupportRaw ← withCompletePrerequisiteBefore pfpRaw `PUnit `PFP
  let (pfpDeclarations, pfpReport) ← runExport pfpSupportRaw
  let pfpGenerated := outputExport pfpSupportRaw pfpDeclarations
  let pfpProjection := Naming.projectionName `PFP 0
  let pfpRule := Naming.projectionIotaName `PFP 0
  let pfpSlots := #[Naming.modelName `PFP, Naming.modelName `PFP.mk,
    Naming.modelName `PFP.rec, Naming.iotaName `PFP.rec 0, pfpProjection, pfpRule]
  let pfpNames := pfpDeclarations.flatMap (·.names.toArray)
  let pfpOrdered ← match Order.reorder pfpGenerated with
    | .ok output => pure output
    | .error error => throw <| IO.userError s!"cannot order late-PUnit fixture: {repr error}"
  state := state.check "parameterized proposition-field fixture has a late PUnit" <|
    (declarationIndex? pfpRaw `PFP).any fun owner =>
      (declarationIndex? pfpRaw `PUnit).any (owner < ·)
  state := state.check "raw-order proposition field declines before PUnit without a partial model" <|
    pfpRawReport.declined == #[(`PFP, "prim model name taken (PUnit)")] &&
      noModeledBlockDescendants pfpRaw pfpRawDeclarations `PFP
  state := state.check "prerequisite-first proposition field uses the input PUnit" <|
    pfpReport.generated.any (·.1 == `PFP) && !pfpReport.declined.any (·.1 == `PFP) &&
      pfpSlots.all pfpNames.contains && !pfpReport.spliced.any fun (_, names) =>
        names.contains `PUnit
  state := state.check "ordered late-lift projection interface is exact" <|
    (Check.check pfpOrdered).all (·.familyOwner != `PFP)

  -- A one-member, unindexed recursive family exposes a public one-layer
  -- carrier over its private fixpoint.  Both ordinary and infinitary fields
  -- therefore reduce to the literal mapped constructor field; dependency on
  -- an earlier field must not reintroduce the old public `Eq.rec` transport.
  let wRawOriginal ← readExport "test/fixtures/inductive-models/prim_w.ndjson"
  let (wRawDeclarations, wRawReport) ← runExport wRawOriginal
  let wLateEqOwners := #[`Tree, `Wty, `Triple, `P, `Q, `Wt, `Dep, `Bad, `TwinInf, `Br]
  let wRaw ← withCompletePrerequisiteBefore wRawOriginal `Eq `Tree
  let (wDeclarations, wReport) ← runExport wRaw
  let wGenerated := outputExport wRaw wDeclarations
  let wNames := wDeclarations.flatMap (·.names.toArray)
  let wtyProjection0 := Naming.projectionName `Wty 0
  let wtyProjection1 := Naming.projectionName `Wty 1
  let wtyRule0 := Naming.projectionIotaName `Wty 0
  let wtyRule1 := Naming.projectionIotaName `Wty 1
  let wtyPrivateRoot := `Wty._model._impl
  let wtyCertificate := #[Name.str wtyPrivateRoot "self", Name.str wtyPrivateRoot "ctor_0",
    Name.str wtyPrivateRoot "rec", Name.str wtyPrivateRoot "rec_iota_0",
    Name.str wtyPrivateRoot "roll", Name.str wtyPrivateRoot "unroll",
    Name.str wtyPrivateRoot "unroll_roll", Name.str wtyPrivateRoot "roll_unroll"]
  state := state.check "raw-order recursive owners before Eq decline without partial models" <|
    wRawReport.declined == wLateEqOwners.map (·, "prim model name taken (Eq)") &&
      wLateEqOwners.all fun owner =>
        noModeledBlockDescendants wRawOriginal wRawDeclarations owner
  state := state.check "dependent recursive singleton carries the complete one-layer certificate" <|
    wtyCertificate.all wNames.contains
  let wtyShape := wRaw.decls.findSome? fun declaration => match declaration with
    | .induct types _ _ => types.toArray.find? (·.name == `Wty)
    | _ => none
  state := state.check "dependent recursive singleton is in the phase-1 source shape" <|
    wtyShape.any fun type => oneLayerProjectionFamily #[type] type
  state := state.check "dependent recursive singleton emits every intrinsic field" <|
    wReport.generated.any (·.1 == `Wty) && !wReport.declined.any (·.1 == `Wty) &&
      wReport.unreplayable.isNone && wReport.stmtErrors.isEmpty &&
      #[wtyProjection0, wtyProjection1, wtyRule0, wtyRule1].all wNames.contains
  state := state.check "dependent recursive singleton projection interface is exact" <|
    (Check.check wGenerated).all fun violation =>
      violation.familyOwner != `Wty || violation matches .modelNotBefore ..
  state := state.check "independent recursive field retains the literal rule" <|
    (declarationType? wGenerated wtyRule0).any fun type => !containsConst ``Eq.rec type
  state := state.check "dependent infinitary recursive field retains the literal rule" <|
    (declarationType? wGenerated wtyRule1).any fun type => !containsConst ``Eq.rec type
  let wtyPublicStatements := #[Naming.modelName `Wty, Naming.modelName `Wty.mk,
    Naming.modelName `Wty.rec, Naming.iotaName `Wty.rec 0,
    wtyProjection0, wtyProjection1, wtyRule0, wtyRule1]
  state := state.check "complete direct one-layer public interface introduces no Eq.rec" <|
    wtyPublicStatements.all fun name =>
      (declarationType? wGenerated name).any fun type => !containsConst ``Eq.rec type

  -- Exact public syntax is a name-only rewrite.  Definitional equality is not
  -- enough here: redundant level spelling from the exporter must survive the
  -- private adapter, public carrier, recursor/iota, and projection family.
  let wExactRaw := mapOwnerSyntax wRaw `Wty redundantSourceLevels
  let (wExactDeclarations, wExactReport) ← runExport wExactRaw
  let wExactGenerated := outputExport wExactRaw wExactDeclarations
  let wExactFaces := #[Naming.modelName `Wty, Naming.modelName `Wty.mk,
    Naming.modelName `Wty.rec, Naming.iotaName `Wty.rec 0,
    wtyProjection0, wtyProjection1, wtyRule0, wtyRule1]
  state := state.check "one-layer carrier retains the exact redundant source level syntax" <|
    wExactReport.unreplayable.isNone && wExactReport.stmtErrors.isEmpty &&
      declarationType? wExactGenerated (Naming.modelName `Wty) ==
        declarationType? wExactRaw `Wty &&
      (Check.check wExactGenerated).all fun violation =>
        violation.familyOwner != `Wty || violation matches .modelNotBefore ..
  state := state.check "redundant source levels span carrier ctor rec iota and projections" <|
    wExactFaces.all fun name =>
      (declarationType? wExactGenerated name).any containsRedundantZeroMax

  -- A clean source has no `Eq.rec` in these propositions, but the generator
  -- must not turn that into a blanket erasure rule.  A source-authored,
  -- definitionally trivial transport in the exact recursor telescope remains
  -- literal in both private and public recursor/iota statements.
  let wAuthoredRaw := mapRecursorSyntax wRaw `Wty.rec authoredOuterSortTransport
  let (wAuthoredDeclarations, wAuthoredReport) ← runExport wAuthoredRaw
  let wAuthoredGenerated := outputExport wAuthoredRaw wAuthoredDeclarations
  let wAuthoredFaces := #[Naming.modelName `Wty.rec, Naming.iotaName `Wty.rec 0,
    Name.str wtyPrivateRoot "rec", Name.str wtyPrivateRoot "rec_iota_0"]
  state := state.check "source-authored Eq.rec survives one-layer recursor faces" <|
    wAuthoredReport.unreplayable.isNone && wAuthoredReport.stmtErrors.isEmpty &&
      wAuthoredFaces.all fun name =>
        (declarationType? wAuthoredGenerated name).any (containsConst ``Eq.rec)
  state := state.check "authored transport family remains an exact checked model" <|
    (Check.check wAuthoredGenerated).all fun violation =>
      violation.familyOwner != `Wty || violation matches .modelNotBefore ..
  let treePrivateRoot := `Tree._model._impl
  let treeOneLayerCertificate := #[Name.str treePrivateRoot "self",
    Name.str treePrivateRoot "ctor_0", Name.str treePrivateRoot "rec",
    Name.str treePrivateRoot "rec_iota_0", Name.str treePrivateRoot "roll",
    Name.str treePrivateRoot "unroll", Name.str treePrivateRoot "unroll_roll",
    Name.str treePrivateRoot "roll_unroll"]
  state := state.check "multi-constructor and multi-recursive Tree stays outside phase one" <|
    treeOneLayerCertificate.all fun name => !wNames.contains name
  let missingOneLayerLaw := Check.check <|
    withoutDeclaration wGenerated (Name.str wtyPrivateRoot "roll_unroll")
  state := state.check "partial one-layer certificate is rejected, not treated as legacy" <|
    missingOneLayerLaw.any
      (hasTypeViolation `Wty (Name.str wtyPrivateRoot "roll_unroll"))
  let malformedOneLayerMap := Check.check <|
    replaceDeclarationType wGenerated (Name.str wtyPrivateRoot "roll")
      (.sort (.succ .zero))
  state := state.check "malformed one-layer map is rejected structurally" <|
    malformedOneLayerMap.any (hasTypeViolation `Wty (Name.str wtyPrivateRoot "roll"))
  let noOneLayerCertificate := wtyCertificate.foldl withoutDeclaration wGenerated
  state := state.check "literal recursive rules require the complete certificate" <|
    (Check.check noOneLayerCertificate).any (hasTypeViolation `Wty wtyRule1)

  -- The next production tranche folds the same private/public compatibility
  -- proof once per recursive constructor field.  These owners differ only in
  -- the recursive suffix: direct/direct, direct/infinitary,
  -- infinitary/infinitary, and an ordinary dependent prefix followed by two
  -- direct fields.  Every public proposition remains the literal name-only
  -- source rewrite; transports are confined to proof values.
  let multiFieldOwners : Array (Name × Nat) :=
    #[(`Twin, 2), (`Mixed, 3), (`TwinInf, 2), (`Prefix, 4)]
  for (owner, fieldCount) in multiFieldOwners do
    let privateRoot := Name.str (Naming.modelName owner) "_impl"
    let certificate := #[Name.str privateRoot "self", Name.str privateRoot "ctor_0",
      Name.str privateRoot "rec", Name.str privateRoot "rec_iota_0",
      Name.str privateRoot "roll", Name.str privateRoot "unroll",
      Name.str privateRoot "unroll_roll", Name.str privateRoot "roll_unroll"]
    let publicFaces := #[Naming.modelName owner, Naming.modelName (Name.str owner "mk"),
      Naming.modelName (Name.str owner "rec"), Naming.iotaName (Name.str owner "rec") 0] ++
      (Array.range fieldCount).flatMap fun index =>
        #[Naming.projectionName owner index, Naming.projectionIotaName owner index]
    state := state.check s!"{owner} carries the complete multi-field one-layer certificate" <|
      certificate.all wNames.contains
    state := state.check s!"{owner} public family is exact and generated" <|
      wReport.generated.any (fun row => row.1 == owner) &&
        !wReport.declined.any (fun row => row.1 == owner) &&
        (Check.check wGenerated).all (fun violation =>
          violation.familyOwner != owner || violation matches .modelNotBefore ..)
    state := state.check s!"{owner} public statements introduce no Eq.rec" <|
      publicFaces.all fun name =>
        (declarationType? wGenerated name).any fun type => !containsConst ``Eq.rec type
    state := state.check s!"{owner} projection iotas retain literal field RHS" <|
      (Array.range fieldCount).all fun index =>
        (declarationType? wGenerated (Naming.projectionIotaName owner index)).any fun type =>
          !containsConst ``Eq.rec type

  let twinAuthoredRaw := mapRecursorSyntax wRaw `TwinInf.rec authoredOuterSortTransport
  let (twinAuthoredDeclarations, twinAuthoredReport) ← runExport twinAuthoredRaw
  let twinAuthoredGenerated := outputExport twinAuthoredRaw twinAuthoredDeclarations
  state := state.check "multi-field source-authored Eq.rec is preserved" <|
    twinAuthoredReport.unreplayable.isNone && twinAuthoredReport.stmtErrors.isEmpty &&
      #[Naming.modelName `TwinInf.rec, Naming.iotaName `TwinInf.rec 0,
        `TwinInf._model._impl.rec, `TwinInf._model._impl.rec_iota_0].all fun name =>
        (declarationType? twinAuthoredGenerated name).any (containsConst ``Eq.rec)
  let tripleCertificateRoot := `Triple._model._impl
  let tripleCertificate := #[Name.str tripleCertificateRoot "self",
    Name.str tripleCertificateRoot "ctor_0", Name.str tripleCertificateRoot "rec",
    Name.str tripleCertificateRoot "rec_iota_0", Name.str tripleCertificateRoot "roll",
    Name.str tripleCertificateRoot "unroll", Name.str tripleCertificateRoot "unroll_roll",
    Name.str tripleCertificateRoot "roll_unroll"]
  state := state.check "three recursive fields remain on the legacy route" <|
    wReport.generated.any (·.1 == `Triple) && tripleCertificate.all fun name => !wNames.contains name

  let (wrapperDeclarations, wrapperReport) ← runExport wrapperRaw
  let wrapperGenerated := outputExport wrapperRaw wrapperDeclarations
  let wrapperNames := wrapperDeclarations.flatMap (·.names.toArray)
  state := state.check "incidental exported wrappers do not change intrinsic types" <|
    wrapperReport.stmtErrors.isEmpty && projectionNames.all fun name =>
      declarationType? wrapperGenerated name == declarationType? generated name
  state := state.check "incidental wrappers receive no legacy model declarations" <|
    #[`Dep.key._model, `Dep.payload._model, `Dep.witness._model].all fun name =>
      !wrapperNames.contains name

  state := state.check "intrinsic fields need no exported projection wrappers" <|
    #[`Dep.key, `Dep.payload, `Dep.witness].all fun name =>
      (declarationIndex? raw name).isNone
  state := state.check "dependent structure generated" <|
    report.generated.any (·.1 == `Dep) && report.stmtErrors.isEmpty
  state := state.check "exact projection definitions and rules emitted" <|
    projectionNames.all names.contains && projectionRules.all names.contains
  state := state.check "nonrecursive dependent projection iotas are all literal" <|
    #[keyRule, payloadRule, witnessRule].all fun rule =>
      (declarationType? generated rule).any (fun type => !containsConst ``Eq.rec type)
  state := state.check "nonrecursive dependent projection iotas are reflexivity proofs" <|
    #[keyRule, payloadRule, witnessRule].all fun rule =>
      (theoremValue? generated rule).any (containsConst ``Eq.refl)

  let modelsBeforeOwner := match declarationIndex? generated `Dep with
    | none => false
    | some owner => (projectionNames ++ projectionRules).all fun name =>
        (declarationIndex? generated name).any (· < owner)
  state := state.check "intrinsic projection interface precedes owner"
    modelsBeforeOwner

  state := state.check "projection definitions eliminate with the model recursor" <|
    projectionNames.all fun name =>
      (definitionValue? generated name).any fun value =>
        containsConst (Naming.modelName `Dep.rec) value && !containsProjection value
  state := state.check "payload type uses the preceding projection model literally" <|
    (declarationType? generated payloadModel).any fun type =>
      containsConst keyModel type
  state := state.check "witness type uses both preceding projection models literally" <|
    (declarationType? generated witnessModel).any fun type =>
      containsConst keyModel type && containsConst payloadModel type &&
        !containsConst `Dep.key type && !containsConst `Dep.payload type
  state := state.check "format-only checker accepts generated projection family" <|
    Check.check generated |>.all (·.familyOwner != `Dep)
  state := state.check "projection universe inference covers sorts, functions, lets and dependencies" <|
    sortFieldProjections.all names.contains &&
      (Check.check generated |>.all (·.familyOwner != `SortFields))

  let wcore ← readExport "test/fixtures/inductive-models/w_core.ndjson"
  state := state.check "Prop-valued Iff exposes its two proof fields" <|
    intrinsicFieldsFor wcore `Iff == #[0, 1]
  state := state.check "Prop-valued Nonempty cannot expose its data field" <|
    (intrinsicFieldsFor wcore `Nonempty).isEmpty
  let indexedProjections := (Array.range 1).flatMap fun fieldIndex =>
    #[Naming.projectionName `Indexed fieldIndex,
      Naming.projectionIotaName `Indexed fieldIndex]
  let indexedDepProjections := (Array.range 2).flatMap fun fieldIndex =>
    #[Naming.projectionName `IndexedDep fieldIndex,
      Naming.projectionIotaName `IndexedDep fieldIndex]
  let recursiveProjections := (Array.range 2).flatMap fun fieldIndex =>
    #[Naming.projectionName `Recursive fieldIndex,
      Naming.projectionIotaName `Recursive fieldIndex]
  state := state.check "indexed one-constructor fields are intrinsic projections" <|
    intrinsicFieldsFor raw `Indexed == #[0] && indexedProjections.all names.contains &&
      (Check.check generated).all (·.familyOwner != `Indexed)
  state := state.check "dependent indexed fibre uses literal projection rules" <|
    intrinsicFieldsFor raw `IndexedDep == #[0, 1] &&
      indexedDepProjections.all names.contains &&
      (declarationType? generated (Naming.projectionIotaName `IndexedDep 0)).any
        (!containsConst ``Eq.rec ·) &&
      (declarationType? generated (Naming.projectionIotaName `IndexedDep 1)).any
        (!containsConst ``Eq.rec ·) &&
      (Check.check generated).all (·.familyOwner != `IndexedDep)
  state := state.check "recursive one-constructor fields are intrinsic projections" <|
    intrinsicFieldsFor raw `Recursive == #[0, 1] && recursiveProjections.all names.contains &&
      (Check.check generated).all (·.familyOwner != `Recursive)
  state := state.check "legacy generated recursive skeleton remains on its legacy contract" <|
    !#[`Recursive._model._impl.self, `Recursive._model._impl.ctor_0,
        `Recursive._model._impl.rec, `Recursive._model._impl.rec_iota_0].any names.contains
  state := state.check "recursive projections retain the recursor fallback" <|
    (Array.range 2).all fun fieldIndex =>
      (definitionValue? generated (Naming.projectionName `Recursive fieldIndex)).any
        (containsConst (Naming.modelName `Recursive.rec))

  let directRecursiveRaw ← readExport "test/fixtures/inductive-models/unitlike.ndjson"
  let (directRecursiveDeclarations, directRecursiveReport) ← runExport directRecursiveRaw
  let directRecursiveGenerated := outputExport directRecursiveRaw directRecursiveDeclarations
  let directRecursiveRule := Naming.projectionIotaName `Recursive 0
  state := state.check "direct recursive one-layer projection rule is literal" <|
    directRecursiveReport.generated.any (·.1 == `Recursive) &&
      directRecursiveReport.stmtErrors.isEmpty &&
      (declarationType? directRecursiveGenerated directRecursiveRule).any fun type =>
        !containsConst ``Eq.rec type
  state := state.check "Prop dependency and multi-constructor fields are excluded" <|
    (intrinsicFieldsFor raw `PropDependent).isEmpty &&
      (intrinsicFieldsFor raw `Multi).isEmpty &&
      !names.contains (Naming.projectionName `PropDependent 0) &&
      !names.contains (Naming.projectionName `Multi 0)
  let extraIndexed := Naming.projectionName `Indexed 2
  let extraViolations := Check.check (insertCollision generated extraIndexed)
  state := state.check "checker rejects an out-of-range intrinsic projection slot" <|
    extraViolations.any (hasExtraProjectionViolation `Indexed extraIndexed)
  state := state.check "projection route choice emits no public marker" <|
    declarations.all fun declaration =>
      !(declarationNames declaration).contains `InductiveModels.projectionIotaUsesLiteralField

  let missingModel := Check.check (withoutDeclaration generated payloadModel)
  state := state.check "checker rejects a missing projection definition" <|
    missingModel.any (hasMissingViolation `Dep payloadModel)
  let missingRule := Check.check (withoutDeclaration generated witnessRule)
  state := state.check "checker rejects a missing projection rule" <|
    missingRule.any (hasMissingViolation `Dep witnessRule)
  let axiomProjection := Check.check <|
    replaceImplementationWithAxiom generated payloadModel
  state := state.check "checker requires a projection implementation definition" <|
    axiomProjection.any
      (hasKindViolation `Dep payloadModel .defn .axiom)
  let unsafeProjection := Check.check <|
    replaceDefinitionSafety generated payloadModel "unsafe"
  state := state.check "checker requires a safe projection implementation" <|
    unsafeProjection.any (hasSafetyViolation `Dep payloadModel "unsafe")
  let definitionRule := Check.check <|
    replaceTheoremWithDefinition generated payloadRule
  state := state.check "checker requires a projection iota theorem" <|
    definitionRule.any
      (hasKindViolation `Dep payloadRule .thm .defn)
  let badModelType := Check.check <|
    replaceDeclarationType generated payloadModel (.sort (.succ .zero))
  state := state.check "checker compares projection types syntactically" <|
    badModelType.any (hasTypeViolation `Dep payloadModel)
  let badRuleType := Check.check <|
    replaceDeclarationType generated keyRule (.sort (.succ .zero))
  state := state.check "checker compares projection iota statements syntactically" <|
    badRuleType.any (hasTypeViolation `Dep keyRule)
  let raisedEqExport := (declarationType? generated keyRule).bind raiseOuterEqLevel?
    |>.map (replaceDeclarationType generated keyRule ·) |>.getD generated
  let raisedEqViolations := Check.check raisedEqExport
  state := state.check "checker rejects a projection iota with only Eq's universe raised" <|
    raisedEqViolations.any (hasTypeViolation `Dep keyRule)
  let (_, raisedEqReplay) ← runExport raisedEqExport
  state := state.check "raised-Eq projection theorem remains kernel-valid" <|
    raisedEqReplay.unreplayable.isNone

  let roleTable := ModelRoles.table generated
  state := state.check "projection definitions are keyed to the owner record" <|
    (roleTable[payloadModel]?).any fun entry =>
      entry.owner == `Dep && entry.role == .projection
  state := state.check "projection rules are keyed without an eliminating universe" <|
    (roleTable[payloadRule]?).any fun entry =>
      entry.owner == `Dep && entry.role == .projectionIota

  -- A real collision retry requires both spellings in the flattened export.
  -- Manufacture the second module's block using the same explicit whole-name
  -- substitution used by serialization.
  let privateDep := (`_private.ProjectionTest).mkNum 0 |>.str "Dep"
  let sourceNames := raw.decls.flatMap (fun declaration => declaration.names.toArray)
    |>.filter fun name => (`Dep).isPrefixOf name
  let privateAliases := sourceNames.foldl (init := Naming.AliasMap.empty)
    fun aliases name => aliases.insert name (name.replacePrefix `Dep privateDep)
  let privateRecords := raw.decls.map (·.renameAliases privateAliases)
  let privateRaw := { raw with decls := privateRecords }
  let (privateDecls, privateReport) ← runExport privateRaw
  let privateNames := privateDecls.flatMap (·.names.toArray)
  state := state.check "raw private structure gets intrinsic projection names exactly" <|
    privateReport.generated.any (·.1 == privateDep) &&
      privateNames.contains (Naming.projectionName privateDep 1) &&
      privateNames.contains (Naming.projectionIotaName privateDep 1)
  let leakedAliases := privateDecls.flatMap declarationNames |>.filter fun name =>
    name.components.any (· == `_inductive_models_alias)
  state := state.check "projection retry aliases do not leak into serialized records" <|
    leakedAliases.isEmpty

  let (_, collisionReport) ← runExport (insertCollision raw keyModel)
  state := state.check "an exact projection model collision withdraws the owner atomically" <|
    !collisionReport.generated.any (·.1 == `Dep) &&
      collisionReport.declined.any fun (owner, reason) =>
        owner == `Dep && reason == s!"prim model name taken ({keyModel})"
  let (legacyDecls, legacyReport) ← runExport
    (insertCollision raw `Dep.key._model)
  state := state.check "a legacy wrapper-shaped name is irrelevant" <|
    legacyReport.generated.any (·.1 == `Dep) &&
      legacyDecls.any (·.names.contains payloadModel)

  let mutualWrapperRaw ← readExport "test/fixtures/inductive-models/mutual_structure_projections.ndjson"
  let mutualRawOriginal := #[`MLeft.value, `MRight.key, `MRight.payload,
    `leftValue, `rightPayload].foldl withoutDeclaration mutualWrapperRaw
  let (mutualRawDecls, mutualRawReport) ← runExport mutualRawOriginal
  let mutualRaw ← withCompletePrerequisiteBefore mutualRawOriginal `PUnit `MLeft
  let (mutualDecls, mutualReport) ← runExport mutualRaw
  let mutualGenerated := outputExport mutualRaw mutualDecls
  let mutualNames := mutualDecls.flatMap (·.names.toArray)
  let leftProjection := Naming.projectionName `MLeft 0
  let leftRule := Naming.projectionIotaName `MLeft 0
  let rightKeyProjection := Naming.projectionName `MRight 0
  let rightPayloadProjection := Naming.projectionName `MRight 1
  let rightPayloadRule := Naming.projectionIotaName `MRight 1
  state := state.check "mutual projection fixture declares PUnit after its owner" <|
    (declarationIndex? mutualRawOriginal `MLeft).any fun owner =>
      (declarationIndex? mutualRawOriginal `PUnit).any (owner < ·)
  state := state.check "raw-order mutual owner declines before PUnit without a partial model" <|
    mutualRawReport.declined ==
      #[(`MLeft, "mutual model prerequisite occurs later in the input stream")] &&
      noModeledBlockDescendants mutualRawOriginal mutualRawDecls `MLeft
  unless mutualReport.generated.any (·.1 == `MLeft) do
    IO.eprintln s!"mutual projection generation declined: {mutualReport.declined}"
    for error in mutualReport.stmtErrors do
      IO.eprintln s!"mutual projection statement error: {error}"
    for declaration in mutualRaw.decls do
      if let .induct _ _ recursors := declaration then
        for recursor in recursors do
          if recursor.all.contains `MLeft then
            IO.eprintln s!"source recursor {recursor.name}: motives {recursor.all}, rules {recursor.rules.map (·.ctor)}"
  state := state.check "mutual fields need no exported projection wrappers" <|
    #[`MLeft.value, `MRight.key, `MRight.payload].all fun name =>
      (declarationIndex? mutualRaw name).isNone
  state := state.check "plain mutual route emits each member's projection interface" <|
    mutualReport.generated.any (·.1 == `MLeft) && mutualReport.stmtErrors.isEmpty &&
      #[leftProjection, leftRule, rightKeyProjection, rightPayloadProjection,
        rightPayloadRule].all mutualNames.contains
  state := state.check "mutual dependent projection type uses its preceding model" <|
    (declarationType? mutualGenerated rightPayloadProjection).any fun type =>
      containsConst rightKeyProjection type
  state := state.check "nonrecursive mutual dependent projection iota is literal" <|
    (declarationType? mutualGenerated rightPayloadRule).any fun type =>
      !containsConst ``Eq.rec type
  state := state.check "mutual projection models precede their modeled block" <|
    (declarationIndex? mutualGenerated `MLeft).any fun owner =>
      #[leftProjection, leftRule, rightKeyProjection, rightPayloadProjection,
        rightPayloadRule].all fun name =>
          (declarationIndex? mutualGenerated name).any (· < owner)
  state := state.check "checker accepts mutual projection interfaces per member" <|
    Check.check mutualGenerated |>.all fun violation =>
      violation.familyOwner != `MLeft && violation.familyOwner != `MRight
  let mutualRoles := ModelRoles.table mutualGenerated
  state := state.check "a later member's projection is attached to the mutual owner record" <|
    (mutualRoles[rightPayloadProjection]?).any fun entry =>
      entry.owner == `MLeft && entry.role == .projection

  IO.println s!"structure projections: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  unless state.failed.isEmpty do
    IO.eprintln s!"projection declines: {report.declined}"
    for error in report.stmtErrors do IO.eprintln s!"projection statement error: {error}"
    for error in wrapperReport.stmtErrors do IO.eprintln s!"wrapper statement error: {error}"
    for error in mutualReport.stmtErrors do IO.eprintln s!"mutual statement error: {error}"
    for name in projectionNames do
      IO.eprintln s!"wrapper type equal {name}: {declarationType? wrapperGenerated name == declarationType? generated name}"
    IO.eprintln s!"Indexed fields: {intrinsicFieldsFor raw `Indexed}"
    IO.eprintln s!"Recursive fields: {intrinsicFieldsFor raw `Recursive}"
    IO.eprintln s!"generated owners: {report.generated}"
    for name in recursiveProjections do
      IO.eprintln s!"recursive slot {name}: {names.contains name}"
    IO.eprintln s!"Iff fields: {intrinsicFieldsFor wcore `Iff}"
    if let some type := wtyShape then
      IO.eprintln s!"Wty source shape: all={type.all}, ctors={type.ctors}, indices={type.numIndices}, nested={type.numNested}, rec={type.isRec}, unsafe={type.isUnsafe}, reflexive={type.isReflexive}"
    for violation in Check.check generated do
      if #[`Dep, `SortFields, `Indexed, `Recursive].contains violation.familyOwner then
        IO.eprintln s!"projection check violation: {repr violation}"
    for violation in Check.check mutualGenerated do
      if #[`MLeft, `MRight].contains violation.familyOwner then
        IO.eprintln s!"mutual projection check violation: {repr violation}"
    for violation in Check.check wGenerated do
      if violation.familyOwner == `Wty then
        IO.eprintln s!"Wty projection check violation: {repr violation}"
  return if state.failed.isEmpty then 0 else 1
