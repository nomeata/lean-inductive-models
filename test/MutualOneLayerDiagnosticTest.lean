import InductiveModels.Driver
import InductiveModels.Check
import InductiveModels.Order

/-!
# Plain-mutual partial one-layer diagnostic

This is deliberately not a correctness target. It records the exact public
surface already produced for a two-member recursive SCC, then leaves two red
expectations for the next adapter: the source-exact projection-iota telescope
and a complete private/public family certificate. The legacy mutual route's
literal RHS and multi-constructor sibling remain controls rather than being
reinterpreted as failures.
-/

open Lean Meta InductiveModels

set_option maxRecDepth 2048

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

structure OpenBinder where
  name : Name
  type : Expr
  info : BinderInfo
  value : Expr
  deriving Inhabited

partial def openForalls (tag : Name) (expression : Expr) : Array OpenBinder × Expr :=
  let rec loop (expression : Expr) (binders : Array OpenBinder) :=
    match expression with
    | .forallE name type body info =>
      let value := mkFVar (FVarId.mk (tag.mkNum binders.size))
      loop (body.instantiate1 value) (binders.push { name, type, info, value })
    | body => (binders, body)
  loop expression #[]

def closeForalls (binders : Array OpenBinder) (body : Expr) : Expr :=
  binders.reverse.foldl (fun body binder =>
    .forallE binder.name binder.type (body.abstract #[binder.value]) binder.info) body

def instantiateForalls? (expression : Expr) (arguments : Array Expr) : Option Expr := Id.run do
  let mut expression := expression
  for argument in arguments do
    let .forallE _ _ body _ := expression | return none
    expression := body.instantiate1 argument
  return expression

def readExport (path : String) : IO Export := do
  let .ok parsed := InductiveModels.parse (← IO.FS.readFile path) (analyse := false)
    | throw <| IO.userError s!"cannot parse {path}"
  return parsed

def runExport (input : Export) : IO (Export × Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<mutual-one-layer-diagnostic>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let action : MetaM (Export × Report) := do
    let (declarations, report) ← runFilter input false
      { nested := true, mutualModels := true, simple := true, basic := true }
    let generated : Export := { input with decls := declarations }
    let ordered ← match Order.reorder generated with
      | .ok output => pure output
      | .error error => throwError "cannot order mutual diagnostic: {repr error}"
    return (ordered, report)
  return (← Core.CoreM.toIO (MetaM.run' action) context { env }).1

def declarationType? (x : Export) (name : Name) : Option (List Name × Expr) :=
  x.decls.findSome? fun declaration => match declaration with
    | .ax got params type _ | .quot got params type _ =>
      if got == name then some (params, type) else none
    | .defn got params type .. | .thm got params type .. | .opaq got params type .. =>
      if got == name then some (params, type) else none
    | .induct types constructors recursors =>
      (types.find? (·.name == name)).map (fun type => (type.levelParams, type.type)) <|>
      (constructors.find? (·.name == name)).map (fun ctor => (ctor.levelParams, ctor.type)) <|>
      (recursors.find? (·.name == name)).map (fun rec => (rec.levelParams, rec.type))

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

partial def containsConst (target : Name) : Expr -> Bool
  | .const name _ => name == target
  | .proj _ _ subject => containsConst target subject
  | .app fn argument => containsConst target fn || containsConst target argument
  | .lam _ type body _ | .forallE _ type body _ =>
    containsConst target type || containsConst target body
  | .letE _ type value body _ =>
    containsConst target type || containsConst target value || containsConst target body
  | .mdata _ body => containsConst target body
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => false

partial def equalityRhs? : Expr -> Option (Level × Expr × Expr × Expr)
  | .forallE _ _ body _ => equalityRhs? body
  | body => do
    let .const ``Eq [level] := body.getAppFn | none
    let #[alpha, lhs, rhs] := body.getAppArgs | none
    return (level, alpha, lhs, rhs)

def identityTransport (level : Level) (alpha value : Expr) : Expr :=
  let motive := Expr.lam `target alpha
    (Expr.lam `equality
      (mkAppN (.const ``Eq [level]) #[alpha, value, .bvar 0]) alpha .default) .default
  let equality := mkAppN (.const ``Eq.refl [level]) #[alpha, value]
  mkAppN (.const ``Eq.rec [level, level])
    #[alpha, value, motive, value, value, equality]

partial def transportOuterEqualityRhs? : Expr -> Option Expr
  | .forallE name domain body info =>
    return .forallE name domain (← transportOuterEqualityRhs? body) info
  | body => do
    let (level, alpha, lhs, rhs) ← equalityRhs? body
    return mkAppN (.const ``Eq [level]) #[alpha, lhs, identityTransport level alpha rhs]

def hasTypeViolation (owner declaration : Name) : Check.Violation -> Bool
  | .declarationType gotOwner gotDeclaration =>
    gotOwner == owner && gotDeclaration == declaration
  | _ => false

def sourceBlock? (x : Export) (owner : Name) : Option (List EIndType × List ECtor × List ERec) :=
  x.decls.findSome? fun declaration => match declaration with
    | .induct types constructors recursors =>
      if types.any (·.name == owner) then some (types, constructors, recursors) else none
    | _ => none

/-- Exact source-name projection faces, reconstructed from the raw constructor
telescope. This is intentionally stricter than opening an installed telescope:
the payload binder retains its source head beta-redex. -/
def exactProjectionFaces (x : Export) (family : Check.Family) (ownerType : EIndType)
    (constructor : ECtor) (modelParams : List Name) : Array (Name × Expr) := Id.run do
  let mappedConstructorType := family.correspondence.expectedType
    constructor.levelParams modelParams constructor.type
  let (constructorBinders, constructorResult) := openForalls
    `_diagnostic.mutualOneLayerCtor mappedConstructorType
  let mappedOwnerType := family.correspondence.expectedType
    ownerType.levelParams modelParams ownerType.type
  let (ownerBinders, _) := openForalls `_diagnostic.mutualOneLayerOwner mappedOwnerType
  let ownerArgs := ownerBinders.map (·.value)
  let ownerParams := ownerArgs.extract 0 ownerType.numParams
  let some fieldsType := instantiateForalls? mappedConstructorType ownerParams | return #[]
  let (fieldBinders, _) := openForalls `_diagnostic.mutualOneLayerFields fieldsType
  let constructorArgs := constructorBinders.map (·.value)
  let params := constructorArgs.extract 0 constructor.numParams
  let fields := constructorBinders.extract constructor.numParams constructorBinders.size
  let levels := modelParams.map Level.param
  let some typePair := family.correspondence.typeFormers.find? (·.owner == ownerType.name)
    | return #[]
  let some constructorPair := family.correspondence.constructors.find?
      (·.owner == constructor.name) | return #[]
  let major := mkAppN (.const constructorPair.model levels) constructorArgs
  let ownerArity := ownerType.numParams + ownerType.numIndices
  let indices := constructorResult.getAppArgs.extract constructor.numParams ownerArity
  let selfValue := mkFVar (FVarId.mk `_diagnostic.mutualOneLayerSelf)
  let selfBinder : OpenBinder :=
    { name := `self, type := mkAppN (.const typePair.model levels) ownerArgs,
      info := .default, value := selfValue }
  let mut result := #[]
  for projection in family.correspondence.projections do
    if projection.owner == ownerType.name then
      let some selected := fieldBinders[projection.fieldIndex]? | return #[]
      let mut projectionResult := selected.type
      for earlier in [:projection.fieldIndex] do
        projectionResult := projectionResult.replace fun subexpression =>
          if subexpression == fieldBinders[earlier]!.value then
            some <| mkAppN
              (.const (Naming.projectionName ownerType.name earlier) levels)
              (ownerArgs.push selfValue)
          else none
      let projectionType := closeForalls (ownerBinders.push selfBinder) projectionResult
      result := result.push (projection.name, projectionType)
      let some alpha := instantiateForalls? projectionType (params ++ indices ++ #[major])
        | return #[]
      let lhs := mkAppN (.const projection.name levels) (params ++ indices ++ #[major])
      -- Reuse only the actual equality universe. The oracle below is about the
      -- exact source telescope and literal RHS, not duplicating sort inference.
      let some (_, actualRule) := declarationType? x projection.iota | return #[]
      let some (equalityLevel, _, _, _) := equalityRhs? actualRule | return #[]
      let ruleType := closeForalls constructorBinders <|
        mkAppN (.const ``Eq [equalityLevel])
          #[alpha, lhs, fields[projection.fieldIndex]!.value]
      result := result.push (projection.iota, ruleType)
  return result

def run (root : String) : IO UInt32 := do
  let input ← readExport
    s!"{root}/test/fixtures/inductive-models/mutual_one_layer_boundary.ndjson"
  let (generated, report) ← runExport input
  let some family := Check.discover generated |>.find? (·.owner == `MutualLayerA)
    | throw <| IO.userError "generated fixture has no MutualLayerA family"
  let some (types, constructors, recursors) := sourceBlock? input `MutualLayerA
    | throw <| IO.userError "fixture has no mutual source block"
  let some ownerType := types.find? (·.name == `MutualLayerA)
    | throw <| IO.userError "fixture has no MutualLayerA owner"
  let some siblingType := types.find? (·.name == `MutualLayerB)
    | throw <| IO.userError "fixture has no MutualLayerB owner"
  let some constructor := constructors.find? (·.name == `MutualLayerA.mk)
    | throw <| IO.userError "fixture has no MutualLayerA.mk"
  let some typePair := family.correspondence.typeFormers.find? (·.owner == `MutualLayerA)
    | throw <| IO.userError "MutualLayerA has no modeled carrier"
  let some (modelParams, _) := declarationType? generated typePair.model
    | throw <| IO.userError "MutualLayerA modeled carrier is absent"
  let exactFaces := exactProjectionFaces generated family ownerType constructor modelParams
  let expected := fun name => exactFaces.find? (·.1 == name) |>.map (·.2)
  let actual := fun name => declarationType? generated name |>.map (·.2)
  let keyProjection := Naming.projectionName `MutualLayerA 0
  let childProjection := Naming.projectionName `MutualLayerA 1
  let payloadProjection := Naming.projectionName `MutualLayerA 2
  let keyRule := Naming.projectionIotaName `MutualLayerA 0
  let childRule := Naming.projectionIotaName `MutualLayerA 1
  let payloadRule := Naming.projectionIotaName `MutualLayerA 2
  let siblingProjection := Naming.projectionName `MutualLayerB 0
  let siblingRule := Naming.projectionIotaName `MutualLayerB 0
  let generatedNames := generated.decls.flatMap (·.names.toArray)

  -- Proposed partial-family certificate. The family root is the first source
  -- owner, while each member retains an owner-keyed private carrier and maps.
  let familyImpl := `MutualLayerA._model._impl
  let memberImpl := fun owner => Name.str familyImpl (lastStr owner)
  let memberCertificate := fun owner =>
    let root := memberImpl owner
    #[Name.str root "self", Name.str root "roll", Name.str root "unroll",
      Name.str root "unroll_roll", Name.str root "roll_unroll"]
  let certificate := memberCertificate `MutualLayerA ++ memberCertificate `MutualLayerB

  let mut state : TestState := {}
  state := state.check "diagnostic reaches mutual generation and checking" <|
    report.generated.any (·.1 == `MutualLayerA) &&
      !report.declined.any (·.1 == `MutualLayerA) &&
      report.unreplayable.isNone && report.stmtErrors.isEmpty &&
      (Check.check generated).all fun violation =>
        !#[`MutualLayerA, `MutualLayerB].contains violation.familyOwner
  state := state.check "source is one unindexed recursive SCC keyed by owners" <|
    types.map (·.name) == [`MutualLayerA, `MutualLayerB] &&
      ownerType.all == [`MutualLayerA, `MutualLayerB] &&
      siblingType.all == ownerType.all && ownerType.numIndices == 0 &&
      siblingType.numIndices == 0 && ownerType.isRec && siblingType.isRec &&
      recursors.all fun recursor => recursor.all == ownerType.all
  state := state.check "one-constructor member exposes all exact projection slots" <|
    ownerType.ctors == [`MutualLayerA.mk] &&
      #[keyProjection, childProjection, payloadProjection,
        keyRule, childRule, payloadRule].all generatedNames.contains
  state := state.check "ordinary and recursive projection types are source-exact" <|
    actual keyProjection == expected keyProjection &&
      actual childProjection == expected childProjection &&
      actual payloadProjection == expected payloadProjection
  state := state.check "payload iota preserves source-authored Eq.rec syntax" <|
    containsConst ``Eq.rec constructor.type &&
      (actual payloadRule).any (containsConst ``Eq.rec)
  state := state.check "legacy mutual route keeps literal projection RHSs" <|
    #[keyRule, childRule, payloadRule].all fun rule =>
      (actual rule).any fun type =>
        (equalityRhs? type).any fun (_, _, _, rhs) => !containsConst ``Eq.rec rhs
  state := state.check "payload iota retains the exact source telescope" <|
    actual payloadRule == expected payloadRule
  state := state.check "partial mutual family carries complete owner-keyed certificate" <|
    certificate.all generatedNames.contains

  let transportedCandidate := (actual payloadRule).bind transportOuterEqualityRhs?
    |>.map (replaceDeclarationType generated payloadRule ·) |>.getD generated
  state := state.check "checker rejects the old transported payload RHS" <|
    (Check.check transportedCandidate).any
      (hasTypeViolation `MutualLayerA payloadRule)
  state := state.check "multi-constructor sibling stays projection-free and public" <|
    siblingType.ctors.length == 2 &&
      !generatedNames.contains siblingProjection && !generatedNames.contains siblingRule &&
      #[Naming.modelName `MutualLayerB, Naming.modelName `MutualLayerB.stop,
        Naming.modelName `MutualLayerB.back, Naming.modelName `MutualLayerB.rec,
        Naming.iotaName `MutualLayerB.rec 0, Naming.iotaName `MutualLayerB.rec 1].all
          generatedNames.contains

  IO.println s!"mutual one-layer diagnostic: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1

def main (args : List String) : IO UInt32 :=
  run (args.head?.getD ".")
