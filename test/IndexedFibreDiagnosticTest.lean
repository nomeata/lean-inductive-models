import InductiveModels.Driver
import InductiveModels.Check
import InductiveModels.Order

/-!
# Indexed one-layer fibre diagnostic

`IndexedDep` is the first production indexed fibre: a minimal one-constructor
indexed `Type` with an ordinary dependent field.  Its public statements retain
the exact source-name rewrite, while a complete private/public certificate
authorizes the literal dependent projection rule.

The final guarded declaration pins the source boundary separately: Lean does
not admit a result index which mentions a recursive constructor field, even
when a reducible function erases the apparent dependency.  The adapter must
not manufacture semantics beyond that kernel-accepted boundary.
-/

open Lean Meta InductiveModels

set_option maxRecDepth 2048

namespace IndexedFibreRejectedBoundary

inductive Ix where
  | here
  | elsewhere

def erasedResultIndex {alpha : Sort u} (_ : alpha) : Ix :=
  Ix.here

/--
error: (kernel) invalid return type for 'IndexedFibreRejectedBoundary.MovedRecursiveResult.mk'
-/
#guard_msgs in
inductive MovedRecursiveResult : Ix -> Type where
  | mk (child : MovedRecursiveResult Ix.here) :
      MovedRecursiveResult (erasedResultIndex child)

end IndexedFibreRejectedBoundary

namespace IndexedFibreLaterDependencyBoundary

inductive Ix where
  | here

axiom Witness {alpha : Type u} (_ : alpha) : Type u

/--
error: (kernel) arg #2 of 'IndexedFibreLaterDependencyBoundary.LaterDependency.mk' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
inductive LaterDependency : Ix -> Type where
  | mk (child : LaterDependency Ix.here) (evidence : Witness child) :
      LaterDependency Ix.here

end IndexedFibreLaterDependencyBoundary

namespace IndexedFibreDiagnosticTest

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
  let .ok parsed := InductiveModels.parse (← IO.FS.readFile path)
    | throw <| IO.userError s!"cannot parse {path}"
  return parsed

def runExport (input : Export) : IO (Export × Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<indexed-fibre-diagnostic>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let action : MetaM (Export × Report) := do
    let (declarations, report) ← runFilter input false
      { nested := true, mutualModels := true, simple := true, basic := true }
    let generated : Export := { input with decls := declarations }
    let ordered ← match Order.reorder generated with
      | .ok output => pure output
      | .error error => throwError "cannot order indexed diagnostic: {repr error}"
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

def withoutDeclaration (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.filterMap fun declaration => match declaration with
    | .ax got .. | .defn got .. | .thm got .. | .opaq got .. | .quot got .. =>
      if got == name then none else some declaration
    | .induct types constructors recursors =>
      let types := types.filter (·.name != name)
      let constructors := constructors.filter (·.name != name)
      let recursors := recursors.filter (·.name != name)
      if types.isEmpty && constructors.isEmpty && recursors.isEmpty then none
      else some (.induct types constructors recursors) }

def insertCollision (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.push (.ax name [] (.sort (.succ .zero)) false) }

def replaceRuleFieldCount (x : Export) (owner : Name) (nfields : Nat) : Export :=
  { x with decls := x.decls.map fun declaration => match declaration with
    | .induct types constructors recursors =>
      .induct types constructors <| recursors.map fun recursor =>
        if recursor.all.contains owner then
          { recursor with rules := recursor.rules.map fun rule => { rule with nfields } }
        else recursor
    | _ => declaration }

def replaceConstructorType (x : Export) (name : Name) (type : Expr) : Export :=
  { x with decls := x.decls.map fun declaration => match declaration with
    | .induct types constructors recursors =>
      .induct types (constructors.map fun constructor =>
        if constructor.name == name then { constructor with type } else constructor) recursors
    | _ => declaration }

def recursiveLaterDependencyType? (constructor : ECtor) : Option Expr := do
  let (binders, result) := openForalls `_test.recursiveLaterDependency constructor.type
  let recursiveIndex := constructor.numParams + 2
  let laterIndex := constructor.numParams + 3
  let recursive ← binders[recursiveIndex]?
  let later ← binders[laterIndex]?
  let witness := mkAppN (.const `RecursiveWitness [.zero])
    #[recursive.type, recursive.value]
  let binders := binders.set! laterIndex { later with type := witness }
  return closeForalls binders result

def twoRecursiveIndexDependencyType? (constructor : ECtor) : Option Expr := do
  let (binders, result) := openForalls `_test.twoRecursiveIndexDependency constructor.type
  let keyIndex := constructor.numParams
  let rightIndex := constructor.numParams + 3
  let key ← binders[keyIndex]?
  let right ← binders[rightIndex]?
  let index := mkAppN (.const `erasedResultIndex [.succ .zero]) #[key.type, key.value]
  let recursiveType := mkApp (.const `TwoRecursiveDependentResults []) index
  let binders := binders.set! rightIndex { right with type := recursiveType }
  return closeForalls binders result

def twoRecursiveLaterDependencyType? (constructor : ECtor)
    (recursiveOffset : Nat) : Option Expr := do
  let (binders, result) := openForalls `_test.twoRecursiveLaterDependency constructor.type
  let recursiveIndex := constructor.numParams + 2 + recursiveOffset
  let laterIndex := constructor.numParams + 4
  let recursive ← binders[recursiveIndex]?
  let later ← binders[laterIndex]?
  -- Deliberately malformed as a kernel type: the structural checker must
  -- reject the dependency from source syntax itself, without an enclosing
  -- constant whose implicit type argument would trigger the earlier
  -- non-bare-occurrence guard instead.
  let binders := binders.set! laterIndex { later with type := recursive.value }
  return closeForalls binders result

def declarationValue? (x : Export) (name : Name) : Option Expr :=
  x.decls.findSome? fun declaration => match declaration with
    | .defn got _ _ value .. | .thm got _ _ value .. | .opaq got _ _ value .. =>
      if got == name then some value else none
    | _ => none

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

partial def equalityLevel? : Expr -> Option Level
  | .forallE _ _ body _ => equalityLevel? body
  | body => match body.getAppFn with
    | .const ``Eq [level] => some level
    | _ => none

/-- A definitionally trivial, deliberately nonliteral equality RHS.  It is
used only to keep the rejection oracle live after the generator starts
emitting the desired literal rule. -/
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
    let .const ``Eq [level] := body.getAppFn | none
    let #[alpha, lhs, rhs] := body.getAppArgs | none
    some <| mkAppN (.const ``Eq [level]) #[alpha, lhs, identityTransport level alpha rhs]

def hasTypeViolation (owner declaration : Name) : Check.Violation -> Bool
  | .declarationType gotOwner gotDeclaration =>
    gotOwner == owner && gotDeclaration == declaration
  | _ => false

def projectionExpectations (x : Export) (family : Check.Family)
    (ownerType : EIndType) (constructor : ECtor)
    (modelParams : List Name) : MetaM (Array (Name × Expr)) := do
  let mappedConstructorType := family.correspondence.expectedType
    constructor.levelParams modelParams constructor.type
  let (constructorBinders, constructorResult) := openForalls
    `_test.indexedFibreCtor mappedConstructorType
  let mappedOwnerType := family.correspondence.expectedType
    ownerType.levelParams modelParams ownerType.type
  let (ownerBinders, _) := openForalls `_test.indexedFibreOwner mappedOwnerType
  let ownerArgs := ownerBinders.map (·.value)
  let ownerArity := ownerType.numParams + ownerType.numIndices
  let ownerParams := ownerArgs.extract 0 ownerType.numParams
  let some fieldsType := instantiateForalls? mappedConstructorType ownerParams
    | throwError "cannot instantiate IndexedDep constructor parameters"
  let (fieldBinders, _) := openForalls `_test.indexedFibreFields fieldsType
  let fields := constructorBinders.extract constructor.numParams constructorBinders.size
  let constructorArgs := constructorBinders.map (·.value)
  let params := constructorArgs.extract 0 constructor.numParams
  let levels := modelParams.map Level.param
  let some typePair := family.correspondence.typeFormers.find? (·.owner == ownerType.name)
    | throwError "missing IndexedDep modeled owner"
  let some constructorPair := family.correspondence.constructors.find?
      (·.owner == constructor.name)
    | throwError "missing IndexedDep modeled constructor"
  let major := mkAppN (.const constructorPair.model levels) constructorArgs
  let indices := constructorResult.getAppArgs.extract constructor.numParams ownerArity
  let selfValue := mkFVar (FVarId.mk `_test.indexedFibreSelf)
  let selfBinder : OpenBinder :=
    { name := `self, type := mkAppN (.const typePair.model levels) ownerArgs,
      info := .default, value := selfValue }
  let mut result := #[]
  for projection in family.correspondence.projections do
    if projection.owner == ownerType.name then
      let some selected := fieldBinders[projection.fieldIndex]?
        | throwError "missing IndexedDep field {projection.fieldIndex}"
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
        | throwError "cannot instantiate IndexedDep projection {projection.fieldIndex}"
      let lhs := mkAppN (.const projection.name levels) (params ++ indices ++ #[major])
      let rhs := fields[projection.fieldIndex]!.value
      let some (_, actualRuleType) := declarationType? x projection.iota
        | throwError "missing IndexedDep projection rule {projection.iota}"
      let some eqLevel := equalityLevel? actualRuleType
        | throwError "IndexedDep projection rule {projection.iota} is not an equality"
      let expectedRule := closeForalls constructorBinders <|
        mkAppN (.const ``Eq [eqLevel]) #[alpha, lhs, rhs]
      result := result.push (projection.iota, expectedRule)
  return result

def sourceShape? (x : Export) (owner : Name) : Option (EIndType × ECtor × ERec) :=
  x.decls.findSome? fun declaration => match declaration with
    | .induct types constructors recursors => do
      let type ← types.find? (·.name == owner)
      let constructor ← constructors.find? (·.induct == owner)
      let recursor ← recursors.find? (·.all.contains owner)
      return (type, constructor, recursor)
    | _ => none

def recursiveResultIndependent (constructor : ECtor) : Bool :=
  let (binders, result) := openForalls `_test.fixedRecursiveResult constructor.type
  let fields := binders.extract constructor.numParams binders.size
  fields.all fun field =>
    !containsConst constructor.induct field.type || !result.containsFVar field.value.fvarId!

def run (root : String) : IO UInt32 := do
  let input ← readExport s!"{root}/test/fixtures/inductive-models/structure_projections.ndjson"
  let (generated, report) ← runExport input
  let some family := Check.discover generated |>.find? (·.owner == `IndexedDep)
    | throw <| IO.userError "generated fixture has no IndexedDep family"
  let some (ownerType, constructor, recursor) := sourceShape? generated `IndexedDep
    | throw <| IO.userError "generated fixture has no IndexedDep source shape"
  let some typePair := family.correspondence.typeFormers.find? (·.owner == `IndexedDep)
    | throw <| IO.userError "IndexedDep has no modeled carrier"
  let some ctorPair := family.correspondence.constructors.find? (·.owner == `IndexedDep.mk)
    | throw <| IO.userError "IndexedDep has no modeled constructor"
  let some recPair := family.correspondence.recursors.find? (·.owner == `IndexedDep.rec)
    | throw <| IO.userError "IndexedDep has no modeled recursor"
  let iotaName := Naming.iotaName `IndexedDep.rec 0
  let some iotaPair := family.correspondence.iotas.find? (·.name == iotaName)
    | throw <| IO.userError "IndexedDep has no modeled recursor iota"
  let some (typeParams, actualCarrier) := declarationType? generated typePair.model
    | throw <| IO.userError "IndexedDep modeled carrier is absent"
  let some (ctorParams, actualConstructor) := declarationType? generated ctorPair.model
    | throw <| IO.userError "IndexedDep modeled constructor is absent"
  let some (recParams, actualRecursor) := declarationType? generated recPair.model
    | throw <| IO.userError "IndexedDep modeled recursor is absent"
  let some (iotaParams, actualIota) := declarationType? generated iotaPair.name
    | throw <| IO.userError "IndexedDep modeled iota is absent"
  let some (_, sourceIota) := Check.iotaProposition? generated family.ownerDecl recursor.name 0
    | throw <| IO.userError "cannot reconstruct IndexedDep source iota"
  let expectedCarrier := family.correspondence.expectedType
    ownerType.levelParams typeParams ownerType.type
  let expectedConstructor := family.correspondence.expectedType
    constructor.levelParams ctorParams constructor.type
  let expectedRecursor := family.correspondence.expectedType
    recursor.levelParams recParams recursor.type
  let expectedIota := family.correspondence.expectedIotaType
    recursor.levelParams iotaParams sourceIota
  let projectionEnv ← importModules #[] {}
  let projectionContext : Core.Context :=
    { fileName := "<indexed-fibre-projection-oracle>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (projectionFaces, _) ← Core.CoreM.toIO
    (MetaM.run' (projectionExpectations generated family ownerType constructor typeParams))
    projectionContext { env := projectionEnv }

  let keyProjection := Naming.projectionName `IndexedDep 0
  let payloadProjection := Naming.projectionName `IndexedDep 1
  let keyRule := Naming.projectionIotaName `IndexedDep 0
  let payloadRule := Naming.projectionIotaName `IndexedDep 1
  let expectedProjection := fun name => projectionFaces.find? (·.1 == name) |>.map (·.2)
  let actual := fun name => declarationType? generated name |>.map (·.2)
  let privateRoot := `IndexedDep._model._impl
  let certificate := #[Name.str privateRoot "self", Name.str privateRoot "ctor_0",
    Name.str privateRoot "rec", Name.str privateRoot "rec_iota_0",
    Name.str privateRoot "roll", Name.str privateRoot "unroll",
    Name.str privateRoot "unroll_roll", Name.str privateRoot "roll_unroll"]
  let generatedNames := generated.decls.flatMap (·.names.toArray)

  let mut state : TestState := {}
  state := state.check "IndexedDep uses the exact public source names" <|
    typePair.model == Naming.modelName `IndexedDep &&
      ctorPair.model == Naming.modelName `IndexedDep.mk &&
      recPair.model == Naming.modelName `IndexedDep.rec &&
      iotaPair.name == Naming.iotaName `IndexedDep.rec 0 &&
      #[keyProjection, payloadProjection, keyRule, payloadRule].all generatedNames.contains
  state := state.check "indexed carrier is the exact source-name rewrite" <|
    actualCarrier == expectedCarrier
  state := state.check "indexed constructor is the exact source-name rewrite" <|
    actualConstructor == expectedConstructor
  state := state.check "indexed recursor is the exact source-name rewrite" <|
    actualRecursor == expectedRecursor
  state := state.check "indexed recursor iota is the exact source-name rewrite" <|
    actualIota == expectedIota
  state := state.check "indexed ordinary projection type is exact" <|
    actual keyProjection == expectedProjection keyProjection
  state := state.check "indexed dependent projection type is exact" <|
    actual payloadProjection == expectedProjection payloadProjection
  state := state.check "indexed ordinary projection iota has the literal field RHS" <|
    actual keyRule == expectedProjection keyRule
  state := state.check "indexed dependent projection iota has the literal field RHS" <|
    actual payloadRule == expectedProjection payloadRule
  state := state.check "indexed family carries the complete one-layer fibre certificate" <|
    certificate.all generatedNames.contains
  -- **The carrier is the direct route's stored fibre and no longer arm C's
  -- carve.**  Both write a `PSigma'` whose second component is an `Eq`; what
  -- separates them is what sits underneath.  Arm C splices the family's index
  -- erasure as an *inductive* and carves the family out of it through a
  -- `good` predicate, so its model owes a model for that skeleton too.  The
  -- direct indexed route stores the fields in the `PSigma'` tower — a
  -- definition, taken apart by primitive projections — and pairs it with one
  -- packed index equation, splicing nothing.  So the skeleton and its `good`
  -- must **not** be here, and their absence is asserted rather than left
  -- implied: it is the whole of what this route is cheaper by.
  state := state.check "indexed public carrier is the direct route's stored fibre" <|
    (declarationValue? generated typePair.model).any
        (fun value => containsConst `PSigma' value && containsConst ``Eq value) &&
      #[Name.str privateRoot "good", Name.str privateRoot "skel"].all fun name =>
        !generatedNames.contains name

  let missingLaw := Check.check <|
    withoutDeclaration generated (Name.str privateRoot "roll_unroll")
  state := state.check "partial indexed fibre certificate fails closed" <|
    missingLaw.any
      (hasTypeViolation `IndexedDep (Name.str privateRoot "roll_unroll"))
  let malformedMap := Check.check <|
    replaceDeclarationType generated (Name.str privateRoot "roll")
      (.sort (.succ .zero))
  state := state.check "malformed indexed fibre map fails closed" <|
    malformedMap.any (hasTypeViolation `IndexedDep (Name.str privateRoot "roll"))
  -- The rule's *proposition* is certificate-independent: its right-hand side
  -- is the constructor field binder on every route, so removing the whole
  -- certificate cannot change the statement the checker rebuilds.  What the
  -- certificate is still required for is its own exactness, which the partial
  -- and malformed cases immediately above pin.
  let noCertificate := Check.check (certificate.foldl withoutDeclaration generated)
  state := state.check "the literal indexed rule is certificate-independent" <|
    #[payloadProjection, payloadRule, keyProjection, keyRule].all fun name =>
      !noCertificate.any (hasTypeViolation `IndexedDep name)

  let currentPayloadRule := actual payloadRule
  let transportedCandidate := if currentPayloadRule.any (containsConst ``Eq.rec) then
      generated
    else
      currentPayloadRule.bind transportOuterEqualityRhs?
        |>.map (replaceDeclarationType generated payloadRule ·) |>.getD generated
  state := state.check "checker rejects the old transported dependent projection rule" <|
    (Check.check transportedCandidate).any (hasTypeViolation `IndexedDep payloadRule)
  state := state.check "current diagnostic reaches generation and kernel replay" <|
    report.generated.any (·.1 == `IndexedDep) && report.unreplayable.isNone &&
      report.stmtErrors.isEmpty

  let boundary ← readExport
    s!"{root}/test/fixtures/inductive-models/indexed_fibre_boundary.ndjson"
  let fixedShape := sourceShape? boundary `FixedRecursiveResult
  state := state.check "exportable recursive control has a fixed result index" <|
    fixedShape.any fun (type, constructor, _) =>
      type.numIndices == 1 && type.isRec && type.ctors.length == 1 &&
        recursiveResultIndependent constructor
  let (boundaryGenerated, boundaryReport) ← runExport boundary
  let boundaryNames := boundaryGenerated.decls.flatMap (·.names.toArray)
  let indexedUnitRoot := `IndexedUnit._model._impl
  let indexedUnitCertificate := #[Name.str indexedUnitRoot "self",
    Name.str indexedUnitRoot "ctor_0", Name.str indexedUnitRoot "rec",
    Name.str indexedUnitRoot "rec_iota_0", Name.str indexedUnitRoot "roll",
    Name.str indexedUnitRoot "unroll", Name.str indexedUnitRoot "unroll_roll",
    Name.str indexedUnitRoot "roll_unroll"]
  state := state.check "zero-field indexed family carries a complete certificate" <|
    boundaryReport.generated.any (·.1 == `IndexedUnit) &&
      indexedUnitCertificate.all boundaryNames.contains
  let zeroFieldPartial := Check.check <|
    withoutDeclaration boundaryGenerated (Name.str indexedUnitRoot "roll_unroll")
  state := state.check "zero-field partial certificate fails at family boundary" <|
    zeroFieldPartial.any
      (hasTypeViolation `IndexedUnit (Name.str indexedUnitRoot "roll_unroll"))

  let hiddenRoot := `HiddenIndexed._model._impl
  let hiddenCertificate := #[Name.str hiddenRoot "self", Name.str hiddenRoot "ctor_0",
    Name.str hiddenRoot "rec", Name.str hiddenRoot "rec_iota_0",
    Name.str hiddenRoot "roll", Name.str hiddenRoot "unroll",
    Name.str hiddenRoot "unroll_roll", Name.str hiddenRoot "roll_unroll"]
  state := state.check "reducible-hidden result former stays structurally legacy" <|
    boundaryReport.generated.any (·.1 == `HiddenIndexed) &&
      hiddenCertificate.all fun name => !boundaryNames.contains name
  state := state.check "hidden-result legacy model is complete and checked" <|
    #[Naming.modelName `HiddenIndexed, Naming.modelName `HiddenIndexed.mk,
      Naming.modelName `HiddenIndexed.rec, Naming.iotaName `HiddenIndexed.rec 0].all
        boundaryNames.contains &&
      (Check.check boundaryGenerated).all (·.familyOwner != `HiddenIndexed)

  let recursivePrivateRoot := `FixedRecursiveResult._model._impl
  let recursiveCertificate := #[Name.str recursivePrivateRoot "self",
    Name.str recursivePrivateRoot "ctor_0", Name.str recursivePrivateRoot "rec",
    Name.str recursivePrivateRoot "rec_iota_0", Name.str recursivePrivateRoot "roll",
    Name.str recursivePrivateRoot "unroll", Name.str recursivePrivateRoot "unroll_roll",
    Name.str recursivePrivateRoot "roll_unroll"]
  state := state.check "minimal recursive indexed control carries the complete certificate" <|
    recursiveCertificate.all boundaryNames.contains
  state := state.check "minimal recursive indexed control generates and checks" <|
    boundaryReport.generated.any (·.1 == `FixedRecursiveResult) &&
      !boundaryReport.declined.any (·.1 == `FixedRecursiveResult) &&
      boundaryReport.unreplayable.isNone && boundaryReport.stmtErrors.isEmpty &&
      #[Naming.modelName `FixedRecursiveResult,
        Naming.modelName `FixedRecursiveResult.mk,
        Naming.modelName `FixedRecursiveResult.rec,
        Naming.iotaName `FixedRecursiveResult.rec 0,
        Naming.projectionName `FixedRecursiveResult 0,
        Naming.projectionIotaName `FixedRecursiveResult 0].all boundaryNames.contains &&
      (Check.check boundaryGenerated).all (·.familyOwner != `FixedRecursiveResult)

  let some recursiveLayerFamily := Check.discover boundaryGenerated |>.find?
      (·.owner == `IndexedRecursiveLayer)
    | throw <| IO.userError "generated boundary has no IndexedRecursiveLayer family"
  let some (recursiveLayerType, recursiveLayerConstructor, _) :=
      sourceShape? boundaryGenerated `IndexedRecursiveLayer
    | throw <| IO.userError "generated boundary has no IndexedRecursiveLayer source shape"
  let some recursiveLayerTypePair := recursiveLayerFamily.correspondence.typeFormers.find?
      (·.owner == `IndexedRecursiveLayer)
    | throw <| IO.userError "IndexedRecursiveLayer has no modeled carrier"
  let some (recursiveLayerParams, _) := declarationType? boundaryGenerated
      recursiveLayerTypePair.model
    | throw <| IO.userError "IndexedRecursiveLayer modeled carrier is absent"
  let (recursiveLayerFaces, _) ← Core.CoreM.toIO
    (MetaM.run' (projectionExpectations boundaryGenerated recursiveLayerFamily
      recursiveLayerType recursiveLayerConstructor recursiveLayerParams))
    projectionContext { env := projectionEnv }
  let recursiveLayerExpected := fun name =>
    recursiveLayerFaces.find? (·.1 == name) |>.map (·.2)
  let recursiveLayerActual := fun name =>
    declarationType? boundaryGenerated name |>.map (·.2)
  let recursiveLayerRoot := `IndexedRecursiveLayer._model._impl
  let recursiveLayerCertificate := #[Name.str recursiveLayerRoot "self",
    Name.str recursiveLayerRoot "ctor_0", Name.str recursiveLayerRoot "rec",
    Name.str recursiveLayerRoot "rec_iota_0", Name.str recursiveLayerRoot "roll",
    Name.str recursiveLayerRoot "unroll", Name.str recursiveLayerRoot "unroll_roll",
    Name.str recursiveLayerRoot "roll_unroll"]
  let recursiveLayerKeyRule := Naming.projectionIotaName `IndexedRecursiveLayer 0
  let recursiveLayerPayloadRule := Naming.projectionIotaName `IndexedRecursiveLayer 1
  let recursiveLayerChildRule := Naming.projectionIotaName `IndexedRecursiveLayer 2
  let recursiveLayerTailRule := Naming.projectionIotaName `IndexedRecursiveLayer 3
  state := state.check "dependent recursive indexed family carries a complete certificate" <|
    recursiveLayerCertificate.all boundaryNames.contains
  state := state.check "dependent recursive indexed ordinary rule has the literal field RHS" <|
    recursiveLayerActual recursiveLayerKeyRule == recursiveLayerExpected recursiveLayerKeyRule
  state := state.check "dependent recursive indexed payload rule has the literal field RHS" <|
    recursiveLayerActual recursiveLayerPayloadRule ==
      recursiveLayerExpected recursiveLayerPayloadRule
  state := state.check "recursive child projection iota has the exact literal statement" <|
    recursiveLayerActual recursiveLayerChildRule ==
      recursiveLayerExpected recursiveLayerChildRule
  state := state.check "independent field after the recursive child remains literal" <|
    recursiveLayerActual recursiveLayerTailRule ==
      recursiveLayerExpected recursiveLayerTailRule
  let recursiveLayerAuthoredFaces := #[Naming.modelName `IndexedRecursiveLayer.mk,
    Naming.modelName `IndexedRecursiveLayer.rec,
    Naming.iotaName `IndexedRecursiveLayer.rec 0,
    Name.str recursiveLayerRoot "ctor_0", Name.str recursiveLayerRoot "rec",
    Name.str recursiveLayerRoot "rec_iota_0"]
  state := state.check "source-authored Eq.rec survives recursive indexed faces" <|
    containsConst ``Eq.rec recursiveLayerConstructor.type &&
      recursiveLayerAuthoredFaces.all fun name =>
        (declarationType? boundaryGenerated name).any fun (_, type) =>
          containsConst ``Eq.rec type
  let recursiveLayerWithoutLaw := Check.check <|
    withoutDeclaration boundaryGenerated (Name.str recursiveLayerRoot "roll_unroll")
  state := state.check "partial recursive indexed certificate fails closed" <|
    recursiveLayerWithoutLaw.any (hasTypeViolation `IndexedRecursiveLayer
      (Name.str recursiveLayerRoot "roll_unroll"))
  let recursiveLayerMalformedRecursor := Check.check <|
    replaceRuleFieldCount boundaryGenerated `IndexedRecursiveLayer 0
  state := state.check "malformed recursive indexed source shape fails closed" <|
    recursiveLayerMalformedRecursor.any (hasTypeViolation `IndexedRecursiveLayer
      (Name.str recursiveLayerRoot "self"))
  let recursiveLayerLaterDependent := recursiveLaterDependencyType?
      recursiveLayerConstructor
    |>.map (replaceConstructorType boundaryGenerated `IndexedRecursiveLayer.mk ·)
    |>.getD boundaryGenerated
  state := state.check "later field depending on the recursive child fails closed" <|
    (Check.check recursiveLayerLaterDependent).any
      (hasTypeViolation `IndexedRecursiveLayer (Name.str recursiveLayerRoot "self"))
  let recursiveLayerCurrentPayloadRule := recursiveLayerActual recursiveLayerPayloadRule
  let recursiveLayerTransported := if recursiveLayerCurrentPayloadRule !=
      recursiveLayerExpected recursiveLayerPayloadRule then boundaryGenerated else
    recursiveLayerCurrentPayloadRule.bind transportOuterEqualityRhs?
      |>.map (replaceDeclarationType boundaryGenerated recursiveLayerPayloadRule ·)
      |>.getD boundaryGenerated
  state := state.check "checker rejects the old recursive indexed payload transport" <|
    (Check.check recursiveLayerTransported).any
      (hasTypeViolation `IndexedRecursiveLayer recursiveLayerPayloadRule)
  state := state.check "dependent recursive indexed family generates and checks" <|
    boundaryReport.generated.any (·.1 == `IndexedRecursiveLayer) &&
      !boundaryReport.declined.any (·.1 == `IndexedRecursiveLayer) &&
      (Check.check boundaryGenerated).all (·.familyOwner != `IndexedRecursiveLayer)

  let some parametricFamily := Check.discover boundaryGenerated |>.find?
      (·.owner == `ParametricRecursiveLayer)
    | throw <| IO.userError "generated boundary has no ParametricRecursiveLayer family"
  let some (parametricType, parametricConstructor, _) :=
      sourceShape? boundaryGenerated `ParametricRecursiveLayer
    | throw <| IO.userError "generated boundary has no ParametricRecursiveLayer source shape"
  let some parametricTypePair := parametricFamily.correspondence.typeFormers.find?
      (·.owner == `ParametricRecursiveLayer)
    | throw <| IO.userError "ParametricRecursiveLayer has no modeled carrier"
  let some (parametricParams, _) := declarationType? boundaryGenerated parametricTypePair.model
    | throw <| IO.userError "ParametricRecursiveLayer modeled carrier is absent"
  let (parametricFaces, _) ← Core.CoreM.toIO
    (MetaM.run' (projectionExpectations boundaryGenerated parametricFamily
      parametricType parametricConstructor parametricParams))
    projectionContext { env := projectionEnv }
  let parametricExpected := fun name => parametricFaces.find? (·.1 == name) |>.map (·.2)
  let parametricActual := fun name => declarationType? boundaryGenerated name |>.map (·.2)
  let parametricRoot := `ParametricRecursiveLayer._model._impl
  let parametricCertificate := #[Name.str parametricRoot "self",
    Name.str parametricRoot "ctor_0", Name.str parametricRoot "rec",
    Name.str parametricRoot "rec_iota_0", Name.str parametricRoot "roll",
    Name.str parametricRoot "unroll", Name.str parametricRoot "unroll_roll",
    Name.str parametricRoot "roll_unroll"]
  state := state.check "parameterized recursive indexed family carries a complete certificate" <|
    parametricCertificate.all boundaryNames.contains
  for fieldIndex in [0:4] do
    let rule := Naming.projectionIotaName `ParametricRecursiveLayer fieldIndex
    state := state.check s!"parameterized recursive indexed field {fieldIndex} is literal" <|
      parametricActual rule == parametricExpected rule
  state := state.check "parameterized recursive indexed universes generate and check" <|
    parametricType.levelParams == [`u, `v] &&
      boundaryReport.generated.any (·.1 == `ParametricRecursiveLayer) &&
      (Check.check boundaryGenerated).all (·.familyOwner != `ParametricRecursiveLayer)

  let some twoRecursiveFamily := Check.discover boundaryGenerated |>.find?
      (·.owner == `TwoRecursiveResults)
    | throw <| IO.userError "generated boundary has no TwoRecursiveResults family"
  let some (twoRecursiveType, twoRecursiveConstructor, _) :=
      sourceShape? boundaryGenerated `TwoRecursiveResults
    | throw <| IO.userError "generated boundary has no TwoRecursiveResults source shape"
  let some twoRecursiveTypePair := twoRecursiveFamily.correspondence.typeFormers.find?
      (·.owner == `TwoRecursiveResults)
    | throw <| IO.userError "TwoRecursiveResults has no modeled carrier"
  let some (twoRecursiveParams, _) := declarationType? boundaryGenerated
      twoRecursiveTypePair.model
    | throw <| IO.userError "TwoRecursiveResults modeled carrier is absent"
  let (twoRecursiveFaces, _) ← Core.CoreM.toIO
    (MetaM.run' (projectionExpectations boundaryGenerated twoRecursiveFamily
      twoRecursiveType twoRecursiveConstructor twoRecursiveParams))
    projectionContext { env := projectionEnv }
  let twoRecursiveExpected := fun name =>
    twoRecursiveFaces.find? (·.1 == name) |>.map (·.2)
  let twoRecursiveActual := fun name =>
    declarationType? boundaryGenerated name |>.map (·.2)
  let twoRecursiveRoot := `TwoRecursiveResults._model._impl
  let twoRecursiveCertificate := #[Name.str twoRecursiveRoot "self",
    Name.str twoRecursiveRoot "ctor_0", Name.str twoRecursiveRoot "rec",
    Name.str twoRecursiveRoot "rec_iota_0", Name.str twoRecursiveRoot "roll",
    Name.str twoRecursiveRoot "unroll", Name.str twoRecursiveRoot "unroll_roll",
    Name.str twoRecursiveRoot "roll_unroll"]
  state := state.check "two-child indexed family carries the complete certificate" <|
    twoRecursiveCertificate.all boundaryNames.contains
  for fieldIndex in [0:2] do
    let rule := Naming.projectionIotaName `TwoRecursiveResults fieldIndex
    state := state.check s!"two-child indexed recursive field {fieldIndex} is literal" <|
      twoRecursiveActual rule == twoRecursiveExpected rule
  let twoRecursiveWithoutLaw := Check.check <|
    withoutDeclaration boundaryGenerated (Name.str twoRecursiveRoot "roll_unroll")
  state := state.check "two-child indexed partial certificate fails closed" <|
    twoRecursiveWithoutLaw.any (hasTypeViolation `TwoRecursiveResults
      (Name.str twoRecursiveRoot "roll_unroll"))
  state := state.check "two-child indexed family generates and checks" <|
    boundaryReport.generated.any (·.1 == `TwoRecursiveResults) &&
      !boundaryReport.declined.any (·.1 == `TwoRecursiveResults) &&
      (Check.check boundaryGenerated).all (·.familyOwner != `TwoRecursiveResults)

  let some twoDependentFamily := Check.discover boundaryGenerated |>.find?
      (·.owner == `TwoRecursiveDependentResults)
    | throw <| IO.userError "generated boundary has no TwoRecursiveDependentResults family"
  let some (twoDependentType, twoDependentConstructor, _) :=
      sourceShape? boundaryGenerated `TwoRecursiveDependentResults
    | throw <| IO.userError
        "generated boundary has no TwoRecursiveDependentResults source shape"
  let some twoDependentTypePair := twoDependentFamily.correspondence.typeFormers.find?
      (·.owner == `TwoRecursiveDependentResults)
    | throw <| IO.userError "TwoRecursiveDependentResults has no modeled carrier"
  let some (twoDependentParams, _) := declarationType? boundaryGenerated
      twoDependentTypePair.model
    | throw <| IO.userError "TwoRecursiveDependentResults modeled carrier is absent"
  let (twoDependentFaces, _) ← Core.CoreM.toIO
    (MetaM.run' (projectionExpectations boundaryGenerated twoDependentFamily
      twoDependentType twoDependentConstructor twoDependentParams))
    projectionContext { env := projectionEnv }
  let twoDependentExpected := fun name =>
    twoDependentFaces.find? (·.1 == name) |>.map (·.2)
  let twoDependentActual := fun name =>
    declarationType? boundaryGenerated name |>.map (·.2)
  let twoDependentRoot := `TwoRecursiveDependentResults._model._impl
  let twoDependentCertificate := #[Name.str twoDependentRoot "self",
    Name.str twoDependentRoot "ctor_0", Name.str twoDependentRoot "rec",
    Name.str twoDependentRoot "rec_iota_0", Name.str twoDependentRoot "roll",
    Name.str twoDependentRoot "unroll", Name.str twoDependentRoot "unroll_roll",
    Name.str twoDependentRoot "roll_unroll"]
  let twoDependentPayloadRule :=
    Naming.projectionIotaName `TwoRecursiveDependentResults 1
  state := state.check "dependent two-child indexed family carries the complete certificate" <|
    twoDependentCertificate.all boundaryNames.contains
  for fieldIndex in [0:5] do
    let rule := Naming.projectionIotaName `TwoRecursiveDependentResults fieldIndex
    state := state.check s!"dependent two-child indexed field {fieldIndex} is literal" <|
      twoDependentActual rule == twoDependentExpected rule
  state := state.check "source-authored transport survives dependent two-child faces" <|
    containsConst ``Eq.rec twoDependentConstructor.type &&
      #[Naming.modelName `TwoRecursiveDependentResults.mk,
        Naming.modelName `TwoRecursiveDependentResults.rec,
        Naming.iotaName `TwoRecursiveDependentResults.rec 0,
        Name.str twoDependentRoot "ctor_0", Name.str twoDependentRoot "rec",
        Name.str twoDependentRoot "rec_iota_0"].all fun name =>
        (declarationType? boundaryGenerated name).any fun (_, type) =>
          containsConst ``Eq.rec type
  let twoDependentCurrentPayloadRule := twoDependentActual twoDependentPayloadRule
  let twoDependentTransported := if twoDependentCurrentPayloadRule !=
      twoDependentExpected twoDependentPayloadRule then boundaryGenerated else
    twoDependentCurrentPayloadRule.bind transportOuterEqualityRhs?
      |>.map (replaceDeclarationType boundaryGenerated twoDependentPayloadRule ·)
      |>.getD boundaryGenerated
  state := state.check "checker rejects old dependent two-child projection transport" <|
    (Check.check twoDependentTransported).any
      (hasTypeViolation `TwoRecursiveDependentResults twoDependentPayloadRule)
  let twoDependentMovingIndex := twoRecursiveIndexDependencyType? twoDependentConstructor
    |>.map (replaceConstructorType boundaryGenerated `TwoRecursiveDependentResults.mk ·)
    |>.getD boundaryGenerated
  -- A recursive occurrence whose index reads an earlier field is **not** a
  -- refusal — `FieldIndexedRecursiveResult` above models exactly that, because
  -- the field it reads is nonrecursive and its selector is reflexive.  What
  -- still fails closed is that the emitted family restates *this* source and no
  -- other: `erasedResultIndex key` reduces to `FibreIx.here`, so the mutation
  -- is definitionally invisible and only exact syntactic restatement sees it.
  let twoDependentMovingViolations := Check.check twoDependentMovingIndex
  state := state.check "a definitionally invisible recursive index change fails closed" <|
    twoDependentMovingViolations.any (hasTypeViolation `TwoRecursiveDependentResults.mk
        (Naming.modelName `TwoRecursiveDependentResults.mk)) &&
      twoDependentMovingViolations.any (hasTypeViolation `TwoRecursiveDependentResults
        (Naming.projectionName `TwoRecursiveDependentResults 3))
  for recursiveOffset in [0:2] do
    let laterDependent := twoRecursiveLaterDependencyType? twoDependentConstructor
        recursiveOffset
      |>.map (replaceConstructorType boundaryGenerated `TwoRecursiveDependentResults.mk ·)
      |>.getD boundaryGenerated
    state := state.check s!"later field depending on recursive child {recursiveOffset} fails closed" <|
      (Check.check laterDependent).any
        (hasTypeViolation `TwoRecursiveDependentResults (Name.str twoDependentRoot "self"))
  let twoDependentWithoutLaw := Check.check <|
    withoutDeclaration boundaryGenerated (Name.str twoDependentRoot "roll_unroll")
  state := state.check "dependent two-child partial certificate fails closed" <|
    twoDependentWithoutLaw.any (hasTypeViolation `TwoRecursiveDependentResults
      (Name.str twoDependentRoot "roll_unroll"))
  state := state.check "dependent two-child indexed family generates and checks" <|
    boundaryReport.generated.any (·.1 == `TwoRecursiveDependentResults) &&
      !boundaryReport.declined.any (·.1 == `TwoRecursiveDependentResults) &&
      (Check.check boundaryGenerated).all
        (·.familyOwner != `TwoRecursiveDependentResults)

  -- **Neither the number of recursive children nor a child's own index is a
  -- condition on this certificate.** `roll`/`unroll` are the identity at the
  -- owner's whole arity and their laws are reflexivity, so a third child costs
  -- what the first one does; and a child index that reads an earlier
  -- *nonrecursive* field is read back by that field's reflexive selector, so
  -- the child's rule is still the literal field.
  for owner in [`ThreeRecursiveResults, `FieldIndexedRecursiveResult] do
    let ownerRoot := Name.str (Naming.modelName owner) "_impl"
    let ownerCertificate := #[Name.str ownerRoot "self", Name.str ownerRoot "ctor_0",
      Name.str ownerRoot "rec", Name.str ownerRoot "rec_iota_0",
      Name.str ownerRoot "roll", Name.str ownerRoot "unroll",
      Name.str ownerRoot "unroll_roll", Name.str ownerRoot "roll_unroll"]
    state := state.check s!"{owner} carries the complete certificate" <|
      ownerCertificate.all boundaryNames.contains
    state := state.check s!"{owner} partial certificate fails closed" <|
      (Check.check <| withoutDeclaration boundaryGenerated
          (Name.str ownerRoot "roll_unroll")).any
        (hasTypeViolation owner (Name.str ownerRoot "roll_unroll"))
    state := state.check s!"{owner} generates and checks" <|
      boundaryReport.generated.any (·.1 == owner) &&
        !boundaryReport.declined.any (·.1 == owner) &&
        (Check.check boundaryGenerated).all (·.familyOwner != owner)

  -- A recursive occurrence below another former is not a constructor field of
  -- the owner, so these two stay outside the tranche for a reason the shape
  -- boundary states directly.
  for owner in [`InfinitaryRecursiveResult, `TransparentRecursiveResult] do
    let ownerRoot := Name.str (Naming.modelName owner) "_impl"
    let ownerCertificate := #[Name.str ownerRoot "self", Name.str ownerRoot "ctor_0",
      Name.str ownerRoot "rec", Name.str ownerRoot "rec_iota_0",
      Name.str ownerRoot "roll", Name.str ownerRoot "unroll",
      Name.str ownerRoot "unroll_roll", Name.str ownerRoot "roll_unroll"]
    state := state.check s!"{owner} remains on the legacy route" <|
      ownerCertificate.all fun name => !boundaryNames.contains name
    state := state.check s!"{owner} legacy model generates and checks" <|
      boundaryReport.generated.any (·.1 == owner) &&
        (Check.check boundaryGenerated).all (·.familyOwner != owner)

  -- Keep the owner exact but give its constructor a raw private spelling.
  -- The first primitive attempt then fails `nameLost` before it reaches the
  -- certificate freshness loop; only the alias-root retry can observe this
  -- reserved exact helper.
  let privateConstructor := (`_private.IndexedFibreDiagnostic).mkNum 0 |>.str "IndexedUnitMk"
  let sourceNames := boundary.decls.flatMap (·.names.toArray)
    |>.filter fun name => name == `IndexedUnit.mk
  let privateAliases := sourceNames.foldl (init := Naming.AliasMap.empty)
    fun aliases name => aliases.insert name privateConstructor
  let privateBoundary := { boundary with
    decls := boundary.decls.map (·.renameAliases privateAliases) }
  let exactCollision := `IndexedUnit._model._impl.roll
  let (_, collisionReport) ← runExport (insertCollision privateBoundary exactCollision)
  state := state.check "retry checks exact private certificate collisions" <|
    !collisionReport.generated.any (·.1 == `IndexedUnit) &&
      collisionReport.unreplayable.isNone && collisionReport.stmtErrors.isEmpty &&
      collisionReport.declined.filter (·.1 == `IndexedUnit) ==
        #[(`IndexedUnit, s!"prim model name taken ({exactCollision})")]

  IO.println s!"indexed fibre diagnostic: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1

def main (args : List String) : IO UInt32 :=
  run (args.head?.getD ".")

end IndexedFibreDiagnosticTest
