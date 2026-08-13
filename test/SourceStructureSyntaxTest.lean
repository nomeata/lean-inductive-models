import InductiveModels.Driver
import InductiveModels.Order

/-!
# Exact source-structure syntax regression

This fixture keeps an inherited projection in a dependent constructor field
and an `optParam` default in the same source-owned structure.  The regression
records the generated declaration, the statement checker's literal
expectation, and kernel readback for every public owner/constructor/recursor
slot and for every intrinsic projection and projection rule.
-/

open Lean Meta InductiveModels

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

def mapForallDomainAt (expression : Expr) (target : Nat) (f : Expr → Expr) : Expr :=
  match target, expression with
  | 0, .forallE name domain body info => .forallE name (f domain) body info
  | n + 1, .forallE name domain body info =>
      .forallE name domain (mapForallDomainAt body n f) info
  | _, _ => expression

/-- Inject one literal metadata node into the exported field domain.  lean4export
already supplies every surrounding structure expression; this controlled raw
syntax perturbation isolates the source-vs-installed metadata seam without
depending on elaborator simplification policy for a particular surface term. -/
def injectFieldSyntax (x : Export) : Export :=
  let wrap (domain : Expr) := .mdata {} domain
  { x with decls := x.decls.map fun declaration => match declaration with
    | .induct types constructors recursors =>
      .induct types (constructors.map fun constructor =>
        if constructor.induct == `SourceStructure then
          -- parameters alpha/family, then inherited parent and betaField
          let type := mapForallDomainAt constructor.type (constructor.numParams + 1) wrap
          { constructor with type }
        else constructor) recursors
    | declaration => declaration }

private partial def firstDifference? (actual expected : Expr)
    (path : String := "root") : Option String :=
  if actual == expected then none else
  match actual, expected with
  | .forallE an ad ab ai, .forallE en ed eb ei =>
      if an != en then some s!"{path}.forall.name: actual={an}, expected={en}"
      else if ai != ei then some s!"{path}.forall.info: actual={repr ai}, expected={repr ei}"
      else firstDifference? ad ed s!"{path}.forall.domain" <|>
        firstDifference? ab eb s!"{path}.forall.body"
  | .app af aa, .app ef ea =>
      firstDifference? af ef s!"{path}.app.fn" <|>
        firstDifference? aa ea s!"{path}.app.arg"
  | .proj atn ai av, .proj etn ei ev =>
      if atn != etn || ai != ei then
        some s!"{path}.proj: actual={atn}.{ai}, expected={etn}.{ei}"
      else firstDifference? av ev s!"{path}.proj.value"
  | .letE an aty av ab anond, .letE en ety ev eb enond =>
      if an != en || anond != enond then some s!"{path}.let metadata differs"
      else firstDifference? aty ety s!"{path}.let.type" <|>
        firstDifference? av ev s!"{path}.let.value" <|>
        firstDifference? ab eb s!"{path}.let.body"
  | _, _ => some s!"{path}: actual={repr actual}, expected={repr expected}"

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

partial def equalityLevel? : Expr → Option Level
  | .forallE _ _ body _ => equalityLevel? body
  | body => match body.getAppFn with
    | .const ``Eq [level] => some level
    | _ => none

structure Face where
  name : Name
  actual : Expr
  expected : Expr
  kernel : Expr
  difference : String

structure Evidence where
  report : Report
  faces : Array Face
  ownerFreeAccepted : Bool

def projectionExpectations (x : Export) (family : Check.Family)
    (ownerType : EIndType) (constructor : ECtor)
    (modelParams : List Name) : MetaM (Array (Name × Expr)) := do
  let mappedConstructorType := family.correspondence.expectedType
    constructor.levelParams modelParams constructor.type
  let (constructorBinders, constructorResult) := openForalls
    `_test.sourceStructureCtor mappedConstructorType
  let mappedOwnerType := family.correspondence.expectedType
    ownerType.levelParams modelParams ownerType.type
  let (ownerBinders, _) := openForalls `_test.sourceStructureOwner mappedOwnerType
  let ownerArgs := ownerBinders.map (·.value)
  let ownerArity := ownerType.numParams + ownerType.numIndices
  let ownerParams := ownerArgs.extract 0 ownerType.numParams
  let some fieldsType := instantiateForalls? mappedConstructorType ownerParams
    | throwError "cannot instantiate mapped constructor parameters"
  let (fieldBinders, _) := openForalls `_test.sourceStructureFields fieldsType
  let fields := constructorBinders.extract constructor.numParams constructorBinders.size
  let constructorArgs := constructorBinders.map (·.value)
  let params := constructorArgs.extract 0 constructor.numParams
  let levels := modelParams.map Level.param
  let some typePair := family.correspondence.typeFormers.find? (·.owner == ownerType.name)
    | throwError "missing modeled source-structure owner"
  let some constructorPair := family.correspondence.constructors.find? (·.owner == constructor.name)
    | throwError "missing modeled source-structure constructor"
  let major := mkAppN (.const constructorPair.model levels) constructorArgs
  let indices := constructorResult.getAppArgs.extract constructor.numParams ownerArity
  let selfValue := mkFVar (FVarId.mk `_test.sourceStructureSelf)
  let selfBinder : OpenBinder :=
    { name := `self, type := mkAppN (.const typePair.model levels) ownerArgs,
      info := .default, value := selfValue }
  let normalizer := x.exactNormalizationEnv
  let theoremBinders := constructorBinders.map fun binder =>
    { binder with type := normalizer.beta binder.type }
  let mut result := #[]
  for projection in family.correspondence.projections do
    let some selected := fieldBinders[projection.fieldIndex]?
      | throwError "missing field {projection.fieldIndex}"
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
    let some alpha := instantiateForalls? projectionType
        (params ++ indices ++ #[major])
      | throwError "cannot instantiate expected projection type"
    let lhs := mkAppN (.const projection.name levels)
      (params ++ indices ++ #[major])
    let rhs := fields[projection.fieldIndex]!.value
    let some (_, actualRuleType) := declarationType? x projection.iota
      | throwError "missing generated projection rule {projection.iota}"
    let some eqLevel := equalityLevel? actualRuleType
      | throwError "projection rule {projection.iota} is not an equality"
    let expectedRule := closeForalls theoremBinders <|
      mkAppN (.const ``Eq [eqLevel]) #[alpha, lhs, rhs]
    result := result.push (projection.iota, expectedRule)
  return result

def collectEvidence (path : String) : IO Evidence := do
  let .ok parsed := InductiveModels.parse (← IO.FS.readFile path) (analyse := false)
    | throw <| IO.userError s!"cannot parse {path}"
  let input := injectFieldSyntax parsed
  let base ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<source-structure-syntax-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let action : MetaM Evidence := do
    let (declarations, report) ← runFilter input false
      { nested := false, mutualModels := false, simple := true, basic := false }
    let generated : Export := { input with decls := declarations }
    let ordered ← match Order.reorder generated with
      | .ok ordered => pure ordered
      | .error error => throwError "cannot order fixture: {repr error}"
    let some family := Check.discover ordered |>.find? (·.owner == `SourceStructure)
      | throwError "generated fixture has no SourceStructure family"
    let .induct ownerTypes ownerConstructors ownerRecursors := ordered.decls[family.ownerDecl]!
      | throwError "SourceStructure owner is not an inductive record"
    let some ownerType := ownerTypes.find? (·.name == `SourceStructure)
      | throwError "missing SourceStructure type record"
    let some constructor := ownerConstructors.find? (·.induct == `SourceStructure)
      | throwError "missing SourceStructure constructor record"
    let some recursor := ownerRecursors.find? (·.all.contains `SourceStructure)
      | throwError "missing SourceStructure recursor record"
    let some typePair := family.correspondence.typeFormers.find? (·.owner == ownerType.name)
      | throwError "missing SourceStructure type correspondence"
    let some ctorPair := family.correspondence.constructors.find? (·.owner == constructor.name)
      | throwError "missing SourceStructure constructor correspondence"
    let some recPair := family.correspondence.recursors.find? (·.owner == recursor.name)
      | throwError "missing SourceStructure recursor correspondence"
    let some (typeParams, _) := declarationType? ordered typePair.model
      | throwError "missing modeled SourceStructure declaration"
    let some (ctorParams, _) := declarationType? ordered ctorPair.model
      | throwError "missing modeled SourceStructure constructor"
    let some (recParams, _) := declarationType? ordered recPair.model
      | throwError "missing modeled SourceStructure recursor"
    let mut expected : Array (Name × Expr) := #[
      (typePair.model, family.correspondence.expectedType
        ownerType.levelParams typeParams ownerType.type),
      (ctorPair.model, family.correspondence.expectedType
        constructor.levelParams ctorParams constructor.type),
      (recPair.model, family.correspondence.expectedType
        recursor.levelParams recParams recursor.type)]
    expected := expected ++ (← projectionExpectations ordered family ownerType constructor typeParams)

    let mut checked := base
    for declaration in ordered.decls do
      if let some replay := toDeclaration checked declaration then
        match checked.addDeclCore 0 replay none false with
        | .ok next => checked := next
        | .error exception =>
          throwError "kernel replay rejected {declaration.names}: {
            ← (exception.toMessageData {}).toString}"
    setEnv checked
    let mut faces := #[]
    for (name, wanted) in expected do
      let some (_, actual) := declarationType? ordered name
        | throwError "missing generated declaration {name}"
      let some info := checked.find? name
        | throwError "kernel replay did not retain {name}"
      faces := faces.push
        { name, actual, expected := wanted, kernel := info.type,
          difference := (firstDifference? actual wanted).getD "no structural difference" }

    let inputNames := input.decls.foldl (init := ({} : Std.HashSet Name)) fun names declaration =>
      declaration.names.foldl (·.insert ·) names
    let generatedRecords := ordered.decls.filter fun declaration =>
      declaration.names.any fun name => !inputNames.contains name
    let mut sourceBase := base
    for declaration in input.decls do
      unless declaration.names.contains `SourceStructure do
        if let some replay := toDeclaration sourceBase declaration then
          match sourceBase.addDeclCore 0 replay none false with
          | .ok next => sourceBase := next
          | .error _ => pure ()
    let ownerFreeAccepted := match ← checkGeneratedIn sourceBase generatedRecords with
      | .ok _ => true
      | .error _ => false
    return { report, faces, ownerFreeAccepted }
  return (← Core.CoreM.toIO (MetaM.run' action) context { env := base }).1

def containsName (faces : Array Face) (name : Name) : Bool :=
  faces.any (·.name == name)

def run (root : String) : IO UInt32 := do
  let evidence ← collectEvidence s!"{root}/test/fixtures/lean-inductive-models/source_structure_syntax.ndjson"
  for face in evidence.faces do
    IO.println s!"{face.name} first difference: {face.difference}"
    IO.println s!"{face.name} actual: {repr face.actual}"
    IO.println s!"{face.name} checker expected: {repr face.expected}"
    IO.println s!"{face.name} kernel readback: {repr face.kernel}"
  let expectedNames := #[`SourceStructure._model, `SourceStructure.mk._model,
    `SourceStructure.rec._model]
  let coreCovered := expectedNames.all (containsName evidence.faces)
  let projectionCovered := evidence.faces.any fun face =>
    face.name == Naming.projectionName `SourceStructure 0
  let projectionIotaCovered := evidence.faces.any fun face =>
    face.name == Naming.projectionIotaName `SourceStructure 0
  let mismatches := evidence.faces.filter fun face => face.actual != face.expected
  let kernelMatchesActual := evidence.faces.all fun face => face.actual == face.kernel
  let passed := coreCovered && projectionCovered && projectionIotaCovered &&
    mismatches.isEmpty && kernelMatchesActual &&
    evidence.report.stmtErrors.isEmpty && evidence.ownerFreeAccepted
  IO.println s!"source structure exact syntax: {evidence.faces.size} faces; {
    evidence.report.stmtErrors.size} statement mismatches"
  unless passed do
    IO.eprintln s!"FAIL: core={coreCovered}, projection={projectionCovered}, \
      projection-iota={projectionIotaCovered}, mismatches={mismatches.size}, \
      kernel-matches={kernelMatchesActual}, report-errors={evidence.report.stmtErrors.size}, \
      owner-free={evidence.ownerFreeAccepted}"
  return if passed then 0 else 1

def main (args : List String) : IO UInt32 :=
  run (args.head?.getD ".")
