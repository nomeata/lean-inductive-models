import InductiveModels.Check

set_option maxRecDepth 4096

/-!
# Focused tests for the structural model checker

Run from the repository root with `lake exe checktest [ROOT]`.

The synthetic baseline starts from an actual lean4export fixture.  Exact public
type-former, constructor and recursor axioms and iota propositions, plus a
generic helper, are inserted before its `Tree` inductive record.  Their types are obtained by the
same public correspondence operation the checker exposes, with fresh universe
parameter names to exercise positional alignment.  The adversarial cases are
mutations of that baseline, so each changes only the invariant named by it.
They include missing, duplicate, swapped and definitionally-but-not-syntactically
equal recursor and rule declarations.

Additional cases cover declaration names which contain `_model`, raw private
names, and a multi-member mutual record whose public slots do not depend on the
first member or export position.
-/

open Lean InductiveModels InductiveModels.Check

structure TestState where
  passed : Nat := 0
  failed : Nat := 0

def TestState.check (state : TestState) (label : String) (condition : Bool) : IO TestState := do
  if condition then
    return { state with passed := state.passed + 1 }
  else
    IO.eprintln s!"FAIL: {label}"
    return { state with failed := state.failed + 1 }

def ownerIndex? (x : Export) (owner : Name) : Option Nat :=
  x.decls.findIdx? fun declaration =>
    match declaration with
    | .induct types _ _ => types.any (·.name == owner)
    | _ => false

def declarationType? (declaration : EDecl) (name : Name) : Option (List Name × Expr) :=
  match declaration with
  | .ax got params type _ | .quot got params type _ =>
      if got == name then some (params, type) else none
  | .defn got params type .. | .thm got params type .. | .opaq got params type .. =>
      if got == name then some (params, type) else none
  | .induct types ctors recursors =>
      (types.find? (·.name == name)).map (fun type => (type.levelParams, type.type)) <|>
      (ctors.find? (·.name == name)).map (fun ctor => (ctor.levelParams, ctor.type)) <|>
      (recursors.find? (·.name == name)).map (fun recursor =>
        (recursor.levelParams, recursor.type))

def exportDeclarationType? (x : Export) (name : Name) : Option (List Name × Expr) :=
  x.decls.findSome? (declarationType? · name)

def exportDeclaration? (x : Export) (name : Name) : Option EDecl :=
  x.decls.find? (·.names.contains name)

def indexedFamilyStatements? (x : Export) (owner : Name) : Option StatementReport := do
  let family ← (discover x).find? (·.owner == owner)
  return checkFamilyStatementsWithIndex x (.ofExport x) family

def indexedStatementsFor (x : Export) (owners : Std.HashSet Name) : StatementReport :=
  checkStatementFamiliesWithIndex x (.ofExport x) (statementFamiliesFor x owners)

def compactMatches (x : Export) : Bool :=
  match compactOrderedCheckReport x with
  | .ok compact => compact == checkReport x
  | .error _ => false

def compactRejected (result : Except String Report) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

/-- Exercise compact no-output representation: owner decisions are captured
record-by-record, then only ordered names and value-free templates survive for
the one global-extra sweep. -/
def compactIndexedStatementsFor (x : Export) (owners : Std.HashSet Name) : StatementReport :=
  let index := SyntaxIndex.ofSource x
  let families := statementFamiliesFor x owners
  let localReport := checkStatementFamiliesLocalWithIndex x index families
  let diagnosticOwners := families.foldl (init := ({} : Std.HashSet Name))
    fun result family => family.correspondence.diagnosticOwners.foldl
      (fun result owner => result.insert owner) result
  let global := compactGlobalExtrasWithIndex index x.decls |>.filter fun violation =>
    diagnosticOwners.contains violation.familyOwner
  { localReport with violations := localReport.violations ++ global }

def indexedFamilyUnionFor (x : Export) (owners : Std.HashSet Name) : StatementReport :=
  let index := SyntaxIndex.ofExport x
  (statementFamiliesFor x owners).foldl
      (init := { statementsChecked := 0, violations := #[] }) fun union family =>
    let report := checkFamilyStatementsWithIndex x index family
    { statementsChecked := union.statementsChecked + report.statementsChecked
      violations := union.violations ++ report.violations }

def modelParams (params : List Name) : List Name :=
  (List.range params.length).map fun index => Name.str .anonymous s!"model_u_{index}"

partial def forallBody : Expr → Expr
  | .forallE _ _ body _ => forallBody body
  | body => body

def modelDefinition (table : Correspondence) (x : Export) (pair : ConstantPair) : Option EDecl := do
  let (ownerParams, ownerType) ← exportDeclarationType? x pair.owner
  let params := modelParams ownerParams
  return .defn pair.model params (table.expectedType ownerParams params ownerType)
    (.sort .zero) .opaque "safe" [pair.model]

def modelIotaTheorem (table : Correspondence) (x : Export) (ownerDecl : Nat)
    (iota : Naming.Iota) : Option EDecl := do
  let (ownerParams, ownerType) ←
    iotaProposition? x ownerDecl iota.recursor iota.ruleIndex
  let params := modelParams ownerParams
  return .thm iota.name params (table.expectedIotaType ownerParams params ownerType)
    (.sort .zero) [iota.name]

private structure EtaBinder where
  name : Name
  type : Expr
  info : BinderInfo
  value : Expr

private partial def openEtaForalls (tag : Name) (expression : Expr) :
    Array EtaBinder × Expr :=
  let rec loop (expression : Expr) (binders : Array EtaBinder) :=
    match expression with
    | .forallE name type body info =>
      let value := mkFVar (FVarId.mk (tag.mkNum binders.size))
      loop (body.instantiate1 value) (binders.push { name, type, info, value })
    | body => (binders, body)
  loop expression #[]

private def closeEtaForalls (binders : Array EtaBinder) (body : Expr) : Expr :=
  binders.reverse.foldl (fun body binder =>
    .forallE binder.name binder.type (body.abstract #[binder.value]) binder.info) body

def modelEtaTheorem (table : Correspondence) (x : Export) (ownerDecl : Nat)
    (metadata : Naming.Metadata) : Option EDecl := do
  let .induct types constructors _ ← x.decls[ownerDecl]? | none
  let ownerType ← types.find? (·.name == metadata.owner)
  let [constructorName] := ownerType.ctors | none
  let constructor ← constructors.find? fun candidate =>
    candidate.name == constructorName && candidate.induct == metadata.owner
  guard <| ownerType.numIndices == 0
  guard <| constructor.numFields ==
    (table.projections.filter (·.owner == metadata.owner)).size
  let typePair ← table.typeFormers.find? (·.owner == metadata.owner)
  let constructorPair ← table.constructors.find? (·.owner == constructorName)
  let params := modelParams ownerType.levelParams
  let levels := params.map Level.param
  let mappedOwnerType := table.expectedType ownerType.levelParams params ownerType.type
  let (parameterBinders, ownerResult) :=
    openEtaForalls ((`_checkTest.eta).append metadata.owner) mappedOwnerType
  guard <| parameterBinders.size == ownerType.numParams
  let .sort carrierLevel := ownerResult | none
  let parameterValues := parameterBinders.map (·.value)
  let carrier := mkAppN (.const typePair.model levels) parameterValues
  let selfValue := mkFVar (FVarId.mk ((`_checkTest.etaSelf).append metadata.owner))
  let selfBinder : EtaBinder :=
    { name := `x, type := carrier, info := .default, value := selfValue }
  let mut fields : Array Expr := #[]
  for fieldIndex in [0:constructor.numFields] do
    let projection ← table.projections.find? fun projection =>
      projection.owner == metadata.owner && projection.fieldIndex == fieldIndex
    fields := fields.push <| mkAppN (.const projection.name levels)
      (parameterValues.push selfValue)
  let reconstruction := mkAppN (.const constructorPair.model levels)
    (parameterValues ++ fields)
  let proposition := mkAppN (.const ``Eq [carrierLevel])
    #[carrier, selfValue, reconstruction]
  let type := closeEtaForalls (parameterBinders.push selfBinder) proposition
  return .thm metadata.name params type (.sort .zero) [metadata.name]

def modelMetadataTheorem (table : Correspondence) (x : Export) (ownerDecl : Nat)
    (metadata : Naming.Metadata) : Option EDecl := do
  if metadata.kind == .eta then
    return ← modelEtaTheorem table x ownerDecl metadata
  let (ownerParams, ownerType) ← match metadata.kind with
    | .unitlike => unitlikeProposition? x ownerDecl metadata.owner
    | .ruleK => ruleKProposition? x ownerDecl metadata.owner
    | _ => none
  let params := modelParams ownerParams
  return .thm metadata.name params (table.expectedIotaType ownerParams params ownerType)
    (.sort .zero) [metadata.name]

def modelDeclarations (x : Export) (table : Correspondence) (helper : Name) : Array EDecl :=
  let constants := (table.typeFormers ++ table.constructors ++ table.recursors).filterMap
    (modelDefinition table x)
  let iotas := match table.typeFormers[0]?.bind (ownerIndex? x ·.owner) with
    | some ownerDecl => table.iotas.filterMap (modelIotaTheorem table x ownerDecl)
    | none => #[]
  let metadata := match table.typeFormers[0]?.bind (ownerIndex? x ·.owner) with
    | some ownerDecl => table.metadata.filterMap (modelMetadataTheorem table x ownerDecl)
    | none => #[]
  #[EDecl.ax helper [] (.sort (.succ .zero)) false] ++ constants ++ iotas ++ metadata

def withValidModel (x : Export) (ownerDecl : Nat) (models : Array EDecl) : Export :=
  { x with decls := x.decls.extract 0 ownerDecl ++ models ++
      x.decls.extract ownerDecl x.decls.size }

def withLateCarrier (x : Export) (ownerDecl : Nat) (models : Array EDecl)
    (carrier : Name) : Export :=
  match models.find? (·.names.contains carrier) with
  | none => x
  | some carrierDecl =>
    let early := models.filter (!·.names.contains carrier)
    { x with decls := x.decls.extract 0 ownerDecl ++ early ++
        #[x.decls[ownerDecl]!, carrierDecl] ++
        x.decls.extract (ownerDecl + 1) x.decls.size }

def withOwnerType (x : Export) (ownerDecl : Nat) (type : Expr) : Export :=
  let declaration := match x.decls[ownerDecl]! with
    | .induct (first :: rest) ctors recursors =>
        .induct ({ first with type } :: rest) ctors recursors
    | declaration => declaration
  { x with decls := x.decls.set! ownerDecl declaration }

def withDeclarationType (x : Export) (name : Name) (type : Expr) : Export :=
  { x with decls := x.decls.map fun declaration =>
      match declaration with
      | .ax got params _ isUnsafe =>
          if got == name then .ax got params type isUnsafe else declaration
      | .defn got params _ value hints safety all =>
          if got == name then .defn got params type value hints safety all else declaration
      | .thm got params _ value all =>
          if got == name then .thm got params type value all else declaration
      | .opaq got params _ value isUnsafe all =>
          if got == name then .opaq got params type value isUnsafe all else declaration
      | _ => declaration }

def withDefinitionSafety (x : Export) (name : Name) (safety : String) : Export :=
  { x with decls := x.decls.map fun declaration => match declaration with
      | .defn got params type value hints _ all =>
          if got == name then .defn got params type value hints safety all else declaration
      | _ => declaration }

def withImplementationAxiom (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.map fun declaration => match declaration with
      | .defn got params type _ _ _ _ =>
          if got == name then .ax got params type false else declaration
      | _ => declaration }

def withProofDefinition (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.map fun declaration => match declaration with
      | .thm got params type value all =>
          if got == name then .defn got params type value .opaque "safe" all else declaration
      | _ => declaration }

def withUnsafeOwner (x : Export) (ownerDecl : Nat) : Export :=
  let declaration := match x.decls[ownerDecl]! with
    | .induct types constructors recursors =>
        .induct (types.map fun type => { type with isUnsafe := true })
          (constructors.map fun constructor => { constructor with isUnsafe := true })
          (recursors.map fun recursor => { recursor with isUnsafe := true })
    | declaration => declaration
  { x with decls := x.decls.set! ownerDecl declaration }

def withoutDeclaration (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.filter (!·.names.contains name) }

def insertBeforeOwner (x : Export) (owner : Name) (declaration : EDecl) : Export :=
  match ownerIndex? x owner with
  | none => x
  | some index =>
      { x with decls := x.decls.extract 0 index ++ #[declaration] ++
          x.decls.extract index x.decls.size }

def renameExportRoot (x : Export) (owner renamed : Name) : Export :=
  let names := x.decls.flatMap fun declaration => declaration.names.toArray
  let aliases := Naming.AliasMap.forRetry owner renamed names
  { x with decls := x.decls.map (·.renameAliases aliases) }

def isLateCarrier (owner carrier : Name) : Violation → Bool
  | .modelNotBefore gotOwner declaration _ _ => gotOwner == owner && declaration == carrier
  | _ => false

def isBackreference (owner target : Name) : Violation → Bool
  | .ownerBackreference gotOwner gotTarget => gotOwner == owner && gotTarget == target
  | _ => false

def isMissing (owner declaration : Name) : Violation → Bool
  | .missingPublic gotOwner gotDeclaration =>
      gotOwner == owner && gotDeclaration == declaration
  | _ => false

def isTypeMismatch (owner declaration : Name) : Violation → Bool
  | .declarationType gotOwner gotDeclaration =>
      gotOwner == owner && gotDeclaration == declaration
  | _ => false

def isKindMismatch (owner declaration : Name) (expected actual : DeclarationKind) :
    Violation → Bool
  | .declarationKind gotOwner gotDeclaration gotExpected gotActual =>
      gotOwner == owner && gotDeclaration == declaration &&
        gotExpected == expected && gotActual == actual
  | _ => false

def isSafetyMismatch (owner declaration : Name) (safety : String) : Violation → Bool
  | .declarationSafety gotOwner gotDeclaration actual =>
      gotOwner == owner && gotDeclaration == declaration && actual == safety
  | _ => false

def isDuplicate (owner declaration : Name) : Violation → Bool
  | .duplicatePublic gotOwner gotDeclaration count =>
      gotOwner == owner && gotDeclaration == declaration && count > 1
  | _ => false

def isExtraRule (owner declaration : Name) : Violation → Bool
  | .extraRule gotOwner gotDeclaration =>
      gotOwner == owner && gotDeclaration == declaration
  | _ => false

def isExtraUnitlike (owner declaration : Name) : Violation → Bool
  | .extraMetadata gotOwner gotDeclaration .unitlike =>
      gotOwner == owner && gotDeclaration == declaration
  | _ => false

/-! Keep the former quadratic implementation as a test-only specification.
The production implementation indexes projection-shaped names once; this
oracle deliberately repeats the full ordered-name scan for every type template
so randomized equivalence tests exercise two independent algorithms. -/

private def referenceProjectionSlot? (owner name : Name) : Option Nat := do
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

def referenceGlobalExtrasFromRecords (records : Array GlobalExtraRecord) : Array Violation :=
    Id.run do
  let orderedNames := records.flatMap (·.names)
  let declared := orderedNames.foldl (fun names name => names.insert name)
    ({} : Std.HashSet Name)
  let mut violations : Array Violation := #[]
  for record in records do
    for template in record.templates do
      match template with
      | .type owner validFields allowsUnitlike allowsEta =>
        for name in orderedNames do
          if let some fieldIndex := referenceProjectionSlot? owner name then
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

/-! Keep family discovery's former whole-export reconstruction as a second
test-only specification. Production discovery now shares one `SyntaxIndex`;
this oracle deliberately calls `correspondenceAt?` independently for every
owner, preserving the previous algorithm and observable family order. -/

private def referenceAppendUnique (names : Array Name) (more : List Name) : Array Name :=
  more.foldl (fun out name => if out.contains name then out else out.push name) names

def referenceDiscover (x : Export) : Array Family := Id.run do
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
      (fun names i => referenceAppendUnique names x.decls[i]!.names) #[]
    let modelRoot := Naming.modelName root
    families := families.push
      { owner := root, modelRoot, carrier := modelRoot, ownerDecl, correspondence,
        decls := modelDecls, names := modelNames }
  return families

private def propertyMix (seed index : Nat) : Nat :=
  (seed * 1103515245 + index * 12345 + index * index * 97) % 2147483647

private structure PropertyDecl where
  key : Nat
  ordinal : Nat
  declaration : EDecl

/-- Deterministic randomized permutations plus missing/duplicate declaration
mutations. Family discovery is order-sensitive in its indices, so both the
indexed implementation and the former reference run on the same mutation. -/
def propertyDiscoveryExport (x : Export) (seed : Nat) : Export :=
  let declarations :=
    if x.decls.isEmpty then x.decls
    else
      let selected := propertyMix seed 17 % x.decls.size
      match seed % 4 with
      | 0 => x.decls.push x.decls[selected]!
      | 1 => x.decls.extract 0 selected ++ x.decls.extract (selected + 1) x.decls.size
      | _ => x.decls
  let keyed := declarations.mapIdx fun ordinal declaration =>
    { key := propertyMix seed (ordinal + 211), ordinal, declaration : PropertyDecl }
  let ordered := keyed.qsort fun left right =>
    left.key < right.key || (left.key == right.key && left.ordinal < right.ordinal)
  { x with decls := ordered.map (·.declaration) }

private def propertyOwner (seed index : Nat) : Name :=
  let base := Name.str `GlobalExtraProperty s!"owner_{propertyMix seed index % 11}"
  if propertyMix seed (index + 31) % 4 == 0 then Name.str base "_model" else base

private def propertyName (seed index : Nat) : Name :=
  let owner := propertyOwner seed (propertyMix seed (index + 1))
  let field := propertyMix seed (index + 2) % 9
  match propertyMix seed (index + 3) % 10 with
  | 0 | 1 | 9 => Naming.projectionName owner field
  | 2 => Naming.projectionIotaName owner field
  | 3 => Naming.unitlikeName owner
  | 4 => Naming.etaName owner
  | 5 => Naming.ruleKName owner
  | 6 => Name.str (Naming.modelName owner) "proj_not_a_number"
  | 7 => Name.str (Name.str (Naming.modelName owner) "proj_bad") "iota"
  | _ => Name.str owner s!"ordinary_{field}"

def propertyGlobalExtraRecords (seed : Nat) : Array GlobalExtraRecord :=
  (Array.range 29).map fun recordIndex =>
    let names := (Array.range 7).map fun localIndex =>
      propertyName seed (recordIndex * 7 + localIndex)
    let owner := propertyOwner seed (recordIndex * 3)
    let validFields := (Array.range 9).filter fun field =>
      propertyMix seed (recordIndex * 17 + field) % 3 != 0
    let templates : Array GlobalExtraTemplate :=
      #[.type owner validFields
          (propertyMix seed (recordIndex + 101) % 2 == 0)
          (propertyMix seed (recordIndex + 103) % 2 == 0),
        .recursor (propertyOwner seed (recordIndex * 5 + 1))
          (propertyMix seed (recordIndex + 107) % 2 == 0)] ++
      (if recordIndex % 5 == 0 then
        #[.type (propertyOwner seed (recordIndex + 1))
            (validFields.reverse.extract 0 (validFields.size / 2)) false false]
      else #[])
    { names, templates }

/-- A retained source-index shape for ownership profiling.  The declarations
are deliberately irrelevant to the checked family: they enlarge only the
source tables which `prependRecords` must share with each disposable island
overlay. -/
def overlayOwnershipSource (x : Export) (size : Nat := 4096) : Export :=
  { x with decls := x.decls ++ ((Array.range size).map fun i =>
      EDecl.ax ((`_check.overlayOwnership).mkNum i) [] (.sort .zero) false) }

/-- One island for chained round `round`: `count` declarations whose names
cannot collide with the fixture, with the model island, or with any other
round, so `prependRecords` cannot reject the repeat. -/
def overlayChainIsland (round count : Nat) : Array EDecl :=
  (Array.range count).map fun i =>
    EDecl.ax (((`_check.overlayChain).mkNum round).mkNum i) [] (.sort .zero) false

/-- Chain `repetitions` island overlays onto `base`, each prepending an island
of `islandSize` declarations onto the accumulated prefix its predecessors left
behind.  Only chaining reaches the accumulating side of `prependRecords`:
re-prepending from the same base index leaves `recordPrefix` empty every time.

True when every round is accepted, every chained name is declared by the final
index, and `raw`'s local family report for `families` equals `expected` both
after the first overlay and after the whole chain. -/
def chainedOverlaysPreserveReport (raw : Export) (base : SyntaxIndex)
    (families : Array Family) (expected : StatementReport)
    (islandSize repetitions : Nat) : Bool := Id.run do
  unless checkStatementFamiliesLocalWithIndex raw base families == expected do
    return false
  let mut chained := base
  for round in [0:repetitions] do
    match chained.prependRecords (overlayChainIsland round islandSize) with
    | .error _ => return false
    | .ok next => chained := next
  for round in [0:repetitions] do
    for declaration in overlayChainIsland round islandSize do
      unless declaration.names.all chained.declares do return false
  return checkStatementFamiliesLocalWithIndex raw chained families == expected

/-- Chain `repetitions` island overlays onto one retained source index: every
prepend sees the record prefix its predecessors accumulated, which is the only
way to reach the accumulating side of `SyntaxIndex.prependRecords`.  Repeating
the same prepend from the same base index instead — as this probe used to do —
leaves the prefix empty on every call and measures nothing but path copying of
the already-persistent source tables, so it cannot see a regression in the
overlay path itself.

The assertions stay structural rather than timing-based: the first island's
local family report must equal the whole-export reference report, every chained
island must be accepted and still be declared by the accumulated index, and the
first island's report must survive the whole chain unchanged.  Wall time and
`perf stat -e instructions` over the run remain the profiling signal, now over
a chain whose cost is linear in `repetitions` only if the overlay path is: the
chain is long enough that a per-prepend rescan of the accumulated prefix shows
up as super-linear growth when `repetitions` is doubled. -/
def runOverlayOwnershipProbe (root : String) (size := 32768)
    (repetitions := 4096) : IO UInt32 := do
  let path := s!"{root}/test/fixtures/inductive-models/nested_iota_arm.ndjson"
  let text ← IO.FS.readFile path
  let .ok raw := InductiveModels.parse text
    | throw <| IO.userError s!"cannot parse {path}"
  let owner := `Tree
  let some ownerDecl := ownerIndex? raw owner
    | throw <| IO.userError s!"{path} does not declare {owner}"
  let some table := correspondenceAt? raw ownerDecl
    | throw <| IO.userError s!"no correspondence table for {owner}"
  let models := modelDeclarations raw table `Tree._model._impl.helper
  let source := SyntaxIndex.ofSourceIncremental (overlayOwnershipSource raw size)
  let families := source.sourceStatementFamilies owner
  let .ok first := source.prependRecords models
    | throw <| IO.userError "valid ownership-probe overlay was rejected"
  let referenceSource := SyntaxIndex.ofSource raw
  let .ok reference := referenceSource.prependRecords models
    | throw <| IO.userError "valid reference overlay was rejected"
  let expected := checkStatementFamiliesLocalWithIndex raw reference
    (referenceSource.sourceStatementFamilies owner)
  let semantic := checkStatementFamiliesLocalWithIndex raw first families == expected
  let mut chained := first
  let mut chainAccepted := true
  for round in [0:repetitions] do
    match chained.prependRecords (overlayChainIsland round models.size) with
    | .error _ => chainAccepted := false
    | .ok next => chained := next
  let chainDeclared := (Array.range repetitions).all fun round =>
    (overlayChainIsland round models.size).all fun declaration =>
      declaration.names.all chained.declares
  let chainSemantic :=
    checkStatementFamiliesLocalWithIndex raw chained families == expected
  if semantic && chainAccepted && chainDeclared && chainSemantic then
    IO.println
      s!"overlay-ownership-probe: {size} source rows, {repetitions} chained overlays passed"
    return 0
  else
    IO.eprintln "overlay-ownership-probe: report mismatch"
    return 1

/-! ## The checks

The checks are grouped by the invariant they exercise, one `def` per group,
each threading the same `TestState` and returning `none` once a fixture
precondition fails so `run` can stop exactly where the single block used to.

They are separate declarations because Lean's `do` elaborator is superlinear in
block length: as one several-hundred-statement block these checks needed
`maxHeartbeats 0` and minutes of elaboration, while the same statements in
short blocks elaborate in seconds. -/

def checkDiscovery (valid : Export) (families : Array Family)
    (state : TestState) : IO (Option TestState) := do
  let mut state := state
  state ← state.check "indexed family discovery equals the former implementation" <|
    families == referenceDiscover valid
  state ← state.check "indexed discovery preserves randomized adversarial families" <|
    (Array.range 128).all fun seed =>
      let candidate := propertyDiscoveryExport valid seed
      let index := SyntaxIndex.ofSource candidate
      discoverWithIndex candidate index == referenceDiscover candidate &&
        discover candidate == referenceDiscover candidate
  return some state

def checkGlobalExtraRecords (state : TestState) : IO (Option TestState) := do
  let mut state := state
  let interleavedAProjection := Naming.projectionName `Interleave.A 3
  let interleavedBProjection := Naming.projectionName `Interleave.B 7
  let interleavedGlobal : Array GlobalExtraRecord := #[
    { names := #[`Interleave.A]
      templates := #[.type `Interleave.A #[] true true] },
    { names := #[interleavedBProjection], templates := #[] },
    { names := #[`Interleave.B]
      templates := #[.type `Interleave.B #[] true true] },
    { names := #[interleavedAProjection], templates := #[] }]
  state ← state.check "bound global-extra records preserve interleaved owner order" <|
    globalExtrasFromRecords interleavedGlobal == #[
      .extraProjection `Interleave.A interleavedAProjection,
      .extraProjection `Interleave.B interleavedBProjection]
  let duplicateProjection := Naming.projectionName `Interleave.A 9
  let duplicateMetadata := Naming.unitlikeName `Interleave.A
  let duplicateGlobal : Array GlobalExtraRecord := #[
    { names := #[duplicateProjection, duplicateMetadata, duplicateProjection]
      templates := #[] },
    { names := #[Naming.projectionIotaName `Interleave.A 9]
      templates := #[.type `Interleave.A #[] false true,
        .type `Interleave.A #[9] false false] }]
  state ← state.check "global-extra index preserves duplicate names and templates" <|
    globalExtrasFromRecords duplicateGlobal ==
      referenceGlobalExtrasFromRecords duplicateGlobal
  state ← state.check "linear global extras equal the quadratic specification" <|
    (Array.range 128).all fun seed =>
      let records := propertyGlobalExtraRecords seed
      globalExtrasFromRecords records == referenceGlobalExtrasFromRecords records
  let onlyB := ({} : Std.HashSet Name).insert `Interleave.B
  let lateFiltered := (globalExtrasFromRecords interleavedGlobal).filter fun violation =>
    onlyB.contains violation.familyOwner
  state ← state.check "owner-filtered global extras equal the historical late filter" <|
    globalExtrasFromRecordsFor interleavedGlobal onlyB == lateFiltered &&
      lateFiltered == #[.extraProjection `Interleave.B interleavedBProjection]
  state ← state.check "empty owner selection skips every global-extra template" <|
    (globalExtrasFromRecordsFor interleavedGlobal {}).isEmpty
  return some state

def checkFamilyIdentity (owner modelRoot carrier helper : Name)
    (table : Correspondence) (models : Array EDecl) (validOwnerDecl : Nat)
    (families : Array Family) (state : TestState) : IO (Option TestState) := do
  let mut state := state
  state ← state.check "one public family discovered" (families.size == 1)
  if let some family := families[0]? then
    state ← state.check "family key" <|
      family.owner == owner && family.modelRoot == modelRoot &&
        family.carrier == carrier && family.ownerDecl == validOwnerDecl &&
        family.correspondence == table
    state ← state.check "only exact public records establish the family" <|
      family.decls.size + 1 == models.size &&
        !family.names.contains helper && family.names.contains carrier
  else
    state ← state.check "family key" false
    state ← state.check "only exact public records establish the family" false
  return some state

def checkValidReport (valid : Export) (state : TestState) : IO (Option TestState) := do
  let mut state := state
  state ← state.check "valid ordering and independence" (check valid).isEmpty
  state ← state.check "compact ordered report equals the valid full checker" <|
    compactMatches valid
  return some state

def checkCompactCertificates (owner : Name) (valid : Export)
    (state : TestState) : IO (Option TestState) := do
  let mut state := state
  let compactIndex := SyntaxIndex.ofSource valid
  let compactFamilyRows := compactFamilyCertificateRecordsWithIndex
    valid compactIndex (discover valid)
  let compactRows := (globalExtraRecordsWithIndex compactIndex valid.decls).mapIdx
    fun i globalExtra =>
      { owner := match valid.decls[i]! with
          | .induct (type :: _) _ _ => some type.name
          | _ => none
        globalExtra, families := compactFamilyRows[i]! : CompactCheckRecord }
  let some ownerRow := compactRows.findIdx? (fun row => row.owner == some owner) | do
    IO.eprintln "checktest: compact owner row missing"
    return none
  let ownerCertificate := compactRows[ownerRow]!.families[0]!
  let compactRows := compactRows.set! ownerRow
    { compactRows[ownerRow]! with modelSlots := ownerCertificate.publicNames }
  state ← state.check "duplicate compact family certificates fail closed" <|
    compactRejected <| compactOrderedReport (compactRows.set! ownerRow
      { compactRows[ownerRow]! with families := #[ownerCertificate, ownerCertificate] })
  state ← state.check "misbound compact family certificates fail closed" <|
    compactRejected <| compactOrderedReport (compactRows.set! ownerRow
      { compactRows[ownerRow]! with owner := some `Wrong.Owner })
  state ← state.check "missing active compact family certificates fail closed" <|
    compactRejected <| compactOrderedReport (compactRows.set! ownerRow
      { compactRows[ownerRow]! with families := #[] })
  return some state

def checkIndexedStatementViews (owner : Name) (valid : Export)
    (state : TestState) : IO (Option TestState) := do
  let mut state := state
  state ← state.check "indexed one-family statements equal the aggregate checker" <|
    indexedFamilyStatements? valid owner == some (checkStatements valid)
  let treeOwners := ({} : Std.HashSet Name).insert owner
  state ← state.check "indexed nested generated view equals aggregate selection" <|
    indexedFamilyUnionFor valid treeOwners == checkStatementsFor valid treeOwners
  state ← state.check "compact nested generated view equals aggregate selection" <|
    compactIndexedStatementsFor valid treeOwners == checkStatementsFor valid treeOwners
  let invalidProjection := Naming.projectionName owner 99
  let duplicateInvalidProjection := insertBeforeOwner
    (insertBeforeOwner valid owner (.ax invalidProjection [] (.sort .zero) false))
    owner (.ax invalidProjection [] (.sort .zero) false)
  state ← state.check "compact projection extras retain duplicate order and multiplicity" <|
    compactIndexedStatementsFor duplicateInvalidProjection treeOwners ==
      checkStatementsFor duplicateInvalidProjection treeOwners
  state ← state.check "compact ordered report rejects duplicate declaration names" <|
    compactRejected (compactOrderedCheckReport duplicateInvalidProjection)
  return some state

def checkIslandOverlays (owner : Name) (raw valid : Export) (models : Array EDecl)
    (state : TestState) : IO (Option TestState) := do
  let mut state := state
  let treeOwners := ({} : Std.HashSet Name).insert owner
  let sourceIndex := SyntaxIndex.ofSource raw
  let .ok overlaidIndex := sourceIndex.prependRecords models | do
    IO.eprintln "checktest: valid island overlay was rejected"
    return none
  let overlaidFamilies := sourceIndex.sourceStatementFamilies owner
  let combinedView := { raw with decls := models ++ raw.decls }
  state ← state.check "island overlay exposes generated family occurrences" <|
    discoverWithIndex combinedView overlaidIndex == discover combinedView
  state ← state.check "persistent source index plus island overlay equals whole-export indexing" <|
    checkStatementFamiliesLocalWithIndex raw overlaidIndex overlaidFamilies ==
      checkStatementFamiliesLocalWithIndex valid (.ofExport valid)
        (statementFamiliesFor valid treeOwners)
  let retainedIndex := SyntaxIndex.ofSourceIncremental (overlayOwnershipSource raw)
  let retainedFamilies := retainedIndex.sourceStatementFamilies owner
  let expectedRetainedReport :=
    checkStatementFamiliesLocalWithIndex raw overlaidIndex overlaidFamilies
  state ← state.check "chained overlays preserve a retained large source index" <|
    match retainedIndex.prependRecords models with
    | .error _ => false
    | .ok overlay =>
      chainedOverlaysPreserveReport raw overlay retainedFamilies
        expectedRetainedReport models.size 32
  let duplicateIsland := models.push models[0]!
  state ← state.check "island overlay rejects duplicate declaration names" <|
    match sourceIndex.prependRecords duplicateIsland with
    | .error _ => true
    | .ok _ => false
  return some state

def checkModelSafety (owner carrier : Name) (valid : Export) (validOwnerDecl : Nat)
    (state : TestState) : IO (Option TestState) := do
  let mut state := state
  state ← state.check "unsafe owner may have an independently safe model" <|
    (check (withUnsafeOwner valid validOwnerDecl)).isEmpty
  let unsafeModel := withDefinitionSafety valid carrier "unsafe"
  state ← state.check "indexed family preserves corrupted statement diagnostics" <|
    indexedFamilyStatements? unsafeModel owner == some (checkStatements unsafeModel)
  state ← state.check "unsafe model implementation is rejected" <|
    (check unsafeModel).any
      (isSafetyMismatch owner carrier "unsafe")
  state ← state.check "compact ordered report retains local interface failures" <|
    compactMatches unsafeModel
  state ← state.check "partial model implementation is rejected" <|
    (check (withDefinitionSafety valid carrier "partial")).any
      (isSafetyMismatch owner carrier "partial")
  state ← state.check "axiom model implementation is rejected" <|
    (check (withImplementationAxiom valid carrier)).any
      (isKindMismatch owner carrier .defn .axiom)
  return some state

def checkEqUniverses (path : String) (raw : Export)
    (state : TestState) : IO (Option TestState) := do
  let mut state := state
  let eqOwner := `Eq
  let some rawEqDecl := ownerIndex? raw eqOwner | do
    IO.eprintln s!"checktest: {path} does not declare {eqOwner}"
    return none
  let some eqTable := correspondenceAt? raw rawEqDecl | do
    IO.eprintln s!"checktest: no correspondence table for {eqOwner}"
    return none
  let eqModels := modelDeclarations raw eqTable `Eq._model.helper
  let validEq := withValidModel raw rawEqDecl eqModels
  state ← state.check "universe parameters align positionally" <|
    (discover validEq).any (·.owner == eqOwner) &&
      (check validEq).all (·.familyOwner != eqOwner)
  state ← state.check "modeling Eq retains ambient equality" <|
    eqTable.iotas[0]?.bind (fun rule =>
      exportDeclarationType? validEq rule.name |>.map fun (_, type) =>
        match (forallBody type).getAppFn with
        | .const name _ => name == ``Eq
        | _ => false) |>.getD false
  return some state

def checkCarrierOrder (owner carrier : Name) (raw : Export) (rawOwnerDecl : Nat)
    (models : Array EDecl) (state : TestState) : IO (Option TestState) := do
  let mut state := state
  let late := withLateCarrier raw rawOwnerDecl models carrier
  let lateViolations := check late
  state ← state.check "carrier after owner is rejected" <|
    lateViolations.any (isLateCarrier owner carrier)
  return some state

def checkOwnerBackreferences (owner carrier : Name) (valid : Export)
    (validOwnerDecl : Nat) (table : Correspondence) (families : Array Family)
    (state : TestState) : IO (Option TestState) := do
  let mut state := state
  let constantBackref := withOwnerType valid validOwnerDecl (.const carrier [])
  state ← state.check "constant backreference is rejected" <|
    (check constantBackref).any (isBackreference owner carrier)
  state ← state.check "constant backreference survives a name-only owner certificate" <|
    ownerBackreferenceFromCertificate?
        (ownerReferenceCertificate constantBackref.decls[validOwnerDecl]!) families[0]!.names ==
      some (owner, carrier)
  state ← state.check "compact report retains constant backreferences" <|
    compactMatches constantBackref

  -- `Expr.getUsedConstants` does not include this name: it lives in the
  -- projection node's `typeName` field, so this pins the checker's explicit
  -- projection traversal.
  let some firstCtor := table.constructors[0]? | do
    IO.eprintln "checktest: Tree has no constructor correspondence"
    return none
  let projectionBackref :=
    withOwnerType valid validOwnerDecl (.proj firstCtor.model 0 (.bvar 0))
  state ← state.check "projection type-name public backreference is rejected" <|
    (check projectionBackref).any (isBackreference owner firstCtor.model)
  state ← state.check "projection backreference survives a name-only owner certificate" <|
    ownerBackreferenceFromCertificate?
        (ownerReferenceCertificate projectionBackref.decls[validOwnerDecl]!)
        families[0]!.names == some (owner, firstCtor.model)
  state ← state.check "compact report retains projection type-name backreferences" <|
    compactMatches projectionBackref
  return some state

def checkMissingSlots (owner carrier : Name) (valid : Export) (table : Correspondence)
    (state : TestState) : IO (Option TestState) := do
  let mut state := state
  let some firstCtor := table.constructors[0]? | do
    IO.eprintln "checktest: Tree has no constructor correspondence"
    return none
  let missingCtor := withoutDeclaration valid firstCtor.model
  state ← state.check "missing constructor slot is rejected" <|
    (check missingCtor).any (isMissing firstCtor.owner firstCtor.model)
  state ← state.check "compact ordered report retains missing slots" <|
    compactMatches missingCtor

  -- Constructor slots still claim the family when the carrier is missing,
  -- so exactness cannot disappear with the declaration it must diagnose.
  let missingCarrier := withoutDeclaration valid carrier
  state ← state.check "missing carrier slot is rejected" <|
    (check missingCarrier).any (isMissing owner carrier)
  return some state

def checkRecursorSlots (owner : Name) (valid : Export) (table : Correspondence)
    (state : TestState) : IO (Option TestState) := do
  let mut state := state
  let some firstRec := table.recursors[0]? | do
    IO.eprintln "checktest: Tree has no recursor correspondence"
    return none
  let some secondRec := table.recursors[1]? | do
    IO.eprintln "checktest: Tree has no second recursor correspondence"
    return none
  state ← state.check "missing recursor is rejected" <|
    (check (withoutDeclaration valid firstRec.model)).any
      (isMissing firstRec.owner firstRec.model)
  let some firstRecDecl := exportDeclaration? valid firstRec.model | do
    IO.eprintln "checktest: modeled recursor declaration missing"
    return none
  let duplicateRec := insertBeforeOwner valid owner firstRecDecl
  state ← state.check "extra recursor occurrence is rejected" <|
    (check duplicateRec).any (isDuplicate firstRec.owner firstRec.model)
  state ← state.check "compact ordered report rejects duplicate public slots" <|
    compactRejected (compactOrderedCheckReport duplicateRec)
  let some (_, firstRecType) := exportDeclarationType? valid firstRec.model | do
    IO.eprintln "checktest: modeled recursor type missing"
    return none
  let some (_, secondRecType) := exportDeclarationType? valid secondRec.model | do
    IO.eprintln "checktest: second modeled recursor type missing"
    return none
  let swappedRecs := withDeclarationType
    (withDeclarationType valid firstRec.model secondRecType) secondRec.model firstRecType
  state ← state.check "swapped recursors are rejected" <|
    (check swappedRecs).any (isTypeMismatch firstRec.owner firstRec.model) &&
      (check swappedRecs).any (isTypeMismatch secondRec.owner secondRec.model)
  let defeqRecType :=
    .letE `recType (.sort (.succ (.succ .zero))) firstRecType (.bvar 0) false
  state ← state.check "definitionally equal recursor syntax is rejected" <|
    (check (withDeclarationType valid firstRec.model defeqRecType)).any
      (isTypeMismatch firstRec.owner firstRec.model)
  return some state

def checkIotaSlots (owner : Name) (valid : Export) (table : Correspondence)
    (state : TestState) : IO (Option TestState) := do
  let mut state := state
  let some firstRec := table.recursors[0]? | do
    IO.eprintln "checktest: Tree has no recursor correspondence"
    return none
  let firstRules := table.iotas.filter (·.recursor == firstRec.owner)
  let some firstRule := firstRules[0]? | do
    IO.eprintln "checktest: Tree recursor has no first rule"
    return none
  let some secondRule := firstRules[1]? | do
    IO.eprintln "checktest: Tree recursor has no second rule"
    return none
  state ← state.check "missing iota theorem is rejected" <|
    (check (withoutDeclaration valid firstRule.name)).any
      (isMissing firstRule.recursor firstRule.name)
  state ← state.check "non-theorem iota proof slot is rejected" <|
    (check (withProofDefinition valid firstRule.name)).any
      (isKindMismatch firstRule.recursor firstRule.name .thm .defn)
  let some firstRuleDecl := exportDeclaration? valid firstRule.name | do
    IO.eprintln "checktest: first iota declaration missing"
    return none
  state ← state.check "extra iota occurrence is rejected" <|
    (check (insertBeforeOwner valid owner firstRuleDecl)).any
      (isDuplicate firstRule.recursor firstRule.name)
  let extraRuleName := Naming.iotaName firstRec.owner firstRules.size
  let extraRule := insertBeforeOwner valid owner
    (.ax extraRuleName [] (.sort .zero) false)
  state ← state.check "out-of-range iota theorem is rejected" <|
    (check extraRule).any (isExtraRule firstRec.owner extraRuleName)
  state ← state.check "compact ordered report recomputes extra rules" <|
    compactMatches extraRule
  let some (_, firstRuleType) := exportDeclarationType? valid firstRule.name | do
    IO.eprintln "checktest: first iota type missing"
    return none
  let some (_, secondRuleType) := exportDeclarationType? valid secondRule.name | do
    IO.eprintln "checktest: second iota type missing"
    return none
  let swappedRules := withDeclarationType
    (withDeclarationType valid firstRule.name secondRuleType) secondRule.name firstRuleType
  state ← state.check "swapped iota statements are rejected" <|
    (check swappedRules).any (isTypeMismatch firstRule.recursor firstRule.name) &&
      (check swappedRules).any (isTypeMismatch secondRule.recursor secondRule.name)
  let defeqRuleType := .letE `ruleType (.sort .zero) firstRuleType (.bvar 0) false
  state ← state.check "definitionally equal iota syntax is rejected" <|
    (check (withDeclarationType valid firstRule.name defeqRuleType)).any
      (isTypeMismatch firstRule.recursor firstRule.name)
  return some state

def checkExactNames (root : String) (owner modelRoot : Name) (valid : Export)
    (state : TestState) : IO (Option TestState) := do
  let mut state := state
  let legacySlot := Name.str modelRoot "ctor_99"
  let unrelatedLegacyName := insertBeforeOwner valid owner
    (.ax legacySlot [] (.sort (.succ .zero)) false)
  state ← state.check "legacy numbered name is not a public slot" <|
    (discover unrelatedLegacyName).all fun family => !family.names.contains legacySlot

  -- `IdxP.at_a` and `IdxP.at_b` have the same binder shape and differ only
  -- in their result indices.  Exact declaration-local names must prevent a
  -- type-shape heuristic from pairing them interchangeably.
  let shapesPath := s!"{root}/test/fixtures/inductive-models/prim_shapes.ndjson"
  let shapesText ← IO.FS.readFile shapesPath
  match InductiveModels.parse shapesText with
  | .error error =>
      IO.eprintln s!"checktest: could not parse {shapesPath}: {error}"
      state ← state.check "swapped equal-looking constructors" false
  | .ok shapes =>
    let idxOwner := `IdxP
    match ownerIndex? shapes idxOwner with
    | none => state ← state.check "swapped equal-looking constructors" false
    | some idxOwnerDecl =>
      match correspondenceAt? shapes idxOwnerDecl with
      | none => state ← state.check "swapped equal-looking constructors" false
      | some idxTable =>
        let idxModels := modelDeclarations shapes idxTable `IdxP._model.helper
        let idxValid := withValidModel shapes idxOwnerDecl idxModels
        match idxTable.constructors[0]?, idxTable.constructors[1]? with
        | some first, some second =>
          match exportDeclarationType? idxValid first.model,
              exportDeclarationType? idxValid second.model with
          | some (_, firstType), some (_, secondType) =>
            let swapped := withDeclarationType
              (withDeclarationType idxValid first.model secondType) second.model firstType
            state ← state.check "swapped equal-looking constructors" <|
              (check swapped).any (isTypeMismatch first.owner first.model) &&
                (check swapped).any (isTypeMismatch second.owner second.model)
          | _, _ => state ← state.check "swapped equal-looking constructors" false
        | _, _ => state ← state.check "swapped equal-looking constructors" false
  return some state

def checkRenamedOwners (owner carrier : Name) (raw valid : Export)
    (state : TestState) : IO (Option TestState) := do
  let mut state := state
  let some (_, carrierType) := exportDeclarationType? valid carrier | do
    IO.eprintln s!"checktest: no declaration for {carrier}"
    return none
  -- `let x : Type 1 := carrierType; x` is definitionally equal to the
  -- universe-free fixture's carrier type (`Type`) but not syntactically the
  -- same exported expression.
  let defeqCarrierType :=
    .letE `x (.sort (.succ (.succ .zero))) carrierType (.bvar 0) false
  let defeqCarrier := withDeclarationType valid carrier defeqCarrierType
  state ← state.check "definitionally equal carrier syntax is rejected" <|
    (check defeqCarrier).any (isTypeMismatch owner carrier)

  let modelNamedOwner := `Tree._model
  let modelNamedRaw := renameExportRoot raw owner modelNamedOwner
  let some modelNamedOwnerDecl := ownerIndex? modelNamedRaw modelNamedOwner | do
    IO.eprintln "checktest: renamed _model owner missing"
    return none
  let some modelNamedTable := correspondenceAt? modelNamedRaw modelNamedOwnerDecl | do
    IO.eprintln "checktest: renamed _model correspondence missing"
    return none
  let modelNamedModels := modelDeclarations modelNamedRaw modelNamedTable
    `Tree._model._model._impl.helper
  let modelNamedValid := withValidModel modelNamedRaw modelNamedOwnerDecl modelNamedModels
  state ← state.check "original _model component is preserved exactly" <|
    modelNamedTable.typeFormers[0]?.map (·.model) == some `Tree._model._model &&
      (discover modelNamedValid).any (·.owner == modelNamedOwner) &&
      (check modelNamedValid).isEmpty
  return some state

def checkPrivateAliases (owner : Name) (raw : Export)
    (state : TestState) : IO (Option TestState) := do
  let mut state := state
  let privateOwner := (`_private.CheckTest).mkNum 0 |>.str "Tree"
  let privateRaw := renameExportRoot raw owner privateOwner
  let some privateOwnerDecl := ownerIndex? privateRaw privateOwner | do
    IO.eprintln "checktest: private owner missing"
    return none
  let some privateTable := correspondenceAt? privateRaw privateOwnerDecl | do
    IO.eprintln "checktest: private correspondence missing"
    return none
  let privateModels := modelDeclarations privateRaw privateTable
    (Name.str (Naming.modelName privateOwner) "_impl")
  let privateValid := withValidModel privateRaw privateOwnerDecl privateModels
  state ← state.check "private originals retain raw correspondence names" <|
    privateTable.typeFormers[0]?.map (·.model) == some (Naming.modelName privateOwner) &&
      (discover privateValid).any (·.owner == privateOwner) &&
      (check privateValid).isEmpty
  let privateOwners := ({} : Std.HashSet Name).insert privateOwner
  state ← state.check "indexed private-alias family equals aggregate selection" <|
    indexedFamilyUnionFor privateValid privateOwners ==
      checkStatementsFor privateValid privateOwners
  state ← state.check "compact private-alias family equals aggregate selection" <|
    compactIndexedStatementsFor privateValid privateOwners ==
      checkStatementsFor privateValid privateOwners
  let privateSourceIndex := SyntaxIndex.ofSource privateRaw
  let .ok privateOverlay := privateSourceIndex.prependRecords privateModels | do
    IO.eprintln "checktest: private-alias island overlay was rejected"
    return none
  state ← state.check "private-alias island overlay equals whole-export indexing" <|
    checkStatementFamiliesLocalWithIndex privateRaw privateOverlay
        (privateSourceIndex.sourceStatementFamilies privateOwner) ==
      checkStatementFamiliesLocalWithIndex privateValid (.ofExport privateValid)
        (statementFamiliesFor privateValid privateOwners)
  return some state

def checkMutualMembers (root : String) (state : TestState) : IO (Option TestState) := do
  let mut state := state
  let mutualPath := s!"{root}/test/fixtures/inductive-models/mutual_shapes.ndjson"
  let mutualText ← IO.FS.readFile mutualPath
  match InductiveModels.parse mutualText with
  | .error error =>
      IO.eprintln s!"checktest: could not parse {mutualPath}: {error}"
      state ← state.check "valid exact mutual family" false
  | .ok mutualExport =>
    let some mutualOwnerDecl := ownerIndex? mutualExport `A | do
      IO.eprintln "checktest: mutual owner missing"
      return none
    let some mutualTable := correspondenceAt? mutualExport mutualOwnerDecl | do
      IO.eprintln "checktest: mutual correspondence missing"
      return none
    let mutualModels := modelDeclarations mutualExport mutualTable `A._model._impl.helper
    let mutualValid := withValidModel mutualExport mutualOwnerDecl mutualModels
    let mutualViolations := check mutualValid
    let bProjection := Naming.projectionName `B 0
    let bProjectionIota := Naming.projectionIotaName `B 0
    let mutualNonProjectionViolations := mutualViolations.filter fun violation =>
      match violation with
      | .missingPublic `B declaration =>
        declaration != bProjection && declaration != bProjectionIota
      | _ => true
    state ← state.check "mutual correspondence is declaration-local" <|
      mutualTable.typeFormers.any (fun pair =>
        pair.owner == `B && pair.model == Naming.modelName `B) &&
      mutualTable.constructors.any (fun pair =>
        pair.owner == `B.bC && pair.model == Naming.modelName `B.bC) &&
      mutualTable.recursors.any (fun pair =>
        pair.owner == `C.rec && pair.model == Naming.modelName `C.rec) &&
      mutualTable.iotas.any (fun rule =>
        rule.recursor == `C.rec && rule.ruleIndex == 2 &&
          rule.name == Naming.iotaName `C.rec 2)
    state ← state.check "valid exact mutual non-projection family" <|
      (discover mutualValid).any (fun family =>
        family.owner == `A && family.correspondence == mutualTable) &&
      mutualNonProjectionViolations.isEmpty
    let generatedMutualOwners := ({} : Std.HashSet Name).insert `A
    let mutualStatements := checkStatementsFor mutualValid generatedMutualOwners
    state ← state.check "mutual statement count uses the complete root family" <|
      mutualStatements.statementsChecked == mutualTable.statementCount
    state ← state.check "indexed mutual/member diagnostics equal aggregate selection" <|
      indexedFamilyUnionFor mutualValid generatedMutualOwners == mutualStatements
    state ← state.check "compact mutual/member diagnostics equal aggregate selection" <|
      compactIndexedStatementsFor mutualValid generatedMutualOwners == mutualStatements
    let mutualPublicNames := mutualTable.publicNames
    let missingMutualInterface : Export := { mutualValid with
      decls := mutualValid.decls.filter fun declaration =>
        !declaration.names.any mutualPublicNames.contains }
    let missingMutualStatements :=
      checkStatementsFor missingMutualInterface generatedMutualOwners
    state ← state.check "a generated family cannot disappear from discovery" <|
      missingMutualStatements.statementsChecked == mutualTable.statementCount &&
        missingMutualStatements.violations.any
          (isMissing `A (Naming.modelName `A))
    state ← state.check "indexed missing whole family equals aggregate selection" <|
      indexedFamilyUnionFor missingMutualInterface generatedMutualOwners ==
        missingMutualStatements
    state ← state.check "compact missing whole family equals aggregate selection" <|
      compactIndexedStatementsFor missingMutualInterface generatedMutualOwners ==
        missingMutualStatements
    let some bCtor := mutualTable.constructors.find? (·.owner == `B.bC) | do
      IO.eprintln "checktest: B.bC correspondence missing"
      return none
    state ← state.check "mutual diagnostic belongs to exact constructor" <|
      (check (withoutDeclaration mutualValid bCtor.model)).any
        (isMissing bCtor.owner bCtor.model)
    let wrongMutualConstructor := withDeclarationType mutualValid bCtor.model (.sort .zero)
    state ← state.check "root-selected statements retain member diagnostics" <|
      (checkStatementsFor wrongMutualConstructor generatedMutualOwners).violations.any
        (isTypeMismatch bCtor.owner bCtor.model)
  return some state

def checkUnitlikeMetadata (root : String) (state : TestState) : IO (Option TestState) := do
  let mut state := state
  let unitlikePath := s!"{root}/test/fixtures/inductive-models/unitlike.ndjson"
  let unitlikeText ← IO.FS.readFile unitlikePath
  match InductiveModels.parse unitlikeText with
  | .error error =>
      IO.eprintln s!"checktest: could not parse {unitlikePath}: {error}"
      state ← state.check "unit-like metadata fixture" false
  | .ok unitlikeExport =>
    for owner in [`UnitType, `UnitProp, `MU] do
      let some ownerDecl := ownerIndex? unitlikeExport owner | do
        IO.eprintln s!"checktest: unit-like owner {owner} missing"
        return none
      let some ownerTable := correspondenceAt? unitlikeExport ownerDecl | do
        IO.eprintln s!"checktest: unit-like correspondence for {owner} missing"
        return none
      let ownerModels := modelDeclarations unitlikeExport ownerTable
        (Name.str (Naming.modelName owner) "helper")
      let ownerValid := withValidModel unitlikeExport ownerDecl ownerModels
      state ← state.check s!"valid unit-like family {owner}" <|
        ownerTable.metadata.any (·.kind == .unitlike) && (check ownerValid).isEmpty
    -- Several indexed family reports share one SyntaxIndex.  Put a global
    -- extra-slot diagnostic on the last selected owner so concatenating the
    -- per-family reports has exactly the aggregate order and multiplicity.
    let mut multiValid := unitlikeExport
    let mut multiOwners : Std.HashSet Name := {}
    for owner in [`UnitType, `UnitProp] do
      let some ownerDecl := ownerIndex? multiValid owner | do return none
      let some ownerTable := correspondenceAt? multiValid ownerDecl | do return none
      multiValid := withValidModel multiValid ownerDecl
        (modelDeclarations multiValid ownerTable (Name.str (Naming.modelName owner) "helper"))
      multiOwners := multiOwners.insert owner
    let extraOwner := `WithField
    let extraName := Naming.unitlikeName extraOwner
    multiValid := insertBeforeOwner multiValid extraOwner
      (.ax extraName [] (.sort .zero) false)
    multiOwners := multiOwners.insert extraOwner
    state ← state.check "multi-family indexed union equals aggregate with one global extra" <|
      indexedFamilyUnionFor multiValid multiOwners ==
        checkStatementsFor multiValid multiOwners
    state ← state.check "compact global-extra templates equal aggregate with one global extra" <|
      compactIndexedStatementsFor multiValid multiOwners ==
        checkStatementsFor multiValid multiOwners
    let some mutualDecl := ownerIndex? unitlikeExport `MU | do return none
    let some mutualUnitlike := correspondenceAt? unitlikeExport mutualDecl | do return none
    state ← state.check "unit-like is per mutual member" <|
      (mutualUnitlike.metadata.filter (·.kind == .unitlike)).map (·.owner) == #[`MU, `MV]

    let some positiveDecl := ownerIndex? unitlikeExport `UnitType | do return none
    let some positiveTable := correspondenceAt? unitlikeExport positiveDecl | do return none
    let positiveModels := modelDeclarations unitlikeExport positiveTable `UnitType._model.helper
    let positiveValid := withValidModel unitlikeExport positiveDecl positiveModels
    let positiveTheorem := Naming.unitlikeName `UnitType
    state ← state.check "missing unit-like theorem is rejected" <|
      (check (withoutDeclaration positiveValid positiveTheorem)).any
        (isMissing `UnitType positiveTheorem)
    state ← state.check "malformed unit-like theorem is rejected" <|
      (check (withDeclarationType positiveValid positiveTheorem (.sort .zero))).any
        (isTypeMismatch `UnitType positiveTheorem)

    for owner in [`WithField, `Indexed, `Recursive, `TwoCtor, `MR] do
      let some nearDecl := ownerIndex? unitlikeExport owner | do return none
      let some nearTable := correspondenceAt? unitlikeExport nearDecl | do return none
      state ← state.check s!"near miss has no unit-like slot {owner}" <|
        (nearTable.metadata.filter (·.kind == .unitlike)).isEmpty
      let nearModels := modelDeclarations unitlikeExport nearTable
        (Name.str (Naming.modelName owner) "helper")
      let extraName := Naming.unitlikeName owner
      let extra := withValidModel unitlikeExport nearDecl
        (nearModels.push (.ax extraName [] (.sort .zero) false))
      state ← state.check s!"extra unit-like theorem rejected {owner}" <|
        (check extra).any (isExtraUnitlike owner extraName)
      if owner == `WithField then
        let bareExtra := insertBeforeOwner unitlikeExport owner
          (.ax extraName [] (.sort .zero) false)
        let extraOwners := ({} : Std.HashSet Name).insert owner
        state ← state.check "bare extra unit-like theorem is rejected" <|
          (check bareExtra).any (isExtraUnitlike owner extraName)
        state ← state.check "indexed extra-slot sweep equals aggregate selection" <|
          indexedFamilyUnionFor bareExtra extraOwners ==
            checkStatementsFor bareExtra extraOwners
        state ← state.check "compact bare extra-slot sweep equals aggregate selection" <|
          compactIndexedStatementsFor bareExtra extraOwners ==
            checkStatementsFor bareExtra extraOwners
  return some state

/-- Build the shared `Tree` baseline and run every group of checks against it,
stopping at the first group whose fixture preconditions fail. -/
def run (root : String) : IO UInt32 := do
  let path := s!"{root}/test/fixtures/inductive-models/nested_iota_arm.ndjson"
  let text ← IO.FS.readFile path
  match InductiveModels.parse text with
  | .error error =>
      IO.eprintln s!"checktest: could not parse {path}: {error}"
      return 1
  | .ok raw =>
    let owner := `Tree
    let modelRoot := Naming.modelName owner
    let carrier := Naming.modelName owner
    let helper := `Tree._model._impl.helper
    let some rawOwnerDecl := ownerIndex? raw owner | do
      IO.eprintln s!"checktest: {path} does not declare {owner}"
      return 1
    let some table := correspondenceAt? raw rawOwnerDecl | do
      IO.eprintln s!"checktest: no correspondence table for {owner}"
      return 1
    let models := modelDeclarations raw table helper

    let valid := withValidModel raw rawOwnerDecl models
    let validOwnerDecl := rawOwnerDecl + models.size
    let families := discover valid
    let some state ← checkDiscovery valid families {} | return 1
    let some state ← checkGlobalExtraRecords state | return 1
    let some state ← checkFamilyIdentity owner modelRoot carrier helper table models
      validOwnerDecl families state | return 1
    let some state ← checkValidReport valid state | return 1
    let some state ← checkCompactCertificates owner valid state | return 1
    let some state ← checkIndexedStatementViews owner valid state | return 1
    let some state ← checkIslandOverlays owner raw valid models state | return 1
    let some state ← checkModelSafety owner carrier valid validOwnerDecl state | return 1
    let some state ← checkEqUniverses path raw state | return 1
    let some state ← checkCarrierOrder owner carrier raw rawOwnerDecl models state | return 1
    let some state ← checkOwnerBackreferences owner carrier valid validOwnerDecl table
      families state | return 1
    let some state ← checkMissingSlots owner carrier valid table state | return 1
    let some state ← checkRecursorSlots owner valid table state | return 1
    let some state ← checkIotaSlots owner valid table state | return 1
    let some state ← checkExactNames root owner modelRoot valid state | return 1
    let some state ← checkRenamedOwners owner carrier raw valid state | return 1
    let some state ← checkPrivateAliases owner raw state | return 1
    let some state ← checkMutualMembers root state | return 1
    let some state ← checkUnitlikeMetadata root state | return 1

    if state.failed == 0 then
      IO.println s!"checktest: {state.passed} tests passed"
      return 0
    else
      IO.eprintln s!"checktest: {state.failed} failed, {state.passed} passed"
      return 1

def main (args : List String) : IO UInt32 :=
  match args with
  | "--overlay-ownership-probe" :: rest =>
      runOverlayOwnershipProbe (rest.head?.getD ".")
  | _ => run (args.head?.getD ".")
