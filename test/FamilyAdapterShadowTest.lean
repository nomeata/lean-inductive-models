import InductiveModels.Driver

open Lean Meta InductiveModels

def shadowGeneration : Cli.Config :=
  { nested := true, mutualModels := true, simple := true, basic := true }

def readFixture (path : String) : IO Export := do
  let .ok parsed := parse (← IO.FS.readFile path)
    | throw <| IO.userError s!"cannot parse {path}"
  return parsed

def runFixture (path : String) (collectShadow : Bool) :
    IO ((Array EDecl × Report) × Array FamilyAdapter.ShadowObservation × Array String) := do
  let input ← readFixture path
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<family-adapter-shadow-test>", fileMap := default,
      options := {}, maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, state) ← Core.CoreM.toIO
    (MetaM.run' do
      if collectShadow then
        let (declarations, report, shadows) ←
          runFilterWithFamilyAdapterShadow input false shadowGeneration
        return ((declarations, report), shadows)
      else
        return (← runFilter input false shadowGeneration, #[])) context { env }
  let messages ← state.messages.toArray.mapM (·.toString)
  return (result.1, result.2, messages)

def runFixtureTagged (stage path : String) (collectShadow : Bool) := do
  try runFixture path collectShadow
  catch exception => throw <| IO.userError s!"{stage}: {exception}"

/-- An exact source block paired with an intentionally absent public/private
interface.  The shadow must preserve the source keys in its reasons while
excluding every result that depends on the unresolved carrier or recursor. -/
def runMalformedInterface : IO FamilyAdapter.ShadowObservation := do
  let env ← importModules #[`Init] {}
  let context : Core.Context :=
    { fileName := "<family-adapter-malformed-interface-test>", fileMap := default,
      options := {}, maxHeartbeats := 0, maxRecDepth := 8192 }
  let (observation, _) ← Core.CoreM.toIO
    (MetaM.run' do
      let source ← indEDecl #[`Nat]
      let .induct _ constructors _ := source | unreachable!
      let constructorNames := constructors.toArray.map fun constructor =>
        (constructor.name, constructor.name)
      let malformed : Iso :=
        { decls := #[], levelParams := [], members := #[`Nat], selfNames := #[],
          numAll := 1, ctors := constructorNames, recs := #[], iotas := #[], spliced := #[] }
      return (← FamilyAdapter.deriveShadowPlan source malformed).observe) context { env }
  return observation

def observationIsKeyed (observation : FamilyAdapter.ShadowObservation) : Bool :=
  !observation.root.isAnonymous &&
    observation.coverage.members.all (fun key => !key.owner.isAnonymous) &&
    observation.coverage.recursors.all (fun recursor => !recursor.isAnonymous) &&
    observation.coverage.constructors.all (fun key =>
      !key.owner.owner.isAnonymous && !key.constructor.isAnonymous) &&
    observation.coverage.rules.all (fun key =>
      !key.recursorOwner.owner.isAnonymous && !key.recursor.isAnonymous &&
        !key.constructor.constructor.isAnonymous) &&
    observation.coverage.occurrences.all (fun key =>
      !key.constructor.constructor.isAnonymous && !key.target.owner.isAnonymous) &&
    observation.coverage.containerMaps.all (fun key =>
      !key.constructor.constructor.isAnonymous && !key.target.owner.isAnonymous)

def hasOnlyExplicitGaps (observation : FamilyAdapter.ShadowObservation) : Bool :=
  observation.complete || observation.reasons.all fun
    | .unrepresentedSourceRecursor recursor => !recursor.isAnonymous
    | .missingMinorHypothesis constructor _ => !constructor.constructor.isAnonymous
    | .minorHypothesisMismatch rule => !rule.recursor.isAnonymous
    | .malformedMinorTelescope rule => !rule.recursor.isAnonymous
    | _ => false

def multipleSitesShareExactHypothesis (shadows : Array FamilyAdapter.ShadowObservation) : Bool :=
  match shadows.find? (·.root == `Both) with
  | none => false
  | some both =>
    let occurrences := both.coverage.occurrences.filter fun occurrence =>
      occurrence.constructor.constructor == `Both.obj && occurrence.fieldIndex == 0
    match occurrences[0]? with
    | none => false
    | some first =>
      occurrences.size >= 2 && occurrences.all (·.hypothesisIndex == first.hypothesisIndex)

/-- The nested `List Tree` recursor is represented by its exact source rule
sequence. This pins the real-constructor side of the mimic association rather
than accepting a shadow that merely noticed the extra recursor. -/
structure SpecialisationDiagnostics where
  treeRules : Bool := false
  treeMap : Bool := false
  treeClean : Bool := false
  treeNodeCallable : Bool := false
  treeDistinct : Bool := false
  btreeBoxRules : Bool := false
  btreeListRules : Bool := false
  btreeMap : Bool := false
  btreeClean : Bool := false
  btreeTagCallable : Bool := false
  btreeDistinct : Bool := false
  ptMap : Bool := false
  ptClean : Bool := false
  deriving Repr

def SpecialisationDiagnostics.all (diagnostics : SpecialisationDiagnostics) : Bool :=
  diagnostics.treeRules && diagnostics.treeMap && diagnostics.treeClean &&
    diagnostics.treeNodeCallable && diagnostics.treeDistinct &&
    diagnostics.btreeBoxRules && diagnostics.btreeListRules && diagnostics.btreeMap &&
    diagnostics.btreeClean && diagnostics.btreeTagCallable && diagnostics.btreeDistinct &&
    diagnostics.ptMap && diagnostics.ptClean

def listSpecialisationDiagnostics (shadows : Array FamilyAdapter.ShadowObservation) :
    SpecialisationDiagnostics :=
  let covered := fun (observation : FamilyAdapter.ShadowObservation) recursor expected =>
    observation.containerRecursorRules.filterMap (fun rule =>
      if rule.recursor.publicRecursor == recursor then some rule.publicConstructor else none) ==
        expected
  let clean := fun owner wrappers (observation : FamilyAdapter.ShadowObservation) =>
    observation.reasons.all fun
      | .missingInstalledContainerRecursor _ recursor => !wrappers.contains recursor
      | .unrepresentedSourceRecursor recursor => !wrappers.contains recursor
      | .installedRuleMismatch rule _ => rule.recursorOwner.owner != owner
      | .invalidContainerRecursorAssociation key => key.target.owner != owner
      | .invalidPlan _ => false
      | _ => true
  let mapped := fun owner (observation : FamilyAdapter.ShadowObservation) =>
    observation.coverage.containerMaps.any (·.target.owner == owner)
  let callableRuleClean := fun constructor (observation : FamilyAdapter.ShadowObservation) =>
    !observation.reasons.any fun
      | .installedRuleMismatch rule _ => rule.constructor.constructor == constructor
      | _ => false
  let distinct := fun recursor (observation : FamilyAdapter.ShadowObservation) =>
    observation.distinctContainerRecursors.any (·.publicRecursor == recursor)
  match shadows.find? (·.root == `Tree), shadows.find? (·.root == `BTree),
      shadows.find? (·.root == `PT) with
  | some tree, some btree, some pt =>
    { treeRules := covered tree `Tree.rec_1 #[`List.nil, `List.cons]
      treeMap := mapped `Tree tree
      treeClean := clean `Tree #[`Tree.rec_1, `Tree.rec_1._model] tree
      treeNodeCallable := callableRuleClean `Tree.node tree
      treeDistinct := distinct `Tree.rec_1 tree
      btreeBoxRules := covered btree `BTree.rec_1 #[`Box.mk]
      btreeListRules := covered btree `BTree.rec_2 #[`List.nil, `List.cons]
      btreeMap := mapped `BTree btree
      btreeClean := clean `BTree #[`BTree.rec_1, `BTree.rec_1._model,
        `BTree.rec_2, `BTree.rec_2._model] btree
      btreeTagCallable := callableRuleClean `BTree.tag btree
      btreeDistinct := distinct `BTree.rec_1 btree && distinct `BTree.rec_2 btree
      ptMap := mapped `PT pt
      ptClean := clean `PT #[`PT.rec_1, `PT.rec_1._model] pt }
  | _, _, _ => {}

/-- `OK` occurs in a container parameter but is not recursive at that field;
the exact ERec minor therefore supplies no IH and no occurrence is recorded. -/
def nonrecursiveParameterMentionExcluded
    (shadows : Array FamilyAdapter.ShadowObservation) : Bool :=
  let root := Name.mkNum `OK._model._impl 0
  let owner := Name.mkNum `OK._model._impl 1
  match shadows.find? (·.root == root) with
  | none => false
  | some ok =>
    !ok.reasons.any (fun
      | .missingMinorHypothesis constructor fieldIndex =>
        constructor.owner.owner == owner && fieldIndex == 2
      | .minorHypothesisMismatch rule =>
        rule.constructor.owner.owner == owner
      | _ => false) &&
    !ok.coverage.occurrences.any fun occurrence =>
      occurrence.constructor.owner.owner == owner && occurrence.fieldIndex == 2

def malformedDependenciesAreExcluded (observation : FamilyAdapter.ShadowObservation) : Bool :=
  let missingMember := fun side => observation.reasons.any fun
    | .missingInterfaceMember member actual => member.owner == `Nat && actual == side
    | _ => false
  let missingRecursor := fun side => observation.reasons.any fun
    | .missingInterfaceRecursor member actual => member.owner == `Nat && actual == side
    | _ => false
  missingMember .privateModel && missingMember .publicModel &&
    missingRecursor .privateModel && missingRecursor .publicModel &&
    observation.coverage.members.isEmpty && observation.coverage.recursors.isEmpty &&
    observation.coverage.rules.isEmpty && observation.coverage.occurrences.isEmpty

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let nestedPath := "test/fixtures/inductive-models/nested_iota.ndjson"
  let familyPath := "test/fixtures/inductive-models/nest_fam_arg.ndjson"
  let (plain, plainShadows, plainMessages) ←
    runFixtureTagged "nested/plain" nestedPath false
  let (observed, shadows, observedMessages) ←
    runFixtureTagged "nested/shadow" nestedPath true
  let (familyPlain, _, familyPlainMessages) ←
    runFixtureTagged "family/plain" familyPath false
  let (familyObserved, familyShadows, familyObservedMessages) ←
    runFixtureTagged "family/shadow" familyPath true
  let malformed ← runMalformedInterface
  let sameResult := plain == observed
    && familyPlain == familyObserved
  let outputQuiet := (plainMessages ++ observedMessages ++ familyPlainMessages ++
    familyObservedMessages).isEmpty && plainShadows.isEmpty
  let everyAcceptedFamilyRan := shadows.size == observed.2.generated.size &&
    familyShadows.size == familyObserved.2.generated.size
  let keyedReportVisible := (shadows ++ familyShadows).all observationIsKeyed
  let everyOutcomeExplicit := (shadows ++ familyShadows).all hasOnlyExplicitGaps
  let nestedGapVisible := (shadows ++ familyShadows).any fun shadow => !shadow.complete
  let exactHypothesisSharing := multipleSitesShareExactHypothesis familyShadows
  let specialisations := listSpecialisationDiagnostics shadows
  let listRuleAssociation := specialisations.all
  let nonrecursiveMention := nonrecursiveParameterMentionExcluded familyShadows
  let containerMapsVisible := (shadows ++ familyShadows).any
    (fun shadow => !shadow.coverage.containerMaps.isEmpty)
  let malformedRejected := malformedDependenciesAreExcluded malformed
  if sameResult && outputQuiet && everyAcceptedFamilyRan && keyedReportVisible &&
      everyOutcomeExplicit && nestedGapVisible && exactHypothesisSharing && containerMapsVisible &&
      listRuleAssociation && nonrecursiveMention && malformedRejected then
    IO.println s!"family adapter shadow: {shadows.size + familyShadows.size} accepted families, \
      exact gaps reported, output unchanged"
    return 0
  IO.eprintln s!"family adapter shadow failure: same={sameResult}, quiet={outputQuiet}, \
    shadows={shadows.size + familyShadows.size}, keyed={keyedReportVisible}, \
    explicit={everyOutcomeExplicit}, gaps={nestedGapVisible}, hypotheses={exactHypothesisSharing}, \
    listRules={listRuleAssociation}, listDetails={repr specialisations}, \
    nonrecursiveMention={nonrecursiveMention}, containers={containerMapsVisible}, \
    malformed={malformedRejected}"
  for message in plainMessages ++ observedMessages ++ familyPlainMessages ++ familyObservedMessages do
    IO.eprintln message
  for shadow in shadows ++ familyShadows do
    unless shadow.complete do
      IO.eprintln s!"{shadow.root}: {repr shadow.reasons}"
      for diagnostic in shadow.diagnostics do IO.eprintln s!"{shadow.root}: {diagnostic}"
  unless malformedRejected do IO.eprintln s!"malformed Nat: {repr malformed}"
  return 1
