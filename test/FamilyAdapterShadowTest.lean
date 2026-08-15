import InductiveModels.Driver

open Lean Meta InductiveModels

def shadowGeneration : Cli.Config :=
  { nested := true, mutualModels := true, simple := true, basic := true }

def readFixture (path : String) : IO Export := do
  let .ok parsed := parse (← IO.FS.readFile path) (analyse := false)
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
  let containerMapsVisible := (shadows ++ familyShadows).any
    (fun shadow => !shadow.coverage.containerMaps.isEmpty)
  let malformedRejected := malformedDependenciesAreExcluded malformed
  if sameResult && outputQuiet && everyAcceptedFamilyRan && keyedReportVisible &&
      everyOutcomeExplicit && nestedGapVisible && exactHypothesisSharing && containerMapsVisible &&
      malformedRejected then
    IO.println s!"family adapter shadow: {shadows.size + familyShadows.size} accepted families, \
      exact gaps reported, output unchanged"
    return 0
  IO.eprintln s!"family adapter shadow failure: same={sameResult}, quiet={outputQuiet}, \
    shadows={shadows.size + familyShadows.size}, keyed={keyedReportVisible}, \
    explicit={everyOutcomeExplicit}, gaps={nestedGapVisible}, hypotheses={exactHypothesisSharing}, \
    containers={containerMapsVisible}, malformed={malformedRejected}"
  for message in plainMessages ++ observedMessages ++ familyPlainMessages ++ familyObservedMessages do
    IO.eprintln message
  for shadow in shadows ++ familyShadows do
    unless shadow.complete do IO.eprintln s!"{shadow.root}: {repr shadow.reasons}"
  unless malformedRejected do IO.eprintln s!"malformed Nat: {repr malformed}"
  return 1
