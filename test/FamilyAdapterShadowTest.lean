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

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let nestedPath := "test/fixtures/inductive-models/nested_iota.ndjson"
  let familyPath := "test/fixtures/inductive-models/nest_fam_arg.ndjson"
  let (plain, plainShadows, plainMessages) ← runFixture nestedPath false
  let (observed, shadows, observedMessages) ← runFixture nestedPath true
  let (familyPlain, _, familyPlainMessages) ← runFixture familyPath false
  let (familyObserved, familyShadows, familyObservedMessages) ← runFixture familyPath true
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
  if sameResult && outputQuiet && everyAcceptedFamilyRan && keyedReportVisible &&
      everyOutcomeExplicit && nestedGapVisible && exactHypothesisSharing then
    IO.println s!"family adapter shadow: {shadows.size + familyShadows.size} accepted families, \
      exact gaps reported, output unchanged"
    return 0
  IO.eprintln s!"family adapter shadow failure: same={sameResult}, quiet={outputQuiet}, \
    shadows={shadows.size + familyShadows.size}, keyed={keyedReportVisible}, \
    explicit={everyOutcomeExplicit}, gaps={nestedGapVisible}, hypotheses={exactHypothesisSharing}"
  for message in plainMessages ++ observedMessages ++ familyPlainMessages ++ familyObservedMessages do
    IO.eprintln message
  for shadow in shadows ++ familyShadows do
    unless shadow.complete do IO.eprintln s!"{shadow.root}: {repr shadow.reasons}"
  return 1
