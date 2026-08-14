import InductiveModels.Driver

open Lean Meta InductiveModels

def shadowGeneration : Cli.Config :=
  { nested := true, mutualModels := true, simple := true, basic := true }

def readFixture (path : String) : IO Export := do
  let .ok parsed := parse (← IO.FS.readFile path) (analyse := false)
    | throw <| IO.userError s!"cannot parse {path}"
  return parsed

def runFixture (collectShadow : Bool) :
    IO ((Array EDecl × Report) × Array FamilyAdapter.ShadowObservation × Array String) := do
  let input ← readFixture "test/fixtures/inductive-models/nested_iota.ndjson"
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
    observation.coverage.constructors.all (fun key =>
      !key.owner.owner.isAnonymous && !key.constructor.isAnonymous) &&
    observation.coverage.rules.all (fun key =>
      !key.recursorOwner.owner.isAnonymous && !key.recursor.isAnonymous &&
        !key.constructor.constructor.isAnonymous) &&
    observation.coverage.occurrences.all (fun key =>
      !key.constructor.constructor.isAnonymous && !key.target.owner.isAnonymous)

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (plain, plainShadows, plainMessages) ← runFixture false
  let (observed, shadows, observedMessages) ← runFixture true
  let sameResult := plain == observed
  let outputQuiet := plainMessages.isEmpty && observedMessages.isEmpty && plainShadows.isEmpty
  let everyAcceptedFamilyRan := shadows.size == observed.2.generated.size
  let keyedReportVisible := shadows.all observationIsKeyed
  let everyShadowComplete := shadows.all (·.complete)
  if sameResult && outputQuiet && everyAcceptedFamilyRan && keyedReportVisible &&
      everyShadowComplete then
    IO.println s!"family adapter shadow: {shadows.size} accepted families, output unchanged"
    return 0
  IO.eprintln s!"family adapter shadow failure: same={sameResult}, quiet={outputQuiet}, \
    shadows={shadows.size}, generated={observed.2.generated.size}, keyed={keyedReportVisible}, \
    complete={everyShadowComplete}"
  for message in plainMessages ++ observedMessages do IO.eprintln message
  for shadow in shadows do IO.eprintln (repr shadow)
  return 1
