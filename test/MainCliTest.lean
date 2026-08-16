import InductiveModels.Check
import InductiveModels.Naming
import InductiveModels.Output

set_option maxRecDepth 4096

/-!
End-to-end tests for the public `lean-inductive-models` process boundary.

These deliberately execute the built binary: parser-only tests cannot observe
the stdout/stderr split, output suppression, pass ordering, or transactional
output behavior.
-/

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then
    { state with passed := state.passed + 1 }
  else
    { state with failed := state.failed.push label }

def defaultInductiveModelsEnv : Array (String × Option String) :=
  #[("LEAN_INDUCTIVE_MODELS_LEGACY_OUTPUT", none),
    ("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", none),
    ("LEAN_INDUCTIVE_MODELS_PLANNER_LEVEL_TRACE", none)]

def runInductiveModelsWithEnv (binary : String) (args : List String)
    (env : Array (String × Option String)) (input? : Option String := none) :
    IO IO.Process.Output :=
  IO.Process.output {
    cmd := binary
    args := args.toArray
    env := defaultInductiveModelsEnv ++ env } input?

def runInductiveModels (binary : String) (args : List String) (input? : Option String := none) :
    IO IO.Process.Output :=
  runInductiveModelsWithEnv binary args #[] input?

def runInductiveModelsLegacy (binary : String) (args : List String)
    (input? : Option String := none) : IO IO.Process.Output :=
  runInductiveModelsWithEnv binary args #[("LEAN_INDUCTIVE_MODELS_LEGACY_OUTPUT", some "1")] input?

def runInductiveModelsAt (binary : String) (args : List String) (cwd : String)
    (env : Array (String × Option String) := #[]) :
    IO IO.Process.Output :=
  IO.Process.output {
    cmd := binary
    args := args.toArray
    cwd := some cwd
    env := defaultInductiveModelsEnv ++ env }

def runInductiveModelsStdin (binary : String) (args : List String) (input : String) :
    IO IO.Process.Output :=
  runInductiveModels binary args (some input)

def hasDiagnostic (stderr diagnostic : String) : Bool :=
  (stderr.splitOn "\n").contains diagnostic

def familyCount? (text : String) : Option Nat := do
  let parsed ← (InductiveModels.parse text).toOption
  return (InductiveModels.Check.discover parsed).size

def sameSemanticExport (left right : String) : Bool :=
  match InductiveModels.parse left, InductiveModels.parse right with
  | .ok left, .ok right => left.metaLine == right.metaLine && left.decls == right.decls
  | _, _ => false

def removeIfPresent (path : System.FilePath) : IO Unit := do
  try IO.FS.removeFile path
  catch
    | .noFileOrDirectory .. => pure ()
    | error => throw error

def hasOutputSibling (directory : System.FilePath) : IO Bool := do
  return (← directory.readDir).any fun entry =>
    entry.fileName.startsWith ".lean-inductive-models-output-" && entry.fileName.endsWith ".tmp"

def sameDirectoryEntries (left right : Array IO.FS.DirEntry) : Bool :=
  left.size == right.size && left.all fun entry =>
    right.any (·.fileName == entry.fileName)

def mapInductiveType (inputExport : InductiveModels.Export) (target : Lean.Name)
    (f : InductiveModels.EIndType → InductiveModels.EIndType) : InductiveModels.Export :=
  { inputExport with decls := inputExport.decls.map fun declaration => match declaration with
    | .induct types constructors recursors =>
      .induct (types.map fun type => if type.name == target then f type else type)
        constructors recursors
    | other => other }

def mapConstructor (inputExport : InductiveModels.Export) (target : Lean.Name)
    (f : InductiveModels.ECtor → InductiveModels.ECtor) : InductiveModels.Export :=
  { inputExport with decls := inputExport.decls.map fun declaration => match declaration with
    | .induct types constructors recursors =>
      .induct types
        (constructors.map fun constructor =>
          if constructor.name == target then f constructor else constructor)
        recursors
    | other => other }

def mapRecursor (inputExport : InductiveModels.Export) (target : Lean.Name)
    (f : InductiveModels.ERec → InductiveModels.ERec) : InductiveModels.Export :=
  { inputExport with decls := inputExport.decls.map fun declaration => match declaration with
    | .induct types constructors recursors =>
      .induct types constructors
        (recursors.map fun recursor => if recursor.name == target then f recursor else recursor)
    | other => other }

def reverseConstructorsFor (inputExport : InductiveModels.Export) (target : Lean.Name) : InductiveModels.Export :=
  { inputExport with decls := inputExport.decls.map fun declaration => match declaration with
    | .induct types constructors recursors =>
      if types.any (·.name == target) then .induct types constructors.reverse recursors
      else declaration
    | other => other }

/-- The committed fixtures the complete tool declines (exit 2).  Every other
fixture in the sweep below is expected to be accepted (exit 0), so this one
list pins the disposition of all of them. -/
def sweepDeclinedFixtures : Array String :=
  #["e_dependent_field.ndjson", "maybe_zero_pad.ndjson", "prim_shape_declines.ndjson"]

def main (args : List String) : IO UInt32 := do
  let root := args.head?.getD "."
  let binary := s!"{root}/.lake/build/bin/lean-inductive-models"
  unless ← System.FilePath.pathExists binary do
    IO.eprintln s!"mainclitest: missing {binary}; run `lake build lean-inductive-models` first"
    return 1

  let scratch := s!"{root}/_tmp"
  IO.FS.createDirAll scratch
  let nested := s!"{root}/test/fixtures/inductive-models/nested_iota.ndjson"
  let nestedText ← IO.FS.readFile nested
  let .ok nestedExport := InductiveModels.parse nestedText | do
    IO.eprintln "mainclitest: nested fixture did not parse"
    return 1
  let mut state : TestState := {}

  -- A kernel-valid declaration under a reserved basis name is unsupported
  -- unless its complete exported family is canonical. Recursor metadata is
  -- not consumed by `Declaration.inductDecl`, so this pins exit 2 rather than
  -- a kernel/internal exit 1.
  let unusedBasis := { nestedExport with decls := nestedExport.decls.filter (·.names.contains `Eq) }
  let malformedBasis := mapRecursor unusedBasis `Eq.rec fun recursor =>
    { recursor with numMinors := recursor.numMinors + 1 }
  let malformedBasisRun ← runInductiveModelsStdin binary
    ["--no-check", "--no-type-check-generated", "--no-output", "-"]
    malformedBasis.render
  state := state.check "noncanonical unused basis exits unsupported 2" <|
    malformedBasisRun.exitCode == 2 && malformedBasisRun.stdout.isEmpty &&
      (malformedBasisRun.stderr.splitOn "input's Eq is not Lean's").length > 1

  -- The Arena CI path exercises the complete tool: all generation branches,
  -- both structural checks, the input kernel gate, and the generated-island
  -- kernel gate. A
  -- checker can receive its NDJSON path as `$IN`, or read the same bytes from
  -- stdin; `--no-output` suppresses only publication.
  let arenaPath ← runInductiveModels binary [
    "--inductives", "--check-input", "--check-output", "--type-check-input",
    "--type-check-generated", "--no-output", nested]
  state := state.check "arena path generates models and validates input and output" <|
    arenaPath.exitCode == 0 && arenaPath.stdout.isEmpty &&
      hasDiagnostic arenaPath.stderr "input check: 0 model families checked" &&
      arenaPath.stderr.contains "model of" && arenaPath.stderr.contains "output check:" &&
      !arenaPath.stderr.contains "output check: 0 model families checked" &&
      hasDiagnostic arenaPath.stderr "input kernel check: accepted" &&
      hasDiagnostic arenaPath.stderr "generated kernel check: accepted"
  let arenaStdin ← runInductiveModelsStdin binary [
    "--inductives", "--check-input", "--check-output", "--type-check-input",
    "--type-check-generated", "--no-output", "-"] nestedText
  state := state.check "arena stdin runs the same complete pipeline" <|
    arenaStdin.exitCode == 0 && arenaStdin.stdout.isEmpty &&
      arenaStdin.stderr.contains "model of" && arenaStdin.stderr.contains "output check:" &&
      hasDiagnostic arenaStdin.stderr "input kernel check: accepted" &&
      hasDiagnostic arenaStdin.stderr "generated kernel check: accepted"

  -- Input stream order is checked online without constructing a dependency
  -- graph: once an owner has appeared, a later public model slot is too late.
  let modelCycleName := InductiveModels.Naming.modelName `Tree
  let modelCycle : InductiveModels.EDecl :=
    .ax modelCycleName [] (.const `Tree []) false
  let modelCycleText := { nestedExport with decls := nestedExport.decls.push modelCycle }.render
  let arenaModelCycle ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--type-check-generated",
    "--no-output", "-"] modelCycleText
  state := state.check "online input guard rejects a model after its owner" <|
    arenaModelCycle.exitCode == 1 && arenaModelCycle.stdout.isEmpty &&
      arenaModelCycle.stderr.contains "is not before Tree at record"
  let uncheckedModelCycle ← runInductiveModelsStdin binary [
    "--no-check", "--no-type-check-generated", "--no-output", "-"] modelCycleText
  state := state.check "in-memory input guard rejects a model after its owner" <|
    uncheckedModelCycle.exitCode == 1 && uncheckedModelCycle.stdout.isEmpty &&
      uncheckedModelCycle.stderr.contains "is not before Tree at record"

  let uncheckedOutput ← runInductiveModelsWithEnv binary
    ["--no-check", "--no-type-check-generated", "--no-output", nested]
    #[("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")]
  state := state.check "in-memory output-check-off bypasses the generated kernel gate" <|
    uncheckedOutput.exitCode == 0 && uncheckedOutput.stdout.isEmpty &&
      uncheckedOutput.stderr.contains "model of" &&
      hasDiagnostic uncheckedOutput.stderr "output backend: compact-discard" &&
      hasDiagnostic uncheckedOutput.stderr "generated kernel checks: 0"

  let badName := `ArenaBad
  let badDeclaration : InductiveModels.EDecl :=
    .defn badName [] (.sort .zero) (.sort .zero) .opaque "safe" [badName]
  let invalidExport := { nestedExport with decls := nestedExport.decls.push badDeclaration }
  let invalidText := invalidExport.render
  let invalidPath := s!"{scratch}/main-cli-invalid.ndjson"
  IO.FS.writeFile invalidPath invalidText
  let invalidInput ← runInductiveModels binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", invalidPath]
  state := state.check "kernel-invalid path input is rejected with exit 1" <|
    invalidInput.exitCode == 1 &&
      (invalidInput.stderr.splitOn "input kernel check rejected:").length > 1
  let invalidNeither ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--no-type-check-input",
    "--no-type-check-generated", "--no-output", "-"] invalidText
  state := state.check "kernel-invalid source is trusted when both class gates are off" <|
    invalidNeither.exitCode == 0 && invalidNeither.stdout.isEmpty &&
      !invalidNeither.stderr.contains "kernel check"
  let invalidOutputOnly ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--no-type-check-input",
    "--type-check-generated", "--no-output", "-"] invalidText
  state := state.check "generated kernel gate does not recheck input declarations" <|
    invalidOutputOnly.exitCode == 0 && invalidOutputOnly.stdout.isEmpty &&
      !invalidOutputOnly.stderr.contains "input kernel check" &&
      hasDiagnostic invalidOutputOnly.stderr "generated kernel check: accepted"
  let invalidBoth ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--type-check-input",
    "--type-check-generated", "--no-output", "-"] invalidText
  state := state.check "input rejection precedes an enabled generated-output gate" <|
    invalidBoth.exitCode == 1 &&
      invalidBoth.stderr.contains "input kernel check rejected:" &&
      !invalidBoth.stderr.contains "generated kernel check"
  let gatedOutputPath : System.FilePath := s!"{scratch}/main-cli-gated-output.ndjson"
  let gatedSentinel := "output gate sentinel\n"
  IO.FS.writeFile gatedOutputPath gatedSentinel
  let gatedOutput ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--no-type-check-input",
    "--type-check-generated", "-o", gatedOutputPath.toString, "-"] invalidText
  state := state.check "generated-output gate trusts and publishes unchanged input" <|
    gatedOutput.exitCode == 0 && (← IO.FS.readFile gatedOutputPath) == invalidText &&
      hasDiagnostic gatedOutput.stderr "generated kernel check: accepted"
  IO.FS.removeFile gatedOutputPath

  -- A later source replay failure must precede the named output transaction.
  let replayTarget : System.FilePath := s!"{scratch}/main-cli-replay-output.ndjson"
  IO.FS.writeFile replayTarget gatedSentinel
  let lateReplayCorruption := mapConstructor nestedExport `PT.node fun constructor =>
    { constructor with type := .sort .zero }
  let replayRejected ← runInductiveModels binary
    ["--no-check", "--no-type-check-generated", "-o",
      replayTarget.toString, "-"] (some lateReplayCorruption.render)
  let replayUntouched :=
    replayRejected.exitCode == 1 &&
      (← IO.FS.readFile replayTarget) == gatedSentinel &&
      (replayRejected.stderr.splitOn
        "kernel rejected an input declaration during generation:").length > 1
  state := state.check "late replay rejection leaves named output untouched" replayUntouched
  IO.FS.removeFile replayTarget
  IO.FS.removeFile invalidPath

  -- Kernel replay uses declaration dependencies internally, without applying
  -- the model-before-owner output policy or changing the stream's bytes.
  let dependency := `ArenaDependency
  let dependent := `ArenaDependent
  let dependencyDecl : InductiveModels.EDecl :=
    .ax dependency [] (.sort (.succ .zero)) false
  let dependentDecl : InductiveModels.EDecl :=
    .ax dependent [] (.const dependency []) false
  let reversedDependencies : InductiveModels.Export :=
    { nestedExport with decls := #[dependentDecl, dependencyDecl] }
  let reversedText := reversedDependencies.render
  let reversedReplay ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--type-check-generated",
    "--quiet", "-"] reversedText
  state := state.check "kernel replay dependency-orders without transforming output" <|
    reversedReplay.exitCode == 0 && reversedReplay.stdout == reversedText

  let missingDependency : InductiveModels.Export :=
    { nestedExport with decls := #[dependentDecl] }
  let missingReplay ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"]
    missingDependency.render
  state := state.check "missing kernel dependency is rejected with exit 1" <|
    missingReplay.exitCode == 1 &&
      (missingReplay.stderr.splitOn "input kernel check rejected:").length > 1

  let cycleLeft := `ArenaCycleLeft
  let cycleRight := `ArenaCycleRight
  let dependencyCycle : InductiveModels.Export := { nestedExport with decls := #[
    .ax cycleLeft [] (.const cycleRight []) false,
    .ax cycleRight [] (.const cycleLeft []) false] }
  let cycleReplay ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"]
    dependencyCycle.render
  state := state.check "cyclic kernel dependencies are rejected with exit 1" <|
    cycleReplay.exitCode == 1 &&
      (cycleReplay.stderr.splitOn "input kernel check rejected:").length > 1

  -- `Declaration.inductDecl` consumes only type-former and constructor inputs;
  -- all exported bookkeeping and recursor metadata must independently equal
  -- the `ConstantInfo`s minted by Lean's kernel.
  let metadataCorruptions : Array (String × InductiveModels.Export) := #[
    ("inductive name", mapInductiveType nestedExport `N fun type =>
      { type with name := `ArenaWrongInductive }),
    ("inductive level parameters", mapInductiveType nestedExport `N fun type =>
      { type with levelParams := [`ArenaExtraLevel] }),
    ("inductive type", mapInductiveType nestedExport `N fun type =>
      { type with type := .sort .zero }),
    ("inductive all", mapInductiveType nestedExport `N fun type =>
      { type with all := [`Eq] }),
    ("inductive constructor order", mapInductiveType nestedExport `N fun type =>
      { type with ctors := type.ctors.reverse }),
    ("inductive parameter count", mapInductiveType nestedExport `N fun type =>
      { type with numParams := type.numParams + 1 }),
    ("inductive index count", mapInductiveType nestedExport `N fun type =>
      { type with numIndices := type.numIndices + 1 }),
    ("inductive recursion flag", mapInductiveType nestedExport `N fun type =>
      { type with isRec := !type.isRec }),
    ("inductive nested count", mapInductiveType nestedExport `N fun type =>
      { type with numNested := type.numNested + 1 }),
    ("inductive reflexivity flag", mapInductiveType nestedExport `N fun type =>
      { type with isReflexive := !type.isReflexive }),
    ("inductive unsafe flag", mapInductiveType nestedExport `N fun type =>
      { type with isUnsafe := !type.isUnsafe }),
    ("constructor type", mapConstructor nestedExport `N.s fun constructor =>
      { constructor with type := .sort .zero }),
    ("constructor name", mapConstructor nestedExport `N.z fun constructor =>
      { constructor with name := `ArenaWrongConstructor }),
    ("constructor level parameters", mapConstructor nestedExport `N.z fun constructor =>
      { constructor with levelParams := [`ArenaExtraLevel] }),
    ("constructor owner", mapConstructor nestedExport `N.z fun constructor =>
      { constructor with induct := `Eq }),
    ("constructor index", mapConstructor nestedExport `N.z fun constructor =>
      { constructor with cidx := constructor.cidx + 1 }),
    ("constructor parameter count", mapConstructor nestedExport `N.z fun constructor =>
      { constructor with numParams := constructor.numParams + 1 }),
    ("constructor field count", mapConstructor nestedExport `N.s fun constructor =>
      { constructor with numFields := constructor.numFields + 1 }),
    ("constructor unsafe flag", mapConstructor nestedExport `N.z fun constructor =>
      { constructor with isUnsafe := !constructor.isUnsafe }),
    ("recursor name", mapRecursor nestedExport `N.rec fun recursor =>
      { recursor with name := `ArenaWrongRecursor }),
    ("recursor level parameters", mapRecursor nestedExport `N.rec fun recursor =>
      { recursor with levelParams := recursor.levelParams ++ [`ArenaExtraLevel] }),
    ("recursor type", mapRecursor nestedExport `N.rec fun recursor =>
      { recursor with type := .sort .zero }),
    ("recursor all", mapRecursor nestedExport `N.rec fun recursor =>
      { recursor with all := [`Eq] }),
    ("recursor parameter count", mapRecursor nestedExport `N.rec fun recursor =>
      { recursor with numParams := recursor.numParams + 1 }),
    ("recursor index count", mapRecursor nestedExport `N.rec fun recursor =>
      { recursor with numIndices := recursor.numIndices + 1 }),
    ("recursor motive count", mapRecursor nestedExport `N.rec fun recursor =>
      { recursor with numMotives := recursor.numMotives + 1 }),
    ("recursor minor count", mapRecursor nestedExport `N.rec fun recursor =>
      { recursor with numMinors := recursor.numMinors + 1 }),
    ("recursor rule constructor", mapRecursor nestedExport `N.rec fun recursor =>
      { recursor with rules := recursor.rules.map fun rule =>
          { rule with ctor := `Eq.refl } }),
    ("recursor rule field count", mapRecursor nestedExport `N.rec fun recursor =>
      { recursor with rules := recursor.rules.map fun rule =>
          { rule with nfields := rule.nfields + 1 } }),
    ("recursor rule body", mapRecursor nestedExport `N.rec fun recursor =>
      { recursor with rules := recursor.rules.map fun rule =>
          { rule with rhs := .sort .zero } }),
    ("recursor K flag", mapRecursor nestedExport `N.rec fun recursor =>
      { recursor with k := !recursor.k }),
    ("recursor unsafe flag", mapRecursor nestedExport `N.rec fun recursor =>
      { recursor with isUnsafe := !recursor.isUnsafe })]
  for (field, corruption) in metadataCorruptions do
    let result ← runInductiveModelsStdin binary [
      "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"]
      corruption.render
    state := state.check s!"corrupt {field} is rejected with exit 1" <|
      result.exitCode == 1 &&
        (result.stderr.splitOn "input kernel check rejected:").length > 1

  let reorderedConstructorRecords := reverseConstructorsFor nestedExport `N
  let reorderedConstructors ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"]
    reorderedConstructorRecords.render
  state := state.check "constructor record array order is not semantic metadata" <|
    reorderedConstructors.exitCode == 0

  -- General declaration metadata is an input to kernel insertion rather than
  -- kernel-minted output.  Use non-default but valid values to ensure replay
  -- preserves every field instead of silently rebuilding defaults.
  let universeName := `ArenaUniverse
  let proposition := `ArenaProposition
  let proof := `ArenaProof
  let theoremName := `ArenaTheorem
  let definitionName := `ArenaDefinition
  let opaqueName := `ArenaOpaque
  let generalMetadata : InductiveModels.Export := { nestedExport with decls := #[
    .thm theoremName [] (.const proposition []) (.const proof [])
      [theoremName, proof],
    .opaq opaqueName [universeName] (.sort (.succ (.param universeName)))
      (.sort (.param universeName)) false [opaqueName, definitionName],
    .defn definitionName [universeName] (.sort (.succ (.param universeName)))
      (.sort (.param universeName)) (.regular 17) "safe"
      [definitionName, opaqueName],
    .ax proof [] (.const proposition []) false,
    .ax proposition [] (.sort .zero) false,
    -- Invalid bodies and dependencies remain outside the arena verdict when
    -- their safety says that Lean itself cannot kernel-check them.
    .defn `ArenaPartial [] (.sort .zero) (.const `ArenaMissing []) .opaque "partial"
      [`ArenaPartial],
    .ax `ArenaUnsafe [] (.const `ArenaMissing []) true] }
  let generalReplay ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--type-check-generated",
    "--quiet", "-"] generalMetadata.render
  state := state.check "general metadata and arena safety skips replay exactly" <|
    generalReplay.exitCode == 0 && generalReplay.stdout == generalMetadata.render

  let unknownSafety := nestedText.replace "\"safety\":\"safe\"" "\"safety\":\"mystery\""
  let badSafety ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"] unknownSafety
  state := state.check "unknown definition safety is a parse/tool error with exit 3" <|
    unknownSafety != nestedText && badSafety.exitCode == 3 &&
      (badSafety.stderr.splitOn "parse error:").length > 1

  let duplicateText :=
    { nestedExport with decls := nestedExport.decls.push nestedExport.decls[0]! }.render
  let duplicate ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"] duplicateText
  state := state.check "duplicate declaration is an Arena rejection with exit 1" <|
    duplicate.exitCode == 1 &&
      duplicate.stderr.contains "invalid export: duplicate declaration"
  let duplicateWithoutKernel ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--no-type-check-input", "--no-output", "-"] duplicateText
  state := state.check "duplicate declaration without kernel checking is rejected" <|
    duplicateWithoutKernel.exitCode == 1 &&
      duplicateWithoutKernel.stderr.contains "invalid export: duplicate declaration"

  let quotientPath := s!"{root}/test/fixtures/inductive-models/prim_graph_pre.ndjson"
  let quotientText ← IO.FS.readFile quotientPath
  let unknownQuotient := quotientText.replace "\"kind\":\"type\"" "\"kind\":\"mystery\""
  let badQuotient ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"]
    unknownQuotient
  state := state.check "unknown quotient kind is a parse/tool error with exit 3" <|
    unknownQuotient != quotientText && badQuotient.exitCode == 3 &&
      (badQuotient.stderr.splitOn "parse error:").length > 1
  let .ok quotientExport := InductiveModels.parse quotientText | do
    IO.eprintln "mainclitest: quotient fixture did not parse"
    return 1
  let quotientRecords := quotientExport.decls.filter fun declaration =>
    match declaration with | .quot .. => true | _ => false
  let some equalityRecord := quotientExport.decls.find? fun declaration =>
      declaration.names.contains `Eq | do
    IO.eprintln "mainclitest: quotient fixture did not contain Eq"
    return 1
  -- The arena erases the three companion records, but `quotDecl` itself still
  -- needs the exported Eq declaration which its minted lift/ind types use.
  let quotientPrincipal :=
    { quotientExport with decls := #[equalityRecord, quotientRecords[0]!] }
  let principalReplay ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"]
    quotientPrincipal.render
  state := state.check "arena-compatible quotient principal replays with Eq but no companions" <|
    quotientRecords.size == 4 && principalReplay.exitCode == 0
  let quotientWithoutEquality := { quotientExport with decls := quotientRecords.extract 0 1 }
  let principalWithoutEquality ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"]
    quotientWithoutEquality.render
  state := state.check "quotient principal without Eq is kernel-invalid" <|
    quotientRecords.size == 4 && principalWithoutEquality.exitCode == 1
  let quotientCompanions := { quotientExport with decls := quotientRecords.extract 1 4 }
  let companionsReplay ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"]
    quotientCompanions.render
  state := state.check "arena-compatible quotient companions alone are ignored" <|
    quotientRecords.size == 4 && companionsReplay.exitCode == 0

  -- A valid declaration occupying a required public model slot is a genuine
  -- unsupported-generation result, not a kernel rejection.  Conversely, the
  -- fixed basis exemptions in the ordinary default run remain accepted.
  let collisionName := InductiveModels.Naming.modelName `Tree
  let collision : InductiveModels.EDecl := .ax collisionName [] (.sort (.succ .zero)) false
  let some ownerIndex := nestedExport.decls.findIdx? (fun declaration =>
      declaration.names.contains `Tree) | do
    IO.eprintln "mainclitest: nested fixture did not contain Tree"
    return 1
  -- A preexisting model slot must precede its owner to pass the online input
  -- order guard. It then reaches generation and occupies the exact public name
  -- which the Tree island would publish.
  let declinedDeclarations := nestedExport.decls.extract 0 ownerIndex ++ #[collision] ++
    nestedExport.decls.extract ownerIndex nestedExport.decls.size
  let declinedText := { nestedExport with decls := declinedDeclarations }.render
  let declined ← runInductiveModelsStdin binary
    ["--no-check", "--no-type-check-generated", "--no-output", "-"] declinedText
  state := state.check "unsupported generation declines with exit 2" <|
    declined.exitCode == 2 && (declined.stderr.splitOn "declined").length > 1
  let kernelCheckedDecline ← runInductiveModelsStdin binary
    ["--no-check", "--type-check-generated", "--no-output", "-"] declinedText
  state := state.check "generated-island kernel acceptance preserves generation exit 2" <|
    kernelCheckedDecline.exitCode == 2 && kernelCheckedDecline.stdout.isEmpty &&
      (kernelCheckedDecline.stderr.splitOn "declined").length > 1 &&
      hasDiagnostic kernelCheckedDecline.stderr "generated kernel check: accepted"

  let malformed ← runInductiveModelsStdin binary
    ["--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"] "not ndjson\n"
  state := state.check "malformed Arena stdin is a tool error with exit 3" <|
    malformed.exitCode == 3 && (malformed.stderr.splitOn "parse error:").length > 1
  let arenaHoles : Array (String × String) := #[
    ("name", "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"Defined\"}}\n" ++
      "{\"il\":1,\"param\":1}\n"),
    ("level", "{\"il\":2,\"succ\":0}\n{\"ie\":0,\"sort\":1}\n"),
    ("expression", "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Owner\"}}\n" ++
      "{\"ie\":2,\"sort\":0}\n" ++
      "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":1}}\n")]
  for (kind, arenaHole) in arenaHoles do
    let result ← runInductiveModelsStdin binary
      ["--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"] arenaHole
    state := state.check s!"undefined sparse {kind} ID is a tool error with exit 3" <|
      result.exitCode == 3 && (result.stderr.splitOn "parse error:").length > 1

  let malformedArenaRecords : Array (String × String) := #[
    ("extra top-level key", "{\"bvar\":0,\"extra\":null,\"ie\":0}\n"),
    ("multiple expression tags", "{\"bvar\":0,\"ie\":0,\"sort\":0}\n"),
    ("wrong max arity", "{\"il\":1,\"max\":[0]}\n"),
    ("invalid natural literal", "{\"ie\":0,\"natVal\":\"not-a-natural\"}\n")]
  for (kind, input) in malformedArenaRecords do
    let result ← runInductiveModelsStdin binary
      ["--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"] input
    state := state.check s!"{kind} is a parse/tool error with exit 3" <|
      result.exitCode == 3 && (result.stderr.splitOn "parse error:").length > 1

  -- `lean4export --export-mdata` records are valid arena input.  Metadata is
  -- non-semantic and the ordinary writer intentionally removes it again.
  let metadataInput :=
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"ArenaMetadata\"}}\n" ++
    "{\"ie\":0,\"sort\":0}\n" ++
    "{\"ie\":1,\"mdata\":{\"data\":{\"synthetic\":true},\"expr\":0}}\n" ++
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":1}}\n"
  let metadataRun ← runInductiveModelsStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--type-check-generated",
    "--quiet", "-"] metadataInput
  let metadataDecl : InductiveModels.EDecl := .ax `ArenaMetadata [] (.sort .zero) false
  state := state.check "metadata expression input passes both arena kernel gates" <|
    metadataRun.exitCode == 0 &&
      match InductiveModels.parse metadataRun.stdout with
      | .ok output => output.decls == #[metadataDecl]
      | .error _ => false
  let missing ← runInductiveModels binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output",
    s!"{scratch}/does-not-exist.ndjson"]
  state := state.check "missing $IN path is a tool error with exit 3" (missing.exitCode == 3)
  let badOption ← runInductiveModels binary ["--unknown-arena-option", nested]
  state := state.check "CLI misuse is a tool error with exit 3" (badOption.exitCode == 3)
  -- A literal `-` is standard input, not an unknown option.  The streaming
  -- reader sees the same records as a file reader; stdin cannot use the
  -- verbatim-copy shortcut after it has been consumed, so compare exports
  -- structurally rather than requiring its harmless re-interning to preserve
  -- whitespace.
  let stdinRun ← runInductiveModels binary
    ["--no-inductives", "--no-check", "--quiet", "-"] (some nestedText)
  state := state.check "stdin input succeeds" (stdinRun.exitCode == 0)
  state := state.check "stdin and file parse to the same export" <|
    match InductiveModels.parse stdinRun.stdout,
        InductiveModels.parse nestedText with
    | .ok stdinExport, .ok fileExport => stdinExport.decls == fileExport.decls
    | _, _ => false

  -- All defaults are exercised here, including stdout output, both structural
  -- checks, and incremental generated-island kernel checking.
  let defaults ← runInductiveModels binary [nested]
  state := state.check "defaults succeed" (defaults.exitCode == 0)
  state := state.check "defaults write an export to stdout" (!defaults.stdout.isEmpty)
  state := state.check "diagnostics stay off stdout"
    ((defaults.stdout.splitOn "model of").length == 1)
  let some defaultOutputFamilies := familyCount? defaults.stdout | do
    IO.eprintln "mainclitest: generated default output did not parse"
    return 1
  state := state.check "default input check reports its exact empty family count" <|
    hasDiagnostic defaults.stderr "input check: 0 model families checked"
  state := state.check "default output check reports its exact nonempty family count" <|
    defaultOutputFamilies > 0 && hasDiagnostic defaults.stderr
      s!"output check: {defaultOutputFamilies} model families checked"
  state := state.check "default generated kernel check reports acceptance" <|
    hasDiagnostic defaults.stderr "generated kernel check: accepted"

  -- Feed the generated result back through the default checker.  This is an
  -- actual input-side model family, rather than the vacuous check of an
  -- unmodelled source fixture.
  let modeledPath := s!"{scratch}/main-cli-modeled.ndjson"
  IO.FS.writeFile modeledPath defaults.stdout
  let checkedAgain ← runInductiveModels binary ["--no-output", modeledPath]
  state := state.check "default input check accepts generated models"
    (checkedAgain.exitCode == 0 && checkedAgain.stdout.isEmpty)
  state := state.check "input check reports its exact nonempty family count" <|
    hasDiagnostic checkedAgain.stderr
      s!"input check: {defaultOutputFamilies} model families checked"
  IO.FS.removeFile modeledPath

  let checkOnly ← runInductiveModels binary
    ["--no-inductives", "--check", "--no-output", nested]
  state := state.check "check-only invocation succeeds" (checkOnly.exitCode == 0)
  state := state.check "no-output suppresses stdout" checkOnly.stdout.isEmpty

  -- With generation disabled, stdout and a named output file must contain the
  -- same byte-for-byte export.  `-o` also re-enables output after --no-output.
  let stdoutRun ← runInductiveModels binary
    ["--no-inductives", "--no-check", "--quiet", nested]
  state := state.check "stdout output succeeds" (stdoutRun.exitCode == 0)
  let generationDisabled ← runInductiveModelsWithEnv binary
    ["--no-inductives", "--no-check", "--quiet", nested]
    #[("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")]
  state := state.check "generation-disabled output selects the legacy backend" <|
    generationDisabled.exitCode == 0 && generationDisabled.stdout == stdoutRun.stdout &&
      hasDiagnostic generationDisabled.stderr "output backend: legacy"
  let fallbackCwd := s!"{scratch}/main-cli-no-workspace-root"
  IO.FS.createDirAll fallbackCwd
  let nestedPath : System.FilePath := nested
  let binaryPath : System.FilePath := binary
  let currentDirectory ← IO.currentDir
  let nestedAbsolute := if nestedPath.isAbsolute then nestedPath else currentDirectory / nestedPath
  let binaryAbsolute := if binaryPath.isAbsolute then binaryPath else currentDirectory / binaryPath
  let fallbackRun ← runInductiveModelsAt binaryAbsolute.toString
    ["--no-check", "--quiet", nestedAbsolute.toString] fallbackCwd
    #[("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")]
  state := state.check "actual output creates no scratch directory beside the process" <|
    fallbackRun.exitCode == 0 && sameSemanticExport fallbackRun.stdout defaults.stdout &&
      hasDiagnostic fallbackRun.stderr "output backend: declaration-stream" &&
      !(← System.FilePath.pathExists ((fallbackCwd : System.FilePath) / "_tmp")) &&
      (← ((fallbackCwd : System.FilePath)).readDir).isEmpty
  IO.FS.removeDir fallbackCwd
  -- Actual generated output is declaration-wise, independently of whether
  -- the generated-island kernel gate is enabled.
  let observedDefault ← runInductiveModelsWithEnv binary [nested]
    #[("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")]
  state := state.check "default output selects declaration streaming off the one parse" <|
    observedDefault.exitCode == defaults.exitCode &&
      hasDiagnostic observedDefault.stderr "output backend: declaration-stream" &&
      observedDefault.stderr.contains "generated kernel checks:" &&
      !hasDiagnostic observedDefault.stderr "generated kernel checks: 0" &&
      sameSemanticExport observedDefault.stdout defaults.stdout
  state := state.check "streamed stdout parses with each model before its owner" <|
    match InductiveModels.parse observedDefault.stdout with
    | .error _ => false
    | .ok streamed =>
      let model := InductiveModels.Naming.modelName `Tree
      match streamed.decls.findIdx? (·.names.contains model),
          streamed.decls.findIdx? (·.names.contains `Tree) with
      | some modelIndex, some ownerIndex => modelIndex < ownerIndex
      | _, _ => false
  let observedLegacy ← runInductiveModelsWithEnv binary [nested] #[
    ("LEAN_INDUCTIVE_MODELS_LEGACY_OUTPUT", some "1"),
    ("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")]
  state := state.check "A/B override still streams output" <|
    observedLegacy.exitCode == defaults.exitCode &&
      hasDiagnostic observedLegacy.stderr "output backend: declaration-stream" &&
      sameSemanticExport observedLegacy.stdout defaults.stdout
  let discardCwd := s!"{scratch}/main-cli-compact-discard-root"
  IO.FS.createDirAll discardCwd
  let discarded ← runInductiveModelsAt binaryAbsolute.toString
    ["--no-output", "--no-type-check-generated", nestedAbsolute.toString] discardCwd
    #[("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")]
  state := state.check "generated no-output selects compact discard without a scratch root" <|
    discarded.exitCode == defaults.exitCode && discarded.stdout.isEmpty &&
      hasDiagnostic discarded.stderr "output backend: compact-discard" &&
      !(← System.FilePath.pathExists (discardCwd / "_tmp"))
  IO.FS.removeDir discardCwd
  let discardSentinelCwd := s!"{scratch}/main-cli-compact-discard-sentinel"
  let discardSentinelRoot := (discardSentinelCwd : System.FilePath) / "_tmp"
  let discardSentinel := discardSentinelRoot / "input-only-sentinel"
  IO.FS.createDirAll discardSentinelRoot
  IO.FS.writeFile discardSentinel "untouched"
  let discardedWithSentinel ← runInductiveModelsAt binaryAbsolute.toString
    ["--no-output", "--no-type-check-generated", nestedAbsolute.toString] discardSentinelCwd
    #[("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")]
  let sentinelExists ← System.FilePath.pathExists discardSentinel
  let sentinelContents ← if sentinelExists then IO.FS.readFile discardSentinel else pure ""
  state := state.check "unchecked compact discard leaves a preexisting scratch sentinel untouched" <|
    discardedWithSentinel.exitCode == defaults.exitCode &&
      discardedWithSentinel.stdout.isEmpty &&
      hasDiagnostic discardedWithSentinel.stderr "output backend: compact-discard" &&
      sentinelContents == "untouched"
  IO.FS.removeFile discardSentinel
  IO.FS.removeDir discardSentinelRoot
  IO.FS.removeDir discardSentinelCwd
  let discardedPlain ← runInductiveModels binary
    ["--no-output", "--no-type-check-generated", nested]
  let discardedLegacy ← runInductiveModelsLegacy binary
    ["--no-output", "--no-type-check-generated", nested]
  state := state.check "compact discard preserves the legacy report and exit" <|
    discardedPlain.exitCode == discardedLegacy.exitCode && discardedPlain.stdout.isEmpty &&
      discardedLegacy.stdout.isEmpty && discardedPlain.stderr == discardedLegacy.stderr
  let discardedStdin ← runInductiveModelsStdin binary
    ["--no-output", "--no-type-check-generated", "-"] nestedText
  state := state.check "compact discard stdin preserves the path verdict" <|
    discardedStdin.exitCode == discardedPlain.exitCode && discardedStdin.stdout.isEmpty &&
      discardedStdin.stderr == discardedPlain.stderr.replace nested "-"
  let discardedOverride ← runInductiveModelsWithEnv binary
    ["--no-output", "--no-type-check-generated", nested] #[
      ("LEAN_INDUCTIVE_MODELS_LEGACY_OUTPUT", some "1"),
      ("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")]
  state := state.check "legacy override excludes compact discard" <|
    discardedOverride.exitCode == discardedPlain.exitCode && discardedOverride.stdout.isEmpty &&
      hasDiagnostic discardedOverride.stderr "output backend: legacy"
  let fullNamedPath := s!"{scratch}/main-cli-full-opt-out.ndjson"
  removeIfPresent fullNamedPath
  let fullNamed ← runInductiveModelsWithEnv binary
    ["--no-type-check-generated", "-o", fullNamedPath, nested]
    #[("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")]
  let fullNamedText ← if ← System.FilePath.pathExists fullNamedPath then
      IO.FS.readFile fullNamedPath
    else pure ""
  state := state.check "generated-kernel opt-out named output streams without a gate" <|
    fullNamed.exitCode == defaults.exitCode && fullNamed.stdout.isEmpty &&
      hasDiagnostic fullNamed.stderr "output backend: declaration-stream" &&
      hasDiagnostic fullNamed.stderr "generated kernel checks: 0" &&
      sameSemanticExport fullNamedText defaults.stdout
  removeIfPresent fullNamedPath
  state := state.check "streamed named output leaves no transaction sibling" <|
    !(← hasOutputSibling scratch)

  -- Parseable but noncanonical raw bytes retain the accepted semantic output
  -- on the ordinary retained-input streaming path.
  let noncanonicalInput := "\n" ++ nestedExport.render
  let noncanonicalDefault ← runInductiveModelsWithEnv binary
    ["--no-check", "--no-type-check-generated", "-"]
    #[("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")] (some noncanonicalInput)
  let noncanonicalLegacy ← runInductiveModelsLegacy binary
    ["--no-check", "--no-type-check-generated", "-"] (some noncanonicalInput)
  state := state.check "noncanonical raw input preserves semantic streaming output" <|
    noncanonicalDefault.exitCode == noncanonicalLegacy.exitCode &&
      hasDiagnostic noncanonicalDefault.stderr "output backend: declaration-stream" &&
      sameSemanticExport noncanonicalDefault.stdout noncanonicalLegacy.stdout
  let noncanonicalDiscard ← runInductiveModelsWithEnv binary
    ["--no-output", "--no-type-check-generated", "-"]
    #[("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")] (some noncanonicalInput)
  state := state.check "noncanonical no-output input is accepted unchanged" <|
    noncanonicalDiscard.exitCode == defaults.exitCode && noncanonicalDiscard.stdout.isEmpty &&
      hasDiagnostic noncanonicalDiscard.stderr "output backend: compact-discard"
  let noncanonicalKernelArgs :=
    ["--no-output", "--no-check", "--type-check-generated", "-"]
  let noncanonicalKernelLegacy ← runInductiveModelsLegacy binary noncanonicalKernelArgs
    (some noncanonicalInput)
  let noncanonicalKernelBefore ← System.FilePath.readDir scratch
  let noncanonicalKernelCompact ← runInductiveModels binary noncanonicalKernelArgs
    (some noncanonicalInput)
  let noncanonicalKernelAfter ← System.FilePath.readDir scratch
  state := state.check "generated checking preserves noncanonical report and exit" <|
    noncanonicalKernelCompact.exitCode == noncanonicalKernelLegacy.exitCode &&
      noncanonicalKernelCompact.stdout.isEmpty && noncanonicalKernelLegacy.stdout.isEmpty &&
      noncanonicalKernelCompact.stderr == noncanonicalKernelLegacy.stderr &&
      hasDiagnostic noncanonicalKernelCompact.stderr "generated kernel check: accepted"
  state := state.check "noncanonical generation writes nothing under the scratch root" <|
    sameDirectoryEntries noncanonicalKernelBefore noncanonicalKernelAfter

  let traceMode ← runInductiveModelsWithEnv binary
    ["--no-check-output", "--no-type-check-generated", nested]
    #[("LEAN_INDUCTIVE_MODELS_PLANNER_LEVEL_TRACE", some "1"),
      ("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")]
  state := state.check "planner trace mode retains input but streams output" <|
    traceMode.exitCode == 0 &&
      hasDiagnostic traceMode.stderr "output backend: declaration-stream"
  let discardTraceMode ← runInductiveModelsWithEnv binary
    ["--no-output", "--no-check-output", "--no-type-check-generated", nested]
    #[("LEAN_INDUCTIVE_MODELS_PLANNER_LEVEL_TRACE", some "1"),
      ("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")]
  state := state.check "planner trace excludes compact discard" <|
    discardTraceMode.exitCode == 0 && discardTraceMode.stdout.isEmpty &&
      hasDiagnostic discardTraceMode.stderr "output backend: legacy"

  let kernelOutputMode ← runInductiveModelsWithEnv binary
    ["--no-check", "--type-check-generated", nested]
    #[("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")]
  state := state.check "generated kernel checking selects declaration streaming" <|
    kernelOutputMode.exitCode == 0 &&
      hasDiagnostic kernelOutputMode.stderr "output backend: declaration-stream" &&
      !hasDiagnostic kernelOutputMode.stderr "generated kernel checks: 0"
  let checkedDiscardBefore ← System.FilePath.readDir scratch
  let kernelDiscardMode ← runInductiveModelsWithEnv binary
    ["--no-output", "--no-check", "--type-check-generated", nested]
    #[("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")]
  state := state.check "no-output generated checking selects compact discard" <|
    kernelDiscardMode.exitCode == 0 && kernelDiscardMode.stdout.isEmpty &&
      hasDiagnostic kernelDiscardMode.stderr "output backend: compact-discard" &&
      hasDiagnostic kernelDiscardMode.stderr "generated kernel check: accepted"
  let checkedDiscardAfter ← System.FilePath.readDir scratch
  state := state.check "successful generated check writes nothing under the scratch root" <|
    sameDirectoryEntries checkedDiscardBefore checkedDiscardAfter
  let checkedDiscardArgs := ["--no-output", "--no-check", "--type-check-generated", nested]
  let checkedDiscardPlain ← runInductiveModels binary checkedDiscardArgs
  let checkedDiscardLegacy ← runInductiveModelsLegacy binary checkedDiscardArgs
  state := state.check "checked generated no-output preserves exact ordinary diagnostics" <|
    checkedDiscardPlain.exitCode == checkedDiscardLegacy.exitCode &&
      checkedDiscardPlain.stdout.isEmpty &&
      checkedDiscardLegacy.stdout.isEmpty &&
      checkedDiscardPlain.stderr == checkedDiscardLegacy.stderr
  let outputMetadataCorruption := mapRecursor nestedExport `N.rec fun recursor =>
    { recursor with numMinors := recursor.numMinors + 1 }
  let metadataFallbackArgs :=
    ["--no-output", "--no-check", "--no-type-check-input", "--type-check-generated", "-"]
  let metadataFallbackLegacy ← runInductiveModelsLegacy binary metadataFallbackArgs
    (some outputMetadataCorruption.render)
  let metadataFallbackCompact ← runInductiveModels binary metadataFallbackArgs
    (some outputMetadataCorruption.render)
  -- Exact source-layout validation precedes final output checking in both
  -- retention modes. The compact route must preserve that ordinary generation
  -- failure, including its diagnostic, rather than exposing a feed-order
  -- kernel error.
  let expectedMetadataFailure :=
    "-: internal error: N.rec's exact recursor layout differs from its installed metadata\n"
  let metadataFallbackParity :=
    metadataFallbackCompact.exitCode == metadataFallbackLegacy.exitCode &&
      metadataFallbackCompact.stdout.isEmpty && metadataFallbackLegacy.stdout.isEmpty &&
      metadataFallbackCompact.stderr == metadataFallbackLegacy.stderr &&
      metadataFallbackCompact.stderr == expectedMetadataFailure
  unless metadataFallbackParity do
    IO.eprintln s!"metadata fallback legacy stderr: {repr metadataFallbackLegacy.stderr}"
    IO.eprintln s!"metadata fallback compact stderr: {repr metadataFallbackCompact.stderr}"
  state := state.check "compact metadata rejection preserves ordinary generation diagnostic"
    metadataFallbackParity
  let rootedPlannedCwd : System.FilePath := s!"{scratch}/main-cli-rooted-discard-cwd"
  let rootedPlannedTmp : System.FilePath := s!"{scratch}/main-cli-rooted-external-tmp"
  let rootedPlannedScratch := rootedPlannedCwd / "_tmp"
  IO.FS.createDir rootedPlannedCwd
  IO.FS.createDir rootedPlannedScratch
  IO.FS.createDir rootedPlannedTmp
  let rootedSentinel := rootedPlannedScratch / "keep"
  let externalSentinel := rootedPlannedTmp / "keep"
  IO.FS.writeFile rootedSentinel "rooted\n"
  IO.FS.writeFile externalSentinel "external\n"
  let rootedPlannedRun ← runInductiveModelsAt binaryAbsolute.toString
    ["--no-output", "--type-check-generated", "--no-check", nestedAbsolute.toString]
    rootedPlannedCwd.toString #[
      ("TMPDIR", some rootedPlannedTmp.toString),
      ("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")]
  state := state.check "generated no-output writes neither a cwd scratch file nor an ambient TMPDIR file" <|
    rootedPlannedRun.exitCode == 0 && rootedPlannedRun.stdout.isEmpty &&
      hasDiagnostic rootedPlannedRun.stderr "output backend: compact-discard" &&
      hasDiagnostic rootedPlannedRun.stderr "generated kernel check: accepted" &&
      (← IO.FS.readFile rootedSentinel) == "rooted\n" &&
      (← IO.FS.readFile externalSentinel) == "external\n" &&
      (← rootedPlannedScratch.readDir).size == 1 && (← rootedPlannedTmp.readDir).size == 1
  IO.FS.removeFile rootedSentinel
  IO.FS.removeFile externalSentinel
  IO.FS.removeDir rootedPlannedScratch
  IO.FS.removeDir rootedPlannedCwd
  IO.FS.removeDir rootedPlannedTmp
  let plannedCwd : System.FilePath := s!"{scratch}/main-cli-planned-cwd"
  let externalPlannedTmp : System.FilePath := s!"{scratch}/main-cli-external-planned-tmp"
  IO.FS.createDir plannedCwd
  IO.FS.createDir externalPlannedTmp
  let plannedCwdScratch := plannedCwd / "_tmp"
  IO.FS.writeFile plannedCwdScratch "not a directory\n"
  let plannedCwdRun ← runInductiveModelsAt binaryAbsolute.toString
    ["--no-output", "--type-check-generated", "--no-check", nestedAbsolute.toString]
    plannedCwd.toString #[
      ("TMPDIR", some externalPlannedTmp.toString),
      ("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")]
  state := state.check "generated no-output needs no scratch directory when _tmp is a plain file" <|
    plannedCwdRun.exitCode == 0 && plannedCwdRun.stdout.isEmpty &&
      hasDiagnostic plannedCwdRun.stderr "output backend: compact-discard" &&
      (← IO.FS.readFile plannedCwdScratch) == "not a directory\n" &&
      (← externalPlannedTmp.readDir).isEmpty
  IO.FS.removeFile plannedCwdScratch
  IO.FS.removeDir plannedCwd
  IO.FS.removeDir externalPlannedTmp
  let plannedFailureEntriesBefore ← System.FilePath.readDir scratch
  let failedPlannedKernel ← runInductiveModelsWithEnv binary
    ["--no-output", "--no-check", "--type-check-generated", "-"]
    #[("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")]
    (some lateReplayCorruption.render)
  let plannedFailureEntriesAfter ← System.FilePath.readDir scratch
  state := state.check "a kernel-rejected generated no-output run leaves the scratch root untouched" <|
    failedPlannedKernel.exitCode == 1 && failedPlannedKernel.stdout.isEmpty &&
      hasDiagnostic failedPlannedKernel.stderr "output backend: compact-discard" &&
      sameDirectoryEntries plannedFailureEntriesBefore plannedFailureEntriesAfter
  -- Compare parsed exports, exact declaration order, diagnostics, and exit
  -- status so this pins the semantic contract independently of byte layout.
  for (label, fixture) in #[
      ("nested multi-model island", nested),
      ("late source support", s!"{root}/test/fixtures/inductive-models/prim_late_basis.ndjson")] do
    let args := #["--no-check-output", "--no-type-check-generated", fixture]
    let legacy ← runInductiveModelsLegacy binary args.toList
    let full ← runInductiveModels binary args.toList
    state := state.check s!"opt-out stream {label} preserves report and exit" <|
      full.exitCode == legacy.exitCode && full.stderr == legacy.stderr
    state := state.check s!"opt-out stream {label} preserves semantic output and order" <|
      sameSemanticExport full.stdout legacy.stdout
  let checkedLegacy ← runInductiveModelsLegacy binary ["--no-type-check-generated", nested]
  let checkedFull ← runInductiveModels binary ["--no-type-check-generated", nested]
  state := state.check "opt-out stream output check preserves report and exit" <|
    checkedFull.exitCode == checkedLegacy.exitCode && checkedFull.stderr == checkedLegacy.stderr
  state := state.check "opt-out stream output check preserves semantic output and order" <|
    sameSemanticExport checkedFull.stdout checkedLegacy.stdout
  -- Actual output stays on the declaration stream even when a future generated
  -- provider is unavailable at an earlier source transition.
  let futureModel := InductiveModels.Naming.modelName `Tree
  let stabilityMiss := { nestedExport with decls :=
    #[InductiveModels.EDecl.ax `CompactFallbackProbe [] (.const futureModel []) false] ++
      nestedExport.decls }
  let fallbackArgs := #["--no-type-check-input", "--no-type-check-generated", "-"]
  let fallbackLegacy ← runInductiveModelsLegacy binary fallbackArgs.toList (some stabilityMiss.render)
  let fallbackFull ← runInductiveModels binary fallbackArgs.toList (some stabilityMiss.render)
  state := state.check "actual output future provider preserves exact report and exit" <|
    fallbackFull.exitCode == fallbackLegacy.exitCode && fallbackFull.stderr == fallbackLegacy.stderr
  state := state.check "actual output future provider preserves exact output" <|
    fallbackFull.stdout == fallbackLegacy.stdout
  let plannedProviderArgs :=
    ["--no-type-check-input", "--type-check-generated", "--no-output", "-"]
  let plannedProviderLegacy ← runInductiveModelsLegacy binary plannedProviderArgs
    (some stabilityMiss.render)
  let plannedProviderBefore ← System.FilePath.readDir scratch
  let plannedProvider ← runInductiveModels binary plannedProviderArgs (some stabilityMiss.render)
  let plannedProviderAfter ← System.FilePath.readDir scratch
  state := state.check "generated-only checking does not inspect source provider order" <|
    plannedProvider.exitCode == plannedProviderLegacy.exitCode && plannedProvider.stdout.isEmpty &&
      plannedProviderLegacy.stdout.isEmpty && plannedProvider.stderr == plannedProviderLegacy.stderr &&
      hasDiagnostic plannedProvider.stderr "generated kernel check: accepted"
  state := state.check "generated-provider run writes nothing under the scratch root" <|
    sameDirectoryEntries plannedProviderBefore plannedProviderAfter
  let tracedPlannedProvider ← runInductiveModelsWithEnv binary plannedProviderArgs
    #[("LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE", some "1")]
    (some stabilityMiss.render)
  state := state.check "generated-provider run stays on compact discard" <|
    tracedPlannedProvider.exitCode == plannedProvider.exitCode &&
      tracedPlannedProvider.stdout.isEmpty &&
      hasDiagnostic tracedPlannedProvider.stderr "output backend: compact-discard"
  let outputPath := s!"{scratch}/main-cli-output.ndjson"
  if ← System.FilePath.pathExists outputPath then IO.FS.removeFile outputPath
  let fileRun ← runInductiveModels binary
    ["--no-inductives", "--no-check", "--quiet", "--no-output", "-o", outputPath, nested]
  state := state.check "file output succeeds" (fileRun.exitCode == 0)
  state := state.check "file output does not leak to stdout" fileRun.stdout.isEmpty
  if ← System.FilePath.pathExists outputPath then
    let fileText ← IO.FS.readFile outputPath
    state := state.check "stdout and file output agree" (fileText == stdoutRun.stdout)
    IO.FS.removeFile outputPath
  else
    state := state.check "file output was created" false

  -- Named output uses a fresh sibling and one rename. Each injected failure
  -- happens after the sibling has received bytes, but before the destination
  -- can be replaced; the old file and directory must remain clean.
  let failureTarget : System.FilePath := s!"{scratch}/main-cli-output-failure.ndjson"
  for failure in #[InductiveModels.Output.Test.Failure.write, .flush, .rename] do
    IO.FS.writeFile failureTarget "old-output\n"
    let rejected ← try
        InductiveModels.Output.Test.writeNamedFailing failureTarget failure
        pure false
      catch _ => pure true
    state := state.check s!"injected {repr failure} preserves named output" <|
      rejected && (← IO.FS.readFile failureTarget) == "old-output\n" &&
        !(← hasOutputSibling scratch)
  IO.FS.writeFile failureTarget "old-output\n"
  InductiveModels.Output.Test.writeNamedRollingBack failureTarget
  state := state.check "semantic rollback preserves named output" <|
    (← IO.FS.readFile failureTarget) == "old-output\n" &&
      !(← hasOutputSibling scratch)
  IO.FS.removeFile failureTarget

  let lateFailureTarget : System.FilePath := s!"{scratch}/main-cli-late-stream-failure.ndjson"
  IO.FS.writeFile lateFailureTarget "existing-target\n"
  let lateNamedFailure ← runInductiveModelsStdin binary
    ["--no-check", "--type-check-generated", "-o", lateFailureTarget.toString, "-"]
    lateReplayCorruption.render
  state := state.check "late generation rejection rolls back the named stream" <|
    lateNamedFailure.exitCode == 1 && lateNamedFailure.stdout.isEmpty &&
      (← IO.FS.readFile lateFailureTarget) == "existing-target\n" &&
      !(← hasOutputSibling scratch)
  IO.FS.removeFile lateFailureTarget
  let lateStdoutFailure ← runInductiveModelsStdin binary
    ["--no-check", "--type-check-generated", "-"] lateReplayCorruption.render
  state := state.check "late stdout rejection exposes only a parseable prefix" <|
    lateStdoutFailure.exitCode == 1 && !lateStdoutFailure.stdout.isEmpty &&
      (InductiveModels.parse lateStdoutFailure.stdout).isOk &&
      lateStdoutFailure.stdout != lateReplayCorruption.render

  let noBasenameRejected ← try
      InductiveModels.Output.write "." fun stream => stream.putStr "unreachable"
      pure false
    catch _ => pure true
  state := state.check "named output requires a final file name" noBasenameRejected

  let contained ← InductiveModels.Output.containToolErrors do
    throw <| IO.userError "injected uncaught tool failure"
  state := state.check "uncaught IO is contained as exit 3" (contained == 3)

  -- Atomic replacement acts on the literal final directory entry. It does
  -- not write through a symbolic link or mutate the other name of a hardlink.
  let linkReferent : System.FilePath := s!"{scratch}/main-cli-link-referent.ndjson"
  let symbolicTarget : System.FilePath := s!"{scratch}/main-cli-symbolic-output.ndjson"
  let linkSentinel := "symbolic referent sentinel\n"
  removeIfPresent symbolicTarget
  IO.FS.writeFile linkReferent linkSentinel
  unless System.Platform.isWindows do
    discard <| IO.Process.run {
      cmd := "ln", args := #["-s", linkReferent.toString, symbolicTarget.toString] }
    let symbolicRun ← runInductiveModels binary [
      "--no-inductives", "--no-check", "--quiet", "-o", symbolicTarget.toString, nested]
    state := state.check "named output replaces a symlink, not its referent" <|
      symbolicRun.exitCode == 0 && (← IO.FS.readFile linkReferent) == linkSentinel &&
        (← symbolicTarget.symlinkMetadata).type == .file &&
        (InductiveModels.parse (← IO.FS.readFile symbolicTarget)).isOk
  removeIfPresent symbolicTarget
  IO.FS.removeFile linkReferent

  let hardSource : System.FilePath := s!"{scratch}/main-cli-hard-source.ndjson"
  let hardTarget : System.FilePath := s!"{scratch}/main-cli-hard-output.ndjson"
  removeIfPresent hardTarget
  IO.FS.writeFile hardSource nestedText
  IO.FS.hardLink hardSource hardTarget
  let hardRun ← runInductiveModels binary [
    "--no-inductives", "--no-check", "--quiet", "-o", hardTarget.toString,
    hardSource.toString]
  state := state.check "named output replaces only the selected hardlink entry" <|
    hardRun.exitCode == 0 && (← IO.FS.readFile hardSource) == nestedText &&
      (← hardSource.metadata).numLinks == 1 && (← hardTarget.metadata).numLinks == 1 &&
      (InductiveModels.parse (← IO.FS.readFile hardTarget)).isOk
  IO.FS.removeFile hardTarget
  IO.FS.removeFile hardSource

  -- This line is larger than the reader's 4 MiB chunk, pinning carry handling
  -- when no newline occurs in an entire chunk.  Output is deliberately
  -- reserialized from the checked snapshot rather than reopening a path that
  -- may have changed after parsing.
  let boundaryPath := s!"{scratch}/main-cli-chunk-boundary.ndjson"
  let boundaryText :=
    "{\"meta\":{},\"padding\":\"" ++ String.ofList (List.replicate (5 * 1024 * 1024) 'x') ++
      "\"}\r\n"
  let .ok boundaryExport := InductiveModels.parse boundaryText | do
    IO.eprintln "mainclitest: chunk-boundary input did not parse"
    return 1
  IO.FS.writeFile boundaryPath boundaryText
  let boundaryRun ← runInductiveModels binary
    ["--no-inductives", "--no-check", "--quiet", boundaryPath]
  state := state.check "line spanning the chunk boundary parses" (boundaryRun.exitCode == 0)
  state := state.check "chunk-boundary output is the parsed snapshot" <|
    match InductiveModels.parse boundaryRun.stdout,
        InductiveModels.parse boundaryText with
    | .ok output, .ok input => output.decls == input.decls && output.metaLine == input.metaLine
    | _, _ => false
  let inPlaceRun ← runInductiveModels binary
    ["--no-inductives", "--no-check", "--quiet", "-o", boundaryPath, boundaryPath]
  let boundaryAfter ← IO.FS.readFile boundaryPath
  state := state.check "literal in-place output is a complete parsed snapshot" <|
    inPlaceRun.exitCode == 0 && inPlaceRun.stdout.isEmpty &&
      match InductiveModels.parse boundaryAfter with
      | .ok output => output.metaLine == boundaryExport.metaLine
      | .error _ => false
  let aliasPath := s!"{scratch}/./main-cli-chunk-boundary.ndjson"
  let aliasRun ← runInductiveModels binary
    ["--no-inductives", "--no-check", "--quiet", "-o", aliasPath, boundaryPath]
  let boundaryAfterAlias ← IO.FS.readFile boundaryPath
  state := state.check "canonical-path in-place output remains complete" <|
    aliasRun.exitCode == 0 && aliasRun.stdout.isEmpty &&
      (InductiveModels.parse boundaryAfterAlias).isOk
  IO.FS.removeFile boundaryPath

  let malformedPath := s!"{scratch}/main-cli-malformed.ndjson"
  IO.FS.writeFile malformedPath "{not-json}\n"
  let malformedRun ← runInductiveModels binary
    ["--no-inductives", "--no-check", "--no-output", malformedPath]
  state := state.check "malformed NDJSON is a tool error" <|
    malformedRun.exitCode == 3 && malformedRun.stdout.isEmpty &&
      malformedRun.stderr.contains "parse error"
  IO.FS.writeBinFile malformedPath (ByteArray.mk #[0xff, 0x0a])
  let utf8Run ← runInductiveModels binary
    ["--no-inductives", "--no-check", "--no-output", malformedPath]
  state := state.check "malformed UTF-8 is a tool error" <|
    utf8Run.exitCode == 3 && utf8Run.stdout.isEmpty &&
      utf8Run.stderr.contains "the input is not valid UTF-8"
  IO.FS.removeFile malformedPath

  -- Options apply left-to-right at the actual process boundary.  The last
  -- --no-output wins in the first invocation; the later --output wins in the
  -- second.  The later --nested likewise restores just that generation stage.
  let outputOff ← runInductiveModels binary
    ["--output", "--no-output", "--no-inductives", "--no-check", nested]
  state := state.check "later no-output wins" (outputOff.exitCode == 0 && outputOff.stdout.isEmpty)
  let outputOn ← runInductiveModels binary
    ["--no-output", "--output", "--no-inductives", "--no-check", "--quiet", nested]
  state := state.check "later output wins" (outputOn.exitCode == 0 && !outputOn.stdout.isEmpty)
  let nestedOnly ← runInductiveModels binary
    ["--no-inductives", "--nested", "--check", "--quiet", nested]
  state := state.check "later nested restores the nested stage" <|
    nestedOnly.exitCode == 0 && nestedOnly.stdout != stdoutRun.stdout
  state := state.check "quiet suppresses successful check diagnostics" <|
    (nestedOnly.stderr.splitOn "input check:").length == 1 &&
      (nestedOnly.stderr.splitOn "output check:").length == 1

  -- **Every committed fixture, through the complete process boundary.**
  --
  -- A route may decline an owner it does not model, and exit 2 says so; that
  -- is a verdict about the fixture. Exit 1 and exit 3 are not: they say the
  -- tool rejected or could not finish what it itself produced, which is a
  -- defect of the route that produced it. So the sweep asks only that no
  -- committed export makes the tool fail, and it asks it of every one of them
  -- rather than of a list. A fixture is swept from the moment it is committed.
  --
  -- The generated-island kernel gate is what makes this end-to-end rather
  -- than a repetition of the library suites: it replays each exact island in
  -- its own emitted order, so an island that consumes support standing behind
  -- it in the same island is rejected here and nowhere else.
  --
  -- `test/fixtures/rejected` is deliberately outside the sweep: those exports
  -- exist to be refused, and `kernelchecktest` names each one directly.
  let fixtureRoot : System.FilePath := s!"{root}/test/fixtures/inductive-models"
  let mut fixtures : Array System.FilePath := #[]
  for directory in #[fixtureRoot, fixtureRoot / "filtered"] do
    for entry in ← directory.readDir do
      if entry.path.extension == some "ndjson" then
        fixtures := fixtures.push entry.path
  let mut sweptAccepted := 0
  let mut sweptDeclined : Array String := #[]
  let mut sweepFailures : Array String := #[]
  for fixture in fixtures.qsort (·.toString < ·.toString) do
    let sweepRun ← runInductiveModels binary [
      "--inductives", "--check", "--type-check-generated", "--no-output", fixture.toString]
    if sweepRun.exitCode == 0 then sweptAccepted := sweptAccepted + 1
    else if sweepRun.exitCode == 2 then
      -- `filtered/` repeats several base names of the directory above it, so
      -- the label keeps the subdirectory.
      let name := fixture.fileName.getD fixture.toString
      sweptDeclined := sweptDeclined.push <|
        if fixture.parent.any (·.fileName == some "filtered") then s!"filtered/{name}"
        else name
    else
      let reported := (sweepRun.stderr.splitOn "\n").filter (!·.isEmpty)
      sweepFailures := sweepFailures.push
        s!"{fixture}: exit {sweepRun.exitCode}: {reported.getLast?.getD ""}"
  for failure in sweepFailures do IO.eprintln s!"FAIL fixture sweep: {failure}"
  state := state.check
    s!"no committed fixture fails the complete tool ({sweptAccepted} accepted, \
      {sweptDeclined.size} declined, {sweepFailures.size} failed)" sweepFailures.isEmpty
  -- **Accepting and declining are different verdicts, so the sweep says which
  -- one it expects.** Exit 0 and exit 2 were both waved through above and the
  -- two counts were interpolated into a label rather than asserted, so a
  -- fixture that flipped from accepted to declined passed the sweep, and this
  -- sweep is the only thing covering `filtered/`. Naming the declines pins
  -- both sides at once: a fixture is expected to be declined exactly when it
  -- is on this list, and accepted otherwise.
  --
  -- `prim_shape_declines` is what the file exists to be.
  -- `e_dependent_field` is the other, and it is on this list for **one owner**
  -- out of seven. `Decline.projectionCodomain` refuses a projection rule whose
  -- equation would relate two terms of different types, because the field it
  -- selects depends on an earlier field whose modeled projection does not
  -- select it definitionally. Arm E's carrier stores its constructor's
  -- non-recursive fields in a `PSigma'` tower ending at `emptyAt w` — empty
  -- because of its tail, selecting because of its components — so `EDep`,
  -- `EChain`, `EMid`, `ENon`, `EBare` and `EMulti` all model. `EOpaque` is the
  -- one left: its first field is opaque at `Sort (imax u v)`, no `max` absorbs
  -- an `imax` and no box can inspect an opaque type far enough to normalize its
  -- level, so nothing stores it and field 2 names it.
  --
  -- `w_dependent_field` used to be on this list for the same verdict. Arm W
  -- now selects its *stored* fields definitionally — through `_wcore.WT.root`
  -- and the data tower rather than through `WT.Wrec` — and by positivity those
  -- are exactly the fields a codomain can name, so the whole file is accepted.
  state := state.check
    s!"the sweep declines exactly {sweepDeclinedFixtures} (declined \
      {sweptDeclined.qsort (· < ·)})"
    (sweptDeclined.qsort (· < ·) == sweepDeclinedFixtures.qsort (· < ·))

  IO.println s!"main CLI: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1
