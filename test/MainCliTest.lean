import Modelgen.Check
import Modelgen.Naming

/-!
End-to-end tests for the public `modelgen` process boundary.

These deliberately execute the built binary: parser-only tests cannot observe
the stdout/stderr split, output suppression, pass ordering, or the integrated
mode-A monomorphization pass.
-/

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then
    { state with passed := state.passed + 1 }
  else
    { state with failed := state.failed.push label }

def runModelgen (binary : String) (args : List String) (input? : Option String := none) :
    IO IO.Process.Output :=
  IO.Process.output { cmd := binary, args := args.toArray } input?

def runModelgenStdin (binary : String) (args : List String) (input : String) :
    IO IO.Process.Output :=
  IO.Process.output { cmd := binary, args := args.toArray } (some input)

def hasDiagnostic (stderr diagnostic : String) : Bool :=
  (stderr.splitOn "\n").contains diagnostic

def familyCount? (text : String) : Option Nat := do
  let parsed ← (Modelgen.parse text (analyse := false)).toOption
  return (Modelgen.Check.discover parsed).size

def mapInductiveType (inputExport : Modelgen.Export) (target : Lean.Name)
    (f : Modelgen.EIndType → Modelgen.EIndType) : Modelgen.Export :=
  { inputExport with decls := inputExport.decls.map fun declaration => match declaration with
    | .induct types constructors recursors =>
      .induct (types.map fun type => if type.name == target then f type else type)
        constructors recursors
    | other => other }

def mapConstructor (inputExport : Modelgen.Export) (target : Lean.Name)
    (f : Modelgen.ECtor → Modelgen.ECtor) : Modelgen.Export :=
  { inputExport with decls := inputExport.decls.map fun declaration => match declaration with
    | .induct types constructors recursors =>
      .induct types
        (constructors.map fun constructor =>
          if constructor.name == target then f constructor else constructor)
        recursors
    | other => other }

def mapRecursor (inputExport : Modelgen.Export) (target : Lean.Name)
    (f : Modelgen.ERec → Modelgen.ERec) : Modelgen.Export :=
  { inputExport with decls := inputExport.decls.map fun declaration => match declaration with
    | .induct types constructors recursors =>
      .induct types constructors
        (recursors.map fun recursor => if recursor.name == target then f recursor else recursor)
    | other => other }

def reverseConstructorsFor (inputExport : Modelgen.Export) (target : Lean.Name) : Modelgen.Export :=
  { inputExport with decls := inputExport.decls.map fun declaration => match declaration with
    | .induct types constructors recursors =>
      if types.any (·.name == target) then .induct types constructors.reverse recursors
      else declaration
    | other => other }

def main (args : List String) : IO UInt32 := do
  let root := args.head?.getD "."
  let binary := s!"{root}/.lake/build/bin/modelgen"
  unless ← System.FilePath.pathExists binary do
    IO.eprintln s!"mainclitest: missing {binary}; run `lake build modelgen` first"
    return 1

  let scratch := s!"{root}/_tmp"
  IO.FS.createDirAll scratch
  let nested := s!"{root}/test/fixtures/modelgen/nested_iota.ndjson"
  let nestedText ← IO.FS.readFile nested
  let .ok nestedExport := Modelgen.parse nestedText (analyse := false) | do
    IO.eprintln "mainclitest: nested fixture did not parse"
    return 1
  -- This fixture contains `Expr.proj`, so success also pins that the integrated
  -- path asked the reader for projection analysis.
  let mono := s!"{root}/test/fixtures/mono/mono_proj.ndjson"
  let mut state : TestState := {}

  -- Lean Kernel Arena compatibility.  A checker can receive its NDJSON path
  -- as `$IN`, or read the same bytes from stdin.  Whole-stream kernel verdict
  -- gates are independent of generation and of the structural model checks.
  let arenaPath ← runModelgen binary [
    "--no-inductives", "--no-check", "--type-check-input", "--type-check-output",
    "--no-output", nested]
  state := state.check "arena path input is accepted with exit 0" <|
    arenaPath.exitCode == 0 && arenaPath.stdout.isEmpty &&
      hasDiagnostic arenaPath.stderr "input kernel check: accepted" &&
      hasDiagnostic arenaPath.stderr "output kernel check: accepted"
  let arenaStdin ← runModelgenStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"] nestedText
  state := state.check "arena stdin input is accepted with exit 0" <|
    arenaStdin.exitCode == 0 && arenaStdin.stdout.isEmpty &&
      hasDiagnostic arenaStdin.stderr "input kernel check: accepted"

  -- Pure kernel-check mode does not impose this tool's model-before-owner
  -- ordering policy. This export is kernel-valid even though its model-shaped
  -- axiom depends on the source owner and would make that policy cyclic.
  let modelCycleName := Modelgen.Naming.modelName `Tree
  let modelCycle : Modelgen.EDecl :=
    .ax modelCycleName [] (.const `Tree []) false
  let modelCycleText := { nestedExport with decls := nestedExport.decls.push modelCycle }.render
  let arenaModelCycle ← runModelgenStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--type-check-output",
    "--no-output", "-"] modelCycleText
  state := state.check "pure kernel mode does not impose model ordering" <|
    arenaModelCycle.exitCode == 0 && arenaModelCycle.stdout.isEmpty

  let badName := `ArenaBad
  let badDeclaration : Modelgen.EDecl :=
    .defn badName [] (.sort .zero) (.sort .zero) .opaque "safe" [badName]
  let invalidExport := { nestedExport with decls := nestedExport.decls.push badDeclaration }
  let invalidText := invalidExport.render
  let invalidPath := s!"{scratch}/main-cli-invalid.ndjson"
  IO.FS.writeFile invalidPath invalidText
  let invalidInput ← runModelgen binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", invalidPath]
  state := state.check "kernel-invalid path input is rejected with exit 1" <|
    invalidInput.exitCode == 1 &&
      (invalidInput.stderr.splitOn "input kernel check rejected:").length > 1
  let invalidOutput ← runModelgenStdin binary [
    "--no-inductives", "--no-check", "--no-type-check-input",
    "--type-check-output", "--no-output", "-"] invalidText
  state := state.check "kernel-invalid stdin output is rejected with exit 1" <|
    invalidOutput.exitCode == 1 &&
      (invalidOutput.stderr.splitOn "output kernel check rejected:").length > 1
  IO.FS.removeFile invalidPath

  -- Kernel replay uses declaration dependencies internally, without applying
  -- the model-before-owner output policy or changing the stream's bytes.
  let dependency := `ArenaDependency
  let dependent := `ArenaDependent
  let dependencyDecl : Modelgen.EDecl :=
    .ax dependency [] (.sort (.succ .zero)) false
  let dependentDecl : Modelgen.EDecl :=
    .ax dependent [] (.const dependency []) false
  let reversedDependencies : Modelgen.Export :=
    { nestedExport with decls := #[dependentDecl, dependencyDecl] }
  let reversedText := reversedDependencies.render
  let reversedReplay ← runModelgenStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--type-check-output",
    "--quiet", "-"] reversedText
  state := state.check "kernel replay dependency-orders without transforming output" <|
    reversedReplay.exitCode == 0 && reversedReplay.stdout == reversedText

  let missingDependency : Modelgen.Export :=
    { nestedExport with decls := #[dependentDecl] }
  let missingReplay ← runModelgenStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"]
    missingDependency.render
  state := state.check "missing kernel dependency is rejected with exit 1" <|
    missingReplay.exitCode == 1 &&
      (missingReplay.stderr.splitOn "input kernel check rejected:").length > 1

  let cycleLeft := `ArenaCycleLeft
  let cycleRight := `ArenaCycleRight
  let dependencyCycle : Modelgen.Export := { nestedExport with decls := #[
    .ax cycleLeft [] (.const cycleRight []) false,
    .ax cycleRight [] (.const cycleLeft []) false] }
  let cycleReplay ← runModelgenStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"]
    dependencyCycle.render
  state := state.check "cyclic kernel dependencies are rejected with exit 1" <|
    cycleReplay.exitCode == 1 &&
      (cycleReplay.stderr.splitOn "input kernel check rejected:").length > 1

  -- `Declaration.inductDecl` consumes only type-former and constructor inputs;
  -- all exported bookkeeping and recursor metadata must independently equal
  -- the `ConstantInfo`s minted by Lean's kernel.
  let metadataCorruptions : Array (String × Modelgen.Export) := #[
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
    let result ← runModelgenStdin binary [
      "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"]
      corruption.render
    state := state.check s!"corrupt {field} is rejected with exit 1" <|
      result.exitCode == 1 &&
        (result.stderr.splitOn "input kernel check rejected:").length > 1

  let reorderedConstructorRecords := reverseConstructorsFor nestedExport `N
  let reorderedConstructors ← runModelgenStdin binary [
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
  let generalMetadata : Modelgen.Export := { nestedExport with decls := #[
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
  let generalReplay ← runModelgenStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--type-check-output",
    "--quiet", "-"] generalMetadata.render
  state := state.check "general metadata and arena safety skips replay exactly" <|
    generalReplay.exitCode == 0 && generalReplay.stdout == generalMetadata.render

  let unknownSafety := nestedText.replace "\"safety\":\"safe\"" "\"safety\":\"mystery\""
  let badSafety ← runModelgenStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"] unknownSafety
  state := state.check "unknown definition safety is a parse/tool error with exit 3" <|
    unknownSafety != nestedText && badSafety.exitCode == 3 &&
      (badSafety.stderr.splitOn "parse error:").length > 1

  let duplicateText :=
    { nestedExport with decls := nestedExport.decls.push nestedExport.decls[0]! }.render
  let duplicate ← runModelgenStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"] duplicateText
  state := state.check "duplicate declaration is a parse/tool error with exit 3" <|
    duplicate.exitCode == 3 && (duplicate.stderr.splitOn "parse error:").length > 1

  let quotientPath := s!"{root}/test/fixtures/modelgen/prim_graph_pre.ndjson"
  let quotientText ← IO.FS.readFile quotientPath
  let unknownQuotient := quotientText.replace "\"kind\":\"type\"" "\"kind\":\"mystery\""
  let badQuotient ← runModelgenStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"]
    unknownQuotient
  state := state.check "unknown quotient kind is a parse/tool error with exit 3" <|
    unknownQuotient != quotientText && badQuotient.exitCode == 3 &&
      (badQuotient.stderr.splitOn "parse error:").length > 1
  let .ok quotientExport := Modelgen.parse quotientText (analyse := false) | do
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
  let principalReplay ← runModelgenStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"]
    quotientPrincipal.render
  state := state.check "arena-compatible quotient principal replays with Eq but no companions" <|
    quotientRecords.size == 4 && principalReplay.exitCode == 0
  let quotientWithoutEquality := { quotientExport with decls := quotientRecords.extract 0 1 }
  let principalWithoutEquality ← runModelgenStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"]
    quotientWithoutEquality.render
  state := state.check "quotient principal without Eq is kernel-invalid" <|
    quotientRecords.size == 4 && principalWithoutEquality.exitCode == 1
  let quotientCompanions := { quotientExport with decls := quotientRecords.extract 1 4 }
  let companionsReplay ← runModelgenStdin binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"]
    quotientCompanions.render
  state := state.check "arena-compatible quotient companions alone are ignored" <|
    quotientRecords.size == 4 && companionsReplay.exitCode == 0

  -- A valid declaration occupying a required public model slot is a genuine
  -- unsupported-generation result, not a kernel rejection.  Conversely, the
  -- fixed basis exemptions in the ordinary default run remain accepted.
  let collisionName := Modelgen.Naming.modelName `Tree
  let collision : Modelgen.EDecl := .ax collisionName [] (.sort (.succ .zero)) false
  let declinedText := { nestedExport with decls := nestedExport.decls.push collision }.render
  let declined ← runModelgenStdin binary
    ["--no-check", "--no-output", "-"] declinedText
  state := state.check "unsupported generation declines with exit 2" <|
    declined.exitCode == 2 && (declined.stderr.splitOn "declined").length > 1

  let malformed ← runModelgenStdin binary
    ["--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"] "not ndjson\n"
  state := state.check "malformed stdin is a tool error with exit 3" <|
    malformed.exitCode == 3 && (malformed.stderr.splitOn "parse error:").length > 1
  let arenaHoles : Array (String × String) := #[
    ("name", "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"Defined\"}}\n" ++
      "{\"il\":1,\"param\":1}\n"),
    ("level", "{\"il\":2,\"succ\":0}\n{\"ie\":0,\"sort\":1}\n"),
    ("expression", "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Owner\"}}\n" ++
      "{\"ie\":2,\"sort\":0}\n" ++
      "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":1}}\n")]
  for (kind, arenaHole) in arenaHoles do
    let result ← runModelgenStdin binary
      ["--no-inductives", "--no-check", "--type-check-input", "--no-output", "-"] arenaHole
    state := state.check s!"undefined sparse {kind} ID is a tool error with exit 3" <|
      result.exitCode == 3 && (result.stderr.splitOn "parse error:").length > 1
  let missing ← runModelgen binary [
    "--no-inductives", "--no-check", "--type-check-input", "--no-output",
    s!"{scratch}/does-not-exist.ndjson"]
  state := state.check "missing $IN path is a tool error with exit 3" (missing.exitCode == 3)
  let badOption ← runModelgen binary ["--unknown-arena-option", nested]
  state := state.check "CLI misuse is a tool error with exit 3" (badOption.exitCode == 3)
  let monoRefusal := s!"{root}/test/fixtures/mono/marker_taken.ndjson"
  let internal ← runModelgen binary [
    "--no-inductives", "--no-check", "--mono-levels", "--no-output", monoRefusal]
  state := state.check "internal transform refusal is a tool error with exit 3" <|
    internal.exitCode == 3 &&
      (internal.stderr.splitOn "monomorphization refused the export:").length > 1

  -- A literal `-` is standard input, not an unknown option.  The streaming
  -- reader sees the same records as a file reader; stdin cannot use the
  -- verbatim-copy shortcut after it has been consumed, so compare exports
  -- structurally rather than requiring its harmless re-interning to preserve
  -- whitespace.
  let stdinRun ← runModelgen binary
    ["--no-inductives", "--no-check", "--quiet", "-"] (some nestedText)
  state := state.check "stdin input succeeds" (stdinRun.exitCode == 0)
  state := state.check "stdin and file parse to the same export" <|
    match Modelgen.parse stdinRun.stdout (analyse := false),
        Modelgen.parse nestedText (analyse := false) with
    | .ok stdinExport, .ok fileExport => stdinExport.decls == fileExport.decls
    | _, _ => false

  -- All defaults are exercised here, including stdout output and both checks.
  -- This succeeds once all generated model families precede their owners; it
  -- is the integration seam between the CLI and the ordering repair.
  let defaults ← runModelgen binary [nested]
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

  -- Feed the generated result back through the default checker.  This is an
  -- actual input-side model family, rather than the vacuous check of an
  -- unmodelled source fixture.
  let modeledPath := s!"{scratch}/main-cli-modeled.ndjson"
  IO.FS.writeFile modeledPath defaults.stdout
  let checkedAgain ← runModelgen binary ["--no-output", modeledPath]
  state := state.check "default input check accepts generated models"
    (checkedAgain.exitCode == 0 && checkedAgain.stdout.isEmpty)
  state := state.check "input check reports its exact nonempty family count" <|
    hasDiagnostic checkedAgain.stderr
      s!"input check: {defaultOutputFamilies} model families checked"
  IO.FS.removeFile modeledPath

  let checkOnly ← runModelgen binary
    ["--no-inductives", "--check", "--no-output", nested]
  state := state.check "check-only invocation succeeds" (checkOnly.exitCode == 0)
  state := state.check "no-output suppresses stdout" checkOnly.stdout.isEmpty

  -- With generation disabled, stdout and a named output file must contain the
  -- same byte-for-byte export.  `-o` also re-enables output after --no-output.
  let stdoutRun ← runModelgen binary
    ["--no-inductives", "--no-check", "--quiet", nested]
  state := state.check "stdout output succeeds" (stdoutRun.exitCode == 0)
  let outputPath := s!"{scratch}/main-cli-output.ndjson"
  if ← System.FilePath.pathExists outputPath then IO.FS.removeFile outputPath
  let fileRun ← runModelgen binary
    ["--no-inductives", "--no-check", "--quiet", "--no-output", "-o", outputPath, nested]
  state := state.check "file output succeeds" (fileRun.exitCode == 0)
  state := state.check "file output does not leak to stdout" fileRun.stdout.isEmpty
  if ← System.FilePath.pathExists outputPath then
    let fileText ← IO.FS.readFile outputPath
    state := state.check "stdout and file output agree" (fileText == stdoutRun.stdout)
    IO.FS.removeFile outputPath
  else
    state := state.check "file output was created" false

  -- This line is larger than the reader's 4 MiB chunk, pinning carry handling
  -- when no newline occurs in an entire chunk.  Output is deliberately
  -- reserialized from the checked snapshot rather than reopening a path that
  -- may have changed after parsing.
  let boundaryPath := s!"{scratch}/main-cli-chunk-boundary.ndjson"
  let boundaryText :=
    "{\"meta\":{},\"padding\":\"" ++ String.ofList (List.replicate (5 * 1024 * 1024) 'x') ++
      "\"}\r\n"
  let .ok boundaryExport := Modelgen.parse boundaryText (analyse := false) | do
    IO.eprintln "mainclitest: chunk-boundary input did not parse"
    return 1
  IO.FS.writeFile boundaryPath boundaryText
  let boundaryRun ← runModelgen binary
    ["--no-inductives", "--no-check", "--quiet", boundaryPath]
  state := state.check "line spanning the chunk boundary parses" (boundaryRun.exitCode == 0)
  state := state.check "chunk-boundary output is the parsed snapshot" <|
    match Modelgen.parse boundaryRun.stdout (analyse := false),
        Modelgen.parse boundaryText (analyse := false) with
    | .ok output, .ok input => output.decls == input.decls && output.metaLine == input.metaLine
    | _, _ => false
  let inPlaceRun ← runModelgen binary
    ["--no-inductives", "--no-check", "--quiet", "-o", boundaryPath, boundaryPath]
  let boundaryAfter ← IO.FS.readFile boundaryPath
  state := state.check "literal in-place output is a complete parsed snapshot" <|
    inPlaceRun.exitCode == 0 && inPlaceRun.stdout.isEmpty &&
      match Modelgen.parse boundaryAfter (analyse := false) with
      | .ok output => output.metaLine == boundaryExport.metaLine
      | .error _ => false
  let aliasPath := s!"{scratch}/./main-cli-chunk-boundary.ndjson"
  let aliasRun ← runModelgen binary
    ["--no-inductives", "--no-check", "--quiet", "-o", aliasPath, boundaryPath]
  let boundaryAfterAlias ← IO.FS.readFile boundaryPath
  state := state.check "canonical-path in-place output remains complete" <|
    aliasRun.exitCode == 0 && aliasRun.stdout.isEmpty &&
      (Modelgen.parse boundaryAfterAlias (analyse := false)).isOk
  IO.FS.removeFile boundaryPath

  let malformedPath := s!"{scratch}/main-cli-malformed.ndjson"
  IO.FS.writeFile malformedPath "{not-json}\n"
  let malformedRun ← runModelgen binary
    ["--no-inductives", "--no-check", "--no-output", malformedPath]
  state := state.check "malformed NDJSON is a tool error" <|
    malformedRun.exitCode == 3 && malformedRun.stdout.isEmpty &&
      malformedRun.stderr.contains "parse error"
  IO.FS.writeBinFile malformedPath (ByteArray.mk #[0xff, 0x0a])
  let utf8Run ← runModelgen binary
    ["--no-inductives", "--no-check", "--no-output", malformedPath]
  state := state.check "malformed UTF-8 is a tool error" <|
    utf8Run.exitCode == 3 && utf8Run.stdout.isEmpty &&
      utf8Run.stderr.contains "the input is not valid UTF-8"
  IO.FS.removeFile malformedPath

  -- Options apply left-to-right at the actual process boundary.  The last
  -- --no-output wins in the first invocation; the later --output wins in the
  -- second.  The later --nested likewise restores just that generation stage.
  let outputOff ← runModelgen binary
    ["--output", "--no-output", "--no-inductives", "--no-check", nested]
  state := state.check "later no-output wins" (outputOff.exitCode == 0 && outputOff.stdout.isEmpty)
  let outputOn ← runModelgen binary
    ["--no-output", "--output", "--no-inductives", "--no-check", "--quiet", nested]
  state := state.check "later output wins" (outputOn.exitCode == 0 && !outputOn.stdout.isEmpty)
  let nestedOnly ← runModelgen binary
    ["--no-inductives", "--nested", "--check", "--quiet", nested]
  state := state.check "later nested restores the nested stage" <|
    nestedOnly.exitCode == 0 && nestedOnly.stdout != stdoutRun.stdout
  state := state.check "quiet suppresses successful check diagnostics" <|
    (nestedOnly.stderr.splitOn "input check:").length == 1 &&
      (nestedOnly.stderr.splitOn "output check:").length == 1

  -- The integrated switch is mode A: it keeps recursor elimination levels,
  -- runs before inductive generation, and performs Mono's kernel replay.
  let monoRun ← runModelgen binary
    ["--no-inductives", "--mono-levels", "--quiet", mono]
  state := state.check "mono-levels mode A succeeds" (monoRun.exitCode == 0)
  state := state.check "mono-levels writes marker-renamed declarations" <|
    (monoRun.stdout.splitOn "_at").length > 1

  -- Monomorphization runs before generation, so the default inductive branches
  -- can model its result without asking Mono to infer instantiations for the
  -- generated bootstrap basis.  This fixture has distinct universe use sites
  -- and exercises the full default `--inductives --check` pipeline.
  let poly := s!"{root}/test/fixtures/modelgen/poly_nested_used.ndjson"
  let monoModels ← runModelgen binary ["--mono-levels", "--quiet", poly]
  state := state.check "monomorphized generated models pass the final check"
    (monoModels.exitCode == 0 && !monoModels.stdout.isEmpty)

  -- Check the serialized bytes again.  This pins both ordering passes and the
  -- stdout writer: an in-memory result cannot make this second
  -- input check green if serialization changes the declaration order.
  let monoModeledPath := s!"{scratch}/main-cli-mono-modeled.ndjson"
  IO.FS.writeFile monoModeledPath monoModels.stdout
  let monoCheckedAgain ← runModelgen binary [
    "--no-inductives", "--check-input", "--no-check-output", "--no-output",
    monoModeledPath]
  state := state.check "serialized monomorphized models remain ordered and check"
    (monoCheckedAgain.exitCode == 0 && monoCheckedAgain.stdout.isEmpty)
  let some monoFamilies := familyCount? monoModels.stdout | do
    IO.eprintln "mainclitest: monomorphized model output did not parse"
    return 1
  state := state.check "serialized input-only check reports its exact family count" <|
    monoFamilies > 0 && hasDiagnostic monoCheckedAgain.stderr
      s!"input check: {monoFamilies} model families checked"
  state := state.check "disabled output check emits no success diagnostic" <|
    (monoCheckedAgain.stderr.splitOn "output check:").length == 1
  IO.FS.removeFile monoModeledPath

  IO.println s!"main CLI: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1
