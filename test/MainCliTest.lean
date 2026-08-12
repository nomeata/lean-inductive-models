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

  -- File-input identity is stronger than structural equivalence: comments,
  -- metadata formatting and blank lines are copied byte-for-byte. This line
  -- is larger than the reader's 4 MiB chunk, pinning carry handling when no
  -- newline occurs in an entire chunk.
  let boundaryPath := s!"{scratch}/main-cli-chunk-boundary.ndjson"
  let boundaryText :=
    "{\"meta\":{},\"padding\":\"" ++ String.ofList (List.replicate (5 * 1024 * 1024) 'x') ++
      "\"}\r\n"
  IO.FS.writeFile boundaryPath boundaryText
  let boundaryRun ← runModelgen binary
    ["--no-inductives", "--no-check", "--quiet", boundaryPath]
  state := state.check "line spanning the chunk boundary parses" (boundaryRun.exitCode == 0)
  state := state.check "unchanged file output is byte-for-byte verbatim"
    (boundaryRun.stdout == boundaryText)
  let boundaryBefore ← IO.FS.readBinFile boundaryPath
  let inPlaceRun ← runModelgen binary
    ["--no-inductives", "--no-check", "--quiet", "-o", boundaryPath, boundaryPath]
  let boundaryAfter ← IO.FS.readBinFile boundaryPath
  state := state.check "literal in-place no-op does not truncate input" <|
    inPlaceRun.exitCode == 0 && inPlaceRun.stdout.isEmpty && boundaryAfter == boundaryBefore
  let aliasPath := s!"{scratch}/./main-cli-chunk-boundary.ndjson"
  let aliasRun ← runModelgen binary
    ["--no-inductives", "--no-check", "--quiet", "-o", aliasPath, boundaryPath]
  let boundaryAfterAlias ← IO.FS.readBinFile boundaryPath
  state := state.check "canonical-path in-place no-op does not truncate input" <|
    aliasRun.exitCode == 0 && aliasRun.stdout.isEmpty && boundaryAfterAlias == boundaryBefore
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
