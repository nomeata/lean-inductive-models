import Lean

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

def runModelgen (binary : String) (args : List String) : IO IO.Process.Output :=
  IO.Process.output { cmd := binary, args := args.toArray }

def main (args : List String) : IO UInt32 := do
  let root := args.head?.getD "."
  let binary := s!"{root}/.lake/build/bin/modelgen"
  unless ← System.FilePath.pathExists binary do
    IO.eprintln s!"mainclitest: missing {binary}; run `lake build modelgen` first"
    return 1

  let scratch := s!"{root}/_tmp"
  IO.FS.createDirAll scratch
  let nested := s!"{root}/tests/nested_iota.ndjson"
  -- This fixture contains `Expr.proj`, so success also pins that the integrated
  -- path asked the reader for projection analysis.
  let mono := s!"{root}/monotests/mono_proj.ndjson"
  let mut state : TestState := {}

  -- All defaults are exercised here, including stdout output and both checks.
  -- This succeeds once all generated model families precede their owners; it
  -- is the integration seam between the CLI and the ordering repair.
  let defaults ← runModelgen binary [nested]
  state := state.check "defaults succeed" (defaults.exitCode == 0)
  state := state.check "defaults write an export to stdout" (!defaults.stdout.isEmpty)
  state := state.check "diagnostics stay off stdout"
    ((defaults.stdout.splitOn "model of").length == 1)

  -- Feed the generated result back through the default checker.  This is an
  -- actual input-side model family, rather than the vacuous check of an
  -- unmodelled source fixture.
  let modeledPath := s!"{scratch}/main-cli-modeled.ndjson"
  IO.FS.writeFile modeledPath defaults.stdout
  let checkedAgain ← runModelgen binary ["--no-output", modeledPath]
  state := state.check "default input check accepts generated models"
    (checkedAgain.exitCode == 0 && checkedAgain.stdout.isEmpty)
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
  let poly := s!"{root}/tests/poly_nested_used.ndjson"
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
  IO.FS.removeFile monoModeledPath

  IO.println s!"main CLI: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1
