import InductiveModels.Cli

open InductiveModels.Cli

structure TestState where
  passed : Nat := 0
  failed : Nat := 0

def TestState.check (state : TestState) (label : String) (condition : Bool) : IO TestState := do
  if condition then
    return { state with passed := state.passed + 1 }
  else
    IO.eprintln s!"FAIL: {label}"
    return { state with failed := state.failed + 1 }

def TestState.expect (state : TestState) (label : String) (args : List String)
    (predicate : Config → Bool) : IO TestState := do
  match parseArgs args with
  | .error error =>
    IO.eprintln s!"FAIL: {label}: unexpected parse error: {error}"
    return { state with failed := state.failed + 1 }
  | .ok config => state.check label (predicate config)

def TestState.reject (state : TestState) (label : String) (args : List String) : IO TestState := do
  state.check label (match parseArgs args with | .error _ => true | .ok _ => false)

def main : IO UInt32 := do
  let mut state : TestState := {}

  state ← state.expect "defaults" ["in.ndjson"] fun config =>
    config.input == some "in.ndjson" &&
    config.nested && config.mutualModels && config.simple && config.basic &&
    config.checkInput && config.checkOutput &&
    !config.typeCheckInput && config.typeCheckOutput &&
    config.output && config.outputTarget == "-" && !config.quiet

  state ← state.expect "all individual negative forms" [
      "--no-nested", "--no-mutual", "--no-simple", "--no-basic",
      "--no-check-input", "--no-check-output",
      "--no-type-check-input", "--no-type-check-output",
      "--no-output", "--no-quiet", "in.ndjson"] fun config =>
    !config.nested && !config.mutualModels && !config.simple && !config.basic &&
    !config.checkInput && !config.checkOutput &&
    !config.typeCheckInput && !config.typeCheckOutput &&
    !config.output && !config.quiet

  state ← state.expect "inductives bundle then individual override"
    ["--no-inductives", "--simple", "in.ndjson"] fun config =>
      !config.nested && !config.mutualModels && config.simple && !config.basic
  state ← state.expect "individual override then inductives bundle"
    ["--no-basic", "--inductives", "in.ndjson"] fun config =>
      config.nested && config.mutualModels && config.simple && config.basic
  state ← state.expect "check bundle then individual override"
    ["--no-check", "--check-output", "in.ndjson"] fun config =>
      !config.checkInput && config.checkOutput
  state ← state.expect "individual override then check bundle"
    ["--no-check-input", "--check", "in.ndjson"] fun config =>
      config.checkInput && config.checkOutput
  state ← state.expect "kernel verdict gates are independent"
    ["--type-check-input", "--type-check-output", "--no-type-check-input", "in.ndjson"]
    fun config => !config.typeCheckInput && config.typeCheckOutput
  state ← state.expect "output kernel default has an explicit reversible opt-out"
    ["--no-type-check-output", "--type-check-output", "--no-type-check-output",
      "in.ndjson"] fun config => !config.typeCheckOutput
  state ← state.expect "structural check bundle does not enable kernel verdicts"
    ["--type-check-input", "--no-check", "--check", "in.ndjson"] fun config =>
      config.checkInput && config.checkOutput && config.typeCheckInput &&
        config.typeCheckOutput
  state ← state.expect "Arena CI keeps generation and every verdict gate enabled" [
      "--inductives", "--check-input", "--check-output", "--type-check-input",
      "--type-check-output", "--no-output", "in.ndjson"] fun config =>
    config.nested && config.mutualModels && config.simple && config.basic &&
      config.checkInput && config.checkOutput &&
      config.typeCheckInput && config.typeCheckOutput && !config.output
  state ← state.expect "positive option restores default-on boolean"
    ["--no-mutual", "--mutual", "in.ndjson"] fun config => config.mutualModels
  state ← state.expect "short output target"
    ["in.ndjson", "-o", "out.ndjson"] fun config =>
      config.output && config.outputTarget == "out.ndjson"
  state ← state.expect "no-output retains selected target"
    ["-o", "out.ndjson", "--no-output", "in.ndjson"] fun config =>
      !config.output && config.outputTarget == "out.ndjson"
  state ← state.expect "output re-enables retained target"
    ["-o", "out.ndjson", "--no-output", "--output", "in.ndjson"] fun config =>
      config.output && config.outputTarget == "out.ndjson"
  state ← state.expect "later -o re-enables output"
    ["--no-output", "-o", "other.ndjson", "in.ndjson"] fun config =>
      config.output && config.outputTarget == "other.ndjson"
  state ← state.expect "stdout target is explicit"
    ["-o", "-", "in.ndjson"] fun config => config.output && config.outputTarget == "-"
  state ← state.expect "bare dash is standard input" ["-"] fun config =>
    config.input == some "-"

  state ← state.expect "quiet is reversible"
    ["--quiet", "--no-quiet", "in.ndjson"] fun config => !config.quiet

  state ← state.expect "Acc belongs to basic" ["--no-inductives", "--basic", "in"]
    fun config => config.modelsSimpleInput `Acc && !config.modelsSimpleInput `List
  state ← state.expect "Nonempty belongs to basic" ["--no-inductives", "--basic", "in"]
    fun config => config.modelsSimpleInput `Nonempty && !config.modelsSimpleInput `Option
  state ← state.expect "ordinary simple excludes basic names"
    ["--no-inductives", "--simple", "in"] fun config =>
      !config.modelsSimpleInput `Acc && !config.modelsSimpleInput `Nonempty &&
      config.modelsSimpleInput `List

  state ← state.reject "missing input" []
  state ← state.reject "unknown option" ["--wat", "in.ndjson"]
  state ← state.reject "missing -o operand" ["in.ndjson", "-o"]
  state ← state.reject "multiple positional inputs" ["one.ndjson", "two.ndjson"]

  if state.failed == 0 then
    IO.println s!"CLI parser: {state.passed} tests passed"
    return 0
  else
    IO.eprintln s!"CLI parser: {state.failed} failed, {state.passed} passed"
    return 1
