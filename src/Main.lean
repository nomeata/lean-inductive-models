import Modelgen.Driver
import Modelgen.Check
import Modelgen.Mono
import Modelgen.Order

/-!
`modelgen [OPTIONS] IN.ndjson`

The command-line data model and option ordering live in `Modelgen.Cli`.  This
module owns only the IO boundary and the pipeline between the already separate
passes:

1. parse the input export;
2. optionally submit the complete input stream to Lean's kernel;
3. structurally check model families already in the input;
4. optionally monomorphize the input's universe levels;
5. put the resulting records in dependency and model-before-owner order;
6. generate the selected inductive models;
7. order the generated records;
8. structurally check and optionally kernel-check the final in-memory export;
9. emit it, unless output was disabled.

The export is the only stream written to stdout.  Reports and errors go to
stderr, and `--quiet` suppresses successful pass reports without hiding fatal
errors.
-/

open Lean Meta Modelgen

def exitAccepted : UInt32 := 0
def exitRejected : UInt32 := 1
def exitDeclined : UInt32 := 2
def exitToolError : UInt32 := 3

/-- Write an export to stdout or a file.  When no pass changed the export,
`verbatim` preserves the input bytes exactly. -/
def writeExport (target : String) (verbatim : Option String) (x : Export) : IO Unit := do
  let stream ← if target == "-" then
      IO.getStdout
    else
      pure (IO.FS.Stream.ofHandle (← IO.FS.Handle.mk target .write))
  match verbatim with
  | some text => stream.putStr text
  | none => x.writeTo stream
  stream.flush

def reportGeneration (config : Modelgen.Cli.Config) (rep : Modelgen.Report) : IO Unit := do
  if config.quiet then return
  let input := config.input.getD "<input>"
  if let some why := rep.unreplayable then
    IO.eprintln s!"{input}: passed through unchanged — {why}"
  for (name, count) in rep.generated do
    IO.eprintln s!"{name}: model of {count} declarations"
  for (name, names) in rep.spliced do
    IO.eprintln s!"{name}: prelude spliced — {", ".intercalate (names.map toString).toList}"
  for (name, why) in rep.exempt do IO.eprintln s!"{name}: exempt — {why}"
  for (name, why) in rep.declined do IO.eprintln s!"{name}: declined — {why}"
  unless rep.stmtChecked == 0 do
    IO.eprintln s!"statements: {rep.stmtChecked} compared, {rep.stmtErrors.size} differ"
  let calls ← Modelgen.LevelAlgebra.levelCalls.get
  let escapes ← Modelgen.LevelAlgebra.levelEscapes.get
  IO.eprintln s!"levels: {calls} planner comparisons, {escapes} escapes\
    {if Modelgen.LevelAlgebra.stockLevels then " (widening OFF — control run)" else ""}"

def reportMono (config : Modelgen.Cli.Config) (rep : Modelgen.Mono.Report) : IO Unit := do
  if config.quiet then return
  IO.eprintln s!"monomorphization: {rep.declsIn} declarations in, {rep.declsOut} out \
    ({rep.recordsIn} → {rep.recordsOut} records), {rep.groups} groups, \
    {rep.defaulted} defaulted"
  IO.eprintln s!"  copies per group: {rep.hist.toList}"
  IO.eprintln s!"  model groups: {rep.modelGroups} keyed, {rep.modelLoose} loose, \
    {rep.modelDeclined} declined; {rep.recRegen} recursors regenerated"

def violationMessage (violation : Modelgen.Check.Violation) : String :=
  violation.message

def orderErrorMessage : Modelgen.Order.Error → String
  | .duplicateName name first second =>
      s!"declaration name {name} occurs in both records {first} and {second}"
  | .cycle records declarations =>
      s!"declaration dependencies and model-before-owner constraints form a cycle at records \
        {records.toList}: {declarations.toList.map (·.toList)}"

def reportViolations (input stage : String)
    (violations : Array Modelgen.Check.Violation) : IO Unit := do
  for violation in violations do
    IO.eprintln s!"{input}: {stage} check failed: {violationMessage violation}"

/-- Report a successful structural pass with its exact amount of model-facing
work.  Failed passes retain their existing per-violation diagnostics. -/
def reportCheckSuccess (config : Modelgen.Cli.Config) (stage : String)
    (report : Modelgen.Check.Report) : IO Unit := do
  unless config.quiet do
    IO.eprintln s!"{stage} check: {report.familiesChecked} model families checked"

/-- Run the whole-stream kernel gate in a genuinely empty environment.  The
outer `Except` reports a tool failure; the inner one is Lean's rejection of
the submitted export. -/
def typeCheckExportIO (context : Core.Context) (x : Export) :
    IO (Except String (Except String Unit)) := do
  try
    let env ← mkEmptyEnvironment
    let (result, _) ← Lean.Core.CoreM.toIO
      (Lean.Meta.MetaM.run' (Modelgen.typeCheckExport x)) context { env }
    return .ok result
  catch error =>
    return .error (toString error)

def reportTypeCheckSuccess (config : Modelgen.Cli.Config) (stage : String) : IO Unit := do
  unless config.quiet do IO.eprintln s!"{stage} kernel check: accepted"

/-- A reported generation refusal is fulfilled when the exact owner already
had a complete, structurally valid public model in the input, or when another
selected route generated it during this run.  Basis exemptions never enter
this calculation. -/
def unsupportedDeclines (input : Export) (report : Modelgen.Report) : Array (Name × String) :=
  let discovered := Modelgen.Check.discover input
  let violations := Modelgen.Check.check input
  let alreadyCovered : Std.HashSet Name := discovered.foldl (init := {}) fun owners family =>
    if violations.any (·.familyOwner == family.owner) then owners else owners.insert family.owner
  let generated := report.generated.foldl (init := {}) fun owners entry => owners.insert entry.1
  report.declined.filter fun entry =>
    !alreadyCovered.contains entry.1 && !generated.contains entry.1

def run (config : Modelgen.Cli.Config) : IO UInt32 := do
  let input := config.input.getD ""
  let text? ← try
      if input == "-" then
        pure (some (← (← IO.getStdin).readToEnd))
      else
        pure (some (← IO.FS.readFile input))
    catch error =>
      IO.eprintln s!"{input}: {error}"
      pure none
  let some text := text? | return exitToolError
  let parsed ← match Modelgen.parse text (analyse := config.monoLevels) with
    | .error error =>
        IO.eprintln s!"{input}: parse error: {error}"
        return exitToolError
    | .ok parsedExport => pure parsedExport

  initSearchPath (← findSysroot)
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<modelgen>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }

  if config.typeCheckInput then
    match ← typeCheckExportIO context parsed with
    | .error message =>
      IO.eprintln s!"{input}: input kernel check failed internally: {message}"
      return exitToolError
    | .ok (.error message) =>
      IO.eprintln s!"{input}: input kernel check rejected: {message}"
      return exitRejected
    | .ok (.ok ()) => reportTypeCheckSuccess config "input"

  if config.checkInput then
    let report := Modelgen.Check.checkReport parsed
    unless report.violations.isEmpty do
      reportViolations input "input" report.violations
      return exitRejected
    reportCheckSuccess config "input" report

  -- Monomorphize before generation.  Generated simple/bootstrap support is
  -- already monomorphic at this point; feeding that support back through Mono
  -- would instead ask the optional pass to infer instantiations for its
  -- carried primitive basis, which has no such instantiation relation.
  let generationInput ← if config.monoLevels then do
      let result ← try
          let ((output, report), _) ← Lean.Core.CoreM.toIO
            (Lean.Meta.MetaM.run'
              (Modelgen.Mono.monomorphize parsed { check := true })) context { env }
          pure (Except.ok (output, report))
        catch error =>
          pure (Except.error (toString error))
      match result with
      | .error message =>
          IO.eprintln s!"{input}: monomorphization failed: {message}"
          return exitToolError
      | .ok (output, report) =>
          if let some why := report.refused then
            IO.eprintln s!"{input}: monomorphization refused the export: {why}"
            return exitToolError
          unless report.errors.isEmpty do
            IO.eprintln s!"{input}: monomorphization produced {report.errors.size} errors"
            for error in report.errors do IO.eprintln s!"  ! {error}"
            return exitToolError
          reportMono config report
          match Modelgen.Order.reorder output with
          | .error error =>
              IO.eprintln s!"{input}: cannot order monomorphized input: \
                {orderErrorMessage error}"
              return exitRejected
          | .ok orderedOutput => pure orderedOutput
    else
      pure parsed

  let generated ← try
      let ((decls, report), _) ← Lean.Core.CoreM.toIO
        (Lean.Meta.MetaM.run' (Modelgen.runFilter generationInput false config)) context { env }
      pure (Except.ok (decls, report))
    catch error =>
      pure (Except.error (toString error))
  let (decls, generationReport) ← match generated with
    | .error message =>
        IO.eprintln s!"{input}: internal error: {message}"
        return exitToolError
    | .ok result => pure result

  reportGeneration config generationReport
  if let some why := generationReport.unreplayable then
    IO.eprintln s!"{input}: kernel rejected an input declaration during generation: {why}"
    return exitRejected
  unless generationReport.stmtErrors.isEmpty do
    IO.eprintln s!"{input}: internal error: {generationReport.stmtErrors.size} generated \
      statements differ from their exact exported owner interface; no output written"
    for error in generationReport.stmtErrors do IO.eprintln s!"  ! {error}"
    return exitToolError

  let transformed : Export := { generationInput with decls }
  let finalExport ← match Modelgen.Order.reorder transformed with
    | .error error =>
        IO.eprintln s!"{input}: cannot order output: {orderErrorMessage error}"
        return exitRejected
    | .ok output => pure output

  if config.checkOutput then
    let report := Modelgen.Check.checkReport finalExport
    unless report.violations.isEmpty do
      reportViolations input "output" report.violations
      return exitRejected
    reportCheckSuccess config "output" report

  if config.typeCheckOutput then
    match ← typeCheckExportIO context finalExport with
    | .error message =>
      IO.eprintln s!"{input}: output kernel check failed internally: {message}"
      return exitToolError
    | .ok (.error message) =>
      IO.eprintln s!"{input}: output kernel check rejected: {message}"
      return exitRejected
    | .ok (.ok ()) => reportTypeCheckSuccess config "output"

  if config.output then
    let unchanged := !config.monoLevels && finalExport.decls == parsed.decls
    try
      writeExport config.outputTarget (if unchanged then some text else none) finalExport
    catch error =>
      IO.eprintln s!"{config.outputTarget}: cannot write output: {error}"
      return exitToolError
  if !(unsupportedDeclines parsed generationReport).isEmpty then return exitDeclined
  return exitAccepted

def main (args : List String) : IO UInt32 := do
  match Modelgen.Cli.parseArgs args with
  | .error error =>
      IO.eprintln error
      IO.eprintln Modelgen.Cli.usage
      return exitToolError
  | .ok config => run config
