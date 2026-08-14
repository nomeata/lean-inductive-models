import InductiveModels.Driver
import InductiveModels.Check
import InductiveModels.Order
import InductiveModels.Output
import InductiveModels.Supervisor

/-!
`lean-inductive-models [OPTIONS] IN.ndjson`

The command-line data model and option ordering live in `InductiveModels.Cli`.  This
module owns only the IO boundary and the pipeline between the already separate
passes:

1. parse the input export;
2. optionally kernel-check the input declarations;
3. structurally check model families already in the input;
4. reject an input model that appears after its owner;
5. stream source declarations, generating each selected model immediately
    before its owner and optionally kernel-checking that generated island;
6. structurally check the constructively ordered output;
7. emit it, unless output was disabled.

The export is the only stream written to stdout.  Reports and errors go to
stderr, and `--quiet` suppresses successful pass reports without hiding fatal
errors.
-/

open Lean Meta InductiveModels

def exitAccepted : UInt32 := 0
def exitRejected : UInt32 := 1
def exitDeclined : UInt32 := 2
def exitToolError : UInt32 := 3

/-- Write the parsed export rather than reopening the input path. This keeps
the output tied to the bytes that passed parsing and checking even if the
input is replaced or mutated while a long generation pass is running. Named
paths are installed transactionally by [`InductiveModels.Output.write`]. -/
def writeExport (target : String) (x : Export) : IO Unit :=
  InductiveModels.Output.write target x.writeTo

def reportGeneration (config : InductiveModels.Cli.Config) (rep : InductiveModels.Report) : IO Unit := do
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
  let calls ← InductiveModels.LevelAlgebra.levelCalls.get
  let escapes ← InductiveModels.LevelAlgebra.levelEscapes.get
  IO.eprintln s!"levels: {calls} planner comparisons, {escapes} escapes\
    {if InductiveModels.LevelAlgebra.stockLevels then " (widening OFF — control run)" else ""}"

def violationMessage (violation : InductiveModels.Check.Violation) : String :=
  violation.message

def orderErrorMessage : InductiveModels.Order.Error → String
  | .duplicateName name first second =>
      s!"declaration name {name} occurs in both records {first} and {second}"
  | .cycle records declarations =>
      s!"declaration dependencies and model-before-owner constraints form a cycle at records \
        {records.toList}: {declarations.toList.map (·.toList)}"

def reportViolations (input stage : String)
    (violations : Array InductiveModels.Check.Violation) : IO Unit := do
  for violation in violations do
    IO.eprintln s!"{input}: {stage} check failed: {violationMessage violation}"

/-- Report a successful structural pass with its exact amount of model-facing
work.  Failed passes retain their existing per-violation diagnostics. -/
def reportCheckSuccess (config : InductiveModels.Cli.Config) (stage : String)
    (report : InductiveModels.Check.Report) : IO Unit := do
  unless config.quiet do
    IO.eprintln s!"{stage} check: {report.familiesChecked} model families checked"

/-- Run the requested input-only kernel gate in a genuinely empty environment. The
outer `Except` reports a tool failure; the inner one is Lean's rejection of
the submitted export. -/
def typeCheckExportIO (context : Core.Context) (x : Export) :
    IO (Except String (Except String Unit)) := do
  try
    let env ← mkEmptyEnvironment
    let (result, _) ← Lean.Core.CoreM.toIO
      (Lean.Meta.MetaM.run' (InductiveModels.typeCheckExport x)) context { env }
    return .ok result
  catch error =>
    return .error (toString error)

def reportTypeCheckSuccess (config : InductiveModels.Cli.Config) (stage : String) : IO Unit := do
  unless config.quiet do IO.eprintln s!"{stage} kernel check: accepted"

/-- A reported generation refusal is fulfilled when the exact owner already
had a complete, structurally valid public model in the input, or when another
selected route generated it during this run. A noncanonical reserved basis
owner remains unsupported regardless of either condition. -/
def unsupportedDeclines (input : Export) (report : InductiveModels.Report) : Array (Name × String) :=
  if report.declined.isEmpty then
    #[]
  else
    let discovered := InductiveModels.Check.discover input
    let violations := InductiveModels.Check.check input
    let alreadyCovered := discovered.foldl (init := ({} : Std.HashSet Name)) fun owners family =>
      if violations.any (·.familyOwner == family.owner) then owners else owners.insert family.owner
    let generated := report.generated.foldl (init := ({} : Std.HashSet Name))
      fun owners entry => owners.insert entry.1
    report.declined.filter fun entry =>
      InductiveModels.declineIsUnsupported alreadyCovered generated entry.1

/-- Shared compact-generation boundary. Structural and direct kernel checking
consume records while each family is live. -/
def compactModeEligible (config : InductiveModels.Cli.Config) : Bool :=
  InductiveModels.generationEnabled config

/-- No-output compact generation retains value-only verdict certificates and
never creates a generated-output workspace or spool. The checked planned
subroute may separately use an input-only snapshot workspace. -/
def discardModeEligible (config : InductiveModels.Cli.Config) : Bool :=
  !config.output && compactModeEligible config

/-- The planned source reader pays for an input snapshot only when generated
declarations are checked as they are produced. Unchecked no-output generation
uses the ordinary in-memory compact-discard path and opens no workspace. -/
def plannedDiscardModeEligible (config : InductiveModels.Cli.Config) : Bool :=
  discardModeEligible config && config.typeCheckOutput

private inductive FilterOutput where
  | full (declarations : Array InductiveModels.EDecl)
  | discarded (plan : InductiveModels.CompactPlan)

/-- Optional A/B and test diagnostic. This observes the actual filter result;
it never changes output retention or route eligibility. -/
private def reportOutputBackend (output : FilterOutput) (outputKernelChecks : Nat) : IO Unit := do
  if (← IO.getEnv "LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE") == some "1" then
    IO.eprintln s!"output backend: {match output with
      | .full .. => "legacy"
      | .discarded .. => "compact-discard"}"
    IO.eprintln s!"generated kernel checks: {outputKernelChecks}"

private def reportPlannedRouteSelected : IO Unit := do
  if (← IO.getEnv "LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE") == some "1" then
    IO.eprintln "input route: planned-census"

private def runParsedPipeline (config : InductiveModels.Cli.Config)
    (compactEnabled : Bool) (parsed : Export) : IO UInt32 := do
  let input := config.input.getD ""
  if let .error message := parsed.validateUniqueDeclarationNames then
    IO.eprintln s!"{input}: invalid export: {message}"
    return exitRejected
  let inputOrderViolations :=
    (InductiveModels.SourceCensus.ofSource parsed).modelAfterOwnerViolations
  unless inputOrderViolations.isEmpty do
    reportViolations input "input" inputOrderViolations
    return exitRejected

  initSearchPath (← findSysroot)
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<lean-inductive-models>", fileMap := default,
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
    let report := InductiveModels.Check.checkReport parsed
    unless report.violations.isEmpty do
      reportViolations input "input" report.violations
      return exitRejected
    reportCheckSuccess config "input" report

  let generationInput := parsed

  let (filterOutput, generationReport) ← if InductiveModels.generationEnabled config then do
      let generated : Except String (FilterOutput × InductiveModels.Report) ← try
          if compactEnabled && discardModeEligible config then
            let levelCallsBefore ← InductiveModels.LevelAlgebra.levelCalls.get
            let levelEscapesBefore ← InductiveModels.LevelAlgebra.levelEscapes.get
            let ((report, plan), _) ← Lean.Core.CoreM.toIO
              (Lean.Meta.MetaM.run'
                (InductiveModels.runFilterDiscarding generationInput false config))
              context { env }
            match plan.unavailable? with
            | none => pure (Except.ok (FilterOutput.discarded plan, report))
            | some _ =>
              InductiveModels.LevelAlgebra.levelCalls.set levelCallsBefore
              InductiveModels.LevelAlgebra.levelEscapes.set levelEscapesBefore
              let ((decls, fallbackReport), _) ← Lean.Core.CoreM.toIO
                (Lean.Meta.MetaM.run' (InductiveModels.runFilter generationInput false config))
                context { env }
              pure (Except.ok (FilterOutput.full decls, fallbackReport))
          else
            let ((decls, report), _) ← Lean.Core.CoreM.toIO
              (Lean.Meta.MetaM.run' (InductiveModels.runFilter generationInput false config))
              context { env }
            pure (Except.ok (FilterOutput.full decls, report))
        catch error =>
          pure (Except.error (toString error))
      match generated with
      | .error message =>
          IO.eprintln s!"{input}: internal error: {message}"
          return exitToolError
      | .ok result => pure result
    else
      pure (FilterOutput.full generationInput.decls, ({} : InductiveModels.Report))

  reportOutputBackend filterOutput generationReport.outputKernelChecks
  reportGeneration config generationReport
  if let some why := generationReport.unreplayable then
    IO.eprintln s!"{input}: kernel rejected an input declaration during generation: {why}"
    return exitRejected
  unless generationReport.stmtErrors.isEmpty do
    IO.eprintln s!"{input}: internal error: {generationReport.stmtErrors.size} generated \
      statements differ from their exact exported owner interface; no output written"
    for error in generationReport.stmtErrors do IO.eprintln s!"  ! {error}"
    return exitToolError

  -- Force the final semantic verdict before opening an output sibling. The
  -- useful partial candidate is still written for a supported exit-2 decline,
  -- but no analysis remains which could fail after a named output is committed.
  let outcome :=
    if (unsupportedDeclines parsed generationReport).isEmpty then exitAccepted
    else exitDeclined
  match filterOutput with
  | .discarded plan =>
    if config.checkOutput then
      unless plan.checkReport.violations.isEmpty do
        reportViolations input "output" plan.checkReport.violations
        return exitRejected
      reportCheckSuccess config "output" plan.checkReport
    if config.typeCheckOutput then
      match generationReport.outputKernelRejected with
      | some message =>
        IO.eprintln s!"{input}: output kernel check rejected: {message}"
        return exitRejected
      | none => reportTypeCheckSuccess config "output"
    return outcome
  | .full decls =>
    let transformed : Export := { generationInput with decls }
    -- Generation emits each live model island immediately before its source
    -- owner and otherwise preserves source order. That constructive stream is
    -- the output; there is no final global ordering pass.
    let finalExport := transformed

    if config.checkOutput then
      let report := InductiveModels.Check.checkReport finalExport
      unless report.violations.isEmpty do
        reportViolations input "output" report.violations
        return exitRejected
      reportCheckSuccess config "output" report

    if config.typeCheckOutput then
      match generationReport.outputKernelRejected with
      | some message =>
        IO.eprintln s!"{input}: output kernel check rejected: {message}"
        return exitRejected
      | none =>
        -- Every generated island was checked against its trusted source
        -- prefix at close. Input is governed only by typeCheckInput.
        reportTypeCheckSuccess config "output"

    if config.output then
      try
        writeExport config.outputTarget finalExport
      catch error =>
        IO.eprintln s!"{config.outputTarget}: cannot write output: {error}"
        return exitToolError
    return outcome

private def runPipeline (config : InductiveModels.Cli.Config)
    (compactEnabled : Bool) : IO UInt32 := do
  let input := config.input.getD ""
  let parsed? ← try
      if input == "-" then
        let stdin ← IO.getStdin
        pure (some (← InductiveModels.parseStream stdin
          (options := { allowDuplicateNames := true })))
      else
        IO.FS.withFile input .read fun handle => do
          pure (some (← InductiveModels.parseHandle handle
            (options := { allowDuplicateNames := true })))
    catch error =>
      IO.eprintln s!"{input}: {error}"
      pure none
  let some parsedResult := parsed? | return exitToolError
  let parsed ← match parsedResult with
    | .error error =>
        IO.eprintln s!"{input}: parse error: {error}"
        return exitToolError
    | .ok parsedExport => pure parsedExport
  runParsedPipeline config compactEnabled parsed

/-- Declaration-discarding input path for kernel-checked generated no-output runs. The
physical snapshot is input provenance/fallback state only; generated logical
output stays as live `EDecl` values throughout. -/
private def runPlannedDiscardPipeline (config : InductiveModels.Cli.Config) : IO UInt32 := do
  let input := config.input.getD ""
  let scratch := (← IO.currentDir) / "_tmp"
  let consumed ← IO.mkRef false
  try
    IO.FS.createDirAll scratch
    InductiveModels.Spool.withWorkspace scratch fun workspace => do
      let tee ← InductiveModels.Spool.DirectInputTee.create workspace
      let parsedResult ← if input == "-" then
          consumed.set true
          InductiveModels.parsePlannedSourceStreamWithDirectTee (← IO.getStdin) tee
            (options := { allowDuplicateNames := true })
        else
          IO.FS.withFile input .read fun handle => do
            consumed.set true
            InductiveModels.parsePlannedSourceWithDirectTee handle tee
              (options := { allowDuplicateNames := true })
      let planned ← match parsedResult with
        | .error message =>
          IO.eprintln s!"{input}: parse error: {message}"
          return exitToolError
        | .ok planned => pure planned
      if let .error message := planned.census.validateUniqueDeclarationNames then
        IO.eprintln s!"{input}: invalid export: {message}"
        return exitRejected
      let inputOrderViolations := planned.census.modelAfterOwnerViolations
      unless inputOrderViolations.isEmpty do
        reportViolations input "input" inputOrderViolations
        return exitRejected
      let sizes ← tee.finish
      let readerResult ← InductiveModels.Spool.PlannedSourceReader.createDirect
        tee planned.certificate sizes planned.envelope.declarationCount planned.envelope.arena
      let reader ← match readerResult with
        | .ok reader => pure reader
        | .error _ =>
          -- Parser-compatible arena overwrites cannot be reconstructed from a
          -- completed arena. Reparse the exact consumed input snapshot and use
          -- the ordinary full-AST pipeline with unchanged diagnostics.
          let fallback ← tee.parseFallback (options := { allowDuplicateNames := true })
          let parsed ← match fallback with
            | .ok parsed => pure parsed
            | .error message =>
              IO.eprintln s!"{input}: parse error: {message}"
              return exitToolError
          return ← runParsedPipeline config true parsed
      -- All later compatibility fallbacks can materialize exact declarations
      -- from the transferred parser arena, so the full raw snapshot can die.
      tee.releaseFallback

      initSearchPath (← findSysroot)
      let env ← importModules #[] {}
      let context : Core.Context :=
        { fileName := "<lean-inductive-models>", fileMap := default,
          maxHeartbeats := 0, maxRecDepth := 8192 }
      if config.checkInput then
        match ← InductiveModels.checkPlannedSource planned reader with
        | .error message =>
          IO.eprintln s!"{input}: internal error: planned input check failed: {message}"
          return exitToolError
        | .ok report =>
          unless report.violations.isEmpty do
            reportViolations input "input" report.violations
            return exitRejected
          reportCheckSuccess config "input" report

      let levelCallsBefore ← InductiveModels.LevelAlgebra.levelCalls.get
      let levelEscapesBefore ← InductiveModels.LevelAlgebra.levelEscapes.get
      let generated : Except String
          (InductiveModels.Report × InductiveModels.CompactPlan) ← try
        let (result, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run'
          (InductiveModels.runFilterDiscardingPlannedCensus
            planned reader false config)) context { env }
        pure (Except.ok result)
      catch error => pure (Except.error (toString error))
      let (generationReport, plan) ← match generated with
        | Except.error message =>
          InductiveModels.LevelAlgebra.levelCalls.set levelCallsBefore
          InductiveModels.LevelAlgebra.levelEscapes.set levelEscapesBefore
          let fallback ← InductiveModels.materializePlannedSource planned reader
          let parsed ← match fallback with
            | .ok parsed => pure parsed
            | .error fallbackMessage =>
              IO.eprintln s!"{input}: internal error: planned generation failed ({message}); \
                cannot materialize fallback: {fallbackMessage}"
              return exitToolError
          return ← runParsedPipeline { config with checkInput := false } true parsed
        | Except.ok result => pure result
      reportPlannedRouteSelected
      reportOutputBackend (.discarded plan) generationReport.outputKernelChecks
      reportGeneration config generationReport
      if let some why := generationReport.unreplayable then
        IO.eprintln s!"{input}: kernel rejected an input declaration during generation: {why}"
        return exitRejected
      unless generationReport.stmtErrors.isEmpty do
        IO.eprintln s!"{input}: internal error: {generationReport.stmtErrors.size} generated \
          statements differ from their exact exported owner interface; no output written"
        for error in generationReport.stmtErrors do IO.eprintln s!"  ! {error}"
        return exitToolError
      let outcome ← if generationReport.declined.isEmpty then pure exitAccepted else do
        let fallback ← InductiveModels.materializePlannedSource planned reader
        let source ← match fallback with
          | .ok source => pure source
          | .error message =>
            IO.eprintln s!"{input}: internal error: cannot classify direct declines: {message}"
            return exitToolError
        pure <| if (unsupportedDeclines source generationReport).isEmpty then
          exitAccepted else exitDeclined
      if config.checkOutput then
        unless plan.checkReport.violations.isEmpty do
          reportViolations input "output" plan.checkReport.violations
          return exitRejected
        reportCheckSuccess config "output" plan.checkReport
      if config.typeCheckOutput then
        match generationReport.outputKernelRejected with
        | some message =>
          IO.eprintln s!"{input}: output kernel check rejected: {message}"
          return exitRejected
        | none => reportTypeCheckSuccess config "output"
      return outcome
  catch error =>
    if ← consumed.get then
      IO.eprintln s!"{input}: internal error: planned input pipeline failed: {error}"
      return exitToolError
    runPipeline config true

def run (config : InductiveModels.Cli.Config) : IO UInt32 := do
  -- The legacy override remains a deliberate A/B switch for no-output compact
  -- modes. Every actual output uses the ordinary full-AST path.
  let compactEnabled :=
    (← IO.getEnv "LEAN_INDUCTIVE_MODELS_LEGACY_OUTPUT") != some "1" &&
      (← IO.getEnv "LEAN_INDUCTIVE_MODELS_PLANNER_LEVEL_TRACE") != some "1"
  if compactEnabled && plannedDiscardModeEligible config && !config.typeCheckInput then
    runPlannedDiscardPipeline config
  else
    runPipeline config compactEnabled

def workerMain (args : List String) : IO UInt32 := do
  InductiveModels.Output.containToolErrors do
    match InductiveModels.Cli.parseArgs args with
    | .error error =>
        IO.eprintln error
        IO.eprintln InductiveModels.Cli.usage
        return exitToolError
    | .ok config => run config

def main (args : List String) : IO UInt32 :=
  InductiveModels.Output.containToolErrors (InductiveModels.Supervisor.supervise workerMain args)
