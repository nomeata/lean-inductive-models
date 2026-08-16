import InductiveModels.Driver
import InductiveModels.Check
import InductiveModels.Order
import InductiveModels.Output

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

/-- Classify generation declines from compact input-family certificates. This
is the planned/streaming equivalent of [`unsupportedDeclines`] and does not
materialize source declarations. -/
def unsupportedDeclinesFromOwners (coveredInputOwners : Array Name)
    (report : InductiveModels.Report) : Array (Name × String) :=
  let alreadyCovered := coveredInputOwners.foldl
    (fun owners owner => owners.insert owner) ({} : Std.HashSet Name)
  let generated := report.generated.foldl (init := ({} : Std.HashSet Name))
    fun owners entry => owners.insert entry.1
  report.declined.filter fun entry =>
    InductiveModels.declineIsUnsupported alreadyCovered generated entry.1

/-- Shared compact-generation boundary. Structural validation and optional
generated-island checking consume records while each family is live. -/
def compactModeEligible (config : InductiveModels.Cli.Config) : Bool :=
  InductiveModels.generationEnabled config

/-- No-output compact generation retains value-only verdict certificates and
never creates a generated-output workspace. -/
def discardModeEligible (config : InductiveModels.Cli.Config) : Bool :=
  !config.output && compactModeEligible config

private inductive FilterOutput where
  | full (declarations : Array InductiveModels.EDecl)
  | discarded (plan : InductiveModels.CompactPlan)

private inductive OutputBackend where
  | full | compactDiscard | declarationStream

/-- Optional A/B and test diagnostic. This observes the actual filter result;
it never changes output retention or route eligibility. -/
private def reportOutputBackend (backend : OutputBackend) (generatedKernelChecks : Nat) : IO Unit := do
  if (← IO.getEnv "LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE") == some "1" then
    IO.eprintln s!"output backend: {match backend with
      | .full => "legacy"
      | .compactDiscard => "compact-discard"
      | .declarationStream => "declaration-stream"}"
    IO.eprintln s!"generated kernel checks: {generatedKernelChecks}"

private abbrev StreamWriterRef := IO.Ref (Option InductiveModels.DeclarationStreamWriter)

private def readStreamWriter (writer : StreamWriterRef) : IO InductiveModels.DeclarationStreamWriter := do
  let some current ← writer.get
    | throw <| IO.userError "declaration stream writer is already in use"
  return current

private def writeStreamEvent (writer : StreamWriterRef)
    (stream : IO.FS.Stream) : InductiveModels.StreamOutputEmitter := fun event => do
  let declarations := match event with
    | .generatedIsland records => records
    | .source record => #[record]
  for declaration in declarations do
    -- Atomically remove the writer from the ref before extending its persistent
    -- maps. A plain `get` would leave an RC sibling in the ref and force COW.
    let some current ← writer.modifyGet fun current => (current, none)
      | throwError "declaration stream writer is already in use"
    writer.set (some (← current.writeDeclaration stream declaration))

/-- Apply every post-generation verdict before deciding whether a named
streaming sibling may become visible. -/
private def finishStreamingVerdict (config : InductiveModels.Cli.Config)
    (input : String) (report : InductiveModels.Report)
    (plan : InductiveModels.CompactPlan) :
    IO (InductiveModels.Output.TransactionResult UInt32) := do
  reportOutputBackend .declarationStream report.generatedKernelChecks
  reportGeneration config report
  if let some why := report.unreplayable then
    IO.eprintln s!"{input}: kernel rejected an input declaration during generation: {why}"
    return .rollback exitRejected
  unless report.stmtErrors.isEmpty do
    IO.eprintln s!"{input}: internal error: {report.stmtErrors.size} generated \
      statements differ from their exact exported owner interface; no output written"
    for error in report.stmtErrors do IO.eprintln s!"  ! {error}"
    return .rollback exitToolError
  if config.checkOutput then
    unless plan.checkReport.violations.isEmpty do
      reportViolations input "output" plan.checkReport.violations
      return .rollback exitRejected
    reportCheckSuccess config "output" plan.checkReport
  if config.typeCheckGenerated then
    match report.generatedKernelRejected with
    | some message =>
      IO.eprintln s!"{input}: generated kernel check rejected: {message}"
      return .rollback exitRejected
    | none => reportTypeCheckSuccess config "generated"
  let outcome := if (unsupportedDeclinesFromOwners plan.coveredInputOwners report).isEmpty then
      exitAccepted
    else exitDeclined
  return .commit outcome

private def runStreamingParsedGeneration (config : InductiveModels.Cli.Config)
    (parsed : Export) (context : Core.Context) (env : Environment) : IO UInt32 := do
  let input := config.input.getD ""
  try
    InductiveModels.Output.transaction config.outputTarget fun stream => do
      let writer ← IO.mkRef (some (←
        InductiveModels.DeclarationStreamWriter.start parsed.metaLine stream))
      let generated : Except String (InductiveModels.Report × InductiveModels.CompactPlan) ← try
        let (result, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run'
          (InductiveModels.runFilterStreaming parsed false config
            (writeStreamEvent writer stream))) context { env }
        pure (Except.ok result)
      catch error => pure (Except.error (toString error))
      let (report, plan) ← match generated with
        | .ok result => pure result
        | .error message =>
          IO.eprintln s!"{input}: internal error: {message}"
          return InductiveModels.Output.TransactionResult.rollback exitToolError
      let writerState ← readStreamWriter writer
      writerState.finish stream
      unless report.unreplayable.isSome || writerState.declarationsWritten ==
          plan.streamStats.sourceRecords + plan.streamStats.generatedRecords do
        IO.eprintln s!"{input}: internal error: streaming writer/driver counts disagree"
        return InductiveModels.Output.TransactionResult.rollback exitToolError
      finishStreamingVerdict config input report plan
  catch error =>
    IO.eprintln s!"{config.outputTarget}: cannot write output: {error}"
    return exitToolError

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

  if InductiveModels.generationEnabled config && config.output then
    return ← runStreamingParsedGeneration config parsed context env

  let generationInput := parsed

  let (filterOutput, generationReport) ← if InductiveModels.generationEnabled config then do
      let generated : Except String (FilterOutput × InductiveModels.Report) ← try
          if compactEnabled && discardModeEligible config then
            let ((report, plan), _) ← Lean.Core.CoreM.toIO
              (Lean.Meta.MetaM.run'
                (InductiveModels.runFilterDiscarding generationInput false config))
              context { env }
            pure (Except.ok (FilterOutput.discarded plan, report))
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

  reportOutputBackend (match filterOutput with
    | .full .. => .full
    | .discarded .. => .compactDiscard) generationReport.generatedKernelChecks
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
    if config.typeCheckGenerated then
      match generationReport.generatedKernelRejected with
      | some message =>
        IO.eprintln s!"{input}: generated kernel check rejected: {message}"
        return exitRejected
      | none => reportTypeCheckSuccess config "generated"
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

    if config.typeCheckGenerated then
      match generationReport.generatedKernelRejected with
      | some message =>
        IO.eprintln s!"{input}: generated kernel check rejected: {message}"
        return exitRejected
      | none =>
        -- Every generated island was checked against its trusted source
        -- prefix at close. Input is governed only by typeCheckInput.
        reportTypeCheckSuccess config "generated"

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

def run (config : InductiveModels.Cli.Config) : IO UInt32 := do
  -- The legacy override remains a deliberate A/B switch for no-output compact
  -- modes. Actual generated output is declaration-wise, off the one parse.
  let compactEnabled :=
    (← IO.getEnv "LEAN_INDUCTIVE_MODELS_LEGACY_OUTPUT") != some "1" &&
      (← IO.getEnv "LEAN_INDUCTIVE_MODELS_PLANNER_LEVEL_TRACE") != some "1"
  runPipeline config compactEnabled

def main (args : List String) : IO UInt32 := do
  InductiveModels.Output.containToolErrors do
    match InductiveModels.Cli.parseArgs args with
    | .error error =>
        IO.eprintln error
        IO.eprintln InductiveModels.Cli.usage
        return exitToolError
    | .ok config => run config
