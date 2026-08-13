import Modelgen.Driver
import Modelgen.Check
import Modelgen.Mono
import Modelgen.Order
import Modelgen.Output
import Modelgen.Spool
import Modelgen.Supervisor

/-!
`lean-inductive-models [OPTIONS] IN.ndjson`

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

/-- Write the parsed export rather than reopening the input path. This keeps
the output tied to the bytes that passed parsing and checking even if the
input is replaced or mutated while a long generation pass is running. Named
paths are installed transactionally by [`Modelgen.Output.write`]. -/
def writeExport (target : String) (x : Export) : IO Unit :=
  Modelgen.Output.write target x.writeTo

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
selected route generated it during this run. A noncanonical reserved basis
owner remains unsupported regardless of either condition. -/
def unsupportedDeclines (input : Export) (report : Modelgen.Report) : Array (Name × String) :=
  if report.declined.isEmpty then
    #[]
  else
    let discovered := Modelgen.Check.discover input
    let violations := Modelgen.Check.check input
    let alreadyCovered := discovered.foldl (init := ({} : Std.HashSet Name)) fun owners family =>
      if violations.any (·.familyOwner == family.owner) then owners else owners.insert family.owner
    let generated := report.generated.foldl (init := ({} : Std.HashSet Name))
      fun owners entry => owners.insert entry.1
    report.declined.filter fun entry =>
      Modelgen.declineIsUnsupported alreadyCovered generated entry.1

/-- Initial internal fast-path boundary. Structural output checking consumes
the compact report certified while each family was live. Output kernel checking
must still replay the exact final byte stream and therefore retains the legacy
in-memory path. Monomorphization rewrites source declarations, while a no-output
or no-generation invocation has no staged payload to compose. -/
def stagedModeEligible (config : Modelgen.Cli.Config) : Bool :=
  config.output && Modelgen.generationEnabled config && !config.monoLevels &&
    !config.typeCheckOutput

private structure RawStage where
  workspace : Modelgen.Spool.Workspace
  tee : Modelgen.Spool.ParseTee
  certificate : Modelgen.RawCertificate
  sizes : Modelgen.RawSpoolSizes

private inductive FilterOutput where
  | full (declarations : Array Modelgen.EDecl)
  | staged (raw : RawStage) (stage : Modelgen.Spool.IslandStage)
      (plan : Modelgen.StagedPlan)

/-- Optional A/B and test diagnostic. This observes the actual filter result;
it never enables staging or changes eligibility. -/
private def reportOutputBackend (output : FilterOutput) : IO Unit := do
  if (← IO.getEnv "LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE") == some "1" then
    IO.eprintln s!"output backend: {match output with
      | .full .. => "legacy"
      | .staged .. => "staged"}"

private def mixedComposition (raw : RawStage) (sealed : Modelgen.Spool.SealedIsland)
    (spans : Array Modelgen.StagedDeclarationSpan) : Modelgen.Spool.MixedComposition :=
  { sourceMetadataPath := raw.tee.metadata.path
    sourceArenaPath := raw.tee.arena.path
    sourceDeclarationPath := raw.tee.declarations.path
    sourceSizes := raw.sizes
    generatedArenaPath := sealed.arenaPath
    generatedDeclarationPath := sealed.declarationPath
    generatedArenaSize := sealed.arenaSize
    generatedDeclarationSize := sealed.declarationSize
    declarations := spans.map fun span => match span with
      | .source span => .source { offset := span.offset, length := span.bytes }
      | .generated span => .generated span }

private def runWithWorkspace (config : Modelgen.Cli.Config)
    (workspace? : Option Modelgen.Spool.Workspace) : IO UInt32 := do
  let input := config.input.getD ""
  -- Reserve every spool leaf before consuming the input. Failure to establish
  -- the optional tee selects the historical parser; an error after parsing has
  -- begun remains a real IO failure and never reruns a consumed stream.
  let tee? ← match workspace? with
    | none => pure none
    | some workspace => try
        pure (some (← Modelgen.Spool.ParseTee.create workspace))
      catch _ => pure none
  let parsed? ← try
      if input == "-" then
        let stdin ← IO.getStdin
        let result ← match tee? with
          | none => do
            let result ← Modelgen.parseStream stdin
              (analyse := config.monoLevels)
              (allowDuplicateNames := true)
            pure (result.map fun x => (x, none))
          | some tee => do
            let result ← Modelgen.parseStreamWithSink stdin tee.sink
              (analyse := config.monoLevels)
              (allowDuplicateNames := true)
            pure (result.map fun (x, certificate) => (x, some (tee, certificate)))
        pure (some result)
      else
        IO.FS.withFile input .read fun handle => do
          let result ← match tee? with
            | none => do
              let result ← Modelgen.parseHandle handle
                (analyse := config.monoLevels)
                (allowDuplicateNames := true)
              pure (result.map fun x => (x, none))
            | some tee => do
              let result ← Modelgen.parseHandleWithSink handle tee.sink
                (analyse := config.monoLevels)
                (allowDuplicateNames := true)
              pure (result.map fun (x, certificate) => (x, some (tee, certificate)))
          pure (some result)
    catch error =>
      IO.eprintln s!"{input}: {error}"
      pure none
  let some parsedResult := parsed? | return exitToolError
  let (parsed, rawStage?) ← match parsedResult with
    | .error error =>
        IO.eprintln s!"{input}: parse error: {error}"
        return exitToolError
    | .ok (parsedExport, stage?) =>
      if let some (tee, certificate) := stage? then
        let sizes ← tee.finish
        if Modelgen.Spool.rawFastPathEligible certificate sizes
            parsedExport.decls.size config.monoLevels then
          let some workspace := workspace?
            | throw <| IO.userError "certified raw parse lost its spool workspace"
          pure (parsedExport, some { workspace, tee, certificate, sizes })
        else
          pure (parsedExport, none)
      else
        pure (parsedExport, none)

  if let .error message := parsed.validateUniqueDeclarationNames then
    IO.eprintln s!"{input}: invalid export: {message}"
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
              return exitToolError
          | .ok orderedOutput => pure orderedOutput
    else
      pure parsed

  let (filterOutput, generationReport) ← if Modelgen.generationEnabled config then do
      let generated : Except String (FilterOutput × Modelgen.Report) ← try
          if let some raw := rawStage? then
            let levelCallsBefore ← Modelgen.LevelAlgebra.levelCalls.get
            let levelEscapesBefore ← Modelgen.LevelAlgebra.levelEscapes.get
            let stage ← Modelgen.Spool.IslandStage.create raw.workspace
              (Modelgen.Writer.Cursor.ofRaw raw.certificate.cursor)
            let ((report, plan), _) ← Lean.Core.CoreM.toIO
              (Lean.Meta.MetaM.run'
                (Modelgen.runFilterStaged generationInput false config (.ofStage stage)))
              context { env }
            match plan.unavailable? with
            | none => pure (Except.ok (FilterOutput.staged raw stage plan, report))
            | some _ =>
              Modelgen.LevelAlgebra.levelCalls.set levelCallsBefore
              Modelgen.LevelAlgebra.levelEscapes.set levelEscapesBefore
              let ((decls, fallbackReport), _) ← Lean.Core.CoreM.toIO
                (Lean.Meta.MetaM.run' (Modelgen.runFilter generationInput false config))
                context { env }
              pure (Except.ok (FilterOutput.full decls, fallbackReport))
          else
            let ((decls, report), _) ← Lean.Core.CoreM.toIO
              (Lean.Meta.MetaM.run' (Modelgen.runFilter generationInput false config))
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
      pure (FilterOutput.full generationInput.decls, ({} : Modelgen.Report))

  reportOutputBackend filterOutput
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
  | .staged raw stage plan =>
    if config.checkOutput then
      unless plan.checkReport.violations.isEmpty do
        reportViolations input "output" plan.checkReport.violations
        return exitRejected
      reportCheckSuccess config "output" plan.checkReport
    -- Output kernel checking remains on the full-AST path. Seal and validate
    -- the plan before the output transaction, then validate every physical
    -- file before its first destination byte.
    try
      let sealed ← stage.finish
      let spans ← match plan.declarationSpans raw.certificate raw.sizes
          parsed.decls.size sealed with
        | .ok spans => pure spans
        | .error message => throw <| IO.userError s!"invalid staged output plan: {message}"
      let composition := mixedComposition raw sealed spans
      match composition.validate with
      | .ok _ => pure ()
      | .error message => throw <| IO.userError s!"invalid staged composition: {message}"
      Modelgen.Output.write config.outputTarget composition.emit
    catch error =>
      IO.eprintln s!"{config.outputTarget}: cannot write output: {error}"
      return exitToolError
    return outcome
  | .full decls =>
    let transformed : Export := { generationInput with decls }
    let finalExport ← if Modelgen.generationEnabled config || config.monoLevels then
        match Modelgen.Order.reorder transformed with
        | .error error =>
            IO.eprintln s!"{input}: cannot order output: {orderErrorMessage error}"
            return exitToolError
        | .ok output => pure output
      else
        pure transformed

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
      try
        writeExport config.outputTarget finalExport
      catch error =>
        IO.eprintln s!"{config.outputTarget}: cannot write output: {error}"
        return exitToolError
    return outcome

def run (config : Modelgen.Cli.Config) : IO UInt32 := do
  -- Canonical eligible generation uses bounded-memory staged output by default.
  -- The legacy override is retained for deliberate A/B measurements. Statically
  -- ineligible modes never tee their input, and planner trace mode stays on the
  -- full-AST path so a private failed staging attempt cannot duplicate trace lines.
  if (← IO.getEnv "LEAN_INDUCTIVE_MODELS_LEGACY_OUTPUT") != some "1" &&
      (← IO.getEnv "LEAN_INDUCTIVE_MODELS_PLANNER_LEVEL_TRACE") != some "1" &&
      stagedModeEligible config then
    let scratch := (← IO.currentDir) / "_tmp"
    Modelgen.Spool.withOptionalWorkspace scratch (runWithWorkspace config)
  else
    runWithWorkspace config none

def workerMain (args : List String) : IO UInt32 := do
  Modelgen.Output.containToolErrors do
    match Modelgen.Cli.parseArgs args with
    | .error error =>
        IO.eprintln error
        IO.eprintln Modelgen.Cli.usage
        return exitToolError
    | .ok config => run config

def main (args : List String) : IO UInt32 :=
  Modelgen.Supervisor.supervise workerMain args
