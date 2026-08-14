import InductiveModels.Driver
import InductiveModels.Check
import InductiveModels.Mono
import InductiveModels.Order
import InductiveModels.Output
import InductiveModels.Spool
import InductiveModels.Supervisor

/-!
`lean-inductive-models [OPTIONS] IN.ndjson`

The command-line data model and option ordering live in `InductiveModels.Cli`.  This
module owns only the IO boundary and the pipeline between the already separate
passes:

1. parse the input export;
2. optionally submit the complete input stream to Lean's kernel;
3. structurally check model families already in the input;
4. optionally monomorphize the input's universe levels;
5. put the resulting records in dependency and model-before-owner order;
6. generate the selected inductive models;
7. order the generated records;
8. structurally check and optionally kernel-check the final export;
9. emit it, unless output was disabled.

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

private def freshSignalPointVariable : String :=
  "LEAN_INDUCTIVE_MODELS_TEST_FRESH_SIGNAL_POINT"

private def freshCheckerFailureVariable : String :=
  "LEAN_INDUCTIVE_MODELS_TEST_FRESH_CHECKER_FAILURE"

/-- Write one parent-registered private candidate directly. Atomic replacement
is unnecessary because the path is never published; direct exclusive creation
ensures a signal can leave at most this one exact workspace-owned leaf. -/
private def writePrivateCandidate (target : String)
    (emit : IO.FS.Stream → IO Unit) : IO Unit := do
  unless target != "-" do throw <| IO.userError "private candidate requires a named path"
  let path : System.FilePath := target
  let handle ← IO.FS.Handle.mk path .writeNew
  let stream := IO.FS.Stream.ofHandle handle
  if (← IO.getEnv freshSignalPointVariable) == some "during-write" then IO.sleep 1000
  emit stream
  stream.flush
  if (← IO.getEnv freshSignalPointVariable) == some "post-write" then IO.sleep 1000

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

def reportMono (config : InductiveModels.Cli.Config) (rep : InductiveModels.Mono.Report) : IO Unit := do
  if config.quiet then return
  IO.eprintln s!"monomorphization: {rep.declsIn} declarations in, {rep.declsOut} out \
    ({rep.recordsIn} → {rep.recordsOut} records), {rep.groups} groups, \
    {rep.defaulted} defaulted"
  IO.eprintln s!"  copies per group: {rep.hist.toList}"
  IO.eprintln s!"  model groups: {rep.modelGroups} keyed, {rep.modelLoose} loose, \
    {rep.modelDeclined} declined; {rep.recRegen} recursors regenerated"

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

/-- Run the whole-stream kernel gate in a genuinely empty environment.  The
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

/-- Shared compact-generation boundary. Structural output checking consumes
the compact report certified while each family was live. A worker doing kernel
replay itself still needs the complete AST; the public generated no-output path
instead gives this worker `typeCheckOutput = false`, serializes privately, and
starts a fresh checker. Monomorphization rewrites source declarations. -/
def compactModeEligible (config : InductiveModels.Cli.Config) : Bool :=
  InductiveModels.generationEnabled config && !config.monoLevels &&
    !config.typeCheckOutput

/-- Physical staging is needed only when compact generation must emit bytes. -/
def stagedModeEligible (config : InductiveModels.Cli.Config) : Bool :=
  config.output && compactModeEligible config

/-- No-output compact generation retains the same value-only verdict
certificates but deliberately has no workspace or physical spool. -/
def discardModeEligible (config : InductiveModels.Cli.Config) : Bool :=
  !config.output && compactModeEligible config

private structure RawStage where
  workspace : InductiveModels.Spool.Workspace
  tee : InductiveModels.Spool.ParseTee
  certificate : InductiveModels.RawCertificate
  sizes : InductiveModels.RawSpoolSizes

private inductive FilterOutput where
  | full (declarations : Array InductiveModels.EDecl)
  | discarded (plan : InductiveModels.CompactPlan)
  | staged (raw : RawStage) (stage : InductiveModels.Spool.IslandStage)
      (plan : InductiveModels.StagedPlan)

/-- Optional A/B and test diagnostic. This observes the actual filter result;
it never enables staging or changes eligibility. -/
private def reportOutputBackend (output : FilterOutput) : IO Unit := do
  if (← IO.getEnv "LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE") == some "1" then
    IO.eprintln s!"output backend: {match output with
      | .full .. => "legacy"
      | .discarded .. => "compact-discard"
      | .staged .. => "staged"}"

private def mixedComposition (raw : RawStage) (sealed : InductiveModels.Spool.SealedIsland)
    (spans : Array InductiveModels.StagedDeclarationSpan) : InductiveModels.Spool.MixedComposition :=
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

private def runWithWorkspace (config : InductiveModels.Cli.Config)
    (workspace? : Option InductiveModels.Spool.Workspace)
    (compactEnabled : Bool) (privateCandidate : Bool := false) : IO UInt32 := do
  let input := config.input.getD ""
  -- Reserve every spool leaf before consuming the input. Failure to establish
  -- the optional tee selects the historical parser; an error after parsing has
  -- begun remains a real IO failure and never reruns a consumed stream.
  let tee? ← match workspace? with
    | none => pure none
    | some workspace => try
        pure (some (← InductiveModels.Spool.ParseTee.create workspace))
      catch _ => pure none
  let parsed? ← try
      if input == "-" then
        let stdin ← IO.getStdin
        let result ← match tee? with
          | none => do
            let result ← InductiveModels.parseStream stdin
              (analyse := config.monoLevels)
              (allowDuplicateNames := true)
            pure (result.map fun x => (x, none))
          | some tee => do
            let result ← InductiveModels.parseStreamWithSink stdin tee.sink
              (analyse := config.monoLevels)
              (allowDuplicateNames := true)
            pure (result.map fun (x, certificate) => (x, some (tee, certificate)))
        pure (some result)
      else
        IO.FS.withFile input .read fun handle => do
          let result ← match tee? with
            | none => do
              let result ← InductiveModels.parseHandle handle
                (analyse := config.monoLevels)
                (allowDuplicateNames := true)
              pure (result.map fun x => (x, none))
            | some tee => do
              let result ← InductiveModels.parseHandleWithSink handle tee.sink
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
        if InductiveModels.Spool.rawFastPathEligible certificate sizes
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
    let report := InductiveModels.Check.checkReport parsed
    unless report.violations.isEmpty do
      reportViolations input "input" report.violations
      return exitRejected
    reportCheckSuccess config "input" report

  -- Monomorphize before generation.  Generated simple/bootstrap support is
  -- already monomorphic at this point; feeding that support back through Mono
  -- would instead ask the optional pass to infer instantiations for its
  -- carried primitive basis, which has no such instantiation relation.
  if config.monoLevels then
    match (InductiveModels.SourceCensus.ofSource parsed).replayAliases with
    | .error message =>
        IO.eprintln s!"{input}: cannot plan collision-safe source replay: {message}"
        return exitToolError
    | .ok aliases => unless aliases.isEmpty do
        -- Mono owns an independent exact-name replay loop.  Refuse before it
        -- reaches Lean's normalized async map until that loop shares Driver's
        -- explicit exact/replay alias view.
        IO.eprintln s!"{input}: --mono-levels does not yet support normalized source-name \
          collisions ({aliases.entries.size} declaration names require replay aliases)"
        return exitToolError
  let generationInput ← if config.monoLevels then do
      let result ← try
          let ((output, report), _) ← Lean.Core.CoreM.toIO
            (Lean.Meta.MetaM.run'
              (InductiveModels.Mono.monomorphize parsed { check := true })) context { env }
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
          match InductiveModels.Order.reorder output with
          | .error error =>
              IO.eprintln s!"{input}: cannot order monomorphized input: \
                {orderErrorMessage error}"
              return exitToolError
          | .ok orderedOutput => pure orderedOutput
    else
      pure parsed

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
          else if let some raw := rawStage? then
            let levelCallsBefore ← InductiveModels.LevelAlgebra.levelCalls.get
            let levelEscapesBefore ← InductiveModels.LevelAlgebra.levelEscapes.get
            let stage ← InductiveModels.Spool.IslandStage.create raw.workspace
              (InductiveModels.Writer.Cursor.ofRaw raw.certificate.cursor)
            let ((report, plan), _) ← Lean.Core.CoreM.toIO
              (Lean.Meta.MetaM.run'
                (InductiveModels.runFilterStaged generationInput false config (.ofStage stage)))
              context { env }
            match plan.unavailable? with
            | none => pure (Except.ok (FilterOutput.staged raw stage plan, report))
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
  | .discarded plan =>
    if config.checkOutput then
      unless plan.checkReport.violations.isEmpty do
        reportViolations input "output" plan.checkReport.violations
        return exitRejected
      reportCheckSuccess config "output" plan.checkReport
    return outcome
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
      if privateCandidate then
        writePrivateCandidate config.outputTarget composition.emit
      else
        InductiveModels.Output.write config.outputTarget composition.emit
    catch error =>
      IO.eprintln s!"{config.outputTarget}: cannot write output: {error}"
      return exitToolError
    return outcome
  | .full decls =>
    let transformed : Export := { generationInput with decls }
    let finalExport ← if InductiveModels.generationEnabled config || config.monoLevels then
        match InductiveModels.Order.reorder transformed with
        | .error error =>
            IO.eprintln s!"{input}: cannot order output: {orderErrorMessage error}"
            return exitToolError
        | .ok output => pure output
      else
        pure transformed

    if config.checkOutput then
      let report := InductiveModels.Check.checkReport finalExport
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
        if privateCandidate then
          writePrivateCandidate config.outputTarget finalExport.writeTo
        else
          writeExport config.outputTarget finalExport
      catch error =>
        IO.eprintln s!"{config.outputTarget}: cannot write output: {error}"
        return exitToolError
    return outcome

def run (config : InductiveModels.Cli.Config) (privateCandidate : Bool := false)
    (fixedWorkspace? : Option InductiveModels.Spool.Workspace := none) : IO UInt32 := do
  -- Canonical eligible generation uses bounded-memory staged output by default.
  -- The legacy override is retained for deliberate A/B measurements. Statically
  -- ineligible modes never tee their input, and planner trace mode stays on the
  -- full-AST path so a private failed staging attempt cannot duplicate trace lines.
  let compactEnabled :=
    (← IO.getEnv "LEAN_INDUCTIVE_MODELS_LEGACY_OUTPUT") != some "1" &&
      (← IO.getEnv "LEAN_INDUCTIVE_MODELS_PLANNER_LEVEL_TRACE") != some "1"
  if compactEnabled && stagedModeEligible config then
    match fixedWorkspace? with
    | some workspace => runWithWorkspace config (some workspace) compactEnabled privateCandidate
    | none =>
      let scratch := (← IO.currentDir) / "_tmp"
      InductiveModels.Spool.withOptionalWorkspace scratch fun workspace? =>
        runWithWorkspace config workspace? compactEnabled privateCandidate
  else
    runWithWorkspace config none compactEnabled privateCandidate

def workerMain (args : List String) : IO UInt32 := do
  InductiveModels.Output.containToolErrors do
    match InductiveModels.Cli.parseArgs args with
    | .error error =>
        IO.eprintln error
        IO.eprintln InductiveModels.Cli.usage
        return exitToolError
    | .ok config => run config

private def freshPhaseVariable : String :=
  "LEAN_INDUCTIVE_MODELS_INTERNAL_OUTPUT_KERNEL_PHASE"

private def freshDirectoryVariable : String :=
  "LEAN_INDUCTIVE_MODELS_INTERNAL_OUTPUT_KERNEL_DIRECTORY"

private def freshTokenVariable : String :=
  "LEAN_INDUCTIVE_MODELS_INTERNAL_OUTPUT_KERNEL_TOKEN"

private def freshCandidateLeaf : String := "output-kernel-candidate.ndjson"

/-- Private subprocess statuses outside the public 0..3 contract. A direct
phase invocation therefore cannot be mistaken for accepted/declined output;
only the coordinating parent translates these after the complementary phase. -/
private def exitProducedAccepted : UInt32 := 4
private def exitProducedDeclined : UInt32 := 5
private def exitKernelAccepted : UInt32 := 4

private inductive FreshPhase where
  | produce | check

private def FreshPhase.parse? : String → Option FreshPhase
  | "produce" => some .produce
  | "check" => some .check
  | _ => none

/-- Validate the subprocess path boundary without trusting it as a deletion or
publication target. The randomized owner-only directory must be a physical
child of this process's project `_tmp`, and its basename must match the path
component supplied by the coordinator. Environment values are not an
authentication secret; out-of-contract phase success statuses enforce the
public gate boundary. -/
private def freshCandidatePath : IO (Except String System.FilePath) := do
  let some directoryText ← IO.getEnv freshDirectoryVariable
    | return .error "fresh output-kernel phase has no private directory"
  let some token ← IO.getEnv freshTokenVariable
    | return .error "fresh output-kernel phase has no directory basename"
  let directory : System.FilePath := directoryText
  unless directory.fileName == some token do
    return .error "fresh output-kernel basename does not name its private directory"
  try
    let scratch := (← IO.currentDir) / "_tmp"
    let rootMetadata ← scratch.symlinkMetadata
    unless rootMetadata.type == .dir do
      return .error "fresh output-kernel project _tmp is not a physical directory"
    let directoryMetadata ← directory.symlinkMetadata
    unless directoryMetadata.type == .dir do
      return .error "fresh output-kernel path is not a physical directory"
    let canonicalRoot ← IO.FS.realPath scratch
    let canonicalDirectory ← IO.FS.realPath directory
    let rootParts := canonicalRoot.components
    let directoryParts := canonicalDirectory.components
    unless rootParts.length < directoryParts.length &&
        directoryParts.take rootParts.length == rootParts &&
        canonicalDirectory.fileName == some token do
      return .error "fresh output-kernel directory escapes the project _tmp"
    return .ok (canonicalDirectory / freshCandidateLeaf)
  catch error =>
    return .error s!"cannot validate fresh output-kernel path: {error}"

private def parseConfig (args : List String) : IO (Except Unit InductiveModels.Cli.Config) := do
  match InductiveModels.Cli.parseArgs args with
  | .ok config => return .ok config
  | .error error =>
    IO.eprintln error
    IO.eprintln InductiveModels.Cli.usage
    return .error ()

/-- The producer preserves the public invocation's generation, structural
checks, diagnostics, and exit 0/1/2/3. Only publication and the final kernel
gate are redirected to the private candidate. It prefers compact staging and
retains the ordinary full-oracle fallback when raw or compact certification is
unavailable; either producer process terminates before kernel replay starts. -/
private def freshProducerMain (args : List String) : IO UInt32 := do
  let candidateResult ← freshCandidatePath
  let candidate ← match candidateResult with
    | .ok candidate => pure candidate
    | .error message =>
      IO.eprintln s!"lean-inductive-models: invalid fresh output-kernel producer path: \
        {message}"
      return exitToolError
  let .ok config ← parseConfig args
    | return exitToolError
  unless InductiveModels.generationEnabled config && !config.output &&
      config.typeCheckOutput && !config.monoLevels do
    IO.eprintln "lean-inductive-models: fresh output-kernel producer received an ineligible invocation"
    return exitToolError
  if ← candidate.pathExists then
    IO.eprintln "lean-inductive-models: fresh output-kernel candidate was not exclusively reserved"
    return exitToolError
  let producerConfig := { config with typeCheckOutput := false }
  let producerConfig := { producerConfig with
    output := true, outputTarget := candidate.toString }
  let some directory := candidate.parent
    | IO.eprintln "lean-inductive-models: fresh output-kernel candidate has no parent"
      return exitToolError
  let workspace ← InductiveModels.Spool.Workspace.attach ((← IO.currentDir) / "_tmp") directory
  let status ← run producerConfig true (some workspace)
  if status == exitAccepted then return exitProducedAccepted
  if status == exitDeclined then return exitProducedDeclined
  return status

/-- Parse and kernel-replay only the private candidate. This worker has no
generation route and starts only after the producer process has terminated, so
their heaps cannot overlap. -/
private def freshCheckerMain (args : List String) : IO UInt32 := do
  let candidateResult ← freshCandidatePath
  let candidate ← match candidateResult with
    | .ok candidate => pure candidate
    | .error message =>
      IO.eprintln s!"lean-inductive-models: invalid fresh output-kernel checker path: \
        {message}"
      return exitToolError
  let .ok config ← parseConfig args
    | return exitToolError
  unless InductiveModels.generationEnabled config && !config.output &&
      config.typeCheckOutput && !config.monoLevels do
    IO.eprintln "lean-inductive-models: fresh output-kernel checker received an ineligible invocation"
    return exitToolError
  let input := config.input.getD "<input>"
  if (← IO.getEnv freshCheckerFailureVariable) == some "1" then
    IO.eprintln s!"{input}: injected fresh output-kernel checker failure"
    return exitToolError
  let candidateMetadata ← try candidate.symlinkMetadata catch error =>
    IO.eprintln s!"{input}: output kernel replay candidate is unavailable: {error}"
    return exitToolError
  unless candidateMetadata.type == .file do
    IO.eprintln s!"{input}: output kernel replay candidate is not a physical file"
    return exitToolError
  let parsedResult : Except String Export ← try
      IO.FS.withFile candidate .read fun handle => do
        let result ← InductiveModels.parseHandle handle
          (analyse := false) (allowDuplicateNames := true)
        return result.mapError toString
    catch error => pure (.error (toString error))
  let .ok parsed := parsedResult
    | IO.eprintln s!"{input}: output kernel replay could not parse its private candidate"
      return exitToolError
  if let .error message := parsed.validateUniqueDeclarationNames then
    IO.eprintln s!"{input}: output kernel replay candidate is invalid: {message}"
    return exitToolError
  initSearchPath (← findSysroot)
  let context : Core.Context :=
    { fileName := "<lean-inductive-models-output-kernel-worker>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  match ← typeCheckExportIO context parsed with
  | .error message =>
    IO.eprintln s!"{input}: output kernel check failed internally: {message}"
    return exitToolError
  | .ok (.error message) =>
    IO.eprintln s!"{input}: output kernel check rejected: {message}"
    return exitRejected
  | .ok (.ok ()) =>
    reportTypeCheckSuccess config "output"
    return exitKernelAccepted

private def clearedFreshEnvironment : Array (String × Option String) := #[
  (freshPhaseVariable, none), (freshDirectoryVariable, none), (freshTokenVariable, none)]

private def freshPhaseEnvironment (phase : FreshPhase)
    (directory : System.FilePath) (token : String) : Array (String × Option String) := #[
  (freshPhaseVariable, some (match phase with | .produce => "produce" | .check => "check")),
  (freshDirectoryVariable, some directory.toString),
  (freshTokenVariable, some token)]

private def freshOwnedLeaves : Array String := #[
  freshCandidateLeaf,
  "metadata.ndjson", "arena.ndjson", "declarations.ndjson",
  "generated-arena.ndjson", "generated-declarations.ndjson"]

private def freshKernelEligible (config : InductiveModels.Cli.Config) : IO Bool := do
  return InductiveModels.generationEnabled config && !config.output &&
    config.typeCheckOutput && !config.monoLevels &&
    (← IO.getEnv "LEAN_INDUCTIVE_MODELS_LEGACY_OUTPUT") != some "1" &&
    (← IO.getEnv "LEAN_INDUCTIVE_MODELS_PLANNER_LEVEL_TRACE") != some "1"

/-- Coordinate two nonoverlapping workers. A successful kernel checker returns
the producer's accepted/declined status; rejection or tool failure overrides
it exactly as the historical in-process final gate did. -/
private def runFreshKernelPipeline (args : List String) : IO UInt32 := do
  let scratch := (← IO.currentDir) / "_tmp"
  try
    InductiveModels.Spool.withRootedWorkspace scratch fun workspace => do
      let mut candidatePath? : Option System.FilePath := none
      for leaf in freshOwnedLeaves do
        let path ← workspace.reservePath leaf
        if leaf == freshCandidateLeaf then candidatePath? := some path
      let some candidate := candidatePath?
        | throw <| IO.userError "fresh output-kernel candidate leaf was not registered"
      let canonicalDirectory ← IO.FS.realPath workspace.directory
      let some token := canonicalDirectory.fileName
        | throw <| IO.userError "fresh output-kernel workspace has no basename"
      let producer ← InductiveModels.Supervisor.runWorkerRaw args
        (freshPhaseEnvironment .produce canonicalDirectory token)
      let producerOutcome ← if producer == exitProducedAccepted then pure exitAccepted
        else if producer == exitProducedDeclined then pure exitDeclined
        else if producer ≤ exitToolError then return producer
        else
          IO.eprintln s!"lean-inductive-models: producer terminated with native status {producer}; \
            reporting internal tool error 3"
          return exitToolError
      unless ← candidate.pathExists do
        IO.eprintln "lean-inductive-models: fresh producer returned without a kernel candidate"
        return exitToolError
      let metadata ← candidate.symlinkMetadata
      unless metadata.type == .file do
        IO.eprintln "lean-inductive-models: fresh producer did not install a physical kernel candidate"
        return exitToolError
      let checker ← InductiveModels.Supervisor.runWorkerRaw args
        (freshPhaseEnvironment .check canonicalDirectory token)
      if checker == exitKernelAccepted then return producerOutcome
      if checker ≤ exitToolError then return checker
      IO.eprintln s!"lean-inductive-models: output kernel worker terminated with native status \
        {checker}; reporting internal tool error 3"
      return exitToolError
  catch error =>
    IO.eprintln s!"lean-inductive-models: cannot run fresh output kernel worker: {error}"
    return exitToolError

private def supervisedMain (args : List String) : IO UInt32 := do
  if (← IO.getEnv InductiveModels.Supervisor.workerMarker) == some "1" then
    match ← IO.getEnv freshPhaseVariable with
    | none => workerMain args
    | some phase => match FreshPhase.parse? phase with
      | some .produce => freshProducerMain args
      | some .check => freshCheckerMain args
      | none =>
        IO.eprintln "lean-inductive-models: invalid internal output-kernel phase"
        return exitToolError
  else
    match InductiveModels.Cli.parseArgs args with
    | .ok config =>
      if ← freshKernelEligible config then runFreshKernelPipeline args
      else InductiveModels.Supervisor.runWorkerWithEnv args clearedFreshEnvironment
    | .error _ => InductiveModels.Supervisor.runWorkerWithEnv args clearedFreshEnvironment

def main (args : List String) : IO UInt32 :=
  InductiveModels.Output.containToolErrors (supervisedMain args)
