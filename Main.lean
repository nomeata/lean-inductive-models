import Modelgen.Driver

/-!
`modelgen IN.ndjson [-o OUT.ndjson|-] [--check-recursors] [--quiet]`

# The two streams, and why they are two

**The export goes to `-o` and nothing else ever does; the report goes to
stderr.** A consumer that streams — `mini` execs this binary with `-o -` and
feeds the bytes straight to its parser (`mini/src/modelgen.rs`) — therefore
gets the diagnostics *and* an uncorrupted export, without having to silence
one to get the other.

The report used to be on stdout, which forced `--quiet` on every streaming
consumer and cost it every decline reason: `mini` could say `no nested model in
the export` and not *why* there was none. Naming where a value stopped rather
than why is the defect class this repository has paid for most, and a process
boundary is not an excuse for it.

`--quiet` still suppresses the report; it is now a preference rather than a
correctness requirement.

**The export is not moved to stderr instead.** `Environment.addDeclCore`
`panic!`s to stderr on one corpus file (`MODELGEN.md` §5.5), so stderr is not a
stream anything may be *parsed* out of.

# The exit statuses

`MODELGEN.md` §1.4 is the contract; these four constants are it in code.
`mini` keys on them, so they do not move without that section moving.
-/

open Lean Meta Modelgen

/-- Ran to completion, and the export was written if `-o` asked for one.
**A decline is this**: the
input is fine and no model was produced, which the report says and which a
consumer must not read as an error (`MODELGEN.md` §1.3). -/
def exitOk : UInt32 := 0
/-- The command line is not one this tool accepts. Nothing was read. -/
def exitUsage : UInt32 := 1
/-- The input is malformed: it could not be read, or it is not an export this
tool can parse. Nothing was written. -/
def exitInput : UInt32 := 2
/-- This tool's own failure: an exception escaped the filter, or a generated
model did not match the statement its own oracle rebuilt. **Nothing was
written** — an exit of 3 means there is no output to use. -/
def exitInternal : UInt32 := 3

def usage : String :=
  "usage: modelgen IN.ndjson [-o OUT.ndjson|-] [--check-recursors] [--prim-models] \
[--quiet]"

structure Opts where
  input : String := ""
  /-- `some "-"` is stdout; see [`writeExport`]. -/
  output : Option String := none
  checkRecursors : Bool := false
  /-- The third construction: model simple inductives from the five
  primitives (`Modelgen/Simple.lean`). Off by default. -/
  primModels : Bool := false
  quiet : Bool := false

def parseArgs : List String → Except String Opts
  | [] => .error usage
  | args => go args {}
where
  go : List String → Opts → Except String Opts
    | [], o => if o.input.isEmpty then .error "no input file" else .ok o
    | "-o" :: p :: rest, o => go rest { o with output := some p }
    | "--check-recursors" :: rest, o => go rest { o with checkRecursors := true }
    | "--prim-models" :: rest, o => go rest { o with primModels := true }
    | "--quiet" :: rest, o => go rest { o with quiet := true }
    | a :: rest, o =>
      -- `-` alone is only ever the argument of `-o`, which the line above has
      -- already consumed; a bare `-` is a mistake and not an input named `-`.
      if a.startsWith "-" then .error s!"unknown flag {a}" else go rest { o with input := a }

/-- **The export**, to the `-o` target. `-` is stdout, first class, so a
streaming consumer does not have to rely on `/dev/stdout` existing.

`verbatim` is the input's own bytes and is used when there is nothing to splice
(§3). Otherwise the export is **streamed** record by record
([`Modelgen.Export.writeTo`]) instead of rendered into one `String`, which is
what makes a Mathlib-sized export writable at all (`MONOMORPH.md` §9.5) and what
keeps a streaming consumer's memory bounded by the pipe rather than by the
file. -/
def writeExport (out : Option String) (verbatim : Option String) (x : Export) : IO Unit := do
  let some p := out | return
  let s ← if p == "-" then IO.getStdout
          else pure (IO.FS.Stream.ofHandle (← IO.FS.Handle.mk p .write))
  match verbatim with
  | some t => s.putStr t
  | none => x.writeTo s
  s.flush

/-- **The report**, to stderr, and never a line of the export. -/
def report (o : Opts) (rep : Modelgen.Report) : IO Unit := do
  if o.quiet then return
  if let some why := rep.unreplayable then
    IO.eprintln s!"{o.input}: passed through unchanged — {why}"
  for (n, k) in rep.generated do IO.eprintln s!"{n}: model of {k} declarations"
  -- **A splice is reported, never silent.** The input did not declare these and
  -- the model's proofs need them, so `modelgen` wrote Lean's own; a consumer
  -- reading the filtered export is told which of its declarations are not the
  -- input's (`MODELGEN.md` §1.5).
  for (n, ns) in rep.spliced do
    IO.eprintln s!"{n}: prelude spliced — {", ".intercalate (ns.map toString).toList}"
  -- **Exempt before declined, and never counted with it.** A basis primitive
  -- is unmodelled by definition (`MODELGEN.md` §8.17).
  for (n, why) in rep.exempt do IO.eprintln s!"{n}: exempt — {why}"
  for (n, why) in rep.declined do IO.eprintln s!"{n}: declined — {why}"
  unless rep.stmtChecked == 0 do
    IO.eprintln s!"statements: {rep.stmtChecked} compared against the installed recursors' \
      own rules, {rep.stmtErrors.size} differ"
    for e in rep.stmtErrors do IO.eprintln s!"  ! {e}"
  if o.checkRecursors then
    IO.eprintln s!"recursors: {rep.recChecked} checked against Lean's own, \
      {rep.recMismatch.size} differ{if rep.recMismatch.isEmpty then "" else s!": {rep.recMismatch}"}"
  -- The planner's level census (`Modelgen/LevelAlgebra.lean`). An **escape**
  -- is a pair the complete procedure accepts and `Lean.Meta.isLevelDefEq`
  -- rejects, so it is the only place this build can differ from one asking
  -- the elaborator alone. Printed always, because zero is the interesting
  -- number as often as not.
  let calls ← Modelgen.LevelAlgebra.levelCalls.get
  let escapes ← Modelgen.LevelAlgebra.levelEscapes.get
  IO.eprintln s!"levels: {calls} planner comparisons, {escapes} escapes\
    {if Modelgen.LevelAlgebra.stockLevels then " (widening OFF — control run)" else ""}"

def run (o : Opts) : IO UInt32 := do
  -- An unreadable input is the *input's* problem and exits 2, where it used to
  -- escape as Lean's own `uncaught exception:` and exit 1 beside a bad flag.
  let text? ← try pure (some (← IO.FS.readFile o.input))
              catch e => do IO.eprintln s!"{o.input}: {e}"; pure none
  let some text := text? | return exitInput
  let x ←
    -- `analyse := false`: `modelgen` never reads `Export.projNodes`, and the
    -- pass that fills it is a walk of the whole arena.
    match Modelgen.parse text (analyse := false) with
    | .error e => IO.eprintln s!"{o.input}: parse error: {e}"; return exitInput
    | .ok x => pure x
  initSearchPath (← findSysroot)
  let env ← importModules #[] {}
  let ctx : Core.Context :=
    { fileName := "<modelgen>", fileMap := default, maxHeartbeats := 0, maxRecDepth := 8192 }
  -- An exception out of the filter is **this tool's** failure and says so, in
  -- place of Lean's bare `uncaught exception:` — which a consumer cannot tell
  -- from a bad input, since both used to exit 1.
  let res ← try
      let ((decls, rep), _) ←
        (Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run'
          (Modelgen.runFilter x o.checkRecursors
            (Modelgen.legacyGenerationConfig o.primModels))) ctx
          { env })
      pure (Except.ok (decls, rep))
    catch e => pure (Except.error (toString e))
  match res with
  | .error m => IO.eprintln s!"{o.input}: internal error: {m}"; return exitInternal
  | .ok (decls, rep) =>
    report o rep
    -- **A model that failed the tool's own statement oracle is not written.**
    -- It typechecks — axis 2 passed — and states something other than the
    -- export's own rule, which is precisely the model a consumer must not key
    -- on. Nothing in the tree reaches this (450 statements, 0 differing); it
    -- is here so that if anything ever does, the consumer is told rather than
    -- handed the wrong model with a 0.
    unless rep.stmtErrors.isEmpty do
      IO.eprintln s!"{o.input}: internal error: {rep.stmtErrors.size} generated statements \
        differ from the installed recursors' own rules; no output written"
      return exitInternal
    -- A file with nothing to splice is copied byte for byte; re-interning is
    -- only forced because `nanoda` requires continuous back-references.
    writeExport o.output
      (if rep.generated.isEmpty || rep.unreplayable.isSome then some text else none)
      { x with decls }
    return exitOk

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e => IO.eprintln e; return exitUsage
  | .ok o => run o
