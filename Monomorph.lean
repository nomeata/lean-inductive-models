import Modelgen.Mono

/-!
`monomorph IN.ndjson [-o OUT.ndjson] [--mono-recursors] [--default 0,1] [--quiet]`

The contract the output satisfies is `MONOMORPH.md` §1.
-/

open Lean Meta Modelgen Modelgen.Mono

structure Opts' where
  input : String := ""
  output : Option String := none
  opts : Mono.Opts := {}
  quiet : Bool := false

def usage : String :=
  "usage: monomorph IN.ndjson [-o OUT.ndjson] [--mono-recursors] [--default N[,N...]] [--check] [--quiet]"

def parseArgs : List String → Except String Opts'
  | [] => .error usage
  | args => go args {}
where
  go : List String → Opts' → Except String Opts'
    | [], o => if o.input.isEmpty then .error "no input file" else .ok o
    | "-o" :: p :: rest, o => go rest { o with output := some p }
    | "--mono-recursors" :: rest, o =>
      go rest { o with opts := { o.opts with monoRecursors := true } }
    | "--default" :: s :: rest, o =>
      let ds := (s.splitOn ",").filterMap (·.trimAscii.toString.toNat?)
      if ds.isEmpty then .error s!"--default wants a comma-separated list of naturals, got {s}"
      else go rest { o with opts := { o.opts with defaults := ds.toArray } }
    | "--check" :: rest, o => go rest { o with opts := { o.opts with check := true } }
    | "--quiet" :: rest, o => go rest { o with quiet := true }
    | a :: rest, o =>
      if a.startsWith "-" then .error s!"unknown flag {a}" else go rest { o with input := a }

def run (o : Opts') : IO UInt32 := do
  Mono.phase "start"
  -- **Bound, not assigned.** An `x := y` in one arm of a `match` whose other
  -- arm `return`s does not escape the match: `x` reads back as `default` after
  -- it, silently, and the pass reports zero declarations in. Measured the hard
  -- way; the shape to keep is a `match` that *produces* the value.
  let slurp := (← IO.getEnv "MONO_SLURP").isSome
  let read : IO (Except String (String × Modelgen.Export)) := do
    if slurp then
      let t ← IO.FS.readFile o.input
      Mono.phase "readFile"
      return (Modelgen.parse t).map (fun y => (t, y))
    else
      let h ← IO.FS.Handle.mk o.input .read
      Mono.phase "readFile"
      return (← Modelgen.parseHandle h).map (fun y => ("", y))
  let (text, x) ←
    match ← read with
    | .error e => IO.eprintln s!"{o.input}: parse error: {e}"; return 1
    | .ok r => pure r
  Mono.phase "parse"
  initSearchPath (← findSysroot)
  let env ← importModules #[] {}
  let ctx : Core.Context :=
    { fileName := "<monomorph>", fileMap := default, maxHeartbeats := 0, maxRecDepth := 8192 }
  Mono.phase "importModules"
  let ((y, rep), _) ←
    Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (monomorphize x o.opts)) ctx { env }
  Mono.phase "monomorphize"
  unless o.quiet do
    match rep.refused with
    | some why => IO.println s!"{o.input}: passed through unchanged — {why}"
    | none =>
      IO.println s!"{o.input}: {rep.declsIn} declarations in, {rep.declsOut} out \
        ({rep.recordsIn} → {rep.recordsOut} records), {rep.groups} groups, \
        {rep.carried.size} carried, {rep.defaulted} defaulted"
      IO.println s!"  copies per group: {rep.hist.toList}"
      IO.println s!"  model groups keyed to what they model: {rep.modelGroups}; \
        of their own arity: {rep.modelLoose}; declined: {rep.modelDeclined}"
      IO.println s!"  carried: {rep.carried.toList}"
      IO.println s!"  recursors the kernel minted differently: {rep.recRegen}; \
        declarations the replay rejected: {rep.rejected}"
      unless rep.errors.isEmpty do
        IO.println s!"  {rep.errors.size} problems:"
        for e in rep.errors.toList.eraseDups.take 20 do IO.println s!"    ! {e}"
  match o.output with
  | none => pure ()
  | some p =>
    if rep.refused.isSome then do
      -- The refusal path wants the input verbatim; the streaming reader did not
      -- keep it, and re-reading a file we have already read is cheaper than
      -- holding it for a branch that almost never fires.
      let t ← if text.isEmpty then IO.FS.readFile o.input else pure text
      IO.FS.writeFile p t
    else
      -- Streamed, not rendered: the whole file as one `String` is what
      -- `MONOMORPH.md` §9.5 measured failing on Mathlib.
      let h ← IO.FS.Handle.mk p .write
      y.writeTo (IO.FS.Stream.ofHandle h)
  Mono.phase "done"
  return if rep.errors.isEmpty then 0 else 2

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e => IO.eprintln e; return 1
  | .ok o => run o
