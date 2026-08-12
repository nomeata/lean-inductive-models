import Modelgen.Format

/-!
A deliberately tiny, opt-in process for comparing parser retention.  Run each
mode in a fresh process so `/proc/self/status`'s `VmHWM` is meaningful:

```
lake exe memoryprobe whole  INPUT.ndjson
lake exe memoryprobe stream INPUT.ndjson
```

Only resident/high-water sizes and already-owned arena cardinalities are
reported.  The observer never walks expression graphs or retains log samples.
Missing Linux `/proc` counters are an error, not a partial measurement.
-/

private def statusValue (status key : String) : Option Nat := do
  let line ← status.splitOn "\n" |>.find? (fun line => line.startsWith key)
  let digits := (line.drop key.length).toString.foldl
    (fun result character => if character.isDigit then result.push character else result) ""
  digits.toNat?

private def memory (phase : String) (declarations : Nat := 0) : IO Unit := do
  let status ← IO.FS.readFile "/proc/self/status"
  let some rss := statusValue status "VmRSS:"
    | throw <| IO.userError "memoryprobe: /proc/self/status has no VmRSS"
  let some hwm := statusValue status "VmHWM:"
    | throw <| IO.userError "memoryprobe: /proc/self/status has no VmHWM"
  IO.eprintln s!"memoryprobe {phase}: rss={rss}KiB hwm={hwm}KiB declarations={declarations}"

def main (args : List String) : IO UInt32 := do
  let [mode, path] := args | do
    IO.eprintln "usage: memoryprobe (whole|stream) INPUT.ndjson"
    return 1
  memory "start"
  let result ← match mode with
    | "whole" => do
        let text ← IO.FS.readFile path
        memory "whole-read"
        pure (Modelgen.parse text (analyse := false))
    | "stream" =>
        IO.FS.withFile path .read fun handle => Modelgen.parseHandle handle (analyse := false)
    | _ => do
        IO.eprintln s!"memoryprobe: unknown mode {mode}"
        return 1
  match result with
  | .error error =>
      IO.eprintln s!"memoryprobe: parse error: {error}"
      return 2
  | .ok parsed =>
      memory "parsed" parsed.decls.size
      return 0
