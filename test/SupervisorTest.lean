import Modelgen.Supervisor

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def syntheticWorker : List String → IO UInt32
  | ["exit", code] => do
      let some code := code.toNat? | return 3
      IO.println s!"stdout-{code}"
      IO.eprintln s!"stderr-{code}"
      return code.toUInt32
  | ["stdin"] => do
      let stdin ← IO.getStdin
      IO.print (← stdin.readToEnd)
      return 0
  | ["signal", signal] => do
      let pid ← IO.Process.getPID
      let child ← IO.Process.spawn {
        cmd := "/bin/kill"
        args := #[s!"-{signal}", toString pid] }
      discard child.wait
      return 3
  | _ => return 3

def runSynthetic (executable : String) (args : Array String)
    (input? : Option String := none) : IO IO.Process.Output :=
  IO.Process.output {
    cmd := executable
    args
    env := #[(Modelgen.Supervisor.workerMarker, none)] } input?

def runTests (executable : String) : IO UInt32 := do
  let mut state : TestState := {}
  for code in [0, 1, 2, 3] do
    let result ← runSynthetic executable #["exit", toString code]
    state := state.check s!"worker exit {code} is preserved" <|
      result.exitCode == code && result.stdout == s!"stdout-{code}\n" &&
        result.stderr == s!"stderr-{code}\n"
  let stdinText := "supervised stdin\nsecond line\n"
  let stdinResult ← runSynthetic executable #["stdin"] (some stdinText)
  state := state.check "stdin is inherited without rewriting" <|
    stdinResult.exitCode == 0 && stdinResult.stdout == stdinText && stdinResult.stderr.isEmpty
  for (signal, nativeStatus) in [("TERM", 143), ("SEGV", 139)] do
    let result ← runSynthetic executable #["signal", signal]
    state := state.check s!"{signal} maps native status {nativeStatus} to 3" <|
      result.exitCode == 3 && result.stdout.isEmpty &&
        result.stderr.contains s!"worker terminated with native status {nativeStatus}" &&
        result.stderr.contains "reporting internal tool error 3"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  IO.println s!"supervisor: {state.passed} passed, {state.failed.size} failed"
  return if state.failed.isEmpty then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--run-tests", executable] => runTests executable
  | _ => Modelgen.Supervisor.supervise syntheticWorker args
