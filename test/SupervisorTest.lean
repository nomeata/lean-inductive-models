import InductiveModels.Supervisor

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

unsafe def crashWithSegv : IO UInt32 := do
  -- Force a genuine invalid native access without a handwritten FFI shim.
  -- `ByteArray` is represented by a heap pointer, while this cast supplies the
  -- tagged immediate representation of `Nat.zero`; querying its size faults.
  let invalid : ByteArray := unsafeCast (0 : Nat)
  IO.println s!"unreachable byte-array size: {invalid.size}"
  return 3

unsafe def syntheticWorker : List String → IO UInt32
  | ["exit", code] => do
      let some code := code.toNat? | return 3
      IO.println s!"stdout-{code}"
      IO.eprintln s!"stderr-{code}"
      return code.toUInt32
  | ["stdin"] => do
      let stdin ← IO.getStdin
      IO.print (← stdin.readToEnd)
      return 0
  | ["signal", "TERM"] => do
      -- The test controller below discovers this supervised worker through its
      -- supervisor's process tree and delivers a real SIGTERM.
      while true do IO.sleep 1000
      return 3
  | ["signal", "SEGV"] => crashWithSegv
  | _ => return 3

def runSynthetic (executable : String) (args : Array String)
    (input? : Option String := none) : IO IO.Process.Output :=
  IO.Process.output {
    cmd := executable
    args
    env := #[(InductiveModels.Supervisor.workerMarker, none)] } input?

private structure SignaledOutput where
  process : IO.Process.Output
  injector : IO.Process.Output

/-- Start the real supervisor and use Python only as a portable signal sender.
The Python child finds the supervisor's one worker through Linux procfs and
sends that worker a real native signal; it never synthesizes an exit status. -/
def runSignaled (executable signal : String) : IO SignaledOutput := do
  let child ← IO.Process.spawn {
    cmd := executable
    args := #["signal", signal]
    env := #[(InductiveModels.Supervisor.workerMarker, none)]
    stdin := .null
    stdout := .piped
    stderr := .piped }
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  let script :=
    "import os, signal, sys, time\n" ++
    "parent = int(sys.argv[1])\n" ++
    "sig = getattr(signal, 'SIG' + sys.argv[2])\n" ++
    "children = f'/proc/{parent}/task/{parent}/children'\n" ++
    "deadline = time.monotonic() + 10\n" ++
    "while time.monotonic() < deadline:\n" ++
    "    try:\n" ++
    "        pids = open(children, encoding='ascii').read().split()\n" ++
    "    except FileNotFoundError:\n" ++
    "        pids = []\n" ++
    "    if pids:\n" ++
    "        os.kill(int(pids[0]), sig)\n" ++
    "        sys.exit(0)\n" ++
    "    time.sleep(0.01)\n" ++
    "sys.exit(4)\n"
  let injector ← IO.Process.output {
    -- Resolve the standard interpreter through PATH: GitHub's Ubuntu image
    -- installs it as /usr/bin/python3, while the local Nix gate does not.
    cmd := "python3"
    args := #["-c", script, toString child.pid, signal] }
  let exitCode ← child.wait
  let stdout ← IO.ofExcept stdout.get
  let stderr ← IO.ofExcept stderr.get
  return { process := { exitCode, stdout, stderr }, injector }

def runTests (executable : String) : IO UInt32 := do
  let mut state : TestState := {}
  for code in [0, 1, 2, 3] do
    let result ← runSynthetic executable #["exit", toString code]
    state := state.check s!"worker exit {code} is preserved" <|
      result.exitCode == code && result.stdout == s!"stdout-{code}\n" &&
        result.stderr == s!"stderr-{code}\n"
  let impossible ← runSynthetic executable #["exit", "4"]
  state := state.check "out-of-contract worker exit maps to 3" <|
    impossible.exitCode == 3 && impossible.stdout == "stdout-4\n" &&
      impossible.stderr.contains "stderr-4\n" &&
      impossible.stderr.contains "worker terminated with native status 4" &&
      impossible.stderr.contains "reporting internal tool error 3"
  let stdinText := "supervised stdin\nsecond line\n"
  let stdinResult ← runSynthetic executable #["stdin"] (some stdinText)
  state := state.check "stdin is inherited without rewriting" <|
    stdinResult.exitCode == 0 && stdinResult.stdout == stdinText && stdinResult.stderr.isEmpty
  -- libuv exposes POSIX signal termination as 128 + signal on the Linux CI
  -- platform: SIGTERM=15 and SIGSEGV=11.
  let term ← runSignaled executable "TERM"
  state := state.check "TERM injector delivered a real signal" <|
    term.injector.exitCode == 0 && term.injector.stdout.isEmpty &&
      term.injector.stderr.isEmpty
  state := state.check "TERM maps native status 143 to 3" <|
    term.process.exitCode == 3 && term.process.stdout.isEmpty &&
      term.process.stderr.contains "worker terminated with native status 143" &&
      term.process.stderr.contains "reporting internal tool error 3"
  let segv ← runSynthetic executable #["signal", "SEGV"]
  state := state.check "SEGV maps native status 139 to 3" <|
      segv.exitCode == 3 && segv.stdout.isEmpty &&
        segv.stderr.contains "worker terminated with native status 139" &&
        segv.stderr.contains "reporting internal tool error 3"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  IO.println s!"supervisor: {state.passed} passed, {state.failed.size} failed"
  return if state.failed.isEmpty then 0 else 1

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["--run-tests", executable] => runTests executable
  | _ => InductiveModels.Supervisor.supervise syntheticWorker args
