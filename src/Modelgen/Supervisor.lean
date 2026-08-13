import Lean

/-!
# Native crash containment

The public process runs the unchanged command in one child process so a native
signal cannot escape as an Arena verdict. This layer deliberately knows nothing
about exports, models, or checking: it preserves ordinary worker results and
only contains statuses outside the public `0` through `3` contract.
-/

namespace Modelgen.Supervisor

/-- Private recursion guard inherited only by the supervised worker. -/
def workerMarker : String := "LEAN_INDUCTIVE_MODELS_INTERNAL_WORKER"

private def reportFailure (message : String) : IO Unit := do
  try IO.eprintln message
  catch _ => pure ()

/-- Run the current executable once with identical arguments and inherited
standard streams, working directory, environment, limits, and process group.
Only the private marker is added. -/
def runWorker (args : List String) : IO UInt32 := do
  try
    let executable ← IO.appPath
    let child ← IO.Process.spawn {
      cmd := executable.toString
      args := args.toArray
      env := #[(workerMarker, some "1")]
      stdin := .inherit
      stdout := .inherit
      stderr := .inherit }
    let status ← child.wait
    if status ≤ 3 then
      return status
    reportFailure s!"lean-inductive-models: worker terminated with native status {status}; \
      reporting internal tool error 3"
    return 3
  catch error =>
    reportFailure s!"lean-inductive-models: cannot supervise worker: {error}"
    return 3

/-- Enter the worker exactly once. A normal worker result is returned byte for
byte and code for code; only native/impossible process statuses are contained. -/
def supervise (worker : List String → IO UInt32) (args : List String) : IO UInt32 := do
  if (← IO.getEnv workerMarker) == some "1" then worker args else runWorker args

end Modelgen.Supervisor
