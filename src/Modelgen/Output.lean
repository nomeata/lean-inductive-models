import Lean

/-!
# Transactional output

Named output is prepared in a fresh sibling and made visible with one rename.
This keeps an existing target intact when serialization or flushing fails and
also makes literal and path-alias in-place operation safe. Standard output is
necessarily different: once a consumer has received bytes they cannot be
recalled, so it is written only after the caller has completed every gate.
-/

namespace Modelgen.Output

private def maxTempAttempts : Nat := 64

private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n.toNat)
  else Char.ofNat ('a'.toNat + n.toNat - 10)

private def hexSuffix (bytes : ByteArray) : String :=
  bytes.foldl (init := "") fun result byte =>
    (result.push (hexDigit (byte / 16))).push (hexDigit (byte % 16))

private structure Hooks where
  beforeFlush : IO Unit := pure ()
  beforeRename : IO Unit := pure ()

/-- Reserve one fixed-length random sibling without following an existing leaf.
The target's lexical parent is retained deliberately: final rename semantics
apply to the path the caller supplied, including a final symbolic link. -/
private def reserveSibling (target : System.FilePath) : IO (System.FilePath × IO.FS.Handle) := do
  unless target.fileName.isSome do
    throw <| IO.userError s!"output target has no file name: {target}"
  let rec attempt : Nat → IO (System.FilePath × IO.FS.Handle)
    | 0 => throw <| IO.userError
        s!"could not reserve an output sibling after {maxTempAttempts} attempts"
    | remaining + 1 => do
      let suffix := hexSuffix (← IO.getRandomBytes 16)
      let path := target.withFileName s!".lean-inductive-models-output-{suffix}.tmp"
      try
        return (path, ← IO.FS.Handle.mk path .writeNew)
      catch
        | .alreadyExists .. => attempt remaining
        | error => throw error
  attempt maxTempAttempts

/-- Complete all writes inside a separate scope. Lean file handles have no
explicit close operation: their last reference closes them. Returning only the
path and result ensures the handle and its stream are released before rename,
which is required on Windows as well as being the intended ownership boundary
on POSIX systems. `flush` reports buffered write failures; this helper does not
claim power-loss durability (`fsync`). -/
private def prepareSibling (target : System.FilePath) (emit : IO.FS.Stream → IO Unit)
    (hooks : Hooks) : IO (System.FilePath × Except IO.Error Unit) := do
  let (path, handle) ← reserveSibling target
  let result : Except IO.Error Unit ← try
      let stream := IO.FS.Stream.ofHandle handle
      emit stream
      hooks.beforeFlush
      stream.flush
      pure (.ok ())
    catch error => pure (.error error)
  return (path, result)

private def removeSibling (path : System.FilePath) : IO Unit := do
  try
    IO.FS.removeFile path
  catch
    | .noFileOrDirectory .. => pure ()
    | error => throw error

/-- Preserve the primary output error if removal of its private sibling also
fails. Cleanup is deliberately nonrecursive and has exactly one randomized
file as its target. -/
private def failAndCleanup (path : System.FilePath) (primary : IO.Error) : IO α := do
  try
    removeSibling path
  catch cleanupError =>
    try IO.eprintln s!"output sibling cleanup also failed: {cleanupError}"
    catch _ => pure ()
  throw primary

private def writeNamedWith (target : System.FilePath) (emit : IO.FS.Stream → IO Unit)
    (hooks : Hooks := {}) : IO Unit := do
  let (path, prepared) ← prepareSibling target emit hooks
  match prepared with
  | .error error => failAndCleanup path error
  | .ok () =>
    try
      hooks.beforeRename
      IO.FS.rename path target
    catch error => failAndCleanup path error

/-- Write to standard output, or atomically replace one literal named path.

For a symbolic-link target, rename replaces the link rather than its referent.
For one name of a multiply-linked file, it replaces only that directory entry.
These semantics avoid mutating an input inode through an alias. -/
def write (target : String) (emit : IO.FS.Stream → IO Unit) : IO Unit := do
  if target == "-" then
    let stdout ← IO.getStdout
    emit stdout
    stdout.flush
  else
    writeNamedWith target emit

/-- Convert any otherwise uncaught IO failure into the tool-error exit status.
Reporting is best-effort so a broken stderr cannot turn containment itself into
another uncaught exception. -/
def containToolErrors (action : IO UInt32) : IO UInt32 := do
  try
    action
  catch error =>
    try IO.eprintln s!"lean-inductive-models: uncaught tool error: {error}"
    catch _ => pure ()
    return (3 : UInt32)

namespace Test

/-- Deterministic failure points for transaction boundary tests. -/
inductive Failure where
  | write | flush | rename
  deriving Inhabited, Repr, BEq

def writeNamedFailing (target : System.FilePath) (failure : Failure) : IO Unit := do
  let emit : IO.FS.Stream → IO Unit := fun stream => do
    stream.putStr "new-output"
    if failure == .write then
      throw <| IO.userError "injected output write failure"
  let hooks : Hooks :=
    { beforeFlush := if failure == .flush then
        throw <| IO.userError "injected output flush failure" else pure ()
      beforeRename := if failure == .rename then
        throw <| IO.userError "injected output rename failure" else pure () }
  writeNamedWith target emit hooks

end Test

end Modelgen.Output
