import Modelgen.Format

namespace Modelgen.Spool

/-- Largest offset accepted by both POSIX `fseeko` and Windows `_fseeki64` in
the portable shim. The export format uses unsigned counters, but host file
offsets are signed 64-bit. -/
def maxSeekOffset : Nat := 9223372036854775807

/-- A persistent range in a spool file. Both fields are fixed width; all
endpoint arithmetic goes through [`ByteSpan.end?`]. -/
structure ByteSpan where
  offset : UInt64
  length : UInt64
  deriving Inhabited, Repr, BEq

def ByteSpan.end? (span : ByteSpan) : Option UInt64 :=
  if span.offset.toNat + span.length.toNat < UInt64.size then
    some (span.offset + span.length)
  else none

def ByteSpan.validate (span : ByteSpan) (fileSize : UInt64) : Except String Unit := do
  unless span.offset.toNat ≤ maxSeekOffset do
    throw "spool span starts beyond the signed 64-bit seek range"
  let some endpoint := span.end?
    | throw "spool span endpoint overflows UInt64"
  unless endpoint ≤ fileSize do
    throw "spool span extends beyond end of file"

/-- Portable absolute seek supplied by the small native spool shim. The Lean
wrapper rejects offsets outside the common signed-64 range before FFI. -/
@[extern "modelgen_spool_seek"]
private opaque seekHandle (handle : @& IO.FS.Handle) (offset : UInt64) : IO Unit

def seek (handle : IO.FS.Handle) (offset : UInt64) : IO Unit := do
  unless offset.toNat ≤ maxSeekOffset do
    throw <| IO.userError "spool seek offset exceeds signed 64-bit range"
  seekHandle handle offset

@[extern "modelgen_spool_mkdir_private_at"]
private opaque mkdirPrivateAtNative (parent leaf : @& String) : IO Unit

/-- Linux production boundary. Open the trusted parent without following a
symlink, verify by file descriptor that it is owned by the effective user and
not group/world-writable, and create `leaf` atomically with mode 0700 via
`mkdirat`. The leaf must be one freshly randomized path component. -/
def mkdirPrivateAt (parent : System.FilePath) (leaf : String) : IO System.FilePath := do
  unless System.Platform.target.contains "linux" do
    throw <| IO.userError "secure spool workspaces are currently supported only on Linux"
  unless !leaf.isEmpty && leaf != "." && leaf != ".." &&
      !leaf.contains '/' && !leaf.contains '\\' do
    throw <| IO.userError "private spool leaf must be one non-special path component"
  mkdirPrivateAtNative parent.toString leaf
  return parent / leaf

private def copyBufferSize : Nat := 4194304

/-- Copy exactly one validated span. A short read is an error rather than a
silently truncated output. The caller supplies the completed source size so
validation never depends on the handle's mutable current position. -/
def copySpan (source destination : IO.FS.Handle) (fileSize : UInt64)
    (span : ByteSpan) : IO Unit := do
  match span.validate fileSize with
  | .error error => throw <| IO.userError error
  | .ok _ => pure ()
  seek source span.offset
  let mut remaining := span.length
  while remaining != 0 do
    let requested := min remaining.toNat copyBufferSize
    let chunk ← source.read requested.toUSize
    if chunk.size != requested then
      throw <| IO.userError s!"short spool read: wanted {requested} bytes, got {chunk.size}"
    destination.write chunk
    remaining := remaining - requested.toUInt64

/-- One append-only spool payload. The handle is deliberately private: only a
successful full write publishes the new position and returned span. -/
structure SpoolFile where
  path : System.FilePath
  private handle : IO.FS.Handle
  private position : IO.Ref UInt64

def SpoolFile.createNew (path : System.FilePath) : IO SpoolFile := do
  let handle ← IO.FS.Handle.mk path .writeNew
  let position ← IO.mkRef 0
  return { path, handle, position }

def SpoolFile.append (file : SpoolFile) (bytes : ByteArray) : IO ByteSpan := do
  unless bytes.size < UInt64.size do
    throw <| IO.userError "spool append length does not fit UInt64"
  let offset ← file.position.get
  let span : ByteSpan := { offset, length := bytes.size.toUInt64 }
  let some endpoint := span.end?
    | throw <| IO.userError "spool append endpoint overflows UInt64"
  file.handle.write bytes
  file.position.set endpoint
  return span

def SpoolFile.flush (file : SpoolFile) : IO Unit := file.handle.flush

def SpoolFile.size (file : SpoolFile) : IO UInt64 := file.position.get

/-- Flush and compare the append counter with the filesystem's completed size.
This catches external truncation and any unreported short write before spans are
published to a composition. -/
def SpoolFile.finish (file : SpoolFile) : IO UInt64 := do
  file.flush
  let expected ← file.size
  let actual := (← file.path.metadata).byteSize
  unless actual == expected do
    throw <| IO.userError s!"spool size mismatch: appended {expected} bytes, file has {actual}"
  return actual

/-- A set of byte ranges whose arena ranges are emitted before declarations.
`declarationOrder` is a permutation of declaration indices, allowing compact
topological scheduling without retaining declaration ASTs. -/
structure Composition where
  metadata : Option ByteSpan := none
  arenas : Array ByteSpan := #[]
  declarations : Array ByteSpan := #[]
  declarationOrder : Array Nat := #[]
  deriving Inhabited, Repr, BEq

private def allPhysicalSpans (composition : Composition) : Array ByteSpan :=
  let spans := composition.metadata.elim #[] (#[·])
  spans ++ composition.arenas ++ composition.declarations

/-- Validate bounds, exact physical coverage, arena source order, and that the
compact declaration order is a true permutation. Exact coverage rejects
unindexed prefix, gap, overlap, duplicate, or trailing bytes. -/
def Composition.validate (composition : Composition) (fileSize : UInt64) : Except String Unit := do
  let physical := allPhysicalSpans composition
  for span in physical do
    unless span.length != 0 do throw "composition contains an empty span"
    span.validate fileSize

  let sorted := physical.qsort fun left right => left.offset < right.offset
  let mut endpoint : UInt64 := 0
  for span in sorted do
    unless span.offset == endpoint do
      throw "composition spans do not partition the spool exactly"
    let some next := span.end?
      | throw "composition span endpoint overflows UInt64"
    endpoint := next
  unless endpoint == fileSize do
    throw "composition spans do not reach the spool end"

  let mut arenaEndpoint : UInt64 := 0
  let mut firstArena := true
  for span in composition.arenas do
    unless firstArena || arenaEndpoint ≤ span.offset do
      throw "composition arena runs are not in source order"
    arenaEndpoint := (span.end?).getD 0
    firstArena := false

  unless composition.declarationOrder.size == composition.declarations.size do
    throw "composition declaration order has the wrong length"
  let mut seen : Std.HashSet Nat := {}
  for index in composition.declarationOrder do
    unless index < composition.declarations.size do
      throw "composition declaration order contains an out-of-range index"
    unless !seen.contains index do
      throw "composition declaration order contains a duplicate index"
    seen := seen.insert index

/-- Emit metadata, all arenas in source order, then declarations in the compact
requested order. [`Composition.validate`] must succeed before the first byte is
written. -/
def Composition.emit (composition : Composition) (source destination : IO.FS.Handle)
    (fileSize : UInt64) : IO Unit := do
  match composition.validate fileSize with
  | .error error => throw <| IO.userError error
  | .ok _ => pure ()
  if let some metadata := composition.metadata then
    copySpan source destination fileSize metadata
  for arena in composition.arenas do
    copySpan source destination fileSize arena
  for index in composition.declarationOrder do
    copySpan source destination fileSize composition.declarations[index]!

end Modelgen.Spool
