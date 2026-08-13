import Modelgen.Format
import Std.Sync.Mutex

namespace Modelgen.Spool

/-- Main-side eligibility guard. Stream certification is necessary, but a mode
which rewrites the whole export (currently universe monomorphization) always
selects the existing full writer. -/
def rawFastPathEligible (certificate : RawCertificate) (sizes : RawSpoolSizes)
    (declarationCount : Nat) (monoLevels : Bool) : Bool :=
  if monoLevels then false
  else match certificate.validate sizes declarationCount with
    | .ok _ => true
    | .error _ => false

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
  unless endpoint.toNat ≤ maxSeekOffset do
    throw "spool span ends beyond the signed 64-bit seek range"
  unless endpoint ≤ fileSize do
    throw "spool span extends beyond end of file"

/-- Portable absolute seek supplied by the small native spool shim. The Lean
wrapper rejects offsets outside the common signed-64 range before FFI. -/
@[extern "lean_inductive_models_spool_seek"]
private opaque seekHandle (handle : @& IO.FS.Handle) (offset : UInt64) : IO Unit

def seek (handle : IO.FS.Handle) (offset : UInt64) : IO Unit := do
  unless offset.toNat ≤ maxSeekOffset do
    throw <| IO.userError "spool seek offset exceeds signed 64-bit range"
  seekHandle handle offset

@[extern "lean_inductive_models_spool_mkdir_private_at"]
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
private def copySpanWith (source : IO.FS.Handle) (write : ByteArray → IO Unit)
    (fileSize : UInt64) (span : ByteSpan) : IO Unit := do
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
    write chunk
    remaining := remaining - requested.toUInt64

def copySpan (source destination : IO.FS.Handle) (fileSize : UInt64)
    (span : ByteSpan) : IO Unit :=
  copySpanWith source destination.write fileSize span

/-- Copy a validated spool span to the stream abstraction used by transactional
output. This performs the same bounded reads and short-read checks as the
handle-to-handle copier. -/
def copySpanToStream (source : IO.FS.Handle) (destination : IO.FS.Stream)
    (fileSize : UInt64) (span : ByteSpan) : IO Unit :=
  copySpanWith source destination.write fileSize span

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

/-- A secure project-local workspace which records every leaf it owns. Cleanup
never recurses and never accepts a caller-selected deletion target. -/
structure Workspace where
  root : System.FilePath
  directory : System.FilePath
  private ownedFiles : IO.Ref (Array System.FilePath)

private def maxWorkspaceAttempts : Nat := 64

def Workspace.create (root : System.FilePath) : IO Workspace := do
  unless root.fileName == some "_tmp" do
    throw <| IO.userError s!"spool workspace root must be the project _tmp directory: {root}"
  let rec attempt : Nat → IO System.FilePath
    | 0 => throw <| IO.userError
        s!"could not reserve a spool workspace after {maxWorkspaceAttempts} attempts"
    | remaining + 1 => do
      let suffix := rawSpoolSuffixOfBytes (← IO.getRandomBytes 16)
      let leaf := s!"lean-inductive-models-spool-{suffix}"
      try mkdirPrivateAt root leaf
      catch error =>
        let candidate := root / leaf
        if ← candidate.pathExists then attempt remaining else throw error
  let directory ← attempt maxWorkspaceAttempts
  let ownedFiles ← IO.mkRef #[]
  return { root, directory, ownedFiles }

private def validLeaf (leaf : String) : Bool :=
  !leaf.isEmpty && leaf != "." && leaf != ".." &&
    !leaf.contains '/' && !leaf.contains '\\'

def Workspace.createFile (workspace : Workspace) (leaf : String) : IO SpoolFile := do
  unless validLeaf leaf do throw <| IO.userError "spool file must be one non-special path component"
  let path := workspace.directory / leaf
  let file ← SpoolFile.createNew path
  workspace.ownedFiles.modify (fun paths => paths.push path)
  return file

/-- The three logical parser payloads. This is not yet a byte-exact snapshot:
noncanonical ignored records are intentionally absent, and such a certificate
always selects the existing full writer. -/
structure ParseTee where
  metadata : SpoolFile
  arena : SpoolFile
  declarations : SpoolFile

def ParseTee.create (workspace : Workspace) : IO ParseTee := do
  return {
    metadata := ← workspace.createFile "metadata.ndjson"
    arena := ← workspace.createFile "arena.ndjson"
    declarations := ← workspace.createFile "declarations.ndjson" }

def ParseTee.sink (tee : ParseTee) : RawSink where
  emit record := match record.kind with
    | .metadata => discard <| tee.metadata.append record.bytes
    | .arena => discard <| tee.arena.append record.bytes
    | .declaration => discard <| tee.declarations.append record.bytes
    | .ignored => pure ()

def ParseTee.finish (tee : ParseTee) : IO RawSpoolSizes := do
  return {
    metadata := ← tee.metadata.finish
    arena := ← tee.arena.finish
    declarations := ← tee.declarations.finish }

/-- String-only prepared declaration. Once prepared, no generated `EDecl` or
`Expr` is needed to commit the island. -/
structure PreparedDecl where private mk ::
  private split : Writer.DeclSplit
  deriving Repr, BEq

/-- An island-local serialization transaction. Arena IDs are not published to
the shared stage until the whole cursor chain validates and every byte writes. -/
structure PreparedIsland where private mk ::
  private before : Writer.Cursor
  private declarations : Array PreparedDecl
  private after : Writer.Cursor
  deriving Repr, BEq

/-- Serialize one nonempty accepted island in memory. The private constructors
of `PreparedIsland` and `PreparedDecl` make the validated cursor chain the only
payload the append stage can receive. -/
def prepareIsland (cursor : Writer.Cursor) (records : Array EDecl) :
    Except String PreparedIsland := Id.run do
  if records.isEmpty then return .error "cannot prepare an empty generated island"
  let mut writer := Writer.fromCursor cursor
  let mut declarations : Array PreparedDecl := #[]
  for record in records do
    let (next, split) := writer.splitDecl record
    writer := next
    declarations := declarations.push (.mk split)
  return .ok (.mk cursor declarations writer.cursor)

private def PreparedIsland.validate (island : PreparedIsland) : Except String Unit := do
  if island.declarations.isEmpty then throw "prepared island is empty"
  let mut cursor := island.before
  for declaration in island.declarations do
    declaration.split.validateStart cursor
    cursor := declaration.split.after
  unless cursor == island.after do
    throw s!"prepared island ends at {repr cursor}, advertised {repr island.after}"

/-- Spans published by one accepted island. Arena runs remain in serialized
island order; declaration spans may later be scheduled by compact summaries. -/
structure IslandCommit where
  before : Writer.Cursor
  arenas : Array ByteSpan
  declarations : Array ByteSpan
  after : Writer.Cursor
  deriving Inhabited, Repr, BEq

/-- A successfully flushed island payload. Paths are published only in this
sealed result; an open or poisoned stage exposes no composition locators. -/
structure SealedIsland where
  arenaPath : System.FilePath
  declarationPath : System.FilePath
  arenaSize : UInt64
  declarationSize : UInt64
  cursor : Writer.Cursor
  deriving Repr, BEq

private inductive IslandStageState where
  | open (cursor : Writer.Cursor)
  | failed (cursor : Writer.Cursor)
  | finished (result : SealedIsland)

private inductive CommitFault where
  | afterFirstArena
  | afterArenas
  | afterFirstDeclaration
  deriving Repr, BEq

/-- Append-only generated payloads plus the next globally unoccupied arena
IDs. The mutex serializes `commit`, `cursor`, and `finish`; this remains true if
a future caller prepares islands concurrently. -/
structure IslandStage where
  private arena : SpoolFile
  private declarations : SpoolFile
  private state : Std.Mutex IslandStageState
  private injectedFault : Option CommitFault := none

def IslandStage.create (workspace : Workspace) (cursor : Writer.Cursor) : IO IslandStage := do
  return {
    arena := ← workspace.createFile "generated-arena.ndjson"
    declarations := ← workspace.createFile "generated-declarations.ndjson"
    state := ← Std.Mutex.new (.open cursor) }

def IslandStage.cursor (stage : IslandStage) : IO Writer.Cursor := do
  stage.state.atomically fun state => do match ← state.get with
    | .open cursor | .failed cursor => return cursor
    | .finished result => return result.cursor

/-- Current append counters for diagnostics. Access is serialized with commit
so callers never observe the middle of a transaction. -/
def IslandStage.sizes (stage : IslandStage) : IO (UInt64 × UInt64) :=
  stage.state.atomically fun _ => return (← stage.arena.size, ← stage.declarations.size)

private def IslandStage.inject (stage : IslandStage) (point : CommitFault) : IO Unit :=
  if stage.injectedFault == some point then
    throw <| IO.userError s!"injected island commit failure at {repr point}"
  else
    pure ()

/-- Validate before the first write; publish the new cursor only after every
append succeeds. A stale transaction cannot write or advance the stage. Any
write failure permanently poisons this append stage: its old cursor remains
observable for diagnostics, but subsequent commits and `finish` reject the
unindexed tail. Bytes become durable/externally publishable only after the
caller successfully runs `finish`, which flushes and validates both files. -/
def IslandStage.commit (stage : IslandStage) (island : PreparedIsland) : IO IslandCommit := do
  match island.validate with
  | .error error => throw <| IO.userError error
  | .ok _ => pure ()
  stage.state.atomically fun stateRef => do
    let state ← stateRef.get
    let current ← match state with
      | .open cursor => pure cursor
      | .failed _ => throw <| IO.userError "island append stage is poisoned"
      | .finished _ => throw <| IO.userError "island append stage is already finished"
    unless island.before == current do
      throw <| IO.userError
        s!"stale island starts at {repr island.before}, expected {repr current}"
    try
      let mut arenas : Array ByteSpan := #[]
      let mut declarations : Array ByteSpan := #[]
      let mut wroteArena := false
      for declaration in island.declarations do
        for line in declaration.split.arena do
          arenas := arenas.push (← stage.arena.append (line ++ "\n").toUTF8)
          if !wroteArena then
            wroteArena := true
            stage.inject .afterFirstArena
      stage.inject .afterArenas
      for declaration in island.declarations do
        declarations := declarations.push
          (← stage.declarations.append (declaration.split.declaration ++ "\n").toUTF8)
        if declarations.size == 1 then stage.inject .afterFirstDeclaration
      stateRef.set (.open island.after)
      return { before := island.before, arenas, declarations, after := island.after }
    catch error =>
      stateRef.set (.failed current)
      throw error

def IslandStage.finish (stage : IslandStage) : IO SealedIsland := do
  stage.state.atomically fun stateRef => do
    let state ← stateRef.get
    match state with
    | .failed _ => throw <| IO.userError "cannot finish poisoned island append stage"
    | .finished result => return result
    | .open cursor => try
        let result : SealedIsland := {
          arenaPath := stage.arena.path
          declarationPath := stage.declarations.path
          arenaSize := ← stage.arena.finish
          declarationSize := ← stage.declarations.finish
          cursor }
        stateRef.set (.finished result)
        return result
      catch error =>
        stateRef.set (.failed cursor)
        throw error

/-! Failure injection is kept in a visibly test-only namespace; production
construction always uses `IslandStage.create` and has no injected fault. -/
namespace Test

inductive CommitFailure where
  | afterFirstArena
  | afterArenas
  | afterFirstDeclaration
  deriving Inhabited, Repr, BEq

def createFailingIslandStage (workspace : Workspace) (cursor : Writer.Cursor)
    (failure : CommitFailure) : IO IslandStage := do
  let injectedFault := match failure with
    | .afterFirstArena => CommitFault.afterFirstArena
    | .afterArenas => CommitFault.afterArenas
    | .afterFirstDeclaration => CommitFault.afterFirstDeclaration
  return {
    arena := ← workspace.createFile "generated-arena.ndjson"
    declarations := ← workspace.createFile "generated-declarations.ndjson"
    state := ← Std.Mutex.new (.open cursor)
    injectedFault }

/-- Cause `finish` to encounter a real filesystem error after valid appends.
The open file handle remains owned by the workspace; removing its directory
entry makes the subsequent metadata validation fail. -/
def removeArenaBeforeFinish (stage : IslandStage) : IO Unit :=
  IO.FS.removeFile stage.arena.path

end Test

private def Workspace.cleanup (workspace : Workspace) : IO Unit := do
  let mut firstError : Option IO.Error := none
  for path in ← workspace.ownedFiles.get do
    try
      if ← path.pathExists then IO.FS.removeFile path
    catch error => if firstError.isNone then firstError := some error
  try
    if ← workspace.directory.pathExists then IO.FS.removeDir workspace.directory
  catch error => if firstError.isNone then firstError := some error
  if let some error := firstError then throw error

/-- Run an action in a fresh workspace and remove only its registered files and
empty directory. If both the action and cleanup fail, report cleanup separately
and rethrow the primary action exception. -/
private def Workspace.run (workspace : Workspace) (action : Workspace → IO α) : IO α := do
  let result : Except IO.Error α ← try
      pure (Except.ok (← action workspace))
    catch error => pure (Except.error error)
  let cleanupError : Option IO.Error ← try
      workspace.cleanup
      pure none
    catch error => pure (some error)
  match result, cleanupError with
  | .ok value, none => pure value
  | .ok _, some error => throw error
  | .error error, none => throw error
  | .error error, some cleanupError => do
      IO.eprintln s!"spool workspace cleanup also failed: {cleanupError}"
      throw error

def withWorkspace (root : System.FilePath) (action : Workspace → IO α) : IO α := do
  let workspace ← Workspace.create root
  workspace.run action

/-- Try to reserve a workspace before calling `action`. Failure to establish
the optional optimization is represented by `none`; once `action` starts, its
errors propagate and are never mistaken for a reason to rerun the pipeline. -/
def withOptionalWorkspace (root : System.FilePath)
    (action : Option Workspace → IO α) : IO α := do
  let workspace? ← try
      pure (some (← Workspace.create root))
    catch _ => pure none
  match workspace? with
  | none => action none
  | some workspace => workspace.run fun _ => action (some workspace)

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

/-! ## Mixed source/generated composition

The parser and generated-island stages deliberately use separate append-only
files. Keeping them separate avoids another full-size concatenation spool; the
final writer only needs to distinguish which declaration file owns each span.
-/

inductive MixedDeclarationSpan where
  | source (span : ByteSpan)
  | generated (span : ByteSpan)
  deriving Inhabited, Repr, BEq

/-- Every immutable file and completed byte count needed to emit one staged
export. Source metadata and arenas retain parser order, generated arenas retain
cursor publication order, and `declarations` is already in compact final order.
-/
structure MixedComposition where
  sourceMetadataPath : System.FilePath
  sourceArenaPath : System.FilePath
  sourceDeclarationPath : System.FilePath
  sourceSizes : RawSpoolSizes
  generatedArenaPath : System.FilePath
  generatedDeclarationPath : System.FilePath
  generatedArenaSize : UInt64
  generatedDeclarationSize : UInt64
  declarations : Array MixedDeclarationSpan
  deriving Repr, BEq

private def spansPartitionFile (spans : Array ByteSpan) (fileSize : UInt64) : Bool := Id.run do
  let sorted := spans.qsort fun left right => left.offset < right.offset
  let mut endpoint : UInt64 := 0
  for span in sorted do
    unless span.offset == endpoint do return false
    let some next := span.end? | return false
    unless next ≤ fileSize do return false
    endpoint := next
  return endpoint == fileSize

/-- Validate declaration ownership and exact physical coverage before opening
the output transaction. This makes a missing, repeated, overlapping, or
out-of-range span fail before stdout receives its first byte. -/
def MixedComposition.validate (composition : MixedComposition) : Except String Unit := do
  for size in #[composition.sourceSizes.metadata, composition.sourceSizes.arena,
      composition.sourceSizes.declarations, composition.generatedArenaSize,
      composition.generatedDeclarationSize] do
    unless size.toNat ≤ maxSeekOffset do
      throw "staged spool file exceeds the signed 64-bit seek range"
  let mut source : Array ByteSpan := #[]
  let mut generated : Array ByteSpan := #[]
  for declaration in composition.declarations do
    match declaration with
    | .source span =>
      span.validate composition.sourceSizes.declarations
      source := source.push span
    | .generated span =>
      span.validate composition.generatedDeclarationSize
      generated := generated.push span
  unless spansPartitionFile source composition.sourceSizes.declarations do
    throw "source declaration spans do not partition their spool"
  unless spansPartitionFile generated composition.generatedDeclarationSize do
    throw "generated declaration spans do not partition their spool"

private def exactFileSize (path : System.FilePath) (expected : UInt64) : IO Unit := do
  let actual := (← path.metadata).byteSize
  unless actual == expected do
    throw <| IO.userError s!"staged spool size mismatch for {path}: expected {expected}, got {actual}"

/-- Check every path and span, open every input handle, then emit metadata,
source arenas, generated arenas, and compactly ordered declarations. No byte is
written until all validation and opens succeed. Flushing and atomic installation
remain the responsibility of [`Modelgen.Output.write`]. -/
def MixedComposition.emit (composition : MixedComposition)
    (destination : IO.FS.Stream) : IO Unit := do
  match composition.validate with
  | .error error => throw <| IO.userError error
  | .ok _ => pure ()
  exactFileSize composition.sourceMetadataPath composition.sourceSizes.metadata
  exactFileSize composition.sourceArenaPath composition.sourceSizes.arena
  exactFileSize composition.sourceDeclarationPath composition.sourceSizes.declarations
  exactFileSize composition.generatedArenaPath composition.generatedArenaSize
  exactFileSize composition.generatedDeclarationPath composition.generatedDeclarationSize
  IO.FS.withFile composition.sourceMetadataPath .read fun sourceMetadata =>
    IO.FS.withFile composition.sourceArenaPath .read fun sourceArena =>
      IO.FS.withFile composition.sourceDeclarationPath .read fun sourceDeclarations =>
        IO.FS.withFile composition.generatedArenaPath .read fun generatedArena =>
          IO.FS.withFile composition.generatedDeclarationPath .read fun generatedDeclarations => do
            unless composition.sourceSizes.metadata == 0 do
              copySpanToStream sourceMetadata destination composition.sourceSizes.metadata
                { offset := 0, length := composition.sourceSizes.metadata }
            unless composition.sourceSizes.arena == 0 do
              copySpanToStream sourceArena destination composition.sourceSizes.arena
                { offset := 0, length := composition.sourceSizes.arena }
            unless composition.generatedArenaSize == 0 do
              copySpanToStream generatedArena destination composition.generatedArenaSize
                { offset := 0, length := composition.generatedArenaSize }
            for declaration in composition.declarations do
              match declaration with
              | .source span =>
                copySpanToStream sourceDeclarations destination
                  composition.sourceSizes.declarations span
              | .generated span =>
                copySpanToStream generatedDeclarations destination
                  composition.generatedDeclarationSize span

end Modelgen.Spool
