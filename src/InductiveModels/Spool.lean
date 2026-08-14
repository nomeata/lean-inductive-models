import InductiveModels.Format
import Std.Internal.Async.System
import Std.Sync.Mutex

namespace InductiveModels.Spool

/-- Largest spool offset admitted by the source spool format. Keeping the historical
signed-64 bound makes validation independent of host integer and filesystem
limits even though the pure-Lean copier advances with bounded reads. -/
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

private def copyBufferSize : Nat := 4194304

/-- Move a pinned handle to `target` using only Lean's portable file API.
Forward movement discards bytes from the current cursor; backward movement
rewinds first.  Keeping the cursor beside the handle avoids rescanning the
large source spool for the overwhelmingly forward compact order. -/
private def moveTo (source : IO.FS.Handle) (current target : UInt64) : IO Unit := do
  unless target.toNat ≤ maxSeekOffset do
    throw <| IO.userError "spool seek offset exceeds signed 64-bit range"
  let mut position := current
  if target < position then
    source.rewind
    position := 0
  let mut remaining := target - position
  while remaining != 0 do
    let requested := min remaining.toNat copyBufferSize
    let chunk ← source.read requested.toUSize
    if chunk.size != requested then
      throw <| IO.userError s!"short spool seek: wanted {requested} bytes, got {chunk.size}"
    remaining := remaining - requested.toUInt64

/-- Copy exactly one validated span. A short read is an error rather than a
silently truncated output. The caller supplies the completed source size so
validation never depends on the handle's mutable current position. -/
private def copySpanWith (source : IO.FS.Handle) (position : IO.Ref UInt64)
    (write : ByteArray → IO Unit)
    (fileSize : UInt64) (span : ByteSpan) : IO Unit := do
  match span.validate fileSize with
  | .error error => throw <| IO.userError error
  | .ok _ => pure ()
  moveTo source (← position.get) span.offset
  let mut remaining := span.length
  while remaining != 0 do
    let requested := min remaining.toNat copyBufferSize
    let chunk ← source.read requested.toUSize
    if chunk.size != requested then
      throw <| IO.userError s!"short spool read: wanted {requested} bytes, got {chunk.size}"
    write chunk
    remaining := remaining - requested.toUInt64
  position.set ((span.end?).getD span.offset)

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

initialize tempRootMutex : Std.Mutex Unit ← Std.Mutex.new ()

/-- Reserve a runtime temporary directory below `root` without inheriting an
unrelated ambient `TMPDIR`. Environment mutation is process-global, so keep the
bracket synchronous and restore the exact previous value before the caller can
perform any workspace work. -/
private def createTempDirIn (root : System.FilePath) : IO System.FilePath := do
  tempRootMutex.atomically fun _ => do
    let previous ← IO.getEnv "TMPDIR"
    try
      Std.Internal.IO.Async.System.setEnvVar "TMPDIR" root.toString
      IO.FS.createTempDir
    finally
      match previous with
      | some value => Std.Internal.IO.Async.System.setEnvVar "TMPDIR" value
      | none => Std.Internal.IO.Async.System.unsetEnvVar "TMPDIR"

def Workspace.create (root : System.FilePath) : IO Workspace := do
  unless root.fileName == some "_tmp" do
    throw <| IO.userError s!"spool workspace root must be the project _tmp directory: {root}"
  let rootMetadata ← root.symlinkMetadata
  unless rootMetadata.type == .dir do
    throw <| IO.userError s!"spool workspace root is not a physical directory: {root}"
  let canonicalRoot ← IO.FS.realPath root
  -- Lean's runtime reserves this directory atomically with owner-only access.
  -- It does not expose descriptor-relative parent attestation, so unlike the
  -- former Linux shim this does not inspect the parent's UID or mode. Bracket
  -- the runtime's process-global temporary root for the reservation only;
  -- ordinary callers may keep an unrelated TMPDIR without silently disabling
  -- declaration-wise source replay. The exact empty directory is removed on a
  -- containment failure.
  let directory ← createTempDirIn root
  let canonicalDirectory ← IO.FS.realPath directory
  let rootParts := canonicalRoot.components
  let directoryParts := canonicalDirectory.components
  unless rootParts.length < directoryParts.length &&
      directoryParts.take rootParts.length == rootParts do
    try IO.FS.removeDir directory catch _ => pure ()
    throw <| IO.userError s!"secure temporary directory {directory} is outside project root {root}"
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

/-- Opaque identity shared only by one raw tee and readers opened from it.
Unlike a certificate (which describes shape and offsets), pointer identity
cannot accidentally equate distinct same-sized source byte streams. -/
structure SourceProvenance where private mk ::
  private marker : IO.Ref Unit

/-- The three logical parser payloads. This is not yet a byte-exact snapshot:
noncanonical ignored records are intentionally absent, and such a certificate
disqualifies declaration-wise planned source replay. -/
structure ParseTee where private mk ::
  metadata : SpoolFile
  arena : SpoolFile
  declarations : SpoolFile
  private provenance : SourceProvenance

def ParseTee.create (workspace : Workspace) : IO ParseTee := do
  let marker ← IO.mkRef ()
  return {
    metadata := ← workspace.createFile "metadata.ndjson"
    arena := ← workspace.createFile "arena.ndjson"
    declarations := ← workspace.createFile "declarations.ndjson"
    provenance := .mk marker }

def ParseTee.sourceProvenance (tee : ParseTee) : SourceProvenance := tee.provenance

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

/-- Input-only source snapshot for checked no-output CLI parsing. The exact raw
file makes ordinary fallback possible after consuming stdin or a FIFO; the
declaration file supplies random-access feed spans. The completed arena is
transferred in memory by the parser, so this tee deliberately has no second
arena or metadata spool. -/
structure PlannedInputTee where private mk ::
  private raw : SpoolFile
  private declarations : SpoolFile
  private provenance : SourceProvenance

structure PlannedInputSizes where
  raw : UInt64
  declarations : UInt64
  deriving Inhabited, Repr, BEq

def PlannedInputTee.create (workspace : Workspace) : IO PlannedInputTee := do
  let marker ← IO.mkRef ()
  return {
    raw := ← workspace.createFile "input.ndjson"
    declarations := ← workspace.createFile "declarations.ndjson"
    provenance := .mk marker }

def PlannedInputTee.sourceProvenance (tee : PlannedInputTee) : SourceProvenance :=
  tee.provenance

def PlannedInputTee.sink (tee : PlannedInputTee) : RawSink where
  emit record := do
    discard <| tee.raw.append record.bytes
    if record.kind == .declaration then
      discard <| tee.declarations.append record.bytes

def PlannedInputTee.finish (tee : PlannedInputTee) : IO PlannedInputSizes := do
  return { raw := ← tee.raw.finish, declarations := ← tee.declarations.finish }

/-- Reparse the exact consumed input snapshot for an ordinary compatibility
fallback. This is input JSON, never generated logical output. -/
def PlannedInputTee.parseFallback (tee : PlannedInputTee)
    (options : ParseOptions := { allowDuplicateNames := true }) : IO (Except String Export) :=
  IO.FS.withFile tee.raw.path .read fun handle =>
    parseHandle handle options

/-- Release the exact fallback snapshot once declaration replay is certified;
late planned-input fallback materializes from the transferred arena instead. -/
def PlannedInputTee.releaseFallback (tee : PlannedInputTee) : IO Unit := do
  if ← tee.raw.path.pathExists then IO.FS.removeFile tee.raw.path

/-- Random-access source decoder over one completed raw tee. The immutable
arena is the exact graph transferred from the declaration-discarding parser;
only the declaration handle cursor and value-level read counter are mutable.
No decoded declaration is retained by the reader. -/
structure PlannedSourceReader where private mk ::
  private arena : DeclarationArena
  private declarations : IO.FS.Handle
  private position : IO.Ref UInt64
  private readCalls : IO.Ref Nat
  private declarationSize : UInt64
  private spans : Array RawSpan
  private provenance : SourceProvenance

/-- Validate and open a complete tee for declaration-wise reads.  The caller
must have finished all three tee files. Canonical progressive arena IDs are a
hard eligibility condition: parser-compatible interleaved overwrites encode
declaration-time snapshots which one completed arena cannot reconstruct. -/
def PlannedSourceReader.create (tee : ParseTee) (certificate : RawCertificate)
    (sizes : RawSpoolSizes) (declarationCount : Nat)
    (arena? : Option DeclarationArena := none) :
    IO (Except String PlannedSourceReader) := do
  match certificate.validate sizes declarationCount with
  | .error error => return .error error
  | .ok _ => pure ()
  try
    let arenaMetadata ← tee.arena.path.symlinkMetadata
    let declarationMetadata ← tee.declarations.path.symlinkMetadata
    unless arenaMetadata.type == .file && declarationMetadata.type == .file do
      return .error "planned source spool is not backed by physical files"
    unless arenaMetadata.byteSize == sizes.arena &&
        declarationMetadata.byteSize == sizes.declarations do
      return .error "planned source spool changed after completion"
    let arena ← match arena? with
      | some arena => pure arena
      | none =>
        let arenaResult ← IO.FS.withFile tee.arena.path .read DeclarationArena.ofHandle
        match arenaResult with
        | .ok arena => pure arena
        | .error error => return .error error
    let declarations ← IO.FS.Handle.mk tee.declarations.path .read
    let position ← IO.mkRef 0
    let readCalls ← IO.mkRef 0
    return .ok <| PlannedSourceReader.mk arena declarations position readCalls
      sizes.declarations certificate.declarations tee.provenance
  catch error =>
    return .error s!"cannot open planned source spool: {error}"

/-- Open the CLI's input-only declaration spool against the exact parser arena.
No arena JSON is reparsed or retained twice. -/
def PlannedSourceReader.createFromInputTee (tee : PlannedInputTee)
    (certificate : RawCertificate) (sizes : PlannedInputSizes)
    (declarationCount : Nat) (arena : DeclarationArena) :
    IO (Except String PlannedSourceReader) := do
  match certificate.validateReplay sizes.declarations declarationCount with
  | .error error => return .error error
  | .ok _ => pure ()
  try
    let rawMetadata ← tee.raw.path.symlinkMetadata
    let declarationMetadata ← tee.declarations.path.symlinkMetadata
    unless rawMetadata.type == .file && declarationMetadata.type == .file do
      return .error "direct input spool is not backed by physical files"
    unless rawMetadata.byteSize == sizes.raw &&
        declarationMetadata.byteSize == sizes.declarations do
      return .error "direct input spool changed after completion"
    let declarations ← IO.FS.Handle.mk tee.declarations.path .read
    let position ← IO.mkRef 0
    let readCalls ← IO.mkRef 0
    return .ok <| PlannedSourceReader.mk arena declarations position readCalls
      sizes.declarations certificate.declarations tee.provenance
  catch error =>
    return .error s!"cannot open direct input spool: {error}"

/-- Number of source declaration records certified for this reader. -/
def PlannedSourceReader.size (reader : PlannedSourceReader) : Nat := reader.spans.size

/-- Number of declaration-read requests made through this reader. This
value-only observer lets retention tests distinguish the one Phase-A pass plus
owner rereads from accidental materialization or a second all-source pass. -/
def PlannedSourceReader.readCount (reader : PlannedSourceReader) : IO Nat :=
  reader.readCalls.get

/-- Bind a reader to the exact tee observed by a parser/census pass. Shape,
size, and arena-cursor certificates cannot distinguish adversarial or merely
coincidental same-sized inputs; this opaque identity can. -/
def PlannedSourceReader.matchesSource (reader : PlannedSourceReader)
    (source : SourceProvenance) : IO Bool :=
  reader.provenance.marker.ptrEq source.marker

/-- Decode one declaration ordinal. Reads are valid in arbitrary order; a
backward request rewinds the handle, while each result becomes unreachable as
soon as its caller finishes the declaration transition. -/
def PlannedSourceReader.read (reader : PlannedSourceReader)
    (ordinal : Nat) : IO (Except String EDecl) := do
  let some rawSpan := reader.spans[ordinal]?
    | return .error s!"planned source ordinal {ordinal} is out of range"
  reader.readCalls.modify (· + 1)
  let span : ByteSpan := { offset := rawSpan.offset, length := rawSpan.bytes }
  match span.validate reader.declarationSize with
  | .error error => return .error error
  | .ok () => pure ()
  try
    moveTo reader.declarations (← reader.position.get) span.offset
    let mut remaining := span.length
    let mut bytes : ByteArray := .empty
    while remaining != 0 do
      let requested := min remaining.toNat copyBufferSize
      let chunk ← reader.declarations.read requested.toUSize
      if chunk.size != requested then
        return .error s!"short planned source read: wanted {requested} bytes, got {chunk.size}"
      bytes := bytes ++ chunk
      remaining := remaining - requested.toUInt64
    reader.position.set ((span.end?).getD span.offset)
    return reader.arena.decode bytes
  catch error =>
    return .error s!"cannot read planned source declaration {ordinal}: {error}"

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

end InductiveModels.Spool
