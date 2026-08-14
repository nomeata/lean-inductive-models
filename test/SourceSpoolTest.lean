import InductiveModels.Spool

open Lean InductiveModels

set_option maxRecDepth 4096

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def lines (records : Array String) : String :=
  records.foldl (fun text record => text ++ record ++ "\n") ""

def removeIfPresent (path : String) : IO Unit := do
  if ← System.FilePath.pathExists path then IO.FS.removeFile path

def parseHandleAt (path : String) : IO (Except String Export) :=
  IO.FS.withFile path .read fun handle => InductiveModels.parseHandle handle

/-- Deliberately whole-text random-decode oracle for the source reader. -/
def referenceDecode (arena declaration : String) : Except String EDecl := do
  let parsed ← InductiveModels.parse (arena ++ declaration) (analyse := false)
  let #[result] := parsed.decls | throw "reference declaration did not decode alone"
  return result

def referenceDecodesTo (arena declaration : String) (expected : EDecl) : Bool :=
  match referenceDecode arena declaration with
  | .ok actual => actual == expected
  | .error _ => false

def rawCertificateAt (path : String) : IO (Except String (Export × RawCertificate)) :=
  IO.FS.withFile path .read fun handle =>
    InductiveModels.parseHandleWithSink handle { emit := fun _ => pure () } (analyse := false)

def discardingCertificateAt (path : String) (allowDuplicateNames : Bool := false) :
    IO (Except String (ParsedEnvelope × RawCertificate × Nat)) := do
  let callbacks ← IO.mkRef 0
  let result ← IO.FS.withFile path .read fun handle =>
    InductiveModels.parseHandleDiscardingDeclarations handle
      { emit := fun _ => pure () }
      { emit := fun _ => callbacks.modify (· + 1) }
      (analyse := false) allowDuplicateNames
  let count ← callbacks.get
  return result.map fun (envelope, certificate) => (envelope, certificate, count)

def rawFastPathRejected (path text : String) : IO Bool := do
  IO.FS.writeFile path text
  match ← rawCertificateAt path with
  | .ok (_, certificate) => return !certificate.canonical
  | .error _ => return false

def rawFastPathAccepted (path text : String) : IO Bool := do
  IO.FS.writeFile path text
  match ← rawCertificateAt path with
  | .ok (_, certificate) => return certificate.canonical
  | .error _ => return false

def plannedSourceRejected (scratch path text : String) : IO Bool := do
  IO.FS.writeFile path text
  let ordinary ← parseHandleAt path
  unless ordinary matches .ok _ do return false
  Spool.withWorkspace scratch fun workspace => do
    let tee ← Spool.ParseTee.create workspace
    let captured ← IO.FS.withFile path .read fun handle =>
      parseHandleWithSink handle tee.sink (analyse := false) (allowDuplicateNames := true)
    let .ok (output, certificate) := captured | return false
    let sizes ← tee.finish
    return (← Spool.PlannedSourceReader.create tee certificate sizes output.decls.size) matches
      .error _

def plannedDiscardingSourceRejected (scratch path text : String) : IO Bool := do
  IO.FS.writeFile path text
  Spool.withWorkspace scratch fun workspace => do
    let tee ← Spool.ParseTee.create workspace
    let captured ← IO.FS.withFile path .read fun handle =>
      parseHandleDiscardingDeclarations handle tee.sink { emit := fun _ => pure () }
        (analyse := false) (allowDuplicateNames := true)
    let .ok (envelope, certificate) := captured | return false
    let sizes ← tee.finish
    return (← Spool.PlannedSourceReader.create tee certificate sizes
      envelope.declarationCount) matches .error _

def bothReject (whole streamed : Except String Export) : Bool :=
  match whole, streamed with
  | .error _, .error _ => true
  | _, _ => false

def bothHaveDecls (whole streamed : Except String Export) (expected : Array EDecl) : Bool :=
  match whole, streamed with
  | .ok first, .ok second => first.decls == expected && second.decls == expected
  | _, _ => false

def bothProjectionFacts (whole streamed : Except String Export)
    (present absent : Array Expr) : Bool :=
  match whole, streamed with
  | .ok first, .ok second =>
      present.all (first.projNodes.contains ·) && present.all (second.projNodes.contains ·) &&
        absent.all (!first.projNodes.contains ·) && absent.all (!second.projNodes.contains ·)
  | _, _ => false

def isExceptError (result : Except ε α) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

def main (args : List String) : IO UInt32 := do
  let root := args.head?.getD "."
  let scratch := s!"{root}/_tmp"
  IO.FS.createDirAll scratch
  let arenaPath := s!"{scratch}/source-spool-arena.ndjson"
  let firstPath := s!"{scratch}/source-spool-first.ndjson"
  let secondPath := s!"{scratch}/source-spool-second.ndjson"
  let malformedPath := s!"{scratch}/source-spool-malformed.ndjson"
  let nameHolePath := s!"{scratch}/source-spool-name-hole.ndjson"
  let levelHolePath := s!"{scratch}/source-spool-level-hole.ndjson"
  let exprHolePath := s!"{scratch}/source-spool-expr-hole.ndjson"
  let sparsePath := s!"{scratch}/source-spool-sparse.ndjson"
  let overwritePath := s!"{scratch}/source-spool-overwrite.ndjson"
  let projectionOrderPath := s!"{scratch}/source-spool-projection-order.ndjson"
  let projectionOverwritePath := s!"{scratch}/source-spool-projection-overwrite.ndjson"
  let parserCompatibilityPath := s!"{scratch}/source-spool-parser-compatibility.ndjson"
  let rawCanonicalPath := s!"{scratch}/raw-spool-canonical.ndjson"
  let rawNameGapPath := s!"{scratch}/raw-spool-name-gap.ndjson"
  let rawLevelGapPath := s!"{scratch}/raw-spool-level-gap.ndjson"
  let rawExprGapPath := s!"{scratch}/raw-spool-expr-gap.ndjson"
  let rawNameOrderPath := s!"{scratch}/raw-spool-name-order.ndjson"
  let rawNoLfPath := s!"{scratch}/raw-spool-no-lf.ndjson"
  let rawWhitespacePath := s!"{scratch}/raw-spool-whitespace.ndjson"
  let rawBlankPath := s!"{scratch}/raw-spool-blank.ndjson"
  let rawCrlfPath := s!"{scratch}/raw-spool-crlf.ndjson"
  let rawKeyOrderPath := s!"{scratch}/raw-spool-key-order.ndjson"
  let rawRootSentinel := s!"{scratch}/raw-spool-root-sentinel"
  let paths := [arenaPath, firstPath, secondPath, malformedPath,
    nameHolePath, levelHolePath, exprHolePath, sparsePath, overwritePath,
    projectionOrderPath, projectionOverwritePath, parserCompatibilityPath,
    rawCanonicalPath, rawNameGapPath, rawLevelGapPath, rawExprGapPath,
    rawNameOrderPath, rawNoLfPath, rawWhitespacePath, rawBlankPath, rawCrlfPath,
    rawKeyOrderPath, rawRootSentinel]
  for path in paths do removeIfPresent path

  let type := Expr.sort (.param `u)
  let first : EDecl := .ax `Island.A [`u] type false
  let second : EDecl := .ax `Island.B [`u] type false
  let (_, firstSplit) := (Writer.fromCursor {}).splitDecl first
  -- A new island deliberately forgets the first island's structural keys,
  -- but starts after all of its arena IDs.
  let (_, secondSplit) := (Writer.fromCursor firstSplit.after).splitDecl second
  let (sharedAfterFirst, sharedFirstSplit) := (Writer.fromCursor {}).splitDecl first
  let (_, sharedSecondSplit) := sharedAfterFirst.splitDecl second

  IO.FS.writeFile arenaPath (lines (firstSplit.arena ++ secondSplit.arena))
  IO.FS.writeFile firstPath (firstSplit.declaration ++ "\n")
  IO.FS.writeFile secondPath (secondSplit.declaration ++ "\n")
  let arenaText ← IO.FS.readFile arenaPath
  let firstText ← IO.FS.readFile firstPath
  let secondText ← IO.FS.readFile secondPath
  -- Arena order is fixed; declaration records can be consumed in a different
  -- topological order without changing what their IDs decode to.
  let reordered := arenaText ++ secondText ++ firstText
  let parsed := InductiveModels.parse reordered (analyse := false)

  let mut state : TestState := {}
  let secureWorkspacePath ← IO.mkRef (none : Option System.FilePath)
  let secureWorkspaceBoundary ← Spool.withWorkspace scratch fun workspace => do
    secureWorkspacePath.set (some workspace.directory)
    let canonicalRoot ← IO.FS.realPath scratch
    let canonicalDirectory ← IO.FS.realPath workspace.directory
    let rootParts := canonicalRoot.components
    let directoryParts := canonicalDirectory.components
    let metadata ← workspace.directory.symlinkMetadata
    return metadata.type == .dir && rootParts.length < directoryParts.length &&
      directoryParts.take rootParts.length == rootParts
  let secureWorkspacePath? ← secureWorkspacePath.get
  let secureWorkspaceCleaned ← if let some path := secureWorkspacePath? then
      path.pathExists.map Bool.not
    else pure false
  state := state.check "runtime workspace is a secure physical child of project _tmp" <|
    secureWorkspaceBoundary && secureWorkspaceCleaned

  let suffixProbe := rawSpoolSuffixOfBytes <| ByteArray.mk #[
    0x00, 0x0f, 0x10, 0x2a, 0x34, 0x4b, 0x56, 0x67,
    0x78, 0x89, 0x9a, 0xab, 0xbc, 0xcd, 0xde, 0xff]
  let suffixOther := rawSpoolSuffixOfBytes <| ByteArray.mk #[
    0xff, 0xde, 0xcd, 0xbc, 0xab, 0x9a, 0x89, 0x78,
    0x67, 0x56, 0x4b, 0x34, 0x2a, 0x10, 0x0f, 0x00]
  state := state.check "raw spool suffix preserves all 128 entropy bits" <|
    suffixProbe == "000f102a344b566778899aabbccddeff" &&
      suffixProbe.utf8ByteSize == 32 && suffixProbe.all fun char =>
        char.isDigit || ('a' ≤ char && char ≤ 'f')
  state := state.check "different raw spool bytes have different suffixes" <|
    suffixProbe != suffixOther
  state := state.check "split arenas plus reordered declarations parse identically" <|
    match parsed with
    | .ok output => output.decls == #[second, first]
    | .error _ => false
  state := state.check "whole-text random declaration oracle preserves exact records" <|
    referenceDecodesTo arenaText secondText second &&
      referenceDecodesTo arenaText firstText first
  let splitRender := lines sharedFirstSplit.arena ++ sharedFirstSplit.declaration ++ "\n" ++
    lines sharedSecondSplit.arena ++ sharedSecondSplit.declaration ++ "\n"
  state := state.check "split declaration stream is byte-identical to whole export rendering" <|
    splitRender == Export.render { metaLine := .null, decls := #[first, second] }

  state := state.check "fresh island advances every explicit arena counter" <|
    firstSplit.after == { nextName := 4, nextLevel := 2, nextExpr := 1 } &&
      secondSplit.after == { nextName := 7, nextLevel := 3, nextExpr := 2 }
  state := state.check "cross-island structural duplicates are permitted" <|
    firstSplit.arena.size == 5 && secondSplit.arena.size == 5

  -- Within one island, the ordinary structural maps still share the common
  -- name prefix, level and expression.
  state := state.check "one island still hash-conses shared structure" <|
    sharedSecondSplit.arena.size == 1 &&
      sharedSecondSplit.after == { nextName := 5, nextLevel := 2, nextExpr := 1 }

  -- Parse-time source capture sees exact bytes while the input descriptor is still
  -- open.  The source arena remains interleaved here; the three spools split
  -- it without retaining any raw line in the parsed Export.
  let rawMeta := "{\"meta\":\"raw-spool-test\"}\n"
  let rawFirstDecl := firstSplit.declaration ++ "\n"
  let rawSecondDecl := secondSplit.declaration ++ "\n"
  let rawCanonical := rawMeta ++ lines firstSplit.arena ++ rawFirstDecl ++
    lines secondSplit.arena ++ rawSecondDecl
  IO.FS.writeFile rawCanonicalPath rawCanonical
  let captured ← Spool.withWorkspace scratch fun workspace => do
    let tee ← Spool.ParseTee.create workspace
    let parsed ← IO.FS.withFile rawCanonicalPath .read fun handle =>
      parseHandleWithSink handle tee.sink (analyse := false)
    let sizes ← tee.finish
    let decodedParity ← match parsed with
      | .error _ => pure false
      | .ok (output, certificate) => do
        match ← Spool.PlannedSourceReader.create tee certificate sizes output.decls.size with
        | .error _ => pure false
        | .ok reader => do
          let second ← reader.read 1
          let first ← reader.read 0
          let secondAgain ← reader.read 1
          let outside ← reader.read 2
          pure <| reader.size == 2 &&
            (match second with | .ok actual => actual == output.decls[1]! | _ => false) &&
            (match first with | .ok actual => actual == output.decls[0]! | _ => false) &&
            (match secondAgain with | .ok actual => actual == output.decls[1]! | _ => false) &&
            (outside matches .error _)
    let metadata ← IO.FS.readFile tee.metadata.path
    let arena ← IO.FS.readFile tee.arena.path
    let declarations ← IO.FS.readFile tee.declarations.path
    return (parsed, decodedParity, metadata, arena, declarations,
      #[tee.metadata.path, tee.arena.path, tee.declarations.path])
  let (capturedParse, capturedDecodedParity, capturedMetadata, capturedArena, capturedDeclarations,
      capturedPaths) := captured
  let expectedArena := lines (firstSplit.arena ++ secondSplit.arena)
  let expectedDeclarations := rawFirstDecl ++ rawSecondDecl
  state := state.check "canonical parse-time spool preserves exact split bytes" <|
    capturedMetadata == rawMeta && capturedArena == expectedArena &&
      capturedDeclarations == expectedDeclarations
  state := state.check "canonical parse-time spool records exact cursor and spans" <|
    match capturedParse with
    | .ok (output, certificate) =>
      output.decls == #[first, second] && certificate.canonical &&
        certificate.cursor == { nextName := 7, nextLevel := 3, nextExpr := 2 } &&
        certificate.metadataBytes == rawMeta.utf8ByteSize.toUInt64 &&
        certificate.arenaBytes == expectedArena.utf8ByteSize.toUInt64 &&
        certificate.declarationBytes == expectedDeclarations.utf8ByteSize.toUInt64 &&
        certificate.declarations == #[
          { offset := 0, bytes := rawFirstDecl.utf8ByteSize.toUInt64 },
          { offset := rawFirstDecl.utf8ByteSize.toUInt64,
            bytes := rawSecondDecl.utf8ByteSize.toUInt64 }]
    | .error _ => false
  state := state.check "planned source reader decodes arbitrary and backward ordinals" <|
    capturedDecodedParity
  let spoolSizes : RawSpoolSizes :=
    { metadata := capturedMetadata.utf8ByteSize.toUInt64
      arena := capturedArena.utf8ByteSize.toUInt64
      declarations := capturedDeclarations.utf8ByteSize.toUInt64 }
  state := state.check "completed raw spool validates totals, spans and exact cursor" <|
    match capturedParse with
    | .ok (_, certificate) =>
      match certificate.validate spoolSizes 2 with
      | .ok cursor => cursor == certificate.cursor && Writer.Cursor.ofRaw cursor ==
          { nextName := 7, nextLevel := 3, nextExpr := 2 }
      | .error _ => false
    | .error _ => false
  state := state.check "raw spool validation rejects declaration-count drift" <|
    match capturedParse with
    | .ok (_, certificate) => isExceptError (certificate.validate spoolSizes 1)
    | .error _ => false
  state := state.check "raw spool validation rejects file-total drift" <|
    match capturedParse with
    | .ok (_, certificate) =>
      isExceptError <| certificate.validate
        { spoolSizes with declarations := spoolSizes.declarations + 1 } 2
    | .error _ => false
  state := state.check "raw spool validation rejects span endpoint drift" <|
    match capturedParse with
    | .ok (_, certificate) =>
      let malformedSpans := certificate.declarations.set! 1
        { certificate.declarations[1]! with offset := 0 }
      let malformedCertificate := { certificate with declarations := malformedSpans }
      isExceptError (malformedCertificate.validate spoolSizes 2)
    | .error _ => false
  state := state.check "ordinary and captured streaming parses are identical" <|
    match capturedParse, (← parseHandleAt rawCanonicalPath) with
    | .ok (capturedExport, _), .ok ordinary =>
      capturedExport.metaLine == ordinary.metaLine && capturedExport.decls == ordinary.decls &&
        capturedExport.projNodes.isEmpty && ordinary.projNodes.isEmpty
    | _, _ => false
  let discardedParse ← discardingCertificateAt rawCanonicalPath
  state := state.check "declaration-discarding parser shares the exact canonical parse" <|
    match capturedParse, discardedParse with
    | .ok (retained, retainedCertificate), .ok (envelope, certificate, callbacks) =>
      envelope.metaLine == retained.metaLine && envelope.projNodes.isEmpty &&
        envelope.declarationCount == retained.decls.size &&
        envelope.retainedDeclarations == 0 && callbacks == retained.decls.size &&
        certificate == retainedCertificate
    | _, _ => false
  let duplicateInput := rawCanonical ++ rawFirstDecl
  IO.FS.writeFile parserCompatibilityPath duplicateInput
  let retainedDuplicate ← rawCertificateAt parserCompatibilityPath
  let discardedDuplicate ← discardingCertificateAt parserCompatibilityPath
  state := state.check "discarding parser preserves delayed duplicate diagnostics" <|
    match retainedDuplicate, discardedDuplicate with
    | .error retained, .error discarded =>
      retained == discarded && retained == "duplicate declaration Island.A"
    | _, _ => false
  let duplicateThenSyntaxError := duplicateInput ++ "{\n"
  IO.FS.writeFile parserCompatibilityPath duplicateThenSyntaxError
  let retainedSyntax ← rawCertificateAt parserCompatibilityPath
  let discardedSyntax ← discardingCertificateAt parserCompatibilityPath
  state := state.check "later syntax error retains precedence over an earlier duplicate" <|
    match retainedSyntax, discardedSyntax with
    | .error retained, .error discarded =>
      retained == discarded && retained != "duplicate declaration Island.A"
    | _, _ => false
  IO.FS.writeFile parserCompatibilityPath duplicateInput
  let retainedAllowed ← IO.FS.withFile parserCompatibilityPath .read fun handle =>
    parseHandleWithSink handle { emit := fun _ => pure () }
      (analyse := false) (allowDuplicateNames := true)
  let discardedAllowed ← discardingCertificateAt parserCompatibilityPath true
  state := state.check "permitted duplicates preserve certificate and callback cardinality" <|
    match retainedAllowed, discardedAllowed with
    | .ok (retained, retainedCertificate), .ok (envelope, certificate, callbacks) =>
      envelope.declarationCount == retained.decls.size &&
        envelope.retainedDeclarations == 0 && callbacks == retained.decls.size &&
        certificate == retainedCertificate
    | _, _ => false
  state := state.check "raw spool files are removed after success" <|
    (← capturedPaths.allM fun path => return !(← path.pathExists))

  -- Starting the second independent writer at the old cursor reuses arena
  -- IDs. The parser must reject that rather than silently binding the later
  -- declaration to the earlier island's nodes.
  let (_, wrongSplit) := (Writer.fromCursor {}).splitDecl second
  let malformed := lines (firstSplit.arena ++ wrongSplit.arena) ++
    firstSplit.declaration ++ "\n" ++ wrongSplit.declaration ++ "\n"
  IO.FS.writeFile malformedPath malformed
  let malformedText ← IO.FS.readFile malformedPath
  state := state.check "overlapping island offsets fail closed at composition" <|
    match wrongSplit.validateStart firstSplit.after with
    | .error _ => true
    | .ok _ => false
  state := state.check "an unchecked overlapping spool does not roundtrip" <|
    match InductiveModels.parse malformedText (analyse := false) with
    | .error _ => true
    | .ok output => output.decls != #[first, second]

  -- Sparse and out-of-order IDs are part of the arena format, but an ID which
  -- has never been written is not an implicit default value.  Exercise every
  -- table through both parser front ends.
  let nameHole := lines #[
    "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"DefinedName\"}}",
    "{\"il\":1,\"param\":1}"]
  IO.FS.writeFile nameHolePath nameHole
  state := state.check "name references into sparse holes fail closed" <|
    bothReject (InductiveModels.parse nameHole) (← parseHandleAt nameHolePath)

  let levelHole := lines #[
    "{\"il\":2,\"succ\":0}",
    "{\"ie\":0,\"sort\":1}"]
  IO.FS.writeFile levelHolePath levelHole
  state := state.check "level references into sparse holes fail closed" <|
    bothReject (InductiveModels.parse levelHole) (← parseHandleAt levelHolePath)

  let exprHole := lines #[
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"HoleExprOwner\"}}",
    "{\"ie\":2,\"sort\":0}",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":1}}"]
  IO.FS.writeFile exprHolePath exprHole
  state := state.check "expression references into sparse holes fail closed" <|
    bothReject (InductiveModels.parse exprHole) (← parseHandleAt exprHolePath)

  -- A very large explicit ID must remain valid without allocating every gap.
  let sparse := lines #[
    "{\"in\":1000000000,\"str\":{\"pre\":0,\"str\":\"SparseOwner\"}}",
    "{\"il\":1000000000,\"param\":1000000000}",
    "{\"ie\":1000000000,\"sort\":1000000000}",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1000000000,\"type\":1000000000}}"]
  IO.FS.writeFile sparsePath sparse
  let sparseDecl : EDecl := .ax `SparseOwner [] (.sort (.param `SparseOwner)) false
  state := state.check "large sparse IDs remain exact and bounded" <|
    bothHaveDecls (InductiveModels.parse sparse) (← parseHandleAt sparsePath) #[sparseDecl]

  -- The arena parser used by the Kernel Arena gives the latest explicit value
  -- to a repeated ID.  Preserve that behavior independently for all tables.
  let overwrite := lines #[
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Before\"}}",
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"After\"}}",
    "{\"il\":1,\"succ\":0}",
    "{\"il\":1,\"param\":1}",
    "{\"ie\":0,\"sort\":0}",
    "{\"ie\":0,\"sort\":1}",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}"]
  IO.FS.writeFile overwritePath overwrite
  let overwrittenDecl : EDecl := .ax `After [] (.sort (.param `After)) false
  state := state.check "explicit repeated arena IDs overwrite in both readers" <|
    bothHaveDecls (InductiveModels.parse overwrite) (← parseHandleAt overwritePath) #[overwrittenDecl]

  -- Parser compatibility is wider than the raw-hoist contract.  Each axis is
  -- certified independently and any gap, reorder, or overwrite selects the
  -- existing full re-interning path.
  let rawNameGap := lines #[
    "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"NameGap\"}}",
    "{\"il\":1,\"param\":2}",
    "{\"ie\":0,\"sort\":1}",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":2,\"type\":0}}"]
  let rawLevelGap := lines #[
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"LevelGap\"}}",
    "{\"il\":2,\"param\":1}",
    "{\"ie\":0,\"sort\":2}",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}"]
  let rawExprGap := lines #[
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"ExprGap\"}}",
    "{\"il\":1,\"param\":1}",
    "{\"ie\":2,\"sort\":1}",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":2}}"]
  let rawNameOrder := lines #[
    "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"NameTwo\"}}",
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"NameOne\"}}",
    "{\"il\":1,\"param\":2}",
    "{\"ie\":0,\"sort\":1}",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":2,\"type\":0}}"]
  state := state.check "raw certification rejects a name-ID gap"
    (← rawFastPathRejected rawNameGapPath rawNameGap)
  state := state.check "raw certification rejects a level-ID gap"
    (← rawFastPathRejected rawLevelGapPath rawLevelGap)
  state := state.check "raw certification rejects an expression-ID gap"
    (← rawFastPathRejected rawExprGapPath rawExprGap)
  state := state.check "raw certification rejects out-of-order IDs"
    (← rawFastPathRejected rawNameOrderPath rawNameOrder)
  state := state.check "raw certification rejects sparse high IDs"
    (← rawFastPathRejected sparsePath sparse)
  state := state.check "raw certification rejects arena overwrites"
    (← rawFastPathRejected overwritePath overwrite)
  let interleavedOverwrite := lines #[
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Before\"}}",
    "{\"ie\":0,\"sort\":0}",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}",
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"After\"}}",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}"]
  state := state.check "planned source rejects interleaved arena snapshots" <|
    ← plannedSourceRejected scratch parserCompatibilityPath interleavedOverwrite

  let rawNoLf := (rawCanonical.dropEnd 1).toString
  let rawWhitespace := " " ++ rawCanonical
  let rawBlank := "\n" ++ rawCanonical
  let rawCrlf := rawCanonical.replace "\n" "\r\n"
  state := state.check "raw certification requires a final LF"
    (← rawFastPathRejected rawNoLfPath rawNoLf)
  state := state.check "raw certification requires canonical JSON spelling"
    (← rawFastPathRejected rawWhitespacePath rawWhitespace)
  state := state.check "raw certification rejects blank records"
    (← rawFastPathRejected rawBlankPath rawBlank)
  state := state.check "raw certification rejects CRLF records"
    (← rawFastPathRejected rawCrlfPath rawCrlf)
  state := state.check "planned source falls back for missing final LF" <|
    ← plannedSourceRejected scratch rawNoLfPath rawNoLf
  state := state.check "planned source falls back for CRLF input" <|
    ← plannedSourceRejected scratch rawCrlfPath rawCrlf
  state := state.check "declaration-discarding planned source preserves raw-certificate fallback" <|
    ← plannedDiscardingSourceRejected scratch rawWhitespacePath rawWhitespace
  let rawAlternateKeyOrder := lines #[
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"KeyOrderA\"}}",
    "{\"in\":2,\"str\":{\"pre\":0,\"str\":\"KeyOrderB\"}}",
    "{\"const\":{\"name\":2,\"us\":[]},\"ie\":0}",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}"]
  state := state.check "raw certification is independent of compressed object key order" <|
    ← rawFastPathAccepted rawKeyOrderPath rawAlternateKeyOrder

  let exceptionPathsRef ← IO.mkRef (none : Option (Array System.FilePath))
  let cleanupAfterException ← try
      Spool.withWorkspace scratch fun workspace => do
        let tee ← Spool.ParseTee.create workspace
        exceptionPathsRef.set (some #[tee.metadata.path, tee.arena.path, tee.declarations.path])
        throw <| IO.userError "intentional raw spool failure"
      pure false
    catch _ =>
      match ← exceptionPathsRef.get with
      | none => pure false
      | some paths =>
        paths.allM fun path => return !(← path.pathExists)
  state := state.check "raw spool files are removed after exceptions" cleanupAfterException
  let partialDirectoryRef ← IO.mkRef (none : Option System.FilePath)
  let partialOpenCleaned ← try
      Spool.withWorkspace scratch fun workspace => do
        partialDirectoryRef.set (some workspace.directory)
        discard <| workspace.createFile "exclusive.ndjson"
        discard <| workspace.createFile "exclusive.ndjson"
      pure false
    catch _ =>
      match ← partialDirectoryRef.get with
      | some directory => pure !(← directory.pathExists)
      | none => pure false
  state := state.check "raw spool cleans a partial exclusive-open failure" partialOpenCleaned

  -- Two live actions must never share a directory. Promises hold both actions
  -- open until each has observed the other's reserved path.
  let firstReady ← IO.Promise.new (α := System.FilePath)
  let secondReady ← IO.Promise.new (α := System.FilePath)
  let firstTask ← IO.asTask (prio := Task.Priority.dedicated) <|
      Spool.withWorkspace scratch fun workspace => do
    firstReady.resolve workspace.directory
    return (secondReady.result?.get).getD default
  let secondTask ← IO.asTask (prio := Task.Priority.dedicated) <|
      Spool.withWorkspace scratch fun workspace => do
    secondReady.resolve workspace.directory
    return (firstReady.result?.get).getD default
  let concurrentDistinct := match firstTask.get, secondTask.get with
    | .ok pathSeenByFirst, .ok pathSeenBySecond => pathSeenByFirst != pathSeenBySecond
    | _, _ => false
  state := state.check "concurrent raw spools reserve distinct directories" concurrentDistinct

  -- If cleanup itself fails, retain the primary action exception. The extra
  -- leaf deliberately keeps the directory nonempty; the test then removes it
  -- explicitly rather than asking production cleanup to recurse.
  let cleanupFailureDirectory ← IO.mkRef (none : Option System.FilePath)
  let primaryPreserved ← try
      Spool.withWorkspace scratch fun workspace => do
        cleanupFailureDirectory.set (some workspace.directory)
        IO.FS.writeFile (workspace.directory / "unexpected-sentinel") "keep"
        throw <| IO.userError "primary-spool-error"
      pure false
    catch error => pure ((toString error).contains "primary-spool-error")
  if let some directory ← cleanupFailureDirectory.get then
    let unexpected := directory / "unexpected-sentinel"
    if ← unexpected.pathExists then IO.FS.removeFile unexpected
    if ← directory.pathExists then IO.FS.removeDir directory
  state := state.check "cleanup failures do not mask the primary exception" primaryPreserved

  IO.FS.writeFile rawRootSentinel "do-not-delete"
  Spool.withWorkspace scratch fun _ => pure ()
  state := state.check "raw spool cleanup preserves existing scratch contents" <|
    (← IO.FS.readFile rawRootSentinel) == "do-not-delete"
  let missingRoot := s!"{scratch}/raw-spool-missing-root"
  if ← System.FilePath.pathExists missingRoot then IO.FS.removeDirAll missingRoot
  let missingRootRefused ← try
      Spool.withWorkspace missingRoot fun _ => pure false
    catch _ => pure true
  state := state.check "raw spool refuses a missing scratch root without creating it" <|
    missingRootRefused && !(← System.FilePath.pathExists missingRoot)
  let wrongNamedRoot := s!"{root}/raw-spool-not-project-tmp"
  IO.FS.createDirAll wrongNamedRoot
  let wrongNamedRefused ← try
      Spool.withWorkspace wrongNamedRoot fun _ => pure false
    catch _ => pure true
  state := state.check "raw spool refuses arbitrary writable roots" wrongNamedRefused
  IO.FS.removeDir wrongNamedRoot

  -- Projection analysis follows record dependencies, not numeric ID order.
  let projectionOrder := lines #[
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"ProjectionOwner\"}}",
    "{\"ie\":10,\"bvar\":0}",
    "{\"ie\":20,\"proj\":{\"idx\":0,\"struct\":10,\"typeName\":1}}",
    "{\"ie\":2,\"app\":{\"arg\":10,\"fn\":20}}"]
  IO.FS.writeFile projectionOrderPath projectionOrder
  let struct := Expr.bvar 0
  let projection := Expr.proj `ProjectionOwner 0 struct
  let projectionParent := Expr.app projection struct
  state := state.check "projection analysis accepts out-of-order numeric IDs" <|
    bothProjectionFacts (InductiveModels.parse projectionOrder) (← parseHandleAt projectionOrderPath)
      #[projection, projectionParent] #[]

  -- A parent captures the child expression present when its record is parsed.
  -- Overwriting that child ID changes only subsequent parents.
  let projectionOverwrite := lines #[
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"ProjectionOwner\"}}",
    "{\"ie\":10,\"bvar\":0}",
    "{\"ie\":0,\"proj\":{\"idx\":0,\"struct\":10,\"typeName\":1}}",
    "{\"ie\":1,\"app\":{\"arg\":10,\"fn\":0}}",
    "{\"ie\":0,\"sort\":0}",
    "{\"ie\":2,\"app\":{\"arg\":0,\"fn\":0}}"]
  IO.FS.writeFile projectionOverwritePath projectionOverwrite
  let replacement := Expr.sort .zero
  let replacementParent := Expr.app replacement replacement
  state := state.check "projection analysis observes expression overwrite time" <|
    bothProjectionFacts (InductiveModels.parse projectionOverwrite)
      (← parseHandleAt projectionOverwritePath) #[projection, projectionParent]
      #[replacement, replacementParent]

  -- Top-level dispatch follows the Kernel Arena parser's complete-key match.
  -- Pin every recognized record spelling: no variant may silently accept an
  -- extra tag or an arbitrary extension field.
  let taggedRecords : Array String := #[
    "{\"extra\":null,\"in\":1,\"str\":{\"pre\":0,\"str\":\"N\"}}",
    "{\"extra\":null,\"in\":1,\"num\":{\"i\":1,\"pre\":0}}",
    "{\"extra\":null,\"il\":1,\"succ\":0}",
    "{\"extra\":null,\"il\":1,\"param\":0}",
    "{\"extra\":null,\"il\":1,\"max\":[0,0]}",
    "{\"extra\":null,\"il\":1,\"imax\":[0,0]}",
    "{\"bvar\":0,\"extra\":null,\"ie\":0}",
    "{\"extra\":null,\"ie\":0,\"sort\":0}",
    "{\"const\":{\"name\":0,\"us\":[]},\"extra\":null,\"ie\":0}",
    "{\"app\":{\"arg\":0,\"fn\":0},\"extra\":null,\"ie\":0}",
    "{\"extra\":null,\"ie\":0,\"lam\":{\"binderInfo\":\"default\",\"body\":0,\"name\":0,\"type\":0}}",
    "{\"extra\":null,\"forallE\":{\"binderInfo\":\"default\",\"body\":0,\"name\":0,\"type\":0},\"ie\":0}",
    "{\"extra\":null,\"ie\":0,\"letE\":{\"body\":0,\"name\":0,\"nondep\":false,\"type\":0,\"value\":0}}",
    "{\"extra\":null,\"ie\":0,\"proj\":{\"idx\":0,\"struct\":0,\"typeName\":0}}",
    "{\"extra\":null,\"ie\":0,\"natVal\":\"0\"}",
    "{\"extra\":null,\"ie\":0,\"strVal\":\"s\"}",
    "{\"extra\":null,\"ie\":0,\"mdata\":{\"data\":{},\"expr\":0}}",
    "{\"axiom\":{},\"extra\":null}",
    "{\"def\":{},\"extra\":null}",
    "{\"extra\":null,\"thm\":{}}",
    "{\"extra\":null,\"opaque\":{}}",
    "{\"extra\":null,\"quot\":{}}",
    "{\"extra\":null,\"inductive\":{}}"]
  for (record, index) in taggedRecords.toList.zipIdx do
    let input := record ++ "\n"
    IO.FS.writeFile parserCompatibilityPath input
    state := state.check s!"top-level record variant {index} rejects extra keys" <|
      bothReject (InductiveModels.parse input) (← parseHandleAt parserCompatibilityPath)

  let malformedPayloads : Array (String × String) := #[
    ("combined expression tags", "{\"bvar\":0,\"ie\":0,\"sort\":0}\n"),
    ("short max level", "{\"il\":1,\"max\":[0]}\n"),
    ("long imax level", "{\"il\":1,\"imax\":[0,0,0]}\n"),
    ("nonnumeric natural literal", "{\"ie\":0,\"natVal\":\"12x\"}\n"),
    ("nonobject metadata", "{\"ie\":0,\"mdata\":{\"data\":false,\"expr\":0}}\n")]
  for (label, input) in malformedPayloads do
    IO.FS.writeFile parserCompatibilityPath input
    state := state.check s!"{label} fails cleanly in both readers" <|
      bothReject (InductiveModels.parse input) (← parseHandleAt parserCompatibilityPath)

  let metadata := lines #[
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"MetadataOwner\"}}",
    "{\"ie\":0,\"sort\":0}",
    "{\"ie\":1,\"mdata\":{\"data\":{\"synthetic\":true},\"expr\":0}}",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":1}}"]
  IO.FS.writeFile parserCompatibilityPath metadata
  let metadataDecl : EDecl := .ax `MetadataOwner [] (.mdata {} (.sort .zero)) false
  state := state.check "metadata expressions parse in both readers" <|
    bothHaveDecls (InductiveModels.parse metadata) (← parseHandleAt parserCompatibilityPath)
      #[metadataDecl]
  state := state.check "raw certification rejects metadata expressions"
    (← rawFastPathRejected parserCompatibilityPath metadata)

  let legacyOpaque := lines #[
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"LegacyOpaque\"}}",
    "{\"ie\":0,\"sort\":0}",
    "{\"opaque\":{\"all\":[],\"levelParams\":[],\"name\":1,\"type\":0,\"value\":0}}"]
  IO.FS.writeFile parserCompatibilityPath legacyOpaque
  let legacyOpaqueDecl : EDecl := .opaq `LegacyOpaque [] (.sort .zero) (.sort .zero) false []
  state := state.check "opaque records may omit isUnsafe for arena compatibility" <|
    bothHaveDecls (InductiveModels.parse legacyOpaque) (← parseHandleAt parserCompatibilityPath)
      #[legacyOpaqueDecl]

  for path in paths do removeIfPresent path
  IO.println s!"source spool: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1
