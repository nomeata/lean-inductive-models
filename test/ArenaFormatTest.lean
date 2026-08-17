import InductiveModels.Format

namespace ArenaFormatTest

open Lean InductiveModels

set_option maxRecDepth 4096

/-!
# Focused tests for the export arena format

Both readers — [`InductiveModels.parse`] over a whole string and
[`InductiveModels.parseHandle`] over a chunked stream — must agree on every
record spelling the Kernel Arena accepts, and the writer must produce exactly
what they read back. Run from the repository root with
`lake exe test arenaformat [ROOT]`.
-/

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

def parseHandleAt (path : String) (options : ParseOptions := {}) :
    IO (Except String Export) :=
  IO.FS.withFile path .read fun handle => InductiveModels.parseHandle handle options

/-- Deliberately whole-text oracle for one declaration read against its arena. -/
def referenceDecode (arena declaration : String) : Except String EDecl := do
  let parsed ← InductiveModels.parse (arena ++ declaration)
  let #[result] := parsed.decls | throw "reference declaration did not decode alone"
  return result

def referenceDecodesTo (arena declaration : String) (expected : EDecl) : Bool :=
  match referenceDecode arena declaration with
  | .ok actual => actual == expected
  | .error _ => false

def bothReject (whole streamed : Except String Export) : Bool :=
  match whole, streamed with
  | .error _, .error _ => true
  | _, _ => false

def bothHaveDecls (whole streamed : Except String Export) (expected : Array EDecl) : Bool :=
  match whole, streamed with
  | .ok first, .ok second => first.decls == expected && second.decls == expected
  | _, _ => false

def main (args : List String) : IO UInt32 := do
  let root := args.head?.getD "."
  let scratch := s!"{root}/_tmp"
  IO.FS.createDirAll scratch
  let arenaPath := s!"{scratch}/arena-format-arena.ndjson"
  let firstPath := s!"{scratch}/arena-format-first.ndjson"
  let secondPath := s!"{scratch}/arena-format-second.ndjson"
  let malformedPath := s!"{scratch}/arena-format-malformed.ndjson"
  let nameHolePath := s!"{scratch}/arena-format-name-hole.ndjson"
  let levelHolePath := s!"{scratch}/arena-format-level-hole.ndjson"
  let exprHolePath := s!"{scratch}/arena-format-expr-hole.ndjson"
  let sparsePath := s!"{scratch}/arena-format-sparse.ndjson"
  let overwritePath := s!"{scratch}/arena-format-overwrite.ndjson"
  let compatibilityPath := s!"{scratch}/arena-format-compatibility.ndjson"
  let declarationStreamPath := s!"{scratch}/arena-format-declaration-stream.ndjson"
  let paths := [arenaPath, firstPath, secondPath, malformedPath,
    nameHolePath, levelHolePath, exprHolePath, sparsePath, overwritePath,
    compatibilityPath, declarationStreamPath]
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
  let parsed := InductiveModels.parse reordered

  let mut state : TestState := {}
  state := state.check "split arenas plus reordered declarations parse identically" <|
    match parsed with
    | .ok output => output.decls == #[second, first]
    | .error _ => false
  state := state.check "whole-text declaration oracle preserves exact records" <|
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

  let streamStats ← IO.FS.withFile declarationStreamPath .write fun handle => do
    let stream := IO.FS.Stream.ofHandle handle
    let writer ← DeclarationStreamWriter.start .null stream
    let writer ← writer.writeDeclaration stream first
    let writer ← writer.writeDeclaration stream second
    writer.finish stream
    stream.flush
    return writer
  let streamedText ← IO.FS.readFile declarationStreamPath
  state := state.check "persistent streaming writer remains parse-equivalent" <|
    match InductiveModels.parse streamedText with
    | .ok output => output.decls == #[first, second]
    | .error _ => false
  state := state.check "streaming writer reuses cross-declaration arena IDs exactly" <|
    streamStats.declarationsWritten == 2 && streamStats.maxRecordLines == 6 &&
      streamStats.cursor == sharedSecondSplit.after &&
      streamedText == splitRender &&
      (streamedText.splitOn "\n").length == (splitRender.splitOn "\n").length

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
  state := state.check "an unchecked overlapping arena does not roundtrip" <|
    match InductiveModels.parse malformedText with
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
    bothHaveDecls (InductiveModels.parse overwrite) (← parseHandleAt overwritePath)
      #[overwrittenDecl]

  -- Duplicate declaration names are reported after the complete parse, so a
  -- later syntax or arena error keeps its historical precedence.
  let rawMeta := "{\"meta\":\"arena-format-test\"}\n"
  let rawFirstDecl := firstSplit.declaration ++ "\n"
  let rawSecondDecl := secondSplit.declaration ++ "\n"
  let rawCanonical := rawMeta ++ lines firstSplit.arena ++ rawFirstDecl ++
    lines secondSplit.arena ++ rawSecondDecl
  let duplicateInput := rawCanonical ++ rawFirstDecl
  IO.FS.writeFile compatibilityPath duplicateInput
  state := state.check "a repeated declaration name is rejected after the complete parse" <|
    match InductiveModels.parse duplicateInput, ← parseHandleAt compatibilityPath with
    | .error whole, .error streamed =>
      whole == streamed && whole == "duplicate declaration Island.A"
    | _, _ => false
  let duplicateThenSyntaxError := duplicateInput ++ "{\n"
  IO.FS.writeFile compatibilityPath duplicateThenSyntaxError
  state := state.check "later syntax error retains precedence over an earlier duplicate" <|
    match InductiveModels.parse duplicateThenSyntaxError, ← parseHandleAt compatibilityPath with
    | .error whole, .error streamed =>
      whole == streamed && whole != "duplicate declaration Island.A"
    | _, _ => false
  IO.FS.writeFile compatibilityPath duplicateInput
  state := state.check "permitted duplicates preserve every declaration record" <|
    match ← parseHandleAt compatibilityPath { allowDuplicateNames := true } with
    | .ok permitted => permitted.decls == #[first, second, first]
    | .error _ => false

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
    IO.FS.writeFile compatibilityPath input
    state := state.check s!"top-level record variant {index} rejects extra keys" <|
      bothReject (InductiveModels.parse input) (← parseHandleAt compatibilityPath)

  let malformedPayloads : Array (String × String) := #[
    ("combined expression tags", "{\"bvar\":0,\"ie\":0,\"sort\":0}\n"),
    ("short max level", "{\"il\":1,\"max\":[0]}\n"),
    ("long imax level", "{\"il\":1,\"imax\":[0,0,0]}\n"),
    ("nonnumeric natural literal", "{\"ie\":0,\"natVal\":\"12x\"}\n"),
    ("nonobject metadata", "{\"ie\":0,\"mdata\":{\"data\":false,\"expr\":0}}\n")]
  for (label, input) in malformedPayloads do
    IO.FS.writeFile compatibilityPath input
    state := state.check s!"{label} fails cleanly in both readers" <|
      bothReject (InductiveModels.parse input) (← parseHandleAt compatibilityPath)

  let metadata := lines #[
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"MetadataOwner\"}}",
    "{\"ie\":0,\"sort\":0}",
    "{\"ie\":1,\"mdata\":{\"data\":{\"synthetic\":true},\"expr\":0}}",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":1}}"]
  IO.FS.writeFile compatibilityPath metadata
  let metadataDecl : EDecl := .ax `MetadataOwner [] (.mdata {} (.sort .zero)) false
  state := state.check "metadata expressions parse in both readers" <|
    bothHaveDecls (InductiveModels.parse metadata) (← parseHandleAt compatibilityPath)
      #[metadataDecl]

  let legacyOpaque := lines #[
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"LegacyOpaque\"}}",
    "{\"ie\":0,\"sort\":0}",
    "{\"opaque\":{\"all\":[],\"levelParams\":[],\"name\":1,\"type\":0,\"value\":0}}"]
  IO.FS.writeFile compatibilityPath legacyOpaque
  let legacyOpaqueDecl : EDecl := .opaq `LegacyOpaque [] (.sort .zero) (.sort .zero) false []
  state := state.check "opaque records may omit isUnsafe for arena compatibility" <|
    bothHaveDecls (InductiveModels.parse legacyOpaque) (← parseHandleAt compatibilityPath)
      #[legacyOpaqueDecl]

  for path in paths do removeIfPresent path
  IO.println s!"arena format: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1

end ArenaFormatTest
