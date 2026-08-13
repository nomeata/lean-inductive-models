import Modelgen.Format

open Lean Modelgen

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
  IO.FS.withFile path .read fun handle => Modelgen.parseHandle handle

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

def main (args : List String) : IO UInt32 := do
  let root := args.head?.getD "."
  let scratch := s!"{root}/_tmp"
  IO.FS.createDirAll scratch
  let arenaPath := s!"{scratch}/staged-writer-arena.ndjson"
  let firstPath := s!"{scratch}/staged-writer-first.ndjson"
  let secondPath := s!"{scratch}/staged-writer-second.ndjson"
  let malformedPath := s!"{scratch}/staged-writer-malformed.ndjson"
  let nameHolePath := s!"{scratch}/staged-writer-name-hole.ndjson"
  let levelHolePath := s!"{scratch}/staged-writer-level-hole.ndjson"
  let exprHolePath := s!"{scratch}/staged-writer-expr-hole.ndjson"
  let sparsePath := s!"{scratch}/staged-writer-sparse.ndjson"
  let overwritePath := s!"{scratch}/staged-writer-overwrite.ndjson"
  let projectionOrderPath := s!"{scratch}/staged-writer-projection-order.ndjson"
  let projectionOverwritePath := s!"{scratch}/staged-writer-projection-overwrite.ndjson"
  let parserCompatibilityPath := s!"{scratch}/staged-writer-parser-compatibility.ndjson"
  let paths := [arenaPath, firstPath, secondPath, malformedPath,
    nameHolePath, levelHolePath, exprHolePath, sparsePath, overwritePath,
    projectionOrderPath, projectionOverwritePath, parserCompatibilityPath]
  for path in paths do removeIfPresent path

  let type := Expr.sort (.param `u)
  let first : EDecl := .ax `Island.A [`u] type false
  let second : EDecl := .ax `Island.B [`u] type false
  let (_, firstSplit) := (Writer.fromCursor {}).splitDecl first
  -- A new island deliberately forgets the first island's structural keys,
  -- but starts after all of its arena IDs.
  let (_, secondSplit) := (Writer.fromCursor firstSplit.after).splitDecl second

  IO.FS.writeFile arenaPath (lines (firstSplit.arena ++ secondSplit.arena))
  IO.FS.writeFile firstPath (firstSplit.declaration ++ "\n")
  IO.FS.writeFile secondPath (secondSplit.declaration ++ "\n")
  let arenaText ← IO.FS.readFile arenaPath
  let firstText ← IO.FS.readFile firstPath
  let secondText ← IO.FS.readFile secondPath
  -- Arena order is fixed; declaration records can be consumed in a different
  -- topological order without changing what their IDs decode to.
  let reordered := arenaText ++ secondText ++ firstText
  let parsed := Modelgen.parse reordered (analyse := false)

  let mut state : TestState := {}
  state := state.check "split arenas plus reordered declarations parse identically" <|
    match parsed with
    | .ok output => output.decls == #[second, first]
    | .error _ => false
  state := state.check "fresh island advances every explicit arena counter" <|
    firstSplit.after == { nextName := 4, nextLevel := 2, nextExpr := 1 } &&
      secondSplit.after == { nextName := 7, nextLevel := 3, nextExpr := 2 }
  state := state.check "cross-island structural duplicates are permitted" <|
    firstSplit.arena.size == 5 && secondSplit.arena.size == 5

  -- Within one island, the ordinary structural maps still share the common
  -- name prefix, level and expression.
  let (within, _) := (Writer.fromCursor {}).splitDecl first
  let (_, sharedSplit) := within.splitDecl second
  state := state.check "one island still hash-conses shared structure" <|
    sharedSplit.arena.size == 1 &&
      sharedSplit.after == { nextName := 5, nextLevel := 2, nextExpr := 1 }

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
    match Modelgen.parse malformedText (analyse := false) with
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
    bothReject (Modelgen.parse nameHole) (← parseHandleAt nameHolePath)

  let levelHole := lines #[
    "{\"il\":2,\"succ\":0}",
    "{\"ie\":0,\"sort\":1}"]
  IO.FS.writeFile levelHolePath levelHole
  state := state.check "level references into sparse holes fail closed" <|
    bothReject (Modelgen.parse levelHole) (← parseHandleAt levelHolePath)

  let exprHole := lines #[
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"HoleExprOwner\"}}",
    "{\"ie\":2,\"sort\":0}",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":1}}"]
  IO.FS.writeFile exprHolePath exprHole
  state := state.check "expression references into sparse holes fail closed" <|
    bothReject (Modelgen.parse exprHole) (← parseHandleAt exprHolePath)

  -- A very large explicit ID must remain valid without allocating every gap.
  let sparse := lines #[
    "{\"in\":1000000000,\"str\":{\"pre\":0,\"str\":\"SparseOwner\"}}",
    "{\"il\":1000000000,\"param\":1000000000}",
    "{\"ie\":1000000000,\"sort\":1000000000}",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1000000000,\"type\":1000000000}}"]
  IO.FS.writeFile sparsePath sparse
  let sparseDecl : EDecl := .ax `SparseOwner [] (.sort (.param `SparseOwner)) false
  state := state.check "large sparse IDs remain exact and bounded" <|
    bothHaveDecls (Modelgen.parse sparse) (← parseHandleAt sparsePath) #[sparseDecl]

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
    bothHaveDecls (Modelgen.parse overwrite) (← parseHandleAt overwritePath) #[overwrittenDecl]

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
    bothProjectionFacts (Modelgen.parse projectionOrder) (← parseHandleAt projectionOrderPath)
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
    bothProjectionFacts (Modelgen.parse projectionOverwrite)
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
      bothReject (Modelgen.parse input) (← parseHandleAt parserCompatibilityPath)

  let malformedPayloads : Array (String × String) := #[
    ("combined expression tags", "{\"bvar\":0,\"ie\":0,\"sort\":0}\n"),
    ("short max level", "{\"il\":1,\"max\":[0]}\n"),
    ("long imax level", "{\"il\":1,\"imax\":[0,0,0]}\n"),
    ("nonnumeric natural literal", "{\"ie\":0,\"natVal\":\"12x\"}\n"),
    ("nonobject metadata", "{\"ie\":0,\"mdata\":{\"data\":false,\"expr\":0}}\n")]
  for (label, input) in malformedPayloads do
    IO.FS.writeFile parserCompatibilityPath input
    state := state.check s!"{label} fails cleanly in both readers" <|
      bothReject (Modelgen.parse input) (← parseHandleAt parserCompatibilityPath)

  let metadata := lines #[
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"MetadataOwner\"}}",
    "{\"ie\":0,\"sort\":0}",
    "{\"ie\":1,\"mdata\":{\"data\":{\"synthetic\":true},\"expr\":0}}",
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":1}}"]
  IO.FS.writeFile parserCompatibilityPath metadata
  let metadataDecl : EDecl := .ax `MetadataOwner [] (.mdata {} (.sort .zero)) false
  state := state.check "metadata expressions parse in both readers" <|
    bothHaveDecls (Modelgen.parse metadata) (← parseHandleAt parserCompatibilityPath)
      #[metadataDecl]

  let legacyOpaque := lines #[
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"LegacyOpaque\"}}",
    "{\"ie\":0,\"sort\":0}",
    "{\"opaque\":{\"all\":[],\"levelParams\":[],\"name\":1,\"type\":0,\"value\":0}}"]
  IO.FS.writeFile parserCompatibilityPath legacyOpaque
  let legacyOpaqueDecl : EDecl := .opaq `LegacyOpaque [] (.sort .zero) (.sort .zero) false []
  state := state.check "opaque records may omit isUnsafe for arena compatibility" <|
    bothHaveDecls (Modelgen.parse legacyOpaque) (← parseHandleAt parserCompatibilityPath)
      #[legacyOpaqueDecl]

  for path in paths do removeIfPresent path
  IO.println s!"staged writer: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1
