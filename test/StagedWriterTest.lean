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

def main (args : List String) : IO UInt32 := do
  let root := args.head?.getD "."
  let scratch := s!"{root}/_tmp"
  IO.FS.createDirAll scratch
  let arenaPath := s!"{scratch}/staged-writer-arena.ndjson"
  let firstPath := s!"{scratch}/staged-writer-first.ndjson"
  let secondPath := s!"{scratch}/staged-writer-second.ndjson"
  let malformedPath := s!"{scratch}/staged-writer-malformed.ndjson"
  let paths := [arenaPath, firstPath, secondPath, malformedPath]
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

  for path in paths do removeIfPresent path
  IO.println s!"staged writer: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1
