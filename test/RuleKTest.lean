import Modelgen.Driver
import Modelgen.Check
import Modelgen.Mono

open Lean Meta Modelgen

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (s : TestState) (label : String) (ok : Bool) : TestState :=
  if ok then { s with passed := s.passed + 1 }
  else { s with failed := s.failed.push label }

structure Fixture where
  input : Export
  output : Export
  report : Report

def noGeneration : Cli.Config :=
  { nested := false, mutualModels := false, simple := false, basic := false }

def runFixture (path : String) (generation : Cli.Config) : IO Fixture := do
  let text ← IO.FS.readFile path
  let .ok input := parse text (analyse := false)
    | throw <| IO.userError s!"cannot parse {path}"
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<rule-k-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((decls, report), _) ← Lean.Core.CoreM.toIO
    (Lean.Meta.MetaM.run' (runFilter input false generation)) context { env }
  return { input, output := { input with decls }, report }

def recursors (x : Export) : Array ERec :=
  x.decls.flatMap fun declaration => match declaration with
    | .induct _ _ recursors => recursors.toArray
    | _ => #[]

def hasName (x : Export) (name : Name) : Bool :=
  x.decls.any (·.names.contains name)

def modeledK (fixture : Fixture) : Array ERec :=
  (recursors fixture.input).filter fun recursor =>
    recursor.k && hasName fixture.output (Naming.modelName recursor.name)

def modeledNonK (fixture : Fixture) : Array ERec :=
  (recursors fixture.input).filter fun recursor =>
    !recursor.k && hasName fixture.output (Naming.modelName recursor.name)

def eraseName (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.filter fun declaration => !declaration.names.contains name }

def replaceType (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.map fun declaration => match declaration with
    | .thm n levels _ value all =>
      if n == name then .thm n levels (.sort .zero) value all else declaration
    | _ => declaration }

def literalRuleKViolation (theoremNames : Array Name) : Check.Violation → Bool
  | .missingPublic _ name | .duplicatePublic _ name _ |
      .universeArity _ name _ _ | .declarationType _ name => theoremNames.contains name
  | _ => false

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut state : TestState := {}

  let simple ← runFixture "test/fixtures/lean-inductive-models/prim_shapes.ndjson"
    { noGeneration with simple := true, basic := true }
  let positive := modeledK simple
  let baseViolations := Check.check simple.output
  let theoremNames := positive.map fun recursor => Naming.ruleKName recursor.name
  state := state.check "simple route has modeled K recursors" (!positive.isEmpty)
  state := state.check "indexed K recursors retain the constructor-result fiber"
    (positive.any fun recursor => recursor.numIndices > 0 &&
      hasName simple.output (Naming.ruleKName recursor.name))
  state := state.check "every modeled K recursor has exactly named metadata"
    (positive.all fun recursor => hasName simple.output (Naming.ruleKName recursor.name))
  state := state.check "non-K recursors have no rule-K metadata"
    ((modeledNonK simple).all fun recursor =>
      !hasName simple.output (Naming.ruleKName recursor.name))
  state := state.check "generated rule-K statements pass literal checking"
    (!(baseViolations.any (literalRuleKViolation theoremNames)))

  if let some recursor := positive[0]? then
    let theoremName := Naming.ruleKName recursor.name
    let missing := Check.check (eraseName simple.output theoremName)
    state := state.check "missing rule-K theorem is rejected"
      (missing.contains (.missingPublic recursor.name theoremName))
    let changed := Check.check (replaceType simple.output theoremName)
    state := state.check "mutated rule-K proposition is rejected"
      (changed.contains (.declarationType recursor.name theoremName))
    let mono := Mono.modelTable simple.output
    state := state.check "Mono records the exact rule-K role"
      (mono[theoremName]?.any fun entry => entry.role == .ruleK)

  if let some recursor := (modeledNonK simple)[0]? then
    let theoremName := Naming.ruleKName recursor.name
    let extra : EDecl := .thm theoremName [] (.sort .zero) (.sort .zero) [theoremName]
    let violations := Check.check { simple.output with decls := simple.output.decls.push extra }
    state := state.check "metadata on a non-K recursor is rejected"
      (violations.contains (.extraMetadata recursor.name theoremName .ruleK))

  let mutualFixture ← runFixture "test/fixtures/lean-inductive-models/mutual_prop.ndjson"
    { noGeneration with mutualModels := true }
  state := state.check "mutual route never invents K metadata"
    ((modeledNonK mutualFixture).all fun recursor =>
      !hasName mutualFixture.output (Naming.ruleKName recursor.name))

  let nested ← runFixture "test/fixtures/lean-inductive-models/nested_iota.ndjson"
    { noGeneration with nested := true }
  state := state.check "nested route follows every literal K flag"
    ((modeledK nested).all fun recursor =>
      hasName nested.output (Naming.ruleKName recursor.name))
  state := state.check "nested route omits metadata when K is false"
    ((modeledNonK nested).all fun recursor =>
      !hasName nested.output (Naming.ruleKName recursor.name))

  IO.println s!"rule-K: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1
