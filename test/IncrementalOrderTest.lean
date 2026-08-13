import Modelgen.Driver
import Modelgen.Order

/-!
# Compact-order equivalence

The prospective incremental writer retains `Order.DeclSummary`, never an
`EDecl`, after a declaration has been serialized.  This test compares the
summary-only graph with the established full-export ordering implementation on
every committed raw and filtered fixture, including exact error diagnostics.
-/

open Lean Modelgen

namespace Modelgen.IncrementalOrder.Tests

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def axDecl (name : Name) (type : Expr := .sort (.succ .zero)) : EDecl :=
  .ax name [] type false

def modelDef (name : Name) (value : Expr := .sort .zero) : EDecl :=
  .defn name [] (.sort (.succ .zero)) value .opaque "safe" []

def inductiveRecord (name : Name) : EDecl :=
  .induct [{
    name, levelParams := [], type := .sort (.succ .zero), all := [name], ctors := []
    numParams := 0, numIndices := 0, numNested := 0, isRec := false
    isReflexive := false, isUnsafe := false }] [] []

def exportOf (decls : Array EDecl) : Export := { metaLine := .null, decls }

def namesAt (x : Export) (order : Array Nat) : Array (Array Name) :=
  order.map fun i => x.decls[i]!.names.toArray

def fullOutcome (x : Export) (prefer : EDecl → Bool := fun _ => false) :
    Except Order.Error (Array (Array Name)) := do
  return namesAt x (← Order.recordOrderPrioritizing x prefer)

def compactOutcome (x : Export) (prefer : EDecl → Bool := fun _ => false) :
    Except Order.Error (Array (Array Name)) :=
  Order.summaryNameOrder (Order.summaries x prefer)

def sameOutcome [BEq α] (left right : Except Order.Error α) : Bool :=
  match left, right with
  | .ok left, .ok right => left == right
  | .error left, .error right => left == right
  | _, _ => false

def outcomesAgree (x : Export) (prefer : EDecl → Bool := fun _ => false) : Bool :=
  sameOutcome (fullOutcome x prefer) (compactOutcome x prefer)

def noGeneration : Cli.Config :=
  { nested := false, mutualModels := false, simple := false, basic := false }

def compactScheduledOutcome (x : Export) (generation : Cli.Config) :
    Except Order.Error (Array (Array Name)) :=
  let reserved := x.decls.foldl (fun names declaration =>
    declaration.names.foldl (·.insert ·) names) {}
  let selected := x.decls.any (scheduledModelOwner generation reserved)
  compactOutcome x fun declaration =>
    selected && scheduledSupportRecord generation declaration

def fullScheduledOutcome (x : Export) (generation : Cli.Config) :
    Except Order.Error (Array (Array Name)) := do
  let scheduled ← scheduleSource x generation
  return scheduled.decls.map fun declaration => declaration.names.toArray

def schedulingAgrees (x : Export) (generation : Cli.Config) : Bool :=
  sameOutcome (fullScheduledOutcome x generation) (compactScheduledOutcome x generation)

def isExactOrder (outcome : Except Order.Error (Array (Array Name)))
    (expected : Array (Array Name)) : Bool :=
  match outcome with
  | .ok order => order == expected
  | .error _ => false

def readExport (path : System.FilePath) : IO Export := do
  let text ← IO.FS.readFile path
  match Modelgen.parse text (analyse := false) with
  | .ok x => return x
  | .error error => throw <| IO.userError s!"cannot parse {path}: {error}"

def fixturePaths (root : String) : IO (Array System.FilePath) := do
  let paths ← System.FilePath.walkDir s!"{root}/test/fixtures"
  return (paths.filter fun path => path.extension == some "ndjson").qsort
    (fun left right => left.toString < right.toString)

def summary (ordinal : Nat) (introduced : Array Name)
    (referenced : Array Name := #[]) (owner : Option Name := none)
    (support := false) (modelSlots : Array Name := #[])
    (modelBefore : Array Name := #[])
    (origin : Order.SummaryOrigin := .source) : Order.DeclSummary :=
  { ordinal, introduced
    referenced := referenced.foldl (fun names name => names.insert name) {}
    owner, support, modelSlots, modelBefore, origin }

def run (root : String) : IO UInt32 := do
  let mut state : TestState := {}
  let configs : Array (String × Cli.Config) := #[
    ("none", noGeneration),
    ("nested-mutual", { noGeneration with nested := true, mutualModels := true }),
    ("simple", { noGeneration with simple := true }),
    ("default", {})]
  let paths ← fixturePaths root
  for path in paths do
    let x ← readExport path
    let label := path.toString
    state := state.check s!"{label}: ordinary name order/error" (outcomesAgree x)
    for (configName, config) in configs do
      state := state.check s!"{label}: {configName} source schedule"
        (schedulingAgrees x config)

  -- Preferred support brings its complete predecessor closure forward, while
  -- retaining the least original ordinal inside both classes.
  let preferred := exportOf #[
    axDecl `Earlier,
    axDecl `Support (.const `SupportDependency []),
    axDecl `Middle,
    axDecl `SupportDependency]
  let prefer := fun declaration => declaration.names.contains `Support
  state := state.check "preferred dependency closure is exactly equivalent"
    (outcomesAgree preferred prefer &&
      isExactOrder (compactOutcome preferred prefer)
        #[#[`SupportDependency], #[`Support], #[`Earlier], #[`Middle]])

  -- Pre-existing public model records exercise the synthetic model→owner
  -- edge in both source positions. The compact relation is captured while
  -- values are live and remains only as owner names afterwards.
  let owner := inductiveRecord `Owner
  let model := modelDef (Naming.modelName `Owner)
  let modelEarly := exportOf #[model, owner]
  let modelLate := exportOf #[owner, model]
  state := state.check "pre-existing early public model stays before owner"
    (outcomesAgree modelEarly && isExactOrder (compactOutcome modelEarly)
      #[#[Naming.modelName `Owner], #[`Owner]])
  state := state.check "pre-existing late public model moves before owner"
    (outcomesAgree modelLate && isExactOrder (compactOutcome modelLate)
      #[#[Naming.modelName `Owner], #[`Owner]])

  let ownerDependent := exportOf #[owner,
    modelDef (Naming.modelName `Owner) (.const `Owner [])]
  state := state.check "owner-dependent model has the exact cycle diagnostic"
    (sameOutcome (fullOutcome ownerDependent) (compactOutcome ownerDependent))
  let duplicate := exportOf #[axDecl `Duplicate, axDecl `Duplicate]
  state := state.check "duplicate ownership has the exact diagnostic"
    (sameOutcome (fullOutcome duplicate) (compactOutcome duplicate))

  -- This is the composition shape produced by source scheduling followed by
  -- one locally ordered generated island. It contains only names and edges:
  -- no declaration value is available to this check. Ordinary stable ordering
  -- is therefore the identity, which makes a final full Export reorder
  -- unnecessary. Moving the public slot after its owner breaks the invariant
  -- and the same compact pass restores it.
  let composed : Array Order.DeclSummary := #[
    summary 0 #[`SupportDependency],
    summary 1 #[`Support] #[`SupportDependency] (support := true),
    summary 2 #[`Earlier],
    summary 3 #[`Owner._model.impl] #[`Support]
      (origin := .island 7),
    summary 4 #[Naming.modelName `Owner] #[`Owner._model.impl]
      (origin := .island 7),
    summary 5 #[`Owner] #[`Support] (owner := some `Owner)
      (modelSlots := #[Naming.modelName `Owner]),
    summary 6 #[`Later] #[`Owner]]
  state := state.check "scheduled source plus ordered island is a final fixed point"
    (Order.summariesAreOrdered composed)
  let misplaced := composed.swap 4 5
  state := state.check "a public slot after its owner is not a fixed point"
    (!Order.summariesAreOrdered misplaced &&
      isExactOrder (Order.summaryNameOrder misplaced) (composed.map (·.introduced)))

  IO.println s!"compact order: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1

end Modelgen.IncrementalOrder.Tests

def main (args : List String) : IO UInt32 :=
  Modelgen.IncrementalOrder.Tests.run (args.head?.getD ".")
