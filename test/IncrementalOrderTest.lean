import InductiveModels.Driver
import InductiveModels.Order

/-!
# Compact-order equivalence

The prospective incremental writer retains `Order.DeclSummary`, never an
`EDecl`, after a declaration has been serialized.  This test compares the
summary-only graph with the established full-export ordering implementation on
every committed raw and filtered fixture, including exact error diagnostics.
-/

open Lean InductiveModels

namespace InductiveModels.IncrementalOrder.Tests

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
  let selected := sourceNeedsSupportScheduling x generation reserved
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
  match InductiveModels.parse text with
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

/-! A deliberately quadratic copy of the pre-index compact graph builder.
It is test-local so the optimized implementation cannot accidentally share
its owner/model indexing mistake with the equivalence oracle. -/

private def referenceAddEdge (outgoing : Array (Std.HashSet Nat)) (indegree : Array Nat)
    (before after : Nat) : Array (Std.HashSet Nat) × Array Nat :=
  if before == after || outgoing[before]!.contains after then
    (outgoing, indegree)
  else
    (outgoing.set! before (outgoing[before]!.insert after),
      indegree.set! after (indegree[after]! + 1))

def quadraticSummaryOrder (input : Array Order.DeclSummary) :
    Except Order.Error (Array Nat) := do
  let summaries := Order.resolveModelEdges input
  let n := summaries.size
  let mut ownership : Std.HashMap Name Nat := Std.HashMap.emptyWithCapacity (n * 2)
  for i in [0:n] do
    for name in summaries[i]!.introduced do
      if let some first := ownership[name]? then
        throw (.duplicateName name first i)
      ownership := ownership.insert name i

  let mut outgoing : Array (Std.HashSet Nat) := Array.replicate n {}
  let mut indegree : Array Nat := Array.replicate n 0
  for consumer in [0:n] do
    for name in summaries[consumer]!.referenced do
      if let some provider := ownership[name]? then
        (outgoing, indegree) := referenceAddEdge outgoing indegree provider consumer

  for owner in [0:n] do
    let some ownerName := summaries[owner]!.owner | continue
    for model in [0:n] do
      unless summaries[model]!.modelBefore.contains ownerName do continue
      if outgoing[owner]!.contains model then
        let records := #[owner, model].qsort (· < ·)
        let declarations := records.map fun i => summaries[i]!.introduced
        throw (.cycle records declarations)
      (outgoing, indegree) := referenceAddEdge outgoing indegree model owner

  let mut incoming : Array (Array Nat) := Array.replicate n #[]
  for before in [0:n] do
    for after in outgoing[before]! do
      incoming := incoming.set! after (incoming[after]!.push before)
  let mut preferred := summaries.map (·.support)
  let mut work := (Array.range n).filter fun i => preferred[i]!
  while !work.isEmpty do
    let node := work.back!
    work := work.pop
    for before in incoming[node]! do
      unless preferred[before]! do
        preferred := preferred.set! before true
        work := work.push before

  let mut readyPreferred : Std.TreeSet Nat := {}
  let mut readyOrdinary : Std.TreeSet Nat := {}
  for i in [0:n] do
    if indegree[i]! == 0 then
      if preferred[i]! then readyPreferred := readyPreferred.insert i
      else readyOrdinary := readyOrdinary.insert i
  let mut order : Array Nat := #[]
  repeat
    match readyPreferred.min? <|> readyOrdinary.min? with
    | none => break
    | some before =>
      if preferred[before]! then readyPreferred := readyPreferred.erase before
      else readyOrdinary := readyOrdinary.erase before
      order := order.push before
      for after in outgoing[before]! do
        let degree := indegree[after]! - 1
        indegree := indegree.set! after degree
        if degree == 0 then
          if preferred[after]! then readyPreferred := readyPreferred.insert after
          else readyOrdinary := readyOrdinary.insert after
  unless order.size == n do
    let blocked := (Array.range n).filter fun i => indegree[i]! > 0
    let mut predecessor : Array (Option Nat) := Array.replicate n none
    for before in blocked do
      for after in outgoing[before]! do
        if indegree[after]! > 0 && predecessor[after]!.isNone then
          predecessor := predecessor.set! after (some before)
    let mut path : Array Nat := #[]
    let mut position : Std.HashMap Nat Nat := {}
    let mut current := blocked[0]!
    repeat
      if let some start := position[current]? then
        let records := (path.extract start path.size).qsort (· < ·)
        let declarations := records.map fun i => summaries[i]!.introduced
        throw (.cycle records declarations)
      position := position.insert current path.size
      path := path.push current
      let some before := predecessor[current]!
        | throw (.cycle blocked (blocked.map fun i => summaries[i]!.introduced))
      current := before
  return order

def compactOrderAgreesWithQuadratic (summaries : Array Order.DeclSummary) : Bool :=
  sameOutcome (quadraticSummaryOrder summaries)
    (Order.summaryRecordOrderPrioritizing summaries)

def isExactIndexOrder (outcome : Except Order.Error (Array Nat))
    (expected : Array Nat) : Bool :=
  match outcome with
  | .ok order => order == expected
  | .error _ => false

def isExactError (outcome : Except Order.Error (Array Nat))
    (expected : Order.Error) : Bool :=
  match outcome with
  | .error error => error == expected
  | .ok _ => false

private def pseudo (seed index salt modulus : Nat) : Nat :=
  if modulus == 0 then 0
  else (seed * 1664525 + index * 1013904223 + salt * 2246822519) % modulus

def randomSummary (seed size index : Nat) : Order.DeclSummary :=
  let introduced := #[Name.mkSimple s!"random_{seed}_{index}"]
  let referenced := (Array.range (pseudo seed index 1 3)).map fun offset =>
    if pseudo seed index (offset + 10) 5 == 0 then
      Name.mkSimple s!"absent_{seed}_{index}_{offset}"
    else
      Name.mkSimple s!"random_{seed}_{pseudo seed index (offset + 20) size}"
  let ownerRoot := Name.mkSimple s!"owner_{pseudo seed index 30 4}"
  let owner := if pseudo seed index 31 4 == 0 then some ownerRoot else none
  let modelBefore := (Array.range (pseudo seed index 32 4)).map fun offset =>
    -- Deliberately repeat roots: the old `.contains` scan treats duplicates as
    -- one relation and the index must do the same.
    Name.mkSimple s!"owner_{pseudo seed index (offset + 40) 4}"
  let modelSlots := (Array.range (pseudo seed index 50 3)).map fun offset =>
    Name.mkSimple s!"random_{seed}_{pseudo seed index (offset + 60) size}"
  summary index introduced referenced owner (pseudo seed index 70 5 == 0)
    modelSlots modelBefore

def randomSummaries (seed : Nat) : Array Order.DeclSummary :=
  let size := pseudo seed 0 80 25
  (Array.range size).map (randomSummary seed size)

def randomDuplicateSummaries (seed : Nat) :
    Array Order.DeclSummary × Name × Nat × Nat :=
  let size := pseudo seed 0 90 23 + 2
  let summaries := (Array.range size).map (randomSummary seed size)
  let first := pseudo seed 0 91 size
  let second := (first + 1 + pseudo seed 0 92 (size - 1)) % size
  let duplicate := summaries[first]!.introduced[0]!
  let summaries := summaries.modify second fun declaration =>
    { declaration with introduced := declaration.introduced.push duplicate }
  (summaries, duplicate, min first second, max first second)

def randomCycleSummaries (seed : Nat) :
    Array Order.DeclSummary × Array Nat × Array (Array Name) :=
  let prefixSize := pseudo seed 0 93 17
  let prelude := (Array.range prefixSize).map fun i =>
    summary i #[Name.mkSimple s!"cycle_prefix_{seed}_{i}"]
  let a := Name.mkSimple s!"cycle_a_{seed}"
  let b := Name.mkSimple s!"cycle_b_{seed}"
  let c := Name.mkSimple s!"cycle_c_{seed}"
  let summaries := prelude ++ #[
    summary prefixSize #[a] #[c],
    summary (prefixSize + 1) #[b] #[a],
    summary (prefixSize + 2) #[c] #[b]]
  (summaries, #[prefixSize, prefixSize + 1, prefixSize + 2], #[#[a], #[b], #[c]])

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

  -- The production implementation indexes sparse model relations. Compare it
  -- with the deliberately quadratic pre-index algorithm, including malformed
  -- summaries where concrete error choice exposes traversal order.
  let multiOwner : Array Order.DeclSummary := #[
    summary 0 #[`OwnerA] (owner := some `OwnerA),
    summary 1 #[`OwnerB] (owner := some `OwnerB),
    summary 2 #[`ModelA] (modelBefore := #[`OwnerA]),
    summary 3 #[`SharedModel] (modelBefore := #[`OwnerA, `OwnerB]),
    summary 4 #[`ModelB] (modelBefore := #[`OwnerB])]
  state := state.check "indexed multiple-owner model insertion is owner-major" <|
    compactOrderAgreesWithQuadratic multiOwner &&
      isExactIndexOrder (Order.summaryRecordOrderPrioritizing multiOwner) #[2, 3, 0, 4, 1]

  let duplicateOwnerMarkers : Array Order.DeclSummary := #[
    summary 0 #[`OwnerMarker0] (owner := some `SharedOwner),
    summary 1 #[`OwnerMarker1] (owner := some `SharedOwner),
    summary 2 #[`SharedOwnerModel]
      (modelBefore := #[`SharedOwner, `SharedOwner])]
  state := state.check "duplicate owner markers and repeated roots preserve old semantics" <|
    compactOrderAgreesWithQuadratic duplicateOwnerMarkers

  let ownerMajorError : Array Order.DeclSummary := #[
    summary 0 #[`OwnerA] (owner := some `OwnerA),
    summary 1 #[`OwnerB] (owner := some `OwnerB),
    summary 2 #[`ModelB] #[`OwnerB] (modelBefore := #[`OwnerB]),
    summary 3 #[`ModelA] #[`OwnerA] (modelBefore := #[`OwnerA])]
  state := state.check "immediate contradiction remains owner-major then model-major" <|
    compactOrderAgreesWithQuadratic ownerMajorError &&
      isExactError (Order.summaryRecordOrderPrioritizing ownerMajorError)
        (.cycle #[0, 3] #[#[`OwnerA], #[`ModelA]])

  let dependencyCycle : Array Order.DeclSummary := #[
    summary 0 #[`CycleA] #[`CycleC],
    summary 1 #[`CycleB] #[`CycleA],
    summary 2 #[`CycleC] #[`CycleB]]
  state := state.check "residual dependency-cycle diagnostic is unchanged" <|
    compactOrderAgreesWithQuadratic dependencyCycle

  let duplicateWithin : Array Order.DeclSummary := #[
    summary 0 #[`First, `First] #[`Cycle],
    summary 1 #[`Cycle] #[`First]]
  let duplicateAcross : Array Order.DeclSummary := #[
    summary 0 #[`First], summary 1 #[`Second, `First]]
  state := state.check "duplicate errors retain priority and exact ordinals" <|
      compactOrderAgreesWithQuadratic duplicateWithin &&
      compactOrderAgreesWithQuadratic duplicateAcross &&
      isExactError (Order.summaryRecordOrderPrioritizing duplicateWithin)
        (.duplicateName `First 0 0) &&
      isExactError (Order.summaryRecordOrderPrioritizing duplicateAcross)
        (.duplicateName `First 0 1)

  state := state.check "random compact graphs match the quadratic reference exactly" <|
    (Array.range 512).all fun seed =>
      compactOrderAgreesWithQuadratic (randomSummaries seed)

  state := state.check "random duplicate diagnostics match exactly" <|
    (Array.range 256).all fun seed =>
      let (summaries, name, first, second) := randomDuplicateSummaries seed
      compactOrderAgreesWithQuadratic summaries &&
        isExactError (Order.summaryRecordOrderPrioritizing summaries)
          (.duplicateName name first second)

  state := state.check "random residual-cycle diagnostics match exactly" <|
    (Array.range 256).all fun seed =>
      let (summaries, records, declarations) := randomCycleSummaries seed
      compactOrderAgreesWithQuadratic summaries &&
        isExactError (Order.summaryRecordOrderPrioritizing summaries)
          (.cycle records declarations)

  -- Repeated updates to one nested bucket are the shape which exposed the
  -- outer-array copy-on-write regression. Keep both the owner/model list and
  -- dependency adjacency accumulators covered by the independent oracle.
  let fanSize := 128
  let fanNames := (Array.range fanSize).map fun i => Name.mkSimple s!"fan_{i}"
  let fanProviders := (Array.range fanSize).map fun i => summary i #[fanNames[i]!]
  let hub := summary fanSize #[`FanHub] fanNames (support := true)
  let fanConsumers := (Array.range fanSize).map fun i =>
    summary (fanSize + 1 + i) #[Name.mkSimple s!"consumer_{i}"] #[`FanHub]
  let sharedOwner := Name.mkSimple "shared_owner"
  let modelBase := fanSize * 2 + 1
  let ownerAndModels := #[summary modelBase #[sharedOwner] (owner := some sharedOwner)] ++
    (Array.range fanSize).map fun i =>
      summary (modelBase + 1 + i) #[Name.mkSimple s!"shared_model_{i}"]
        (modelBefore := #[sharedOwner])
  let repeatedBuckets := fanProviders ++ #[hub] ++ fanConsumers ++ ownerAndModels
  state := state.check "repeated nested-bucket updates match the quadratic reference" <|
    compactOrderAgreesWithQuadratic repeatedBuckets

  IO.println s!"compact order: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1

end InductiveModels.IncrementalOrder.Tests

def main (args : List String) : IO UInt32 :=
  InductiveModels.IncrementalOrder.Tests.run (args.head?.getD ".")
