import Modelgen.Check
import Std.Data.TreeSet.Basic
import Lean.Util.PtrSet

/-!
# Stable record-level dependency ordering

An export declaration record is the smallest unit this pass moves.  In
particular, an inductive record may introduce a whole mutual block together
with all of its constructors and recursors; splitting that record would no
longer describe the export format.

The graph contains two kinds of edges:

* every name used by record `consumer` and introduced by record `provider`
  contributes `provider → consumer`; and
* every record in a public model family discovered by
  [`Modelgen.Check.discover`] contributes `model → owner`.

The first kind is deliberately exhaustive.  Besides constants in expressions,
it includes `Expr.proj.typeName` and the direct name fields in inductive,
constructor, recursor, and rule records.  Level-parameter and binder names are
binding occurrences, not declaration references.

Kahn's algorithm chooses the least original record index whenever several
nodes are ready.  Thus the result is deterministic and retains input order as
its tie-breaker.  A contradictory backreference is reported rather than
silently emitting a dependency-invalid export.
-/

open Lean

namespace Modelgen.Order

/-- Why a record ordering could not be constructed. -/
inductive Error where
  /-- Two atomic records claim to introduce the same declaration name. -/
  | duplicateName (name : Name) (first second : Nat)
  /-- One cyclic strongly connected component, with each record's declarations. -/
  | cycle (records : Array Nat) (declarations : Array (Array Name))
  deriving Repr, BEq

/-! ## Value-free declaration summaries

The final ordering pass needs declaration *identity* and dependency metadata,
not declaration bodies.  Keep that distinction explicit: a summary contains
no `Expr`, so retaining summaries after an island has been serialized cannot
retain the island's expression graph accidentally.

`modelSlots` stores the exact public names expected by an owner and
`modelBefore` stores already-witnessed source-owner roots rather than array
indices.  Besides surviving a reorder, these are the useful incremental
representation: owner expectations are observed while the owner value is
live; later serialized records can be related using names alone. -/

/-- Where a declaration came from.  Island numbers are diagnostic provenance;
they do not affect dependency ordering. -/
inductive SummaryOrigin where
  | source
  | island (number : Nat)
  deriving Inhabited, Repr, BEq

/-- The compact information needed by record ordering and its diagnostics.

`introduced` and `referenced` carry names only. `owner` marks an inductive
owner root, `support` marks the dependency-closed preferred source class, and
`modelSlots` records the exact public interface an owner would recognize, and
`modelBefore` records the owners whose interface this record contributes to. -/
structure DeclSummary where
  ordinal : Nat
  introduced : Array Name
  referenced : Std.HashSet Name
  origin : SummaryOrigin := .source
  owner : Option Name := none
  support : Bool := false
  modelSlots : Array Name := #[]
  modelBefore : Array Name := #[]
  deriving Inhabited, Repr

namespace ExprReferences

/- `Expr.foldConsts` has exactly the pointer-visited traversal wanted here but
   intentionally ignores `Expr.proj.typeName`.  Keep the same implementation
   shape and count a projection's type name as a used declaration too. -/
unsafe structure State where
  visited : PtrSet Expr := mkPtrSet
  names : Std.HashSet Name := {}

unsafe abbrev M := StateM State

unsafe def visit (e : Expr) : M Unit := do
  if (← get).visited.contains e then return
  modify fun state => { state with visited := state.visited.insert e }
  match e with
  | .const name _ => modify fun state => { state with names := state.names.insert name }
  | .proj typeName _ struct =>
    modify fun state => { state with names := state.names.insert typeName }
    visit struct
  | .app fn arg => visit fn; visit arg
  | .lam _ type body _ | .forallE _ type body _ => visit type; visit body
  | .letE _ type value body _ => visit type; visit value; visit body
  | .mdata _ body => visit body
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => pure ()

unsafe def collectUnsafe (roots : Array Expr) : Std.HashSet Name :=
  ((roots.forM visit).run {}).2.names

end ExprReferences

/-- All declaration names referred to by a record.

Declaration-name fields and level-parameter names are introductions and
binders, not references.  Reference fields may still point back into the same
atomic record; graph construction deliberately ignores those self-edges. -/
@[implemented_by ExprReferences.collectUnsafe]
opaque expressionReferences (roots : Array Expr) : Std.HashSet Name := {}

private def insertNames (set : Std.HashSet Name) (names : List Name) : Std.HashSet Name :=
  names.foldl (fun set name => set.insert name) set

/-- Every direct name reference and expression root in one export record. -/
def references (declaration : EDecl) : Std.HashSet Name := Id.run do
  let mut names : Std.HashSet Name := {}
  let mut roots : Array Expr := #[]
  match declaration with
  | .ax _ _ type _ => roots := roots.push type
  | .defn _ _ type value _ _ all | .thm _ _ type value all =>
    names := insertNames names all
    roots := roots.push type |>.push value
  | .opaq _ _ type value _ all =>
    names := insertNames names all
    roots := roots.push type |>.push value
  | .quot _ _ type _ => roots := roots.push type
  | .induct types ctors recursors =>
    for type in types do
      names := insertNames (insertNames names type.all) type.ctors
      roots := roots.push type.type
    for ctor in ctors do
      names := names.insert ctor.induct
      roots := roots.push ctor.type
    for recursor in recursors do
      names := insertNames names recursor.all
      roots := roots.push recursor.type
      for rule in recursor.rules do
        names := names.insert rule.ctor
        roots := roots.push rule.rhs
  for name in expressionReferences roots do names := names.insert name
  return names

/-- Resolve public model→owner relations from retained names only.

This operation is linear in the introduced/expected name count.  It is what
makes composition genuinely incremental: source-owner expectations may be
summarized before any generated island exists, and island declarations may be
matched after their values have been serialized and released. -/
def resolveModelEdges (summaries : Array DeclSummary) : Array DeclSummary := Id.run do
  let mut expected : Std.HashMap Name (Array Name) := {}
  for owner in summaries do
    let some root := owner.owner | continue
    for slot in owner.modelSlots do
      expected := expected.insert slot ((expected.getD slot #[]).push root)
  let mut result := summaries
  for i in [0:summaries.size] do
    let mut summary := summaries[i]!
    for name in summary.introduced do
      for root in expected.getD name #[] do
        unless summary.modelBefore.contains root do
          summary := { summary with modelBefore := summary.modelBefore.push root }
    result := result.set! i summary
  return result

/-- Summarize an export while its declaration values are available.

The public-model edges are computed by the same exact discovery used by the
current ordering pass.  After this function returns, ordering no longer needs
the `Export` or any declaration value. -/
def summaries (x : Export) (prefer : EDecl → Bool := fun _ => false)
    (origin : SummaryOrigin := .source) : Array DeclSummary := Id.run do
  let mut result := x.decls.mapIdx fun ordinal declaration =>
    let owner := match declaration with
      | .induct types _ _ => types.head?.map (·.name)
      | _ => none
    { ordinal
      introduced := declaration.names.toArray
      referenced := references declaration
      origin
      owner
      support := prefer declaration }
  let roots := result.foldl (fun roots summary =>
    match summary.owner with | some owner => roots.insert owner | none => roots) {}
  -- `statementFamiliesFor` retains owners even if no public model slot exists
  -- yet. This is essential for a source summary built before its generated
  -- island: `Check.discover` alone would forget precisely that future edge.
  for family in Check.statementFamiliesFor x roots do
    let summary := result[family.ownerDecl]!
    result := result.set! family.ownerDecl
      { summary with modelSlots := family.correspondence.publicNames }
  return resolveModelEdges result

/-- Re-tag summaries belonging to one disposable model island.  The owner may
itself be generated by a composed construction; its `owner` and `modelBefore`
roles remain orthogonal to provenance. -/
def tagIsland (number : Nat) (summaries : Array DeclSummary) : Array DeclSummary :=
  summaries.map fun summary => { summary with origin := .island number }


private def addEdge (outgoing : Array (Std.HashSet Nat)) (indegree : Array Nat)
    (before after : Nat) : Array (Std.HashSet Nat) × Array Nat :=
  if before == after || outgoing[before]!.contains after then
    (outgoing, indegree)
  else
    (outgoing.set! before (outgoing[before]!.insert after),
      indegree.set! after (indegree[after]! + 1))

/-- Stable topological ordering over compact declaration summaries.

This is intentionally a second implementation while the incremental writer is
being established.  Equivalence tests compare its order and exact errors with
[`recordOrderPrioritizing`] on every fixture; replacing the value-retaining
pass is justified only after that independent oracle is green. -/
def summaryRecordOrderPrioritizing (summaries : Array DeclSummary) :
    Except Error (Array Nat) := do
  let summaries := resolveModelEdges summaries
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
        (outgoing, indegree) := addEdge outgoing indegree provider consumer

  -- Match `Check.discover`'s owner-record order and each family's sorted model
  -- record order exactly. Edge insertion order is normally observationally
  -- irrelevant, but on a malformed graph it determines which concrete cycle
  -- the established diagnostic reports.
  for owner in [0:n] do
    let some ownerName := summaries[owner]!.owner | continue
    for model in [0:n] do
      unless summaries[model]!.modelBefore.contains ownerName do continue
      if outgoing[owner]!.contains model then
        let records := #[owner, model].qsort (· < ·)
        let declarations := records.map fun i => summaries[i]!.introduced
        throw (.cycle records declarations)
      (outgoing, indegree) := addEdge outgoing indegree model owner

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

/-- Ordinary compact ordering, with no preferred support class. -/
def summaryRecordOrder (summaries : Array DeclSummary) : Except Error (Array Nat) :=
  summaryRecordOrderPrioritizing <| summaries.map fun summary =>
    { summary with support := false }

/-- The exact declaration-name sequence selected by a compact order.  This is
the regression surface used for value-free spooling: values are deliberately
unavailable here. -/
def summaryNameOrder (summaries : Array DeclSummary) :
    Except Error (Array (Array Name)) := do
  let order ← summaryRecordOrderPrioritizing summaries
  return order.map fun i => summaries[i]!.introduced

/-- A compact sequence is already the ordinary stable order.  If true, a
second full-export [`reorder`] is provably record-neutral because both passes
run the same stable graph algorithm. -/
def summariesAreOrdered (summaries : Array DeclSummary) : Bool :=
  match summaryRecordOrder summaries with
  | .ok order => order == Array.range summaries.size
  | .error _ => false

/-- The stable topological order of the export's atomic records, optionally
preferring a class of records and its complete dependency closure whenever
both preferred and ordinary nodes are ready. -/
def recordOrderPrioritizing (x : Export) (prefer : EDecl → Bool) :
    Except Error (Array Nat) := do
  let n := x.decls.size
  let mut ownership : Std.HashMap Name Nat := Std.HashMap.emptyWithCapacity (n * 2)
  for i in [0:n] do
    for name in x.decls[i]!.names do
      if let some first := ownership[name]? then
        throw (.duplicateName name first i)
      ownership := ownership.insert name i

  let mut outgoing : Array (Std.HashSet Nat) := Array.replicate n {}
  let mut indegree : Array Nat := Array.replicate n 0
  for consumer in [0:n] do
    for name in references x.decls[consumer]! do
      if let some provider := ownership[name]? then
        (outgoing, indegree) := addEdge outgoing indegree provider consumer

  for family in Check.discover x do
    for model in family.decls do
      -- A genuine generated model never mentions its source owner. If the
      -- ordinary dependency graph already requires `owner → model`, adding
      -- the public `model → owner` constraint would create an immediate
      -- contradiction. Report this pair before running a whole-graph cycle
      -- algorithm; it also distinguishes a leaked owner reference from an
      -- unrelated source declaration which merely has a model-shaped name.
      if outgoing[family.ownerDecl]!.contains model then
        let records := #[family.ownerDecl, model].qsort (· < ·)
        let declarations := records.map fun i => x.decls[i]!.names.toArray
        throw (.cycle records declarations)
      (outgoing, indegree) := addEdge outgoing indegree model family.ownerDecl

  -- A support record is portable only together with its declaration
  -- dependencies.  Prefer that whole predecessor closure, not merely the
  -- named support record, so an unrelated ready owner cannot overtake a later
  -- support prerequisite.
  let mut incoming : Array (Array Nat) := Array.replicate n #[]
  for before in [0:n] do
    for after in outgoing[before]! do
      incoming := incoming.set! after (incoming[after]!.push before)
  let mut preferred : Array Bool := x.decls.map prefer
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
    -- Kahn's residual contains both the cycle and every node blocked behind
    -- it. Every residual node has a residual predecessor. Select one in a
    -- single edge scan, then follow predecessors: finiteness guarantees that
    -- the path enters an actual cycle. This stays linear on a full Mathlib
    -- export, where a generic hash-map Tarjan traversal is itself expensive.
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
        let declarations := records.map fun i => x.decls[i]!.names.toArray
        throw (.cycle records declarations)
      position := position.insert current path.size
      path := path.push current
      let some before := predecessor[current]!
        | throw (.cycle blocked (blocked.map fun i => x.decls[i]!.names.toArray))
      current := before
  return order

/-- The ordinary stable order uses no preferred class. -/
def recordOrder (x : Export) : Except Error (Array Nat) :=
  recordOrderPrioritizing x fun _ => false

/-- Reorder declaration records, preserving export metadata and expression
analysis.  No record content is rewritten. -/
def reorder (x : Export) : Except Error Export := do
  let order ← recordOrder x
  return { x with decls := order.map fun i => x.decls[i]! }

/-- Reorder with one dependency-closed class scheduled as early as possible. -/
def reorderPrioritizing (x : Export) (prefer : EDecl → Bool) : Except Error Export := do
  let order ← recordOrderPrioritizing x prefer
  return { x with decls := order.map fun i => x.decls[i]! }

end Modelgen.Order
