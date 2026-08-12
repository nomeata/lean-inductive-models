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

private def addEdge (outgoing : Array (Std.HashSet Nat)) (indegree : Array Nat)
    (before after : Nat) : Array (Std.HashSet Nat) × Array Nat :=
  if before == after || outgoing[before]!.contains after then
    (outgoing, indegree)
  else
    (outgoing.set! before (outgoing[before]!.insert after),
      indegree.set! after (indegree[after]! + 1))

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
