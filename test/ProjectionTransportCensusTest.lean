import InductiveModels.Driver

/-!
# The projection-iota transport census, pinned exhaustively

Run from the repository root: `lake exe projectiontransportcensustest [ROOT]`.

Every intrinsic projection rule `T._model.proj_j.iota` is stated as

```
∀ (constructor telescope), @Eq α (T._model.proj_j … (T._model.mk …)) rhs
```

and the goal is that no such **statement** mentions `Eq.rec`.  Today some do,
for two independent reasons, and this file separates them because only one of
them is the generator's doing:

* **`.transport`** — the right-hand side is
  [`InductiveModels.ProjectionField.normalizeProjectionField`]'s nested
  `Eq.rec`, emitted because field `j` transitively depends on an earlier field
  and the owner reaches [`InductiveModels.addProjectionModels`] on none of the
  literal routes (`projectionIotaUsesLiteralField`,
  `propositionProjectionIotaUsesLiteralField`, or a phase-1 one-layer
  certificate).  **This is the set that must shrink to empty.**
* **`.authored`** — the statement mentions `Eq.rec` only in the constructor
  telescope or the projection codomain, i.e. it is source syntax the model is
  required to reproduce exactly.  Generalizing the literal route neither adds
  to nor removes from this set.

The expected table below is the whole committed fixture corpus, not a sample.
A **new** row means a route regressed or a new fixture introduced a
transported projection; a **missing** row means the literal route grew and the
table is stale.  Both fail, and a missing row is the one a human is meant to
delete by hand — the number in the summary line is the progress meter.
-/

set_option maxRecDepth 4096

open Lean Meta InductiveModels

/-- Where an intrinsic projection rule's statement mentions `Eq.rec`. -/
inductive TransportKind where
  /-- In the right-hand side: the generator's canonical dependency transport. -/
  | transport
  /-- Only in the telescope or codomain: exact source syntax. -/
  | authored
  deriving BEq, Repr, Inhabited

def TransportKind.label : TransportKind → String
  | .transport => "transport"
  | .authored => "authored"

/-- One census row: fixture path below `test/fixtures/inductive-models`, owner
type former, zero-based field. -/
structure CensusRow where
  fixture : String
  owner : Name
  field : Nat
  kind : TransportKind
  deriving BEq, Inhabited

def CensusRow.key (row : CensusRow) : String :=
  s!"{row.fixture}\t{row.owner}\t{row.field}\t{row.kind.label}"

/-- **The census, as of the current generator.**  Sorted by `CensusRow.key`.

Every `.transport` row is a projection iota whose right-hand side carries the
canonical `Eq.rec`.  Delete a row only together with the change that removes
its transport; the suite reports which row to delete. -/
def expectedCensus : Array CensusRow :=
  #[ { fixture := "indexed_fibre_boundary", owner := `IndexedRecursiveLayer,
       field := 0, kind := .authored }
   , { fixture := "indexed_fibre_boundary", owner := `IndexedRecursiveLayer,
       field := 1, kind := .authored }
   , { fixture := "indexed_fibre_boundary", owner := `IndexedRecursiveLayer,
       field := 2, kind := .authored }
   , { fixture := "indexed_fibre_boundary", owner := `IndexedRecursiveLayer,
       field := 3, kind := .authored }
   , { fixture := "indexed_fibre_boundary",
       owner := `IndexedRecursiveLayer._model._impl.skel, field := 0, kind := .authored }
   , { fixture := "indexed_fibre_boundary",
       owner := `IndexedRecursiveLayer._model._impl.skel, field := 1, kind := .authored }
   , { fixture := "indexed_fibre_boundary",
       owner := `IndexedRecursiveLayer._model._impl.skel, field := 2, kind := .authored }
   , { fixture := "indexed_fibre_boundary",
       owner := `IndexedRecursiveLayer._model._impl.skel, field := 3, kind := .authored }
   , { fixture := "indexed_fibre_boundary", owner := `TwoRecursiveDependentResults,
       field := 0, kind := .authored }
   , { fixture := "indexed_fibre_boundary", owner := `TwoRecursiveDependentResults,
       field := 1, kind := .authored }
   , { fixture := "indexed_fibre_boundary", owner := `TwoRecursiveDependentResults,
       field := 2, kind := .authored }
   , { fixture := "indexed_fibre_boundary", owner := `TwoRecursiveDependentResults,
       field := 3, kind := .authored }
   , { fixture := "indexed_fibre_boundary", owner := `TwoRecursiveDependentResults,
       field := 4, kind := .authored }
   , { fixture := "indexed_fibre_boundary",
       owner := `TwoRecursiveDependentResults._model._impl.skel, field := 0, kind := .authored }
   , { fixture := "indexed_fibre_boundary",
       owner := `TwoRecursiveDependentResults._model._impl.skel, field := 1, kind := .authored }
   , { fixture := "indexed_fibre_boundary",
       owner := `TwoRecursiveDependentResults._model._impl.skel, field := 2, kind := .authored }
   , { fixture := "indexed_fibre_boundary",
       owner := `TwoRecursiveDependentResults._model._impl.skel, field := 3, kind := .authored }
   , { fixture := "indexed_fibre_boundary",
       owner := `TwoRecursiveDependentResults._model._impl.skel, field := 4, kind := .authored }
   , { fixture := "mutual_one_layer_boundary", owner := `MutualLayerA,
       field := 0, kind := .authored }
   , { fixture := "mutual_one_layer_boundary", owner := `MutualLayerA,
       field := 1, kind := .authored }
   , { fixture := "mutual_one_layer_boundary", owner := `MutualLayerA,
       field := 2, kind := .authored }
   , { fixture := "nested_default_iota", owner := `NestedDefault, field := 2, kind := .transport }
   , { fixture := "nested_value_dependency", owner := `NestedEarly, field := 2, kind := .transport }
   , { fixture := "nested_value_dependency", owner := `NestedLate, field := 1, kind := .transport }
   , { fixture := "nested_one_layer", owner := `NestedLayer, field := 1, kind := .transport }
   , { fixture := "prop_projection_boundaries", owner := `NestedProp,
       field := 1, kind := .transport }
   , { fixture := "prop_recursive_projections", owner := `PropRecIdx,
       field := 0, kind := .authored }
   , { fixture := "prop_recursive_projections", owner := `PropRecIdx,
       field := 1, kind := .authored }
   , { fixture := "prop_recursive_projections", owner := `PropRecIdx,
       field := 2, kind := .authored } ]

/-- Fixtures the maximal generation configuration below cannot run to
completion.  It is empty: `hard_nested_mutual_index`, `indexed_decl`,
`infinitary` and `nest_index_cross` all raised `Unknown constant` for a member
of their own input block, because the shadow derivation opened a raw source
telescope through `MetaM` while that member was deliberately not installed;
every source telescope now has its exact domains installed directly instead.

The list is pinned so that the census above cannot silently stop being
exhaustive: a fixture that starts running must be censused, and a fixture that
stops running must be noticed. -/
def expectedUnrunnable : Array String := #[]

/-- Every generation branch on, so the census sees the maximal set of modeled
owners rather than one suite's slice. -/
def censusGeneration : Cli.Config :=
  { nested := true, mutualModels := true, simple := true, basic := true }

partial def containsEqRec : Expr → Bool
  | .const name _ => name == ``Eq.rec
  | .proj _ _ struct => containsEqRec struct
  | .app fn argument => containsEqRec fn || containsEqRec argument
  | .lam _ type body _ | .forallE _ type body _ => containsEqRec type || containsEqRec body
  | .letE _ type value body _ =>
      containsEqRec type || containsEqRec value || containsEqRec body
  | .mdata _ body => containsEqRec body
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => false

/-- The right-hand side of the outermost equality of a projection rule. -/
partial def ruleRhs? : Expr → Option Expr
  | .forallE _ _ body _ => ruleRhs? body
  | body => body.getAppArgs[2]?

/-- `T._model.proj_j.iota` ⇒ `(T, j)`.  The owner may itself be generated, as
for the erasure skeleton `T._model._impl.skel`. -/
def projectionIotaOwner? (name : Name) : Option (Name × Nat) := do
  let .str projection "iota" := name | none
  let .str model field := projection | none
  let .str owner "_model" := model | none
  let some rest := field.dropPrefix? "proj_" | none
  let some index := rest.toString.toNat? | none
  return (owner, index)

def theoremStatements : EDecl → Array (Name × Expr)
  | .thm name _ type .. => #[(name, type)]
  | _ => #[]

structure FixtureCensus where
  rows : Array CensusRow := #[]
  /-- Every projection iota seen, transported or not. -/
  projectionIotas : Nat := 0
  ran : Bool := true

def censusFixture (fixture path : String) : IO FixtureCensus := do
  let .ok x := parse (← IO.FS.readFile path)
    | throw <| IO.userError s!"cannot parse {path}"
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := path, fileMap := default, maxHeartbeats := 0, maxRecDepth := 8192 }
  let decls? ← try
      let ((decls, _), _) ← Core.CoreM.toIO
        (MetaM.run' (runFilter x false censusGeneration)) context { env }
      pure (some decls)
    catch _ => pure none
  let some decls := decls? | return { ran := false }
  let mut result : FixtureCensus := {}
  for declaration in decls do
    for (name, statement) in theoremStatements declaration do
      let some (owner, field) := projectionIotaOwner? name | continue
      result := { result with projectionIotas := result.projectionIotas + 1 }
      unless containsEqRec statement do continue
      let kind := if (ruleRhs? statement).any containsEqRec then .transport else .authored
      result := { result with rows := result.rows.push { fixture, owner, field, kind } }
  return result

/-- The committed corpus, as (label prefix, directory) pairs.  The filtered
subdirectory repeats several base names of the directory above it, so the
label keeps the subdirectory. -/
def fixtureDirectories : Array (String × String) :=
  #[("", "test/fixtures/inductive-models"),
    ("filtered/", "test/fixtures/inductive-models/filtered")]

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let root := args.head?.getD "."
  let mut paths : Array (String × String) := #[]
  for (prefix_, directory) in fixtureDirectories do
    for entry in ← System.FilePath.readDir s!"{root}/{directory}" do
      if entry.path.extension == some "ndjson" then
        paths := paths.push (prefix_ ++ entry.path.fileStem.getD "", entry.path.toString)
  paths := paths.qsort (fun left right => left.1 < right.1)
  let mut rows : Array CensusRow := #[]
  let mut unrunnable : Array String := #[]
  let mut projectionIotas := 0
  for (fixture, path) in paths do
    let result ← censusFixture fixture path
    rows := rows ++ result.rows
    projectionIotas := projectionIotas + result.projectionIotas
    unless result.ran do unrunnable := unrunnable.push fixture
  rows := rows.qsort (fun left right => left.key < right.key)
  unrunnable := unrunnable.qsort (· < ·)

  let expected := expectedCensus.qsort (fun left right => left.key < right.key)
  let added := rows.filter fun row => !expected.contains row
  let removed := expected.filter fun row => !rows.contains row
  let transported := rows.filter (·.kind == .transport)
  let expectedTransported := expected.filter (·.kind == .transport)

  let mut failures : Array String := #[]
  for row in added do
    failures := failures.push
      s!"NEW {row.kind.label} projection iota {row.owner}._model.proj_{row.field}.iota \
         in {row.fixture}: a route regressed, or add this row to expectedCensus"
  for row in removed do
    failures := failures.push
      s!"GONE {row.kind.label} projection iota {row.owner}._model.proj_{row.field}.iota \
         in {row.fixture}: progress — delete this row from expectedCensus"
  if unrunnable != expectedUnrunnable.qsort (· < ·) then
    failures := failures.push
      s!"unrunnable fixtures are {unrunnable}, expected {expectedUnrunnable}: \
         update expectedUnrunnable"

  IO.println s!"projection iota transport census: \
    {transported.size} transported of {projectionIotas} projection iotas \
    ({rows.size} statements mention Eq.rec, {rows.size - transported.size} of them \
    source-authored) over {paths.size - unrunnable.size} fixtures"
  IO.println s!"  expected transported: {expectedTransported.size}"
  for failure in failures do IO.eprintln s!"FAIL: {failure}"
  return if failures.isEmpty then 0 else 1
