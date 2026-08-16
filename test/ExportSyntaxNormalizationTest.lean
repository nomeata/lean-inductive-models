import InductiveModels.Driver
import InductiveModels.Order

/-!
# Exact export-syntax normalization controls

The format-only checker may reproduce the kernel's weak-head observations, but
only from syntax present in the export.  This test pins that boundary directly:
transparent definitions unfold, opaque definitions do not, cycles terminate,
and declaration types remain literal.  It also exercises the two regressions
which motivated the shared normalizer: `SvIx` is proposition-valued through a
transparent former alias and `Flat`'s generated projection iotas contain
β-normalized local binder types.
-/

open Lean Meta InductiveModels

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def declarationType? (x : Export) (name : Name) : Option Expr :=
  x.decls.findSome? fun declaration => match declaration with
    | .ax got _ type _ | .quot got _ type _ => if got == name then some type else none
    | .defn got _ type .. | .thm got _ type .. | .opaq got _ type .. =>
      if got == name then some type else none
    | .induct types constructors recursors =>
      (types.find? (·.name == name)).map (·.type) <|>
      (constructors.find? (·.name == name)).map (·.type) <|>
      (recursors.find? (·.name == name)).map (·.type)

def readExport (path : String) : IO Export := do
  let .ok result := parse (← IO.FS.readFile path)
    | throw <| IO.userError s!"cannot parse {path}"
  return result

def generatedExport (input : Export) : IO (Export × Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<export-syntax-normalization-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((declarations, report), _) ← Core.CoreM.toIO
    (MetaM.run' (runFilter input false {})) context { env }
  match Order.reorder { input with decls := declarations } with
  | .ok output => return (output, report)
  | .error failure =>
    throw <| IO.userError s!"cannot order generated export: {repr failure}"

/-! ## The environment and the export must agree about shape

The bounded normalizer answers every *shape* question the checker asks: what a
former weak-head reduces to, whether it ends in `Prop`, which constructor
fields admit a kernel projection, and hence which public slots a correspondence
table has.  All of it is driven by one table of transparent `defn` bodies.

Those same bodies are also in the installed environment, because the driver
replays every source record through `toDeclaration`, which copies a `.defn`
record's `levelParams` and `value` into `Declaration.defnDecl` verbatim.  So
one fact has two possible sources, and the section below asserts they never
disagree — over every committed fixture, for every declaration in it.

The comparison varies exactly one thing.  Declaration-type and structure tables
stay export-derived on both sides; only the definition source changes, from
`Export.exactNormalizationEnv` to `ExactNormalizationEnv.ofEnvironment`.  A
disagreement is therefore attributable to the environment and the export
disagreeing about a transparent body and to nothing else.

Two exclusions, both principled.  A constant the replay could not install is
compared on neither side: the claim is that the two agree *wherever both are
populated*, and a deliberately malformed fixture has no installed constant to
ask.  And literal statement comparisons are out of scope and must never move
onto the environment — `toDeclaration` discards exported recursors and lets the
kernel mint its own, so recursor types and iota rule right-hand sides differ by
construction.  Only shape and eligibility are asked here. -/

/-- Replay one export into an environment the way the driver does: in stream
order, through `toDeclaration`, keeping whatever installs and passing over
whatever does not. -/
def replayExport (base : Environment) (x : Export) : Environment := Id.run do
  let mut env := base
  for declaration in x.decls do
    if let some kernelDeclaration := toDeclaration env declaration then
      if let .ok next := env.addDeclCore 0 0 kernelDeclaration none false then
        env := next
  return env

/-- Every expression in a record worth weak-head normalizing. -/
def shapeRoots : EDecl → Array (String × Expr)
  | .ax name _ type _ | .quot name _ type _ | .opaq name _ type .. =>
    #[(s!"{name}.type", type)]
  | .thm name _ type value _ | .defn name _ type value .. =>
    #[(s!"{name}.type", type), (s!"{name}.value", value)]
  | .induct types constructors recursors => Id.run do
    let mut roots := #[]
    for type in types do roots := roots.push (s!"{type.name}.type", type.type)
    for constructor in constructors do
      roots := roots.push (s!"{constructor.name}.type", constructor.type)
    for recursor in recursors do
      roots := roots.push (s!"{recursor.name}.type", recursor.type)
    return roots

structure AgreementCount where
  compared : Nat := 0
  /-- Records the replay did not install every name of, and which are
  therefore not compared at all.  Counted rather than passed over silently:
  a replay that stops installing declarations empties `compared` instead of
  disagreeing, and the suite would be green with nothing behind it. -/
  skippedRecords : Nat := 0
  /-- Fixture directories in `fixtureDirectories` that are not directories. -/
  missingDirectories : Nat := 0
  /-- Committed `.ndjson` files that do not parse. -/
  unparsable : Nat := 0
  /-- Fixtures whose generated export the driver declined or could not
  produce, and which are therefore compared once rather than twice. -/
  ungenerated : Nat := 0
  failed : Array String := #[]

def AgreementCount.check (count : AgreementCount) (label : String)
    (condition : Bool) : AgreementCount :=
  { count with
    compared := count.compared + 1,
    failed := if condition then count.failed else count.failed.push label }

def compareExport (count : AgreementCount) (label : String) (x : Export)
    (env : Environment) : AgreementCount := Id.run do
  let exportNormalizer := x.exactNormalizationEnv
  let environmentNormalizer := ExactNormalizationEnv.ofEnvironment env
  let mut count := count
  for declaration in x.decls do
    -- Only ask about a record every one of whose names the replay installed.
    unless declaration.names.all (env.find? · |>.isSome) do
      count := { count with skippedRecords := count.skippedRecords + 1 }
      continue
    for (root, expression) in shapeRoots declaration do
      count := count.check s!"{label}: whnf {root}"
        (exportNormalizer.whnf expression == environmentNormalizer.whnf expression)
      count := count.check s!"{label}: beta {root}"
        (exportNormalizer.beta expression == environmentNormalizer.beta expression)
      count := count.check s!"{label}: isPropositionFormer {root}"
        (exportNormalizer.isPropositionFormer expression ==
          environmentNormalizer.isPropositionFormer expression)
    -- Projection eligibility folds `whnf`, `isPropositionFormer` and
    -- `inferExactSortLevel?` together over the constructor telescope, so it is
    -- the sharpest single shape query available.
    if let .induct types constructors _ := declaration then
      for type in types do
        count := count.check s!"{label}: intrinsicProjectionFields {type.name}"
          (x.intrinsicProjectionFieldsWith exportNormalizer type constructors ==
            x.intrinsicProjectionFieldsWith environmentNormalizer type constructors)
    count := count.check s!"{label}: correspondenceFor? {declaration.names}"
      (Check.correspondenceFor? exportNormalizer
          (x.intrinsicProjectionFieldsWith exportNormalizer) declaration ==
        Check.correspondenceFor? environmentNormalizer
          (x.intrinsicProjectionFieldsWith environmentNormalizer) declaration)
  -- The queries above are the eligibility predicates, but shape analysis is not
  -- only a side channel deciding which slots exist: it also feeds the compared
  -- expression, at the projection-iota binder β-normalization and at the `Eq`
  -- level inferred for a constructor field.  Running the whole checker under
  -- each definition source and comparing its violations reaches both of those,
  -- and every other consumer, in one comparison.
  let index := Check.SyntaxIndex.ofExport x
  let environmentIndex := index.withExactNormalizer environmentNormalizer
  let families := Check.discoverWithIndex x index
  count := count.check s!"{label}: whole-checker violations"
    (Check.checkFamiliesWithIndex x index families true ==
      Check.checkFamiliesWithIndex x environmentIndex families true)
  count := count.check s!"{label}: discovered families"
    (families == Check.discoverWithIndex x environmentIndex)
  return count

/-- Records the replay does not install every name of, over the whole sweep.
`toDeclaration` discards an exported recursor and lets the kernel mint its
own, so a block whose kernel recursor is named differently — nested and mutual
inputs, mostly — has a name the environment never receives and is compared on
neither side.

It is pinned rather than merely printed because the skip is invisible from the
other direction: a replay that stopped installing declarations, or a
`toDeclaration` that stopped producing them, would raise this number and lower
`compared` without a single disagreement to report. -/
def skippedRecordsExpectation : Nat := 182

/-- Fixtures the driver declines or cannot generate from, and which are
therefore compared once rather than twice.  Every committed fixture generates
today. -/
def ungeneratedExpectation : Nat := 0

/-- A floor under the sweep's total comparison count.  The exact number moves
whenever a fixture is added or a shape query gains a root, so it is a floor
rather than a pin; what it excludes is the sweep quietly shrinking towards
nothing while every assertion above it stays green. -/
def comparisonFloor : Nat := 200000

/-- The directories swept, and the number of committed `.ndjson` exports each
one holds.  `test/fixtures/lean4export` holds `compact_interner.args` and no
export; `test/fixtures/mono` is *not a committed directory at all* and is
swept as zero — it was passed over by `unless ← path.isDir` without a word,
which is exactly the shape of skip this table exists to make visible.

Asserting the counts per directory rather than in total means a directory that
moves, empties or disappears fails here instead of quietly making the sweep
below smaller. -/
def fixtureDirectories : Array (String × Nat) :=
  #[("test/fixtures/inductive-models", 75), ("test/fixtures/lean4export", 0),
    ("test/fixtures/mono", 0), ("test/fixtures/rejected", 1)]

/-- Assert environment/export shape agreement over every committed fixture.

Returns the per-directory export count alongside the whole `AgreementCount`,
so that the skips inside this sweep are numbers the caller asserts rather than
`continue`s that reduce the work silently. -/
def environmentAgreement (root : String) :
    IO (Array (String × Nat) × AgreementCount) := do
  let base ← importModules #[] {}
  let mut count : AgreementCount := {}
  let mut perDirectory : Array (String × Nat) := #[]
  for (directory, _) in fixtureDirectories do
    let path : System.FilePath := root / directory
    unless ← path.isDir do
      count := { count with missingDirectories := count.missingDirectories + 1 }
      perDirectory := perDirectory.push (directory, 0)
      continue
    let mut entries := #[]
    for entry in ← path.readDir do
      if entry.path.extension == some "ndjson" then entries := entries.push entry.path
    perDirectory := perDirectory.push (directory, entries.size)
    for file in entries.qsort (fun a b => a.toString < b.toString) do
      let .ok x := parse (← IO.FS.readFile file)
        | do
            count := { count with unparsable := count.unparsable + 1 }
            continue
      let label := file.fileName.getD file.toString
      count := compareExport count label x (replayExport base x)
      -- A raw input fixture usually declares no model family at all, so the
      -- whole-checker comparison above has little to bite on.  The generated
      -- export is where projections and iotas actually exist, and therefore
      -- where shape analysis reaches the compared expression.  Fixtures that
      -- decline to generate are simply not compared twice.
      match ← (generatedExport x).toBaseIO with
      | .ok (generated, _) =>
        count := compareExport count s!"{label} (generated)" generated
          (replayExport base generated)
      | .error _ =>
        count := { count with ungenerated := count.ungenerated + 1 }
  return (perDirectory, count)

def run (root : String) : IO UInt32 := do
  let literalType :=
    mkApp (.lam `ignored (.sort (.succ .zero)) (.sort .zero) .default) (.sort .zero)
  let synthetic : Export :=
    { metaLine := Json.null
      decls := #[
        .defn `Transparent [] (.sort (.succ .zero)) (.sort .zero) .abbrev "safe" [],
        .opaq `Opaque [] (.sort (.succ .zero)) (.sort .zero) false [],
        .defn `Self [] (.sort (.succ .zero)) (.const `Self []) (.regular 0) "safe" [],
        .defn `CycleA [] (.sort (.succ .zero)) (.const `CycleB []) (.regular 0) "safe" [],
        .defn `CycleB [] (.sort (.succ .zero)) (.const `CycleA []) (.regular 0) "safe" [],
        .defn `Literal [] literalType (.sort .zero) .abbrev "safe" []] }
  let normalizer := synthetic.exactNormalizationEnv
  let mut state : TestState := {}
  let publicDefinitions : Std.HashMap Name ExactNormalizationDef :=
    ({} : Std.HashMap Name ExactNormalizationDef).insert `ExternalDefinition
      { levelParams := [], value := .sort .zero }
  let publicNormalizer : ExactNormalizationEnv := { definitions := publicDefinitions }
  let visibleDefinitions : Std.HashMap Name ExactNormalizationDef :=
    publicNormalizer.definitions
  state := state.check "public Std definition table still constructs and projects" <|
    visibleDefinitions.contains `ExternalDefinition &&
      publicNormalizer.whnf (.const `ExternalDefinition []) == .sort .zero
  state := state.check "transparent exported definition unfolds"
    (normalizer.whnf (.const `Transparent []) == .sort .zero)
  state := state.check "opaque exported definition remains opaque"
    (normalizer.whnf (.const `Opaque []) == .const `Opaque [])
  state := state.check "self-recursive transparent definition terminates"
    (normalizer.whnf (.const `Self []) == .const `Self [])
  state := state.check "cyclic transparent definitions terminate"
    (normalizer.whnf (.const `CycleA []) == .const `CycleA [])
  state := state.check "beta-only face retains named public constants"
    (normalizer.beta
      (mkApp (.lam `ignored (.sort (.succ .zero)) (.const `Transparent []) .default)
        (.sort .zero)) == .const `Transparent [])
  state := state.check "beta-only face retains literal lets"
    (normalizer.beta
      (.letE `X (.sort (.succ .zero)) (.sort .zero) (.bvar 0) false) ==
        .letE `X (.sort (.succ .zero)) (.sort .zero) (.bvar 0) false)
  state := state.check "normalization does not rewrite declaration types"
    (declarationType? synthetic `Literal == some literalType)

  let prim ← readExport s!"{root}/test/fixtures/inductive-models/prim_declines.ndjson"
  let some svIxDecl := prim.decls.findIdx? fun declaration =>
      declaration.names.contains `SvIx
    | throw <| IO.userError "prim_declines does not declare SvIx"
  let some svIxTable := Check.correspondenceAt? prim svIxDecl
    | throw <| IO.userError "SvIx has no correspondence"
  -- The expectation is written out rather than read back from `prim`.  Taking
  -- it from `declarationType? prim `SvIx` and then comparing against
  -- `declarationType? prim `SvIx` is `x == x`: it holds for whatever the
  -- fixture says, and it holds when `SvIx` has vanished from the export and
  -- both sides are `none`.  `SvIxFam` is the transparent former the regression
  -- was about, so an implementation that unfolded it — or that lifted the
  -- binder, or reordered the application — fails here.
  let svIxType : Expr :=
    .forallE `x (.const `P []) (mkApp (.const `SvIxFam []) (.bvar 0)) .default
  state := state.check "transparent Prop former has no illegal projections"
    svIxTable.projections.isEmpty
  state := state.check "SvIx public declaration type stays literal"
    (declarationType? prim `SvIx == some svIxType)

  let flatInput ← readExport s!"{root}/test/fixtures/inductive-models/nest_fam_arg.ndjson"
  let (flatOutput, flatReport) ← generatedExport flatInput
  let flatFamilyOwner := (`Flat._model._impl).mkNum 0
  let flatOwner := (`Flat._model._impl).mkNum 1
  let flatIotas := #[Naming.projectionIotaName flatOwner 0,
    Naming.projectionIotaName flatOwner 1]
  state := state.check "Flat exports both exact projection iotas"
    (flatIotas.all fun name => flatOutput.decls.any (·.names.contains name))
  state := state.check "Flat projection iotas check literally"
    ((Check.check flatOutput).all fun violation =>
      !(flatOwner.isPrefixOf violation.familyOwner))
  state := state.check "generated Flat owner checks through the source syntax overlay"
    (flatReport.generated.any (·.1 == flatFamilyOwner) && flatReport.stmtErrors.isEmpty)

  let (perDirectory, agreement) ← environmentAgreement root
  let disagreements := agreement.failed
  let compared := agreement.compared
  let fixtures := perDirectory.foldl (fun total entry => total + entry.2) 0
  state := state.check "environment and export agree about shape on every fixture"
    disagreements.isEmpty
  -- **The floor under the sweep.**  Every comparison above is a statement
  -- about a record the replay installed, so a replay that stops installing
  -- them, or a fixture directory that moves, reduces `compared` towards zero
  -- and leaves the assertion above green with nothing behind it.  The skips
  -- are counted and asserted rather than passed over.
  state := state.check
    s!"each fixture directory holds the exports it is expected to \
      ({perDirectory} against {fixtureDirectories})"
    (perDirectory == fixtureDirectories)
  state := state.check
    s!"every committed fixture parses ({agreement.unparsable} do not)"
    (agreement.unparsable == 0)
  -- These two are current reality, not a target: they are pinned so that a
  -- *new* silent skip is a failure rather than a smaller number in the line
  -- below.
  state := state.check
    s!"records the replay did not install stay at \
      {skippedRecordsExpectation} ({agreement.skippedRecords} skipped)"
    (agreement.skippedRecords == skippedRecordsExpectation)
  state := state.check
    s!"fixtures compared once rather than twice stay at \
      {ungeneratedExpectation} ({agreement.ungenerated} ungenerated)"
    (agreement.ungenerated == ungeneratedExpectation)
  state := state.check
    s!"the sweep still compares its full corpus ({compared} comparisons, \
      floor {comparisonFloor})"
    (compared >= comparisonFloor)
  IO.println s!"export syntax normalization: {state.passed} passed, {state.failed.size} failed"
  IO.println s!"environment/export shape agreement: {compared} comparisons over \
    {fixtures} fixtures, {disagreements.size} differ \
    ({agreement.skippedRecords} records skipped, \
     {agreement.missingDirectories} directories absent, \
     {agreement.ungenerated} fixtures not generated)"
  for failure in disagreements.extract 0 40 do IO.eprintln s!"DISAGREEMENT: {failure}"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1

def main (args : List String) : IO UInt32 :=
  run (args.head?.getD ".")
