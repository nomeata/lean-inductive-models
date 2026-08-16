import InductiveModels.Driver

/-!
# The intrinsic projection contract, checked as an invariant

Run from the repository root: `lake exe projectiontransportcensustest [ROOT]`.

Every intrinsic projection rule `T._model.proj_j.iota` is stated as

```
∀ (constructor telescope), @Eq α (T._model.proj_j … (T._model.mk …)) rhs
```

over the modeled constructor's own `numParams + numFields` telescope, and the
invariant this suite pins is that `rhs` is **the constructor's field-`j`
binder itself**: the loose `Expr.bvar` the telescope binds at position
`numParams + j`.  Nothing is transported into a projection right-hand side,
and nothing ever has to be.

This is an invariant rather than a census because it cannot regress for a
reason a maintainer would want to record.  A transported right-hand side is
required only when field `j` depends on the *value* of an earlier field whose
modeled projection reduces merely propositionally — that is, on a recursive or
nested occurrence field.  Lean's positivity and nesting rules leave **no
spelling** of a constructor field type that reads such a value;
`test/fixtures/inductive-models/nested_value_dependency.lean` writes out every
attempt and the kernel rejects each one.  So every field a later field can
depend on is non-recursive, every non-recursive field is selected
definitionally, and the literal right-hand side is the only one the generator
ever has to state.

There is therefore no allowlist here and no row to append.  A right-hand side
that stops being its field binder is a defect in the route that produced it;
this suite names the fixture, the owner and the field so it is fixed there.

`expectedUnrunnable` remains, because it is about *exhaustiveness* rather than
about transport: a fixture that starts or stops running under the maximal
generation configuration has to be noticed, or the invariant would quietly
stop covering the corpus.

Source-authored `Eq.rec` in a constructor telescope or a projection codomain
is a different matter: it is the source's own syntax, the model reproduces it
exactly, and it is counted below rather than restricted.
-/

set_option maxRecDepth 4096

open Lean Meta InductiveModels

/-- Every generation branch on, so the invariant sees the maximal set of
modeled owners rather than one suite's slice. -/
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

/-- The exported parameter and field counts of a one-constructor owner.  A
projection rule is stated over exactly `numParams + numFields` binders of the
modeled constructor's telescope, so these two numbers locate the field binder
in the closed statement. -/
structure OwnerArity where
  numParams : Nat
  numFields : Nat
  deriving Inhabited

/-- Every one-constructor inductive owner in the output stream, source and
generated alike.  A projection owner is always an exported inductive record,
so a missing entry is a failure below rather than a reason to skip. -/
def ownerArities (decls : Array EDecl) : Array (Name × OwnerArity) := Id.run do
  let mut result : Array (Name × OwnerArity) := #[]
  for declaration in decls do
    if let .induct types constructors _ := declaration then
      for type in types do
        if let [constructorName] := type.ctors then
          if let some constructor := constructors.find? fun constructor =>
              constructor.name == constructorName && constructor.induct == type.name then
            result := result.push (type.name,
              { numParams := type.numParams, numFields := constructor.numFields })
  return result

/-- Peel exactly `count` `∀` binders.  A short telescope yields `none`, which
is a failure rather than a skip. -/
def peelForalls : Nat → Expr → Option Expr
  | 0, body => some body
  | count + 1, .forallE _ _ body _ => peelForalls count body
  | _, _ => none

/-- The outermost equality's right-hand side under a telescope of exactly
`binders` binders. -/
def closedRuleRhs? (binders : Nat) (statement : Expr) : Option Expr := do
  let body ← peelForalls binders statement
  let .const equality _ := body.getAppFn | none
  unless equality == ``Eq do none
  let arguments := body.getAppArgs
  unless arguments.size == 3 do none
  return arguments[2]!

structure FixtureCensus where
  failures : Array String := #[]
  /-- Projection iotas whose right-hand side is their constructor field
  binder. -/
  literal : Nat := 0
  /-- Every projection iota seen. -/
  projectionIotas : Nat := 0
  /-- Statements mentioning `Eq.rec`; with the invariant met these are exactly
  source-authored telescopes and codomains. -/
  authoredEqRec : Nat := 0
  ran : Bool := true

/-- Record one failed projection rule.  Every failure names the fixture, the
rule and what it states instead. -/
def FixtureCensus.fail (result : FixtureCensus) (message : String) : FixtureCensus :=
  { result with failures := result.failures.push message }

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
  let arities := ownerArities decls
  let mut result : FixtureCensus := {}
  for declaration in decls do
    for (name, statement) in theoremStatements declaration do
      let some (owner, field) := projectionIotaOwner? name | continue
      result := { result with projectionIotas := result.projectionIotas + 1 }
      if containsEqRec statement then
        result := { result with authoredEqRec := result.authoredEqRec + 1 }
      match arities.find? (·.1 == owner) with
      | none =>
        result := result.fail
          s!"{fixture}: {name} has no one-constructor record for owner {owner}"
      | some (_, arity) =>
        if field >= arity.numFields then
          result := result.fail s!"{fixture}: {name} selects field {field} of a \
            {arity.numFields}-field constructor"
        else
          match closedRuleRhs? (arity.numParams + arity.numFields) statement with
          | none =>
            result := result.fail s!"{fixture}: {name} is not an equation under \
              {owner}'s {arity.numParams}+{arity.numFields} constructor telescope"
          | some rhs =>
            -- The telescope binds parameters and then fields, so constructor
            -- field `j` is the de Bruijn index `numFields - 1 - j` at the
            -- equation.
            if rhs == Expr.bvar (arity.numFields - 1 - field) then
              result := { result with literal := result.literal + 1 }
            else
              result := result.fail s!"{fixture}: {name} states a right-hand side \
                that is not constructor field {field}: dependent transport has \
                returned to the projection contract"
  return result

/-- The committed corpus, as (label prefix, directory) pairs.  The filtered
subdirectory repeats several base names of the directory above it, so the
label keeps the subdirectory. -/
def fixtureDirectories : Array (String × String) :=
  #[("", "test/fixtures/inductive-models"),
    ("filtered/", "test/fixtures/inductive-models/filtered")]

/-- Fixtures the maximal generation configuration cannot run to completion.
It is empty: `hard_nested_mutual_index`, `indexed_decl`, `infinitary` and
`nest_index_cross` all raised `Unknown constant` for a member of their own
input block, because the shadow derivation opened a raw source telescope
through `MetaM` while that member was deliberately not installed; every source
telescope now has its exact domains installed directly instead.

The list is pinned so that the invariant above cannot silently stop being
exhaustive: a fixture that starts running must be checked, and a fixture that
stops running must be noticed. -/
def expectedUnrunnable : Array String := #[]

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let root := args.head?.getD "."
  let mut paths : Array (String × String) := #[]
  for (prefix_, directory) in fixtureDirectories do
    for entry in ← System.FilePath.readDir s!"{root}/{directory}" do
      if entry.path.extension == some "ndjson" then
        paths := paths.push (prefix_ ++ entry.path.fileStem.getD "", entry.path.toString)
  paths := paths.qsort (fun left right => left.1 < right.1)
  let mut failures : Array String := #[]
  let mut unrunnable : Array String := #[]
  let mut literal := 0
  let mut projectionIotas := 0
  let mut authoredEqRec := 0
  for (fixture, path) in paths do
    let result ← censusFixture fixture path
    failures := failures ++ result.failures
    literal := literal + result.literal
    projectionIotas := projectionIotas + result.projectionIotas
    authoredEqRec := authoredEqRec + result.authoredEqRec
    unless result.ran do unrunnable := unrunnable.push fixture
  unrunnable := unrunnable.qsort (· < ·)
  if unrunnable != expectedUnrunnable.qsort (· < ·) then
    failures := failures.push
      s!"unrunnable fixtures are {unrunnable}, expected {expectedUnrunnable}: \
         update expectedUnrunnable"

  IO.println s!"intrinsic projection contract: \
    {literal} of {projectionIotas} projection iotas state their constructor \
    field binder literally ({authoredEqRec} statements carry source-authored \
    Eq.rec in the telescope or codomain) over \
    {paths.size - unrunnable.size} fixtures"
  for failure in failures do IO.eprintln s!"FAIL: {failure}"
  return if failures.isEmpty then 0 else 1
