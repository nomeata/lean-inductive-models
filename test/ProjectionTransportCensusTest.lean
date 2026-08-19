import InductiveModels.Driver

namespace ProjectionTransportCensusTest

/-!
# The intrinsic projection contract, checked as an invariant

Run from the repository root: `lake exe test projectiontransportcensus [ROOT]`.

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
required only when field `j` depends on an earlier field whose modeled
projection reduces merely propositionally, and generation no longer emits a
rule in that case at all: the equation would relate two terms of different
types, so the owner declines
([`InductiveModels.Decline.projectionCodomain`], and
`test/fixtures/inductive-models/e_dependent_field.lean`'s `EOpaque` is the one
owner it still declines — a field at an opaque `imax` level that no tower can
store).  Every rule that *is* emitted therefore has its field binder on the
right, and the literal right-hand side is the only one the generator ever has
to state.

`test/fixtures/inductive-models/w_dependent_field.lean` used to be that owner
and is now a positive: arm W selects its stored fields through
`_wcore.WT.root` and the data tower, so a dependent field on that arm states
its rule by `Eq.refl` like every other route and is counted here rather than
declined.  `e_dependent_field` went the same way one construction later: arm
E's carrier stores its constructor's non-recursive fields in a `PSigma'` tower
ending at `emptyAt w`, so its projections are the tower's own and select by π.

Recursion is a separate and stronger reason for the same thing on the routes
that do reach a field definitionally: Lean's positivity and nesting rules
leave **no spelling** of a constructor field type that reads a recursive or
nested occurrence's *value*, and
`test/fixtures/inductive-models/nested_value_dependency.lean` writes out every
attempt for the kernel to reject.

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

/-- The projection iotas each committed fixture emits under `censusGeneration`,
as `(label, count)` pairs in label order.

Without this table the invariant above has no floor.  Every assertion in
`censusFixture` is a statement *about* a rule that was found, so a route that
stopped emitting projection iotas, a rename of the `T._model.proj_j.iota`
shape `projectionIotaOwner?` recognises, or a `censusGeneration` flag that
stopped selecting a route would leave the census with nothing to inspect and
it would print `0 of 0` and exit 0.  `expectedUnrunnable` does not cover that:
it names fixtures that *throw*, not fixtures that run and generate nothing.

The expectation is per fixture rather than a single global minimum, because a
global minimum still passes when one fixture silently stops generating while
the rest carry the total.  Pinning the exact count also makes any change in
coverage visible: a route that starts or stops emitting a rule shows up here
as the fixture it happened in.  The zeros are pinned for the same reason as
the positive counts — `arm_f_guards`, `arm_f_zip`, `default_ctor_iota`,
`maybe_zero_indexed`, `maybe_zero_recursive` and `nonindexed_vanishing` model
no eligible one-constructor record, and a route that starts giving one of them
a projection has to be looked at rather than absorbed.  `prim_shape_declines`
is a zero of the other kind: its four declining owners are exactly the shapes
that reach no arm, and its only model is a two-constructor enumeration, so a
projection appearing there would mean one of the four had started modelling.
`maybe_zero_pad` is the complement and is 16: every one of its ten owners but
the two-constructor `Nt` is a projection-eligible one-constructor record, and
the count is their fields — one each for `IdOne`, `PropOne`, `PadOne` and
`PadIdx`, two each for `PadNone`, `PadMany`, `PadMix`, `PadDep` and `PadIdx2`
— **plus two for `PProd'`**, the binder-free pair the storage tower's constant
rungs are built at, which this export is the first to splice and which the
splice-closure rule then models like any other spliced inductive. Its two
fields are projection-eligible on exactly the terms every other
one-constructor record's are, so it is a row occupant and not an exemption.
Four of the ten are the pad's own occupants, and a route that stopped padding
would drop them out of this row rather than merely change a carrier.

`maybe_zero_projection` (10, was 8) and `tight_psigma_prime` (6, was 4) carry
the same two for the same reason.

**And sixty-three rows carry them now**, because the never-zero chain reaches a
constant rung as well: any export with a `Type`-sorted owner whose stored chain
has a rung no later field's type mentions splices the pair and models it, and
the pair's own two fields are then projection-eligible on the same terms every
other one-constructor record's are. So the +2 in each of those rows is the pair
and nothing about the owner that occasioned it. `default_ctor_iota` is the one
that moved off zero: it had no projection-eligible owner of its own, and its
whole row is now the pair's.

`mutual_one_layer_boundary` is 7 and not 18 because its only consumer of the W
core was an index erasure with no base constructor: arm E models that skeleton
by the lift of `⊥`, so the `_wcore` fragment is not spliced there at all and
the eleven projection iotas its own records carried are gone with it. The
fixture's public interfaces are unchanged; what left is a fragment it no longer
needs.

`dead_owner_mention` is 13: the eleven the spliced `_wcore` fragment always
carries plus `DeadStruct`'s two.  `DeadStruct` is the fixture's owner whose
only owner mention is ζ-dead, so it is a one-constructor *nonrecursive*
record and is asked for both of its fields back; a route that reads its field
domain as written makes it recursive again and this row drops to eleven.

`e_dependent_field` is 18 and not 0: `EDep`'s three fields, `EChain`'s,
`EMid`'s and `ENon`'s four each and `EBare`'s three, every one of them stated
by `Eq.refl` against arm E's stored tower.  `EMulti` contributes nothing — two
constructors, so no intrinsic projection is asked — and neither does `EOpaque`,
which declines.  `Tag` and `Fib` are indexed helpers whose only fields are
their conclusion indices, exactly as in `w_dependent_field`.

`prim_w` is 46 and not 35 because it gained `TripleInf`, `QuadInf` and
`TrineInf` — three one-constructor arm-W owners at three and four recursive
fields, restoring the one-layer adapter over a W carrier past the two
`TwinInf` has.  Each is one-constructor and so projection-eligible, and their
three, four and four fields are the whole of the difference.

`recursor_field_domain` is 2, and both are the spliced pair's: `P` is a
two-constructor enumeration and `Owner` is a two-constructor recursive owner,
so neither is asked for an intrinsic projection at all.  The fixture is about
the *field domain* `Owner.node` reads its recursion through, not about
selecting it. -/
def expectedProjectionIotas : Array (String × Nat) :=
  #[("arm_f_guards", 0), ("arm_f_zip", 0), ("compose_sorts", 23),
    ("dead_owner_mention", 15), ("decline_no_eq", 13), ("default_ctor_iota", 2),
    ("degenerate_graph", 1),
    ("dependent_fields", 13), ("e_dependent_field", 20), ("empty_no_base", 18),
    ("filtered/nat_char_equations", 5),
    ("filtered/nested_deep", 13), ("filtered/nested_iota", 15),
    ("filtered/nested_iota_arm", 13), ("filtered/nested_keying", 13),
    ("filtered/nested_shapes", 19), ("funext_binder", 21),
    ("hard_nested_mutual_index", 13), ("imax_box", 3), ("indexed_container", 13),
    ("indexed_decl", 13), ("indexed_fibre_boundary", 59),
    ("indexed_hidden_erasure", 13), ("infinitary", 25), ("maybe_zero_indexed", 0),
    ("maybe_zero_pad", 16),
    ("maybe_zero_projection", 10), ("maybe_zero_recursive", 0), ("mutual_index", 8),
    ("mutual_keying", 2),
    ("mutual_nonrec", 2), ("mutual_odd_shapes", 17),
    ("mutual_one_layer_boundary", 9), ("mutual_prop", 1), ("mutual_shapes", 20),
    ("mutual_structure_projections", 5), ("nest_binder_cross", 25),
    ("nest_cycle_group", 15), ("nest_fam_arg", 41), ("nest_family_edges", 15),
    ("nest_index_cross", 16), ("nest_mutual_both", 15), ("nest_mutual_cycle", 13),
    ("nest_mutual_index", 15), ("nest_odd_shapes", 33), ("nest_sorts", 19),
    ("nest_through_mutual", 15), ("nest_through_nested", 13), ("nested_deep", 13),
    ("nested_default_iota", 19), ("nested_iota", 15), ("nested_iota_arm", 13),
    ("nested_keying", 13), ("nested_mutual_indexed_container", 13),
    ("nested_one_layer", 19), ("nested_shapes", 19), ("nested_value_dependency", 27),
    ("nonindexed_vanishing", 2), ("poly_nested", 15), ("prim_carve", 19),
    ("prim_declines", 18), ("prim_graph", 8), ("prim_graph_pre", 4), ("prim_idx", 19),
    ("prim_late_basis", 16), ("prim_late_eq", 1),
    ("prim_prop_skipped_field", 4), ("prim_shape_declines", 0),
    ("prim_shapes", 24), ("prim_w", 48),
    ("private_constructor", 3), ("prop_projection_boundaries", 12),
    ("prop_recursive_projections", 3), ("recursor_field_domain", 2),
    ("source_structure_syntax", 7),
    ("structure_eta", 12), ("structure_projections", 19),
    ("tight_prop_field_late", 1), ("tight_psigma_prime", 6),
    ("transparent_owner_aliases", 3), ("unitlike", 6), ("unused_level_param", 0),
    ("w_alias", 13),
    ("wide_block", 48),
    ("w_core", 13), ("w_dependent_field", 30), ("w_imax", 13), ("w_late_iff", 13),
    ("w_max", 13)]

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
  let mut perFixture : Array (String × Nat) := #[]
  for (fixture, path) in paths do
    let result ← censusFixture fixture path
    failures := failures ++ result.failures
    literal := literal + result.literal
    projectionIotas := projectionIotas + result.projectionIotas
    authoredEqRec := authoredEqRec + result.authoredEqRec
    perFixture := perFixture.push (fixture, result.projectionIotas)
    unless result.ran do unrunnable := unrunnable.push fixture
  unrunnable := unrunnable.qsort (· < ·)
  if unrunnable != expectedUnrunnable.qsort (· < ·) then
    failures := failures.push
      s!"unrunnable fixtures are {unrunnable}, expected {expectedUnrunnable}: \
         update expectedUnrunnable"

  -- **The floor.** Each fixture is asserted to have produced exactly the
  -- rules the table above records, so a fixture that stops generating them is
  -- a failure here rather than a smaller number in the line below.
  for (fixture, count) in perFixture do
    match expectedProjectionIotas.find? (·.1 == fixture) with
    | none =>
      failures := failures.push
        s!"{fixture}: is not in expectedProjectionIotas ({count} projection iotas): \
           add the row"
    | some (_, expected) =>
      unless count == expected do
        failures := failures.push
          s!"{fixture}: emitted {count} projection iotas, expected {expected}"
  for (fixture, expected) in expectedProjectionIotas do
    unless perFixture.any (·.1 == fixture) do
      failures := failures.push
        s!"{fixture}: expected {expected} projection iotas but the fixture was not \
           swept: remove the row or restore the fixture"
  -- Every rule that was found also has to have been recognised as literal;
  -- `censusFixture` only counts one when it also passes the invariant, so a
  -- rule that failed above is missing from `literal` rather than from
  -- `projectionIotas`.
  unless literal == projectionIotas do
    failures := failures.push
      s!"{literal} of {projectionIotas} projection iotas state their field binder \
         literally"

  IO.println s!"intrinsic projection contract: \
    {literal} of {projectionIotas} projection iotas state their constructor \
    field binder literally ({authoredEqRec} statements carry source-authored \
    Eq.rec in the telescope or codomain) over \
    {paths.size - unrunnable.size} fixtures"
  for failure in failures do IO.eprintln s!"FAIL: {failure}"
  return if failures.isEmpty then 0 else 1

end ProjectionTransportCensusTest
