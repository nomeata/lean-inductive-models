import InductiveModels.Naming
import InductiveModels.ModelRoles

open Lean InductiveModels InductiveModels.Naming

structure TestState where
  passed : Nat := 0
  failed : Nat := 0

def TestState.check (state : TestState) (label : String) (condition : Bool) : IO TestState := do
  if condition then
    return { state with passed := state.passed + 1 }
  else
    IO.eprintln s!"FAIL: {label}"
    return { state with failed := state.failed + 1 }

private def perfOwner (index : Nat) : Name :=
  Name.num `CollisionCensusPerf index

private def largeReserved (size : Nat) : Std.HashSet Name :=
  (List.range size).foldl (fun names index => names.insert (perfOwner index)) {}

private def perfTable : Table :=
  Table.empty
    |>.addDeclaration .typeFormer `CollisionCensusPerf.hit
    |>.addRecursor `CollisionCensusPerf.rec 2
    |>.addMetadata .eta `CollisionCensusPerf.meta
    |>.addMetadata .eta `CollisionCensusPerf.meta

private def perfReserved (size : Nat) : Std.HashSet Name :=
  largeReserved size
    |>.insert (modelName `CollisionCensusPerf.hit)
    |>.insert (iotaName `CollisionCensusPerf.rec 1)
    |>.insert (etaName `CollisionCensusPerf.meta)

private def perfHelpers : Std.HashSet Name :=
  ({} : Std.HashSet Name).insert (iotaName `CollisionCensusPerf.rec 0)

private def runPerf (direct : Bool) : IO UInt32 := do
  let reserved := perfReserved 20000
  let mut checksum := 0
  for _ in [0:200] do
    let census := if direct then
        perfTable.collisionCensusReservedWith reserved perfHelpers
      else
        perfTable.collisionCensus (reserved.toArray ++ perfHelpers.toArray)
    checksum := checksum + census.taken.size + census.duplicateRequirements.size
  IO.println s!"collision census checksum: {checksum}"
  return if checksum == 1000 then 0 else 1

/-- Exact role discovery must not infer ownership by parsing `_model`
components. This makes that observable with an original type already named
`Foo._model` and a raw private constructor name. -/
private def modelRoleProbe : Array String := Id.run do
  let outer : Name := `Foo
  let typeName : Name := `Foo._model
  let constructorName : Name := (`_private.ModelRoles).mkNum 7 |>.str "mk"
  let recursorName : Name := `Foo._model.rec
  let rule : ERecRule :=
    { ctor := constructorName, nfields := 0, rhs := .sort .zero }
  let type : EIndType :=
    { name := typeName, levelParams := [`u], type := .sort (.param `u),
      all := [typeName], ctors := [constructorName], numParams := 0, numIndices := 0,
      numNested := 0, isRec := false, isReflexive := false, isUnsafe := false }
  let constructor : ECtor :=
    { name := constructorName, levelParams := [`u], type := .sort (.param `u), cidx := 0,
      numParams := 0, numFields := 0, induct := typeName, isUnsafe := false }
  let recursor : ERec :=
    { name := recursorName, levelParams := [`w, `u], type := .sort (.param `u),
      all := [recursorName], numParams := 0, numIndices := 0, numMotives := 1,
      numMinors := 1, rules := [rule], k := true, isUnsafe := false }
  let definition := fun name =>
    EDecl.defn name [`u] (.sort (.param `u)) (.sort (.param `u))
      EHints.abbrev "safe" [name]
  let iota := iotaName recursorName 0
  let unitlike := unitlikeName typeName
  let ruleK := ruleKName recursorName
  let helper := `Foo._model._impl.pack
  let outerType : EIndType :=
    { name := outer, levelParams := [], type := .sort (.succ .zero),
      all := [outer], ctors := [], numParams := 0, numIndices := 0,
      numNested := 0, isRec := false, isReflexive := false, isUnsafe := false }
  let source : Export := { metaLine := .null, decls := #[
    definition (modelName typeName),
    definition (modelName constructorName),
    definition (modelName recursorName),
    .thm iota [`w, `u] (.sort (.param `u)) (.sort (.param `u)) [iota],
    .thm unitlike [`u] (.sort (.param `u)) (.sort (.param `u)) [unitlike],
    .thm ruleK [`w, `u] (.sort (.param `u)) (.sort (.param `u)) [ruleK],
    definition helper,
    .thm (unitlikeName outer) [] (.sort .zero) (.sort .zero) [unitlikeName outer],
    .induct [type] [constructor] [recursor],
    .induct [outerType] [] [] ] }
  let roles := ModelRoles.table source
  let mut errors : Array String := #[]
  let expect := fun (errors : Array String) (name owner : Name) (role : ModelRoles.Role) =>
    match roles[name]? with
    | some entry =>
      if entry.owner == owner && entry.role == role then errors
      else errors.push s!"{name}: wrong model entry ({entry.owner})"
    | none => errors.push s!"{name}: exact model entry missing"
  errors := expect errors (modelName typeName) typeName .typeFormer
  errors := expect errors (modelName constructorName) typeName .constructor
  errors := expect errors (modelName recursorName) typeName .recursor
  errors := expect errors iota typeName .iota
  errors := expect errors unitlike typeName .unitlike
  errors := expect errors ruleK typeName .ruleK
  if roles.contains (modelName outer) then
    errors := errors.push "the original Foo._model inductive was parsed as Foo's carrier"
  if roles.contains helper then
    errors := errors.push "an _impl helper was parsed as a public model declaration"
  if roles.contains (unitlikeName outer) then
    errors := errors.push "an extra unitlike suffix was inferred without kernel metadata"
  return errors

def main (args : List String) : IO UInt32 := do
  if args == ["--perf-direct"] then return ← runPerf true
  if args == ["--perf-materialized"] then return ← runPerf false
  let mut state : TestState := {}

  state ← state.check "exact model roles do not parse generated-looking names"
    modelRoleProbe.isEmpty

  state ← state.check "ordinary declaration" (modelName `Tree == `Tree._model)
  state ← state.check "namespaced declaration"
    (modelName `Data.Tree == `Data.Tree._model)

  let numeric := Name.num `Data.Tree 17
  state ← state.check "numeric declaration keeps numeric component"
    (modelName numeric == Name.str numeric "_model")

  state ← state.check "an original _model component composes"
    (modelName `Foo._model == `Foo._model._model)
  state ← state.check "iota belongs to exact recursor and rule position"
    (iotaName `Data.Tree.rec_1 2 == `Data.Tree.rec_1._model.iota_2)

  state ← state.check "unitlike metadata"
    (unitlikeName `Unitish == `Unitish._model.unitlike)
  state ← state.check "eta metadata"
    (etaName `Pair == `Pair._model.eta)
  state ← state.check "projection model"
    (projectionName `Pair 0 == `Pair._model.proj_0)
  state ← state.check "projection iota metadata"
    (projectionIotaName `Pair 2 == `Pair._model.proj_2.iota)
  state ← state.check "rule-K metadata"
    (ruleKName `Eq.rec == `Eq.rec._model.ruleK)

  let privateOwner := (`_private.M).mkNum 0 |>.str "T"
  state ← state.check "private raw name is retained"
    (modelName privateOwner == Name.str privateOwner "_model")
  state ← state.check "private name is not normalized"
    (modelName privateOwner != modelName (privateToUserName privateOwner))

  let table := Table.empty
    |>.addDeclaration .typeFormer `Data.Tree
    |>.addDeclaration .constructor `Data.Tree.leaf
    |>.addRecursor `Data.Tree.rec_1 2
    |>.addMetadata .unitlike `Data.Tree
    |>.addMetadata .eta `Data.Tree
    |>.addProjection `Data.Tree 0
    |>.addMetadata .ruleK `Data.Tree.rec_1

  state ← state.check "table model lookup uses exact original"
    (table.modelName? .constructor `Data.Tree.leaf == some `Data.Tree.leaf._model)
  state ← state.check "table reverse lookup does not parse prefixes"
    (table.originalName? .typeFormer `Data.Tree._model == some `Data.Tree)
  state ← state.check "table records ordered recursor rules"
    (table.iotas.map (·.name) ==
      #[`Data.Tree.rec_1._model.iota_0, `Data.Tree.rec_1._model.iota_1])

  let occupied := #[
    `unrelated,
    `Data.Tree.leaf._model,
    `Data.Tree.rec_1._model.iota_1,
    `Data.Tree._model.proj_0.iota,
    modelName privateOwner
  ]
  let census := table.collisionCensus occupied
  state ← state.check "collision census finds every exact occupied name"
    (census.taken ==
      #[`Data.Tree.leaf._model, `Data.Tree.rec_1._model.iota_1,
        `Data.Tree._model.proj_0.iota])
  state ← state.check "well-formed table has no duplicate requirements"
    census.duplicateRequirements.isEmpty

  let privateTable := Table.empty.addDeclaration .typeFormer privateOwner
  let normalizedPrivateModel := modelName (privateToUserName privateOwner)
  let normalizedPrivateCensus := privateTable.collisionCensus #[normalizedPrivateModel]
  state ← state.check "private normalized name is not an exact collision"
    normalizedPrivateCensus.isEmpty
  let exactPrivateCensus := privateTable.collisionCensus #[modelName privateOwner]
  state ← state.check "private raw name is an exact collision"
    (exactPrivateCensus.taken == #[modelName privateOwner])
  let normalizedPrivateSet := ({} : Std.HashSet Name).insert normalizedPrivateModel
  state ← state.check "reserved-set census does not normalize private names"
    (privateTable.collisionCensusReserved normalizedPrivateSet).isEmpty
  let exactPrivateSet := ({} : Std.HashSet Name).insert (modelName privateOwner)
  state ← state.check "reserved-set census retains exact private names"
    ((privateTable.collisionCensusReserved exactPrivateSet).taken == #[modelName privateOwner])

  let duplicate := table.addMetadata .eta `Data.Tree
  let duplicateCensus := duplicate.collisionCensus #[]
  state ← state.check "collision census reports duplicate requirements once"
    (duplicateCensus.duplicateRequirements == #[`Data.Tree._model.eta])
  state ← state.check "duplicate requirement makes census nonempty"
    (!duplicateCensus.isEmpty)

  let largeReserved := perfReserved 20000
  let largeCensus := perfTable.collisionCensusReservedWith largeReserved perfHelpers
  state ← state.check "two-set census preserves required-name order"
    (largeCensus.taken == #[modelName `CollisionCensusPerf.hit,
      iotaName `CollisionCensusPerf.rec 0, iotaName `CollisionCensusPerf.rec 1,
      etaName `CollisionCensusPerf.meta])
  state ← state.check "two-set census preserves duplicate diagnostic order"
    (largeCensus.duplicateRequirements == #[etaName `CollisionCensusPerf.meta])
  state ← state.check "two-set census matches materialized union"
    (largeCensus == perfTable.collisionCensus (largeReserved.toArray ++ perfHelpers.toArray))

  if state.failed == 0 then
    IO.println s!"Naming: {state.passed} tests passed"
    return 0
  else
    IO.eprintln s!"Naming: {state.failed} failed, {state.passed} passed"
    return 1
