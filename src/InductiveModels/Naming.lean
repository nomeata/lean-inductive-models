import Lean

/-!
# Public names of inductive models

This module is the single, purely syntactic source of public names emitted for
an inductive model.  Every function takes the exact `Name` stored in an export;
in particular, none of them searches for or removes an `_model` component.

Keeping the operations on raw names matters for declarations whose names are
private, numeric, or already end in `_model`.  Consumers that need to work
around kernel normalization of private names must do so only after constructing
the public names recorded here.
-/

open Lean

namespace InductiveModels.Naming

/-- A collision retry's exact build-name to export-name substitution.

The entries are deliberately whole names, rather than namespace prefixes.  A
private constructor need not live below its inductive's name, so prefix
substitution is not a naming model.  `buildRoot?` is retained only as the
recipe used to register kernel-generated auxiliary names (notably recursors)
when they are read back from the environment; consumers rewrite solely by
looking up `entries`. -/
structure AliasMap where
  entries : Array (Name × Name) := #[]
  buildRoot? : Option (Name × Name) := none
  deriving Inhabited, Repr

def AliasMap.empty : AliasMap := {}

/-- The retry namespace for an exact declaration owner.  Appending the raw
name below a public component keeps an embedded `_private` component from
being stripped by `privateToUserName`. -/
def retryRoot (owner : Name) : Name := `_inductive_models_alias ++ owner

/-- Relocate an exact source declaration for a retry.  Descendants retain
their suffix; declarations outside the owner's namespace (raw private
constructors are the important case) are embedded injectively below `_source`.
-/
opaque relocateSource (owner buildOwner source : Name) : Name :=
  if owner == buildOwner then source
  else if owner.isPrefixOf source then source.replacePrefix owner buildOwner
  else (Name.str buildOwner "_source") ++ source

def AliasMap.insert (aliases : AliasMap) (build exact : Name) : AliasMap :=
  if build == exact || aliases.entries.any (fun p => p.1 == build) then aliases
  else { aliases with entries := aliases.entries.push (build, exact) }

def AliasMap.exact? (aliases : AliasMap) (build : Name) : Option Name :=
  (aliases.entries.find? fun p => p.1 == build).map (·.2)

def AliasMap.exact (aliases : AliasMap) (build : Name) : Name :=
  aliases.exact? build |>.getD build

/-- Register names discovered only after Lean elaborates an inductive block.
This constructs explicit whole-name entries; it does not make prefix matching
part of serialization. -/
def AliasMap.register (aliases : AliasMap) (names : Array Name) : AliasMap :=
  match aliases.buildRoot? with
  | none => aliases
  | some (buildRoot, exactRoot) =>
    names.foldl (fun out build =>
      if buildRoot.isPrefixOf build then
        out.insert build (build.replacePrefix buildRoot exactRoot)
      else out) aliases

/-- Start a retry map and explicitly register the generated names known before
serialization. -/
def AliasMap.forRetry (buildRoot exactRoot : Name) (names : Array Name) : AliasMap :=
  ({ buildRoot? := some (buildRoot, exactRoot) } : AliasMap).register names

/-- The model declaration corresponding to the exact exported declaration `n`. -/
def modelName (n : Name) : Name := Name.str n "_model"

/-- The theorem for rule `j` of the exact exported recursor `recursor`.

Rule numbers are positions in the export's recursor-rule array. -/
def iotaName (recursor : Name) (j : Nat) : Name :=
  Name.str (modelName recursor) s!"iota_{j}"

/-- The proof that a kernel-unit-like inductive has at most one inhabitant. -/
def unitlikeName (typeFormer : Name) : Name :=
  Name.str (modelName typeFormer) "unitlike"

/-- The structure-eta theorem for an inductive type former. -/
def etaName (typeFormer : Name) : Name :=
  Name.str (modelName typeFormer) "eta"

/-- The intrinsic projection of zero-based constructor field `fieldIndex`.

Unlike constructors and recursors, this declaration does not model a source
constant.  Its public name is determined solely by the modeled type former and
the field's position in its unique constructor telescope. -/
def projectionName (typeFormer : Name) (fieldIndex : Nat) : Name :=
  Name.str (modelName typeFormer) s!"proj_{fieldIndex}"

/-- The constructor-reduction theorem for an intrinsic structure projection. -/
def projectionIotaName (typeFormer : Name) (fieldIndex : Nat) : Name :=
  Name.str (projectionName typeFormer fieldIndex) "iota"

/-- The rule-K reduction theorem belonging to a recursor. -/
def ruleKName (recursor : Name) : Name :=
  Name.str (modelName recursor) "ruleK"

/-- The role of an original declaration in a model table. -/
inductive DeclarationKind where
  | typeFormer
  | constructor
  | recursor
  deriving BEq, DecidableEq, Inhabited, Repr

/-- An exact original declaration and its declaration-local model name. -/
structure Declaration where
  kind : DeclarationKind
  original : Name
  model : Name
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Construct the declaration entry for `original`. -/
def Declaration.ofOriginal (kind : DeclarationKind) (original : Name) : Declaration :=
  { kind, original, model := modelName original }

/-- One ordered iota theorem for an exported recursor rule. -/
structure Iota where
  recursor : Name
  ruleIndex : Nat
  name : Name
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Construct the entry for rule position `ruleIndex` of `recursor`. -/
def Iota.ofRecursor (recursor : Name) (ruleIndex : Nat) : Iota :=
  { recursor, ruleIndex, name := iotaName recursor ruleIndex }

/-- The kernel feature certified by an additional model theorem. -/
inductive MetadataKind where
  | unitlike
  | eta
  | ruleK
  deriving BEq, DecidableEq, Inhabited, Repr

/-- A metadata theorem and the exact declaration that owns the feature. -/
structure Metadata where
  kind : MetadataKind
  owner : Name
  name : Name
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Construct a metadata entry from its feature and exact exported owner. -/
def Metadata.ofOwner (kind : MetadataKind) (owner : Name) : Metadata :=
  let name := match kind with
    | .unitlike => unitlikeName owner
    | .eta => etaName owner
    | .ruleK => ruleKName owner
  { kind, owner, name }

/-- One intrinsic structure field projection and its reduction theorem. -/
structure Projection where
  owner : Name
  fieldIndex : Nat
  name : Name
  iota : Name
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Construct the public projection slots for `owner`'s zero-based field. -/
def Projection.ofField (owner : Name) (fieldIndex : Nat) : Projection :=
  { owner, fieldIndex, name := projectionName owner fieldIndex,
    iota := projectionIotaName owner fieldIndex }

/-- The declaration-local public-name requirements for any collection of
inductive groups.  The table does not infer ownership from generated names;
the exact originals remain attached to every entry. -/
structure Table where
  declarations : Array Declaration := #[]
  iotas : Array Iota := #[]
  projections : Array Projection := #[]
  metadata : Array Metadata := #[]
  deriving BEq, Inhabited, Repr

/-- An empty set of public-name requirements. -/
def Table.empty : Table := {}

/-- Add an original declaration and its model declaration to a table. -/
def Table.addDeclaration (table : Table) (kind : DeclarationKind)
    (original : Name) : Table :=
  { table with declarations := table.declarations.push (.ofOriginal kind original) }

/-- Add a recursor and all its iota theorems in exported rule order. -/
def Table.addRecursor (table : Table) (recursor : Name) (numRules : Nat) : Table :=
  let table := table.addDeclaration .recursor recursor
  let rules := (List.range numRules).toArray.map (Iota.ofRecursor recursor)
  { table with iotas := table.iotas ++ rules }

/-- Add one metadata theorem requirement. -/
def Table.addMetadata (table : Table) (kind : MetadataKind) (owner : Name) : Table :=
  { table with metadata := table.metadata.push (.ofOwner kind owner) }

/-- Add an intrinsic projection and its reduction theorem together. -/
def Table.addProjection (table : Table) (owner : Name) (fieldIndex : Nat) : Table :=
  { table with projections := table.projections.push (.ofField owner fieldIndex) }

/-- Look up a model by exact original name and declaration role. -/
def Table.modelName? (table : Table) (kind : DeclarationKind) (original : Name) : Option Name :=
  (table.declarations.find? fun entry =>
    entry.kind == kind && entry.original == original).map (·.model)

/-- Look up an original by exact model name and declaration role.

This is a table lookup, not an attempt to parse `_model` from `model`. -/
def Table.originalName? (table : Table) (kind : DeclarationKind) (model : Name) : Option Name :=
  (table.declarations.find? fun entry =>
    entry.kind == kind && entry.model == model).map (·.original)

/-- Every public name required by the table, retaining requirement order and
duplicates.  Keeping duplicates lets the collision census diagnose a malformed
table instead of silently accepting it. -/
def Table.requiredNames (table : Table) : Array Name :=
  table.declarations.map (·.model) ++ table.iotas.map (·.name) ++
    table.projections.flatMap (fun projection => #[projection.name, projection.iota]) ++
    table.metadata.map (·.name)

private def pushUnique (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

/-- Exact-name conflicts discovered before generating a group.

`taken` lists required names that occur in the input. `duplicateRequirements`
lists names required more than once by the proposed table. Both arrays contain
each conflicting name once, in first-conflict order. -/
structure CollisionCensus where
  taken : Array Name := #[]
  duplicateRequirements : Array Name := #[]
  deriving BEq, Inhabited, Repr

/-- Whether an atomic generation request has any public-name conflict. -/
def CollisionCensus.isEmpty (census : CollisionCensus) : Bool :=
  census.taken.isEmpty && census.duplicateRequirements.isEmpty

private def Table.collisionCensusWhere (table : Table) (occupied : Name → Bool) :
    CollisionCensus := Id.run do
  let mut seen : Array Name := #[]
  let mut taken : Array Name := #[]
  let mut duplicateRequirements : Array Name := #[]
  for name in table.requiredNames do
    if occupied name then
      taken := pushUnique taken name
    if seen.contains name then
      duplicateRequirements := pushUnique duplicateRequirements name
    else
      seen := seen.push name
  return { taken, duplicateRequirements }

/-- Census exact public-name collisions against a small occupied array.

No private-name normalization and no `_model` prefix parsing is performed. -/
def Table.collisionCensus (table : Table) (occupied : Array Name) : CollisionCensus :=
  table.collisionCensusWhere occupied.contains

/-- Census exact public-name collisions directly against a reserved-name set.

This is the model-generation path: unlike array materialization, its cost does
not depend linearly on the file-wide set size. -/
def Table.collisionCensusReserved (table : Table) (reserved : Std.HashSet Name) :
    CollisionCensus :=
  table.collisionCensusWhere reserved.contains

/-- Census against a file-wide reserved set and a small independent helper set.

Keeping the sets separate matters: extending a retained file-wide `HashSet`
can copy its complete bucket array even when only a few helpers are added. -/
def Table.collisionCensusReservedWith (table : Table) (reserved helpers : Std.HashSet Name) :
    CollisionCensus :=
  table.collisionCensusWhere fun name => reserved.contains name || helpers.contains name

end InductiveModels.Naming
