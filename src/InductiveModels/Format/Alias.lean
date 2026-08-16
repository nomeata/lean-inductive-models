import InductiveModels.Format.Types
/-!
# Collision-safe source replay aliases

The explicit, injective exact-name/build-name table used while generating
models, and the record transforms in both directions. Only the record types are
needed here, so this module is a leaf beside the parser and the writer.
-/
open Lean

namespace InductiveModels

/-! ## Collision-safe source replay names

`Lean.Environment` indexes locally replayed constants by
`privateToUserName`.  A flattened export legitimately contains distinct
module-private constants with the same user spelling, so that index cannot
represent every exact source name.  The kernel can: this table is only the
injective build-name view used while generating models.  Source records and
serialized output always retain the exact names in the right-hand column.
-/

/-- One exact source name and its collision-free build name. -/
structure SourceReplayAlias where
  exact : Name
  build : Name
  deriving Inhabited, Repr, BEq

/-- Explicit whole-name aliases for the source replay environment.

There is deliberately no namespace or suffix fallback.  Every changed name
comes from the complete source-name census, and every inverse rewrite is the
same finite table in the opposite direction. -/
structure SourceReplayAliases where
  entries : Array SourceReplayAlias := #[]
  private forward : Std.HashMap Name Name := {}
  private inverse : Std.HashMap Name Name := {}
  deriving Inhabited

/-- Construct and validate both directions of an explicit alias table. -/
def SourceReplayAliases.ofEntries (entries : Array SourceReplayAlias) :
    Except String SourceReplayAliases := do
  let mut forward : Std.HashMap Name Name := {}
  let mut inverse : Std.HashMap Name Name := {}
  for entry in entries do
    if let some first := forward[entry.exact]? then
      throw s!"source replay name {entry.exact} has aliases {first} and {entry.build}"
    if let some first := inverse[entry.build]? then
      throw s!"source replay alias {entry.build} represents {first} and {entry.exact}"
    forward := forward.insert entry.exact entry.build
    inverse := inverse.insert entry.build entry.exact
  return { entries, forward, inverse }

def SourceReplayAliases.isEmpty (aliases : SourceReplayAliases) : Bool :=
  aliases.entries.isEmpty

def SourceReplayAliases.build? (aliases : SourceReplayAliases) (exact : Name) : Option Name :=
  aliases.forward[exact]?

def SourceReplayAliases.exact? (aliases : SourceReplayAliases) (build : Name) : Option Name :=
  aliases.inverse[build]?

def SourceReplayAliases.hasExact (aliases : SourceReplayAliases) (exact : Name) : Bool :=
  aliases.forward.contains exact

def SourceReplayAliases.buildName (aliases : SourceReplayAliases) (exact : Name) : Name :=
  aliases.build? exact |>.getD exact

def SourceReplayAliases.exactName (aliases : SourceReplayAliases) (build : Name) : Name :=
  aliases.exact? build |>.getD build

private def longestAliasPrefix? (entries : Array SourceReplayAlias)
    (name : Name) (buildSide : Bool) : Option SourceReplayAlias :=
  entries.foldl (init := none) fun best entry =>
    let rolePrefix := if buildSide then entry.build else entry.exact
    if rolePrefix.isPrefixOf name &&
        best.all (fun prior =>
          (if buildSide then prior.build else prior.exact).components.length <
            rolePrefix.components.length) then
      some entry
    else best

/-- Rewrite a name below an explicitly aliased source role.  This is used only
to register concrete generated names; record serialization still performs
whole-name table lookup. -/
def SourceReplayAliases.exactDerivedName (aliases : SourceReplayAliases) (build : Name) : Name :=
  match longestAliasPrefix? aliases.entries build true with
  | some entry => build.replacePrefix entry.build entry.exact
  | none => build

def SourceReplayAliases.buildDerivedName (aliases : SourceReplayAliases) (exact : Name) : Name :=
  match longestAliasPrefix? aliases.entries exact false with
  | some entry => exact.replacePrefix entry.exact entry.build
  | none => exact

/-- Every construction spelling induced by an explicit source-role prefix.
Reserved-name guards need all of them, not merely the longest match: an exact
source declaration can itself be moved while also lying below a moved owner. -/
def SourceReplayAliases.buildDerivedNames (aliases : SourceReplayAliases) (exact : Name) :
    Array Name :=
  aliases.entries.filterMap fun entry =>
    if entry.exact.isPrefixOf exact then some (exact.replacePrefix entry.exact entry.build)
    else none

/-- Remove construction-only source identities from a diagnostic string. -/
def SourceReplayAliases.exactMessage (aliases : SourceReplayAliases) (message : String) : String :=
  (aliases.entries.qsort fun left right =>
    left.build.components.length > right.build.components.length).foldl (fun message entry =>
    message.replace entry.build.toString entry.exact.toString) message

/-- Replace one source role while deriving the atomic kernel replay plan. -/
def SourceReplayAliases.replace (aliases : SourceReplayAliases) (exact build : Name) :
    Except String SourceReplayAliases :=
  SourceReplayAliases.ofEntries <|
    if aliases.entries.any (fun entry => entry.exact == exact) then
      aliases.entries.map fun entry => if entry.exact == exact then { exact, build } else entry
    else aliases.entries.push { exact, build }

/-- Register a newly discovered generated name without changing an existing
exact identity. Conflicting registrations fail closed. -/
def SourceReplayAliases.insert (aliases : SourceReplayAliases) (exact build : Name) :
    Except String SourceReplayAliases :=
  match aliases.build? exact with
  | some prior =>
    if prior == build then .ok aliases
    else .error s!"generated exact name {exact} maps to both {prior} and {build}"
  | none => SourceReplayAliases.ofEntries (aliases.entries.push { exact, build })

/-- Explicitly register every generated declaration name lying below a moved
source role. References are then covered because a valid generated record can
refer only to source constants or declarations introduced by its island. -/
def SourceReplayAliases.registerRecords (aliases : SourceReplayAliases)
    (records : Array EDecl) : Except String SourceReplayAliases := do
  let mut result := aliases
  for record in records do
    for build in record.names do
      let exact := aliases.exactDerivedName build
      if exact != build then
        result ← result.insert exact build
  return result

/-- Rename an exact source/output record into the collision-free replay view. -/
def SourceReplayAliases.buildRecord (aliases : SourceReplayAliases) : EDecl → EDecl :=
  EDecl.mapNames aliases.buildName
    (mapConstsE fun name => aliases.build? name)

/-- Return a generated build record to the exact source/output view. -/
def SourceReplayAliases.exactRecord (aliases : SourceReplayAliases) : EDecl → EDecl :=
  EDecl.mapNames aliases.exactName
    (mapConstsE fun name => aliases.exact? name)

/-- Generated-record audit transform for construction identities below an
aliased source role. Unlike `exactRecord`, this follows role prefixes and is
therefore deliberately confined to the post-generation release invariant. -/
def SourceReplayAliases.exactDerivedRecord (aliases : SourceReplayAliases) : EDecl → EDecl :=
  EDecl.mapNames aliases.exactDerivedName
    (mapConstsE fun name =>
      let exact := aliases.exactDerivedName name
      if exact == name then none else some exact)

end InductiveModels
