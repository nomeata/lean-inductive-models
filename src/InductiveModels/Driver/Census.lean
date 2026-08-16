import InductiveModels.Simple.Basis
import InductiveModels.Driver.Records
import InductiveModels.Order

/-!
# What the source export says about itself

A whole-input census taken before any generation: the collision-free replay
aliases, the roles each source declaration plays, and the derived questions a
run needs — duplicate declaration names, a model slot declared after its
owner, the family certificate records, and whether a record is the canonical
declaration of a basis owner.
-/

open Lean Meta

namespace InductiveModels

/-- Deterministic collision-free aliases from the complete source-name census.

Distinct public names never normalize alike, so a public member is the unique
preferred identity of its class.  A private-only class keeps its earliest raw
member exact.  Every other member is embedded below a public internal root
carrying its raw record and within-record position; the salt is used only when
an adversarial input already reserves that exact or normalized spelling. -/
private def sourceReplayAliasesFromSummaries
    (summaries : Array Order.DeclSummary) (reserved : Std.HashSet Name)
    (duplicate? : Option (Name × Nat × Nat)) :
    Except String SourceReplayAliases := do
  if let some (name, first, second) := duplicate? then
    throw s!"duplicate source declaration name {name} at {first} and {second}"
  -- Public names are their own normalized class and are already in `reserved`.
  -- Retain only the earliest private representative of private-only classes;
  -- this avoids another all-source-name map and occurrence array.
  let mut privateCanonical : Std.HashMap Name Name := {}
  for summary in summaries do
    for exact in summary.introduced do
      unless isPrivateName exact do continue
      let normalized := privateToUserName exact
      unless reserved.contains normalized || privateCanonical.contains normalized do
        privateCanonical := privateCanonical.insert normalized exact
  let mut hasMoved := false
  for summary in summaries do
    for exact in summary.introduced do
      if isPrivateName exact then
        let normalized := privateToUserName exact
        if reserved.contains normalized || privateCanonical[normalized]? != some exact then
          hasMoved := true
  unless hasMoved do
    return ← SourceReplayAliases.ofEntries #[]
  let mut root? : Option Name := none
  for salt in [:reserved.size + 1] do
    if root?.isSome then continue
    -- Sibling top-level components make the `reserved.size + 1` bound
    -- constructive: one reserved namespace can overlap at most one attempt.
    let candidate := Name.str .anonymous s!"_inductive_models_source_alias_{salt}"
    let overlaps := fun name : Name =>
      candidate.isPrefixOf name || name.isPrefixOf candidate
    unless reserved.any fun name => overlaps name || overlaps (privateToUserName name) do
      root? := some candidate
  let some root := root?
    | throw "source reserves every bounded collision-safe replay namespace"
  let mut entries : Array SourceReplayAlias := #[]
  for summary in summaries do
    for position in [:summary.introduced.size] do
      let exact := summary.introduced[position]!
      unless isPrivateName exact do continue
      let normalized := privateToUserName exact
      let keep := if reserved.contains normalized then normalized else
        privateCanonical[normalized]?.getD exact
      if exact == keep then continue
      let build := (Name.num (Name.num root summary.ordinal) position) ++ exact
      if isPrivateName build then
        throw s!"source replay alias {build} unexpectedly remains private"
      entries := entries.push { exact, build }
  SourceReplayAliases.ofEntries entries

/-- Value-free exact roles needed to derive construction aliases after a
declaration-discarding parse. -/
structure SourceReplayRoles where
  recursors : Array (Name × Option Name) := #[]
  quotients : Array Name := #[]

def SourceReplayRoles.push (roles : SourceReplayRoles) (declaration : EDecl) :
    SourceReplayRoles := match declaration with
  | .induct types _ recursors =>
    let derived := recursors.toArray.map fun recursor =>
      let owner? := types.foldl (init := none) fun best type =>
        if type.name.isPrefixOf recursor.name &&
            best.all (fun prior =>
              prior.name.components.length < type.name.components.length) then
          some type
        else best
      (recursor.name, owner?.map (·.name))
    { roles with recursors := roles.recursors ++ derived }
  | .quot name .. => { roles with quotients := roles.quotients.push name }
  | _ => roles

/-- Immutable source products accumulated declaration by declaration.  The
syntax index intentionally owns exact declaration types, constructor/owner
records, and transparent definition values. Summaries, reserved names and raw
ordinals do not retain complete `EDecl` values. -/
structure SourceCensus where
  sourceSyntax : Check.SyntaxIndex
  summaries : Array Order.DeclSummary
  reserved : Std.HashSet Name
  rawOrdinals : Std.HashMap Name Nat
  replayAliases : Except String SourceReplayAliases
  replayRoles : SourceReplayRoles
  private duplicate? : Option (Name × Nat × Nat)

/-- Single callback state for all raw-source products. -/
structure SourceCensus.Builder where
  private syntaxBuilder : Check.SyntaxIndex.Builder := {}
  private summaryBuilder : Order.SummaryBuilder := {}
  private reserved : Std.HashSet Name := {}
  private rawOrdinals : Std.HashMap Name Nat := {}
  private duplicate? : Option (Name × Nat × Nat) := none
  private replayRoles : SourceReplayRoles := {}
  private nextOrdinal : Nat := 0

/-- Accumulate one raw source declaration into every census axis. -/
def SourceCensus.Builder.push (builder : SourceCensus.Builder)
    (declaration : EDecl) : SourceCensus.Builder :=
  -- Consume the outer record before pushing onto either nested builder.  In
  -- particular, `SummaryBuilder` erases to its rows array; keeping `builder`
  -- live here would share that array and copy its complete prefix on every
  -- declaration.
  match builder with
  | { syntaxBuilder, summaryBuilder, reserved, rawOrdinals, duplicate?,
      replayRoles, nextOrdinal } =>
    let (duplicate?, _) := declaration.names.foldl
      (init := (duplicate?, ({} : Std.HashSet Name))) fun (duplicate?, seen) name =>
        let duplicate? := duplicate?.orElse fun _ =>
          if seen.contains name then some (name, nextOrdinal, nextOrdinal)
          else rawOrdinals[name]?.map fun first => (name, first, nextOrdinal)
        (duplicate?, seen.insert name)
    { syntaxBuilder := syntaxBuilder.push declaration
      summaryBuilder := summaryBuilder.push declaration
      reserved := declaration.names.foldl (·.insert ·) reserved
      rawOrdinals := declaration.names.foldl
        (fun ordinals name => ordinals.insert name nextOrdinal) rawOrdinals
      duplicate?
      replayRoles := replayRoles.push declaration
      nextOrdinal := nextOrdinal + 1 }

/-- Freeze all callback products while structurally sharing the one immutable
syntax index with the summary-family attachment pass. -/
def SourceCensus.Builder.freeze (builder : SourceCensus.Builder) : SourceCensus :=
  let sourceSyntax := builder.syntaxBuilder.freeze
  let summaries := builder.summaryBuilder.freeze sourceSyntax
  let replayAliases := sourceReplayAliasesFromSummaries summaries builder.reserved builder.duplicate?
  { sourceSyntax
    summaries
    reserved := builder.reserved
    rawOrdinals := builder.rawOrdinals
    replayAliases
    replayRoles := builder.replayRoles
    duplicate? := builder.duplicate? }

def SourceCensus.validateUniqueDeclarationNames (census : SourceCensus) : Except String Unit :=
  match census.duplicate? with
  | none => .ok ()
  | some (name, _, _) => .error s!"duplicate declaration {name}"

/-- Build one source census through declaration callbacks.  The last raw
ordinal for a duplicate name deliberately matches the historical Driver loop;
ordering still reports the duplicate before consuming that map. -/
def SourceCensus.ofSource (source : Export) : SourceCensus :=
  (source.decls.foldl (fun builder declaration => builder.push declaration)
    ({} : SourceCensus.Builder)).freeze

/-- **Is this input record the canonical basis declaration generation already
wrote at that name?**

Generation writes a small fixed set of declarations of its own: the four basis
inductives, `Nonempty`, `Iff`, the tight pair's six derived declarations, the
kernel quotient, `Quot.sound`, `Classical.choice` and `propext`. It writes each
at the first point one is needed, whatever the input reserves, so an island is
never emitted against a constant the output declares later.

That leaves exactly one question, and it is asked in exactly one place: when
the input's own record for such a name is reached, is it the declaration that
was already written? A record that passes carries no information the canonical
declaration does not, so dropping it changes nothing and it is dropped. A
record that does not pass is the input declaring *something else* under a basis
name; substituting this tool's declaration for it would silently re-point every
later record that referenced the input's own, so the run is rejected instead.

**A level-parameter name is not part of a declaration.** Lean states its own
`Eq` at `u_1` and this tool states `eqDecl` at `u`, so every comparison below
restates the installed declaration at the record's own level-parameter names
first — [`InductiveModels.alignBasisLevelParams`] for an inductive, and
`instantiateLevelParams` for everything else. Nothing else about the record is
allowed to differ.

**The non-inductive cases compare against the environment rather than against
a second mint**, because a second mint would be built in a *different*
environment: `hintsFor` reads the heights of the constants a value mentions,
and the tight pair's `rec'` mentions `PSigma'.fst` and `PSigma'.snd`, which by
this point are installed and were not when generation built it. The inductives
are minted, by exactly [`InductiveModels.validateBasisOwner`]'s comparison,
because an inductive record carries the kernel-derived recursor and carries no
hints for an environment to change. -/
def canonicalBasisRecordMatches (record : EDecl) : MetaM Bool := do
  let env ← getEnv
  match record with
  | .induct (type :: _) _ _ =>
    let some (_, canonical) := canonicalSpliceInductives.find? (·.1 == type.name)
      | return false
    isCanonicalInductiveRecord type.name canonical record
  | .quot .. => return installedQuotRecord env record
  | _ =>
    let some (name, levelParams) := (match record with
      | .ax name levelParams .. | .defn name levelParams .. | .thm name levelParams ..
      | .opaq name levelParams .. => some (name, levelParams)
      | _ => none) | return false
    let some info := env.constants.find? name | return false
    unless info.levelParams.length == levelParams.length do return false
    let levels := levelParams.map Level.param
    let restate := fun (e : Expr) => e.instantiateLevelParams info.levelParams levels
    let installed : Declaration ← match info with
      | .defnInfo value =>
        pure (.defnDecl { value with
          levelParams, type := restate value.type, value := restate value.value })
      | .thmInfo value =>
        pure (.thmDecl { value with
          levelParams, type := restate value.type, value := restate value.value })
      | .axiomInfo value =>
        pure (.axiomDecl { value with levelParams, type := restate value.type })
      | .opaqueInfo value =>
        pure (.opaqueDecl { value with
          levelParams, type := restate value.type, value := restate value.value })
      | _ => return false
    return record == (← toEDecl installed)

/-- One-pass model-before-owner guard for an input stream. Once an inductive
owner has appeared, any later record introducing one of that owner's exact
public model slots is too late. This intentionally performs no dependency
graph construction and never reorders the source. -/
def SourceCensus.modelAfterOwnerViolations (census : SourceCensus) :
    Array Check.Violation := Id.run do
  let mut expected : Std.HashMap Name (Array (Name × Nat)) := {}
  let mut violations : Array Check.Violation := #[]
  for recordIndex in [:census.summaries.size] do
    let summary := census.summaries[recordIndex]!
    for name in summary.introduced do
      for (owner, ownerIndex) in expected.getD name #[] do
        violations := violations.push
          (.modelNotBefore owner name recordIndex ownerIndex)
    if let some owner := summary.owner then
      for slot in summary.modelSlots do
        expected := expected.insert slot ((expected.getD slot #[]).push (owner, recordIndex))
  return violations

/-- Kernel recursor names are derived from their inductive type-former names,
not accepted as independent inputs to `Declaration.inductDecl`.  When a type
is moved for replay, register each exported recursor at the name the kernel
will actually mint. -/
def sourceReplayInductiveDerivations (roles : SourceReplayRoles)
    (initial : SourceReplayAliases) : Except String SourceReplayAliases := do
  let mut aliases := initial
  for (recursor, owner?) in roles.recursors do
    let some owner := owner? | do
      if aliases.hasExact recursor then
        throw s!"moved recursor {recursor} has no uniquely moved inductive owner"
      continue
    if !aliases.hasExact owner then
      if aliases.hasExact recursor then
        throw s!"moved recursor {recursor} belongs to unmoved owner {owner}"
      continue
    let some buildOwner := aliases.build? owner
      | throw "moved inductive owner lost its replay alias"
    let buildRecursor := recursor.replacePrefix owner buildOwner
    aliases ← aliases.replace recursor buildRecursor
  return aliases

/-- Build source-family certificate rows in raw declaration order. -/
def SourceCensus.familyCertificateRecords (census : SourceCensus)
    (source : Export) : Array (Array Check.CompactFamilyCertificate) := Id.run do
  let mut byOwner : Std.HashMap Name (Array Check.CompactFamilyCertificate) := {}
  for family in Check.discoverWithIndex source census.sourceSyntax do
    let certificate := Check.compactFamilyCertificateWithIndex source census.sourceSyntax family
    byOwner := byOwner.insert family.owner
      ((byOwner.getD family.owner #[]).push certificate)
  let mut rows := Array.replicate source.decls.size #[]
  for i in [0:source.decls.size] do
    if let .induct (type :: _) _ _ := source.decls[i]! then
      rows := rows.set! i (byOwner.getD type.name #[])
  return rows
