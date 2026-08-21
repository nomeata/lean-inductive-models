import InductiveModels.Driver.Island
import InductiveModels.Cli

/-!
# An `Iso` as exact records

Whether generation is enabled at all, the exact generated blocks a composed
step may look a member up in, and [`serialiseIso`], which turns one completed
construction into the island's records and hands them to the observer.
-/

open Lean Meta

namespace InductiveModels

/-- Whether any model-generation branch is enabled. -/
def generationEnabled (generation : Cli.Config) : Bool :=
  generation.nested || generation.mutualModels || generation.simple || generation.basic

/-- Proof-value-free exact inductive records retained only until the
immediately following composed generation step. They still carry public types
and recursor RHS expressions. Every build member maps to exactly one raw,
pre-alias block; ambiguity is rejected while the snapshot is built. -/
structure ExactGeneratedBlocks where
  private byMember : Std.HashMap Name EDecl := {}

def ExactGeneratedBlocks.find? (blocks : ExactGeneratedBlocks) (member : Name) : Option EDecl :=
  blocks.byMember[member]?

def ExactGeneratedBlocks.require (blocks : ExactGeneratedBlocks) (member : Name) : MetaM EDecl := do
  let some block := blocks.find? member
    | throwError "exact generated block snapshot has no member {member}"
  return block

/-- Serialization result. `exactBlocks` and the island observation are
consumed inside the current island; neither is copied into output/report state. -/
structure SerialisedIso (α : Type) where
  records : Array EDecl
  exactBlocks : ExactGeneratedBlocks
  model : Iso
  observation? : Option α

/-- Read a generated model back from the construction environment, register
every name Lean minted for its inductive blocks, and serialize through exact
alias lookups. The returned `Iso` carries the completed alias and splice
witnesses used for reporting and shared-support persistence. -/
def serialiseIso (source : EDecl) (is : Iso)
    (exactTransform : EDecl → EDecl) (observer? : Option (IslandObserver α)) :
    MetaM (SerialisedIso α) := do
  -- The observation is caller scaffolding: nothing in serialization, route
  -- selection, rejection, or reporting reads it. It is therefore produced only
  -- when a caller supplies an observer, and the driver never learns what it is.
  let observation? ← match observer? with
    | some observe => pure (some (← observe source is))
    | none => pure none
  let mut rawRecords : Array EDecl := #[]
  for declaration in is.decls do
    rawRecords := rawRecords ++ (← toEDecls declaration)
  -- Test-facing transforms observe the same complete emitted-record boundary
  -- as the optional generated kernel gate, not just inductive blocks.
  rawRecords := rawRecords.map exactTransform
  let mut exactBlocks : ExactGeneratedBlocks := {}
  for record in rawRecords do
    if let .induct types _ _ := record then
      for type in types do
        if exactBlocks.byMember.contains type.name then
          throwError "generated member {type.name} occurs in several exact block snapshots"
        exactBlocks := { byMember := exactBlocks.byMember.insert type.name record }
  let names := rawRecords.flatMap fun record => record.names.toArray
  let aliases := is.aliases.register names
  let renamed := rawRecords.map (·.renameAliases aliases)
  let spliced := is.spliced.map fun name => aliases.exact name
  -- **Shared support opens the model's records.**
  --
  -- A model splices shared support where it first needs it, which can be
  -- behind an inductive the model itself generated — the composition's
  -- implementation tag and auxiliary, the carve arm's skeleton. Those inductives are
  -- declarations of the output like any other, so the simple route runs on
  -- them next and its island goes *in front of* the inductive it models. The
  -- support is already installed by then, so the second model splices nothing
  -- and simply names it — from a position ahead of where the record sits.
  -- `mutual_structure_projections`' `MLeft._model._impl.tag._model` naming
  -- `PSigma'` is the smallest instance, and the generated kernel gate replays
  -- the island in its emitted order and rejects it.
  --
  -- Shared support is exactly the closed prelude interface this tool writes,
  -- so it depends on nothing but itself and stays in the order it was spliced
  -- ([`InductiveModels.splicedSupportRecord`]: `ensureEq` before the tight pair
  -- that states its reduction rules at that `Eq`). Everything else keeps its
  -- constructive position. Support that a *previous* island spliced is already
  -- behind this one, and support the input itself declares is the input's own
  -- record at the input's own position; neither is moved here.
  let splicedNames := spliced.foldl (·.insert ·) ({} : Std.HashSet Name)
  let support := renamed.filter (splicedSupportRecord splicedNames)
  let ordered :=
    if support.isEmpty then renamed
    else support ++ renamed.filter (fun record => !splicedSupportRecord splicedNames record)
  -- `Iso` continues to name declarations in the disposable construction
  -- environment. Only serialized records take exact aliases; the completed
  -- map therefore remains available while the exact output identities of
  -- spliced support are recorded for persistence and reporting.
  let model := { is with aliases := aliases, spliced := spliced }
  return {
    records := ordered
    exactBlocks := exactBlocks
    model := model
    observation? }
