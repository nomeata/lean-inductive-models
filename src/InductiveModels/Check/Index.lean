import InductiveModels.Check.Rules
import InductiveModels.Check.Reference

/-!
# Reusable syntax tables, family discovery, and the whole-export check

[`SyntaxIndex`] builds every whole-export table once so each owner performs
only its local correspondence walk; its builder form is fed in declaration
order and never retains a recursor proof graph.  Family discovery, the
value-free global-extra sweep, and [`checkReport`] all consume that one index.
-/

open Lean

namespace InductiveModels.Check

def iotaSlot? (name : Name) : Option (Name × Nat) := do
  let .str parent suffix := name | none
  unless suffix.startsWith "iota_" do none
  return (parent, ← (suffix.drop 5).toNat?)

private def projectionSlot? (owner name : Name) : Option Nat := do
  let modelRoot := Naming.modelName owner
  match name with
  | .str parent suffix =>
    if parent == modelRoot && suffix.startsWith "proj_" then
      (suffix.drop 5).toNat?
    else if suffix == "iota" then
      let .str grandParent projectionSuffix := parent | none
      unless grandParent == modelRoot && projectionSuffix.startsWith "proj_" do none
      (projectionSuffix.drop 5).toNat?
    else none
  | _ => none

private abbrev IotaSlots := Lean.PersistentHashMap Name (Array (Name × Nat))

private def iotaSlots (x : Export) : IotaSlots := Id.run do
  let mut slots : IotaSlots := {}
  for declaration in x.decls do
    for name in declaration.names do
      if let some (parent, index) := iotaSlot? name then
        slots := slots.insert parent ((slots.findD parent #[]).push (name, index))
  return slots

/-- Reusable declaration-facing syntax tables for checking several model
families from the same source snapshot.  The expression graph is shared with
the export; constructing an index does not copy declaration bodies. -/
structure SyntaxIndex where
  private declarations : DeclarationTypes
  private constructors : Constructors
  private structures : StructureOwners
  private ruleSlots : IotaSlots
  private normalizer : ExactNormalizationEnv
  /-- Exact declaration-record occurrences in source order.  Keeping this in
  the shared index prevents family discovery from rebuilding a whole-export
  name table for every consumer. -/
  private records : Std.HashMap Name (Array Nat)
  /-- Sparse occurrences introduced in front of `records` by island overlays.
  Base occurrences are interpreted after `recordOffset`; keeping both axes
  separate avoids copying the whole source map whenever support is prepended.

  An overlay occurrence is stored *back-to-front*, as its distance
  `recordOffset - ordinal` from the front of the combined stream at the time it
  was prepended.  That distance is invariant under every later prepend, because
  a prepend of `k` records raises both `recordOffset` and the occurrence's
  ordinal by the same `k`.  Prepending support therefore only inserts the new
  names instead of rewriting every occurrence already recorded here, which is
  what keeps an overlaid index linear in the records it is handed rather than
  in the support accumulated by all earlier islands. -/
  private recordPrefix : Lean.PersistentHashMap Name (Array Nat) := {}
  private recordOffset : Nat := 0
  globalExtras : Array Violation := #[]
  private sourceFamilies : Std.HashMap Name (Array Family) := {}
  names : Lean.PersistentHashSet Name := {}

/-- Mutable construction state for an immutable [`SyntaxIndex`].  The builder
is fed in declaration order. It retains declaration-facing syntax tables plus
compact inductive owner seeds until `freeze`; recursor types/rule RHS graphs
and complete `EDecl` values die after each callback. -/
structure SyntaxIndex.Builder where
  private declarations : DeclarationTypes := {}
  private constructors : Constructors := {}
  private structures : StructureOwners := {}
  private ruleSlots : IotaSlots := {}
  private definitions : Std.HashMap Name ExactNormalizationDef := {}
  private records : Std.HashMap Name (Array Nat) := {}
  private names : Lean.PersistentHashSet Name := {}
  private owners : Array SourceFamilySeed := #[]
  private nextOrdinal : Nat := 0

/-- Add one exact export record to a syntax-index builder.  Duplicate handling
matches the historical whole-export prepasses: declaration types and record
occurrences append, constructor/structure tables keep the last occurrence,
and transparent normalization keeps the first definition. -/
def SyntaxIndex.Builder.push (builder : SyntaxIndex.Builder)
    (declaration : EDecl) : SyntaxIndex.Builder := Id.run do
  let ordinal := builder.nextOrdinal
  let mut declarations := builder.declarations
  for info in declTypes declaration do
    declarations := declarations.insert info.name
      ((declarations.findD info.name #[]).push info)
  let mut constructors := builder.constructors
  let mut structures := builder.structures
  let mut owners := builder.owners
  if let .induct types ctors _ := declaration then
    for ctor in ctors do constructors := constructors.insert ctor.name ctor
    for type in types do structures := structures.insert type.name (type, ctors)
    if let some owner := SourceFamilySeed.ofDeclaration? ordinal declaration then
      owners := owners.push owner
  let mut ruleSlots := builder.ruleSlots
  let mut records := builder.records
  let mut names := builder.names
  for name in declaration.names do
    if let some (parent, index) := iotaSlot? name then
      ruleSlots := ruleSlots.insert parent
        ((ruleSlots.findD parent #[]).push (name, index))
    records := records.insert name ((records.getD name #[]).push ordinal)
    names := names.insert name
  let mut definitions := builder.definitions
  if let .defn name levelParams _ value .. := declaration then
    unless definitions.contains name do
      definitions := definitions.insert name { levelParams, value }
  let builder := { builder with declarations := declarations }
  let builder := { builder with constructors := constructors }
  let builder := { builder with structures := structures }
  let builder := { builder with ruleSlots := ruleSlots }
  let builder := { builder with definitions := definitions }
  let builder := { builder with records := records }
  let builder := { builder with names := names }
  let builder := { builder with owners := owners }
  return { builder with nextOrdinal := ordinal + 1 }

/-- The exact syntax normalizer already retained by this index.  The returned
value structurally shares its definition table; consumers must reuse it rather
than rebuilding a second whole-export map. -/
def SyntaxIndex.exactNormalizer (index : SyntaxIndex) : ExactNormalizationEnv :=
  index.normalizer

/-- Replace the declaration-facing portion of a syntax index with an explicit
collision-free replay view while retaining exact source occurrence/family
certificates.

Only records which mention a moved source name need appear in `exactRecords` /
`replayRecords`.  The two arrays are positional pairs.  Updating persistent
hash maps here avoids rebuilding a second whole-source index for the rare
flattened-export normalized-name collision. -/
def SyntaxIndex.withReplayRecords (source : SyntaxIndex)
    (exactRecords replayRecords : Array EDecl) : Except String SyntaxIndex := do
  unless exactRecords.size == replayRecords.size do
    throw "replay syntax replacement arrays have different sizes"
  let mut declarations := source.declarations
  let mut constructors := source.constructors
  let mut structures := source.structures
  let mut normalizer := source.normalizer
  let mut names := source.names
  for ordinal in [:exactRecords.size] do
    let exact := exactRecords[ordinal]!
    let replay := replayRecords[ordinal]!
    unless exact.names.length == replay.names.length do
      throw s!"replay syntax replacement {ordinal} changed declaration arity"
    if exact matches .quot .. then
      unless replay matches .quot .. do
        throw s!"replay syntax replacement {ordinal} changed a quotient record's kind"
      unless exact.names == replay.names do
        throw s!"replay syntax replacement {ordinal} moved an atomic quotient role"
    for name in exact.names do
      declarations := declarations.erase name
      normalizer := normalizer.eraseDefinition name
    if let .induct types ctors _ := exact then
      for type in types do structures := structures.erase type.name
      for ctor in ctors do constructors := constructors.erase ctor.name
    for info in declTypes replay do
      declarations := declarations.insert info.name #[info]
      names := names.insert info.name
    if let .induct types ctors _ := replay then
      for ctor in ctors do constructors := constructors.insert ctor.name ctor
      for type in types do structures := structures.insert type.name (type, ctors)
    if let .defn name levelParams _ value .. := replay then
      normalizer := normalizer.insertDefinition name { levelParams, value }
  return { source with
    declarations, constructors, structures,
    normalizer, names }

private def declarationRecords (x : Export) : Std.HashMap Name (Array Nat) := Id.run do
  let mut records : Std.HashMap Name (Array Nat) := {}
  for i in [0:x.decls.size] do
    for name in x.decls[i]!.names do
      records := records.insert name ((records.getD name #[]).push i)
  return records

private def SyntaxIndex.coreOfExport (x : Export) : SyntaxIndex :=
  { declarations := declarationTypes x, constructors := constructorRecords x,
    structures := structureOwners x, ruleSlots := iotaSlots x,
    normalizer := x.exactNormalizationEnv, records := declarationRecords x,
    names := x.decls.foldl (fun names declaration =>
      declaration.names.foldl (·.insert ·) names) {} }

def checkFamilyWithIndex (x : Export) (index : SyntaxIndex)
    (family : Family) (checkOrder : Bool) : Array Violation := Id.run do
  let mut violations : Array Violation := #[]
  if checkOrder then
    for modelDecl in family.decls do
      unless modelDecl < family.ownerDecl do
        let declaration := x.decls[modelDecl]!
        for name in declaration.names do
          if let some owner := family.correspondence.originalOfPublic? name then
            violations := violations.push
              (.modelNotBefore owner name modelDecl family.ownerDecl)
    let targets := family.names.foldl (fun set name => set.insert name) ({} : Std.HashSet Name)
    if let some (owner, target) := ownerReference? targets x.decls[family.ownerDecl]! then
      violations := violations.push (.ownerBackreference owner target)
  for pair in family.correspondence.typeFormers do
    violations := violations ++ checkPair family.correspondence index.declarations pair
  for pair in family.correspondence.constructors do
    violations := violations ++ checkPair family.correspondence index.declarations pair
  for pair in family.correspondence.recursors do
    violations := violations ++ checkPair family.correspondence index.declarations pair
  let ownerTypes : Array EIndType := match x.decls[family.ownerDecl]! with
    | .induct types _ _ => types.toArray
    | _ => #[]
  let ownerConstructors : Array ECtor := match x.decls[family.ownerDecl]! with
    | .induct _ constructors _ => constructors.toArray
    | _ => #[]
  let ownerRecursors : Array ERec := match x.decls[family.ownerDecl]! with
    | .induct _ _ recursors => recursors.toArray
    | _ => #[]
  let mutualCertificate := phase1MutualOneLayerCertificate index.declarations
    ownerTypes ownerConstructors ownerRecursors index.normalizer family
  let certificates := ownerTypes.map fun ownerType =>
    let singleton := phase1OneLayerCertificate index.declarations ownerType
      ownerConstructors ownerRecursors family
    (ownerType.name, if singleton matches .absent then mutualCertificate else singleton)
  for (owner, certificate) in certificates do
    if let .malformed slot := certificate then
      violations := violations.push (.declarationType owner slot)
  for projection in family.correspondence.projections do
    let certificate := match certificates.find? fun entry => entry.1 == projection.owner with
      | some (_, .malformed _) => .absent
      | some (_, certificate) => certificate
      | none => .malformed projection.owner
    violations := violations ++ checkProjection
      x index.structures index.normalizer family index.declarations certificate projection
  for iota in family.correspondence.iotas do
    violations := violations ++ checkIota x index.constructors family index.declarations iota
  for metadata in family.correspondence.metadata do
    violations := violations ++ checkTheoremSlot
      index.declarations metadata.owner metadata.name
    if metadata.kind == .unitlike then
      violations := violations ++ checkUnitlike x family index.declarations metadata
    else if metadata.kind == .eta then
      violations := violations ++ checkEta
        x index.normalizer family index.declarations metadata
    else if metadata.kind == .ruleK then
      violations := violations ++ checkRuleK x family index.declarations metadata
  for pair in family.correspondence.recursors do
    let numRules := (family.correspondence.iotas.filter (·.recursor == pair.owner)).size
    for (name, ruleIndex) in index.ruleSlots.findD pair.model #[] do
      if ruleIndex >= numRules || name != Naming.iotaName pair.owner ruleIndex then
        violations := violations.push (.extraRule pair.owner name)
  return violations

/-- Whether this index already carries a declaration under `name`. -/
def SyntaxIndex.declares (index : SyntaxIndex) (name : Name) : Bool :=
  index.names.contains name

/-- Overlay an island in front of a persistent source index without rescanning
the source export. Any name collision fails closed before first/last-map
semantics could hide it. Declaration and rule arrays are prefixed, generated
transparent definitions win, and generated constructor/owner records extend
the source maps. Global extras remain a final-export concern and are
intentionally not recomputed here. -/
def SyntaxIndex.prependRecords (source : SyntaxIndex) (records : Array EDecl) :
    Except String SyntaxIndex := Id.run do
  let mut names := source.names
  for declaration in records do
    for name in declaration.names do
      if names.contains name then
        return .error s!"island overlay redeclares {name}"
      names := names.insert name
  let mut declarations := source.declarations
  let mut ruleSlots := source.ruleSlots
  for declaration in records.reverse do
    for info in (declTypes declaration).reverse do
      declarations := declarations.insert info.name
        (#[info] ++ declarations.findD info.name #[])
    for name in declaration.names.reverse do
      if let some (parent, index) := iotaSlot? name then
        ruleSlots := ruleSlots.insert parent
          (#[((name, index))] ++ ruleSlots.findD parent #[])
  let mut constructors := source.constructors
  let mut structures := source.structures
  for declaration in records do
    if let .induct types ctors _ := declaration then
      for constructor in ctors do
        unless source.constructors.contains constructor.name do
          constructors := constructors.insert constructor.name constructor
      for type in types do
        unless source.structures.contains type.name do
          structures := structures.insert type.name (type, ctors)
  let mut normalizer := source.normalizer
  for declaration in records.reverse do
    if let .defn name levelParams _ value .. := declaration then
      normalizer := normalizer.insertDefinition name { levelParams, value }
  -- `discoverWithIndex` may consume the resulting index together with the
  -- literal combined view `records ++ source`. Base source occurrences retain
  -- their map and acquire one offset; existing overlay occurrences are already
  -- stored as distances from the front and need no shift at all, so only the
  -- names this call introduces are inserted.
  -- Collision rejection above guarantees new prefix entries cannot hide one.
  let recordOffset := source.recordOffset + records.size
  let mut recordPrefix := source.recordPrefix
  for ordinal in [0:records.size] do
    for name in records[ordinal]!.names do
      recordPrefix := recordPrefix.insert name #[recordOffset - ordinal]
  return .ok {
    declarations := declarations
    constructors := constructors
    structures := structures
    ruleSlots := ruleSlots
    normalizer := normalizer
    records := source.records
    recordPrefix := recordPrefix
    recordOffset := recordOffset
    globalExtras := source.globalExtras
    sourceFamilies := source.sourceFamilies
    names := names }

/-- Fail-closed family templates for one owner from the persistent source
snapshot.  They are built once with the source `SyntaxIndex`; island checks do
not rediscover them by scanning the complete input. -/
def SyntaxIndex.sourceStatementFamilies (index : SyntaxIndex) (owner : Name) : Array Family :=
  index.sourceFamilies.getD owner #[]

private partial def projectionFieldEligibleWithIndex (index : SyntaxIndex)
    (ownerIsProp : Bool) (fieldIndex : Nat) (current : Expr)
    (locals : ExactLocals) : Option Bool := do
  let .forallE _ fieldType body _ := index.normalizer.whnf current | none
  let fieldIsProp := inferExactSortLevel? index.structures index.normalizer
    index.declarations locals fieldType == some .zero
  if fieldIndex == 0 then return !ownerIsProp || fieldIsProp
  if ownerIsProp && body.hasLooseBVars && !fieldIsProp then return false
  let value := mkFVar (FVarId.mk ((`_check.projectionField).mkNum locals.size))
  projectionFieldEligibleWithIndex index ownerIsProp (fieldIndex - 1)
    (body.instantiate1 value) (locals.push (value.fvarId!, fieldType))

private def intrinsicProjectionFieldsWithIndex (index : SyntaxIndex)
    (type : EIndType) (constructors : List ECtor) : Array Nat := Id.run do
  let [constructorName] := type.ctors | return #[]
  let some constructor := constructors.find? fun constructor =>
      constructor.name == constructorName && constructor.induct == type.name
    | return #[]
  let mut ownerType := type.type
  while ownerType.isForall do ownerType := ownerType.bindingBody!
  let ownerIsProp := index.normalizer.isPropositionFormer ownerType
  let mut current := constructor.type
  let mut locals : ExactLocals := #[]
  for parameterIndex in [:type.numParams] do
    let .forallE _ parameterType body _ := index.normalizer.whnf current | return #[]
    let value := mkFVar (FVarId.mk ((`_check.projectionParam).mkNum parameterIndex))
    locals := locals.push (value.fvarId!, parameterType)
    current := body.instantiate1 value
  let mut fields : Array Nat := #[]
  for fieldIndex in [:constructor.numFields] do
    if projectionFieldEligibleWithIndex index ownerIsProp fieldIndex current locals == some true then
      fields := fields.push fieldIndex
  return fields

/-- Kernel-valid intrinsic projection field indices using the syntax tables
already built for this export. Driver readiness checks use this query to avoid
reconstructing whole-export declaration and normalization maps per owner. -/
def SyntaxIndex.intrinsicProjectionFields (index : SyntaxIndex)
    (type : EIndType) (constructors : List ECtor) : Array Nat :=
  intrinsicProjectionFieldsWithIndex index type constructors

private def SyntaxIndex.recordOccurrences (index : SyntaxIndex) (name : Name) : Array Nat :=
  (index.recordPrefix.findD name #[]).map (fun distance => index.recordOffset - distance) ++
    (index.records.getD name #[]).map fun ordinal => index.recordOffset + ordinal

/-! ## Indexed family discovery

The historical discovery helper rebuilt the complete transparent-definition
and declaration-type tables once per inductive owner.  On a flattened export
that is quadratic in the number of records.  Discovery below consumes the one
shared syntax index instead: all whole-export tables are built once and each
owner performs only its local correspondence walk. -/

/-- Indexed core of family discovery. `includeEmpty root` retains an expected
family even when none of its public slots is declared. -/
private def discoverWithIndexWhere (x : Export) (index : SyntaxIndex)
    (includeEmpty : Name → Bool) : Array Family := Id.run do
  let mut families : Array Family := #[]
  for ownerDecl in [0:x.decls.size] do
    let declaration := x.decls[ownerDecl]!
    let .induct types _ _ := declaration | continue
    let some root := types.head?.map (·.name) | continue
    let some correspondence := correspondenceFor? index.normalizer
        (intrinsicProjectionFieldsWithIndex index) declaration
      | continue
    let publicNames := correspondence.publicNames
    unless includeEmpty root ||
        publicNames.any (fun name => !(index.recordOccurrences name).isEmpty) do continue
    -- Both accumulators below are order-preserving deduplications, and both
    -- historically answered their membership test by scanning what they had
    -- already accepted -- `Array.contains` here and [`appendUnique`] below.
    -- A hash set answers the same question without the scan, so one family
    -- costs its own occurrence and declaration-name count rather than their
    -- squares. The accepted arrays are unchanged, element for element.
    let mut modelDecls : Array Nat := #[]
    let mut seenDecls : Std.HashSet Nat := {}
    for name in publicNames do
      for i in index.recordOccurrences name do
        unless seenDecls.contains i do
          seenDecls := seenDecls.insert i
          modelDecls := modelDecls.push i
    modelDecls := modelDecls.qsort (· < ·)
    let mut modelNames : Array Name := #[]
    let mut seenNames : Std.HashSet Name := {}
    for i in modelDecls do
      for name in x.decls[i]!.names do
        unless seenNames.contains name do
          seenNames := seenNames.insert name
          modelNames := modelNames.push name
    let modelRoot := Naming.modelName root
    families := families.push
      { owner := root, modelRoot, carrier := modelRoot, ownerDecl, correspondence,
        decls := modelDecls, names := modelNames }
  return families

/-- Discover public model families using syntax tables already built for the
same export. This is the reusable production entry point for passes which need
both an index and family discovery. -/
def discoverWithIndex (x : Export) (index : SyntaxIndex) : Array Family :=
  discoverWithIndexWhere x index fun _ => false

/-- Discover public model families from exact names computed from each original
inductive record. One family covers each atomic owner record; a declaration
record introducing any exact public slot belongs to that family in its
entirety. -/
def discover (x : Export) : Array Family :=
  discoverWithIndex x (SyntaxIndex.coreOfExport x)

/-- Discover the exact generated-family view, retaining a requested owner even
when every public model slot is absent. -/
def statementFamiliesForWithIndex (x : Export) (index : SyntaxIndex)
    (owners : Std.HashSet Name) : Array Family :=
  (discoverWithIndexWhere x index owners.contains).filter fun family =>
    owners.contains family.owner

def statementFamiliesFor (x : Export) (owners : Std.HashSet Name) : Array Family :=
  statementFamiliesForWithIndex x (SyntaxIndex.coreOfExport x) owners

private def sourceFamilyTable (families : Array Family) : Std.HashMap Name (Array Family) :=
  families.foldl (init := {}) fun table family =>
    let template := { family with decls := #[], names := #[] }
    table.insert family.owner ((table.getD family.owner #[]).push template)

/-- Freeze declaration callbacks into one immutable source syntax index.
Owner templates are computed from compact seeds after the complete transparent
normalizer exists; no full inductive record or recursor proof graph survives
the declaration callback. -/
def SyntaxIndex.Builder.freeze (builder : SyntaxIndex.Builder) : SyntaxIndex := Id.run do
  let index : SyntaxIndex :=
    { declarations := builder.declarations
      constructors := builder.constructors
      structures := builder.structures
      ruleSlots := builder.ruleSlots
      normalizer := { definitions := builder.definitions }
      records := builder.records
      names := builder.names }
  let mut families : Array Family := #[]
  for owner in builder.owners do
    let correspondence := correspondenceForParts index.normalizer
      (intrinsicProjectionFieldsWithIndex index) owner.types owner.ctors owner.recursors
    let modelRoot := Naming.modelName owner.root
    families := families.push
      { owner := owner.root, modelRoot, carrier := modelRoot,
        ownerDecl := owner.ownerDecl, correspondence
        decls := #[], names := #[] }
  return { index with sourceFamilies := sourceFamilyTable families }

/-- Incremental source-index construction.  This is intentionally separate
from `ofSource` during the migration so property tests retain the old
whole-export implementation as an independent reference. -/
def SyntaxIndex.ofSourceIncremental (x : Export) : SyntaxIndex :=
  (x.decls.foldl (fun builder declaration => builder.push declaration)
    ({} : SyntaxIndex.Builder)).freeze

/-- Build persistent generation-time source tables without the final
unexpected-slot sweep. Every owner template is attached after indexed
discovery, breaking the former per-owner whole-export reconstruction. -/
def SyntaxIndex.ofSource (x : Export) : SyntaxIndex :=
  let index := SyntaxIndex.coreOfExport x
  let families := discoverWithIndexWhere x index fun _ => true
  { index with sourceFamilies := sourceFamilyTable families }

/-! ## Value-free global-extra summaries

The whole-export unexpected-slot sweep historically revisits every owner
record after generation. Compact no-output modes cannot retain generated
`EDecl`s just for that pass, so record the eligibility decisions while each
owner is live.
These summaries contain names, field indices, and booleans only; in
particular, they cannot retain an island's expression graph.

The outer array returned by `globalExtraRecordsWithIndex` remains aligned with
its input records, including non-inductive records. Each element binds the
introduced names to its templates so a caller cannot reorder one axis without
the other. A compact final ordering may therefore permute these records with
the same locators it uses for declaration records. -/

/-- One owner-local decision needed by the unexpected public-slot sweep. -/
inductive GlobalExtraTemplate where
  | type (owner : Name) (validProjectionFields : Array Nat)
      (allowsUnitlike allowsEta : Bool)
  | recursor (owner : Name) (allowsRuleK : Bool)
  deriving Inhabited, Repr, BEq

/-- Names and owner decisions captured atomically for one export record. -/
structure GlobalExtraRecord where
  names : Array Name
  templates : Array GlobalExtraTemplate
  deriving Inhabited, Repr, BEq

def GlobalExtraTemplate.owner : GlobalExtraTemplate → Name
  | .type owner .. | .recursor owner .. => owner

/-- Capture unexpected-slot eligibility for each record without retaining an
`Expr`.  Projection eligibility and proposition-former tests use the supplied
overlay index, so generated owners may depend on transparent source aliases.
Duplicate owner declarations must be rejected by compact ordering before
capture; the index's owner table is not a
substitute for that collision check. -/
def globalExtraRecordsWithIndex (index : SyntaxIndex)
    (records : Array EDecl) : Array GlobalExtraRecord :=
  records.map fun declaration => match declaration with
    | .induct types constructors recursors =>
      { names := declaration.names.toArray
        templates := types.toArray.map (fun type =>
          .type type.name (intrinsicProjectionFieldsWithIndex index type constructors)
            (type.isKernelUnitlike constructors)
            (type.isKernelStructureLike constructors &&
              !index.normalizer.isPropositionFormer type.type)) ++
        recursors.toArray.map fun recursor => .recursor recursor.name recursor.k }
    | _ => { names := declaration.names.toArray, templates := #[] }

/-- Recover the modeled-type root and field index from either spelling counted
by [`projectionSlot?`].  Indexing by the already-modeled root avoids repeating
the full declaration-name scan for every inductive type while retaining each
name's original position and multiplicity. -/
private def projectionSlotRoot? (name : Name) : Option (Name × Nat) := do
  match name with
  | .str parent suffix =>
    if suffix.startsWith "proj_" then
      return (parent, ← (suffix.drop 5).toNat?)
    else if suffix == "iota" then
      let .str grandParent projectionSuffix := parent | none
      unless projectionSuffix.startsWith "proj_" do none
      return (grandParent, ← (projectionSuffix.drop 5).toNat?)
    else
      none
  | _ => none

/-- Reproduce the historical global-extra diagnostic order from value-free
records in final order. The flattened names deliberately remain an array:
repeated slot names retain projection-diagnostic order and multiplicity, while
a local set answers metadata presence queries. -/
def globalExtrasFromRecords (records : Array GlobalExtraRecord) : Array Violation := Id.run do
  let orderedNames := records.flatMap (·.names)
  let declared := orderedNames.foldl (fun names name => names.insert name)
    ({} : Std.HashSet Name)
  let projectionSlots := orderedNames.foldl (init :=
      ({} : Std.HashMap Name (Array (Name × Nat)))) fun slots name =>
    match projectionSlotRoot? name with
    | none => slots
    | some (root, fieldIndex) =>
      slots.insert root ((slots.getD root #[]).push (name, fieldIndex))
  let mut violations : Array Violation := #[]
  for record in records do
    for template in record.templates do
      match template with
      | .type owner validFields allowsUnitlike allowsEta =>
        for (name, fieldIndex) in projectionSlots.getD (Naming.modelName owner) #[] do
          unless validFields.contains fieldIndex do
            violations := violations.push (.extraProjection owner name)
        unless allowsUnitlike do
          let name := Naming.unitlikeName owner
          if declared.contains name then
            violations := violations.push (.extraMetadata owner name .unitlike)
        unless allowsEta do
          let name := Naming.etaName owner
          if declared.contains name then
            violations := violations.push (.extraMetadata owner name .eta)
      | .recursor owner allowsRuleK =>
        unless allowsRuleK do
          let name := Naming.ruleKName owner
          if declared.contains name then
            violations := violations.push (.extraMetadata owner name .ruleK)
  return violations

/-- Build all reusable syntax tables, including the whole-export unexpected
slot sweep. Family discovery and projection eligibility share the same index;
the global sweep uses the linear name index above rather than rescanning the
complete declaration stream for every inductive owner. -/
def SyntaxIndex.ofExport (x : Export) : SyntaxIndex :=
  let index := SyntaxIndex.ofSource x
  { index with globalExtras :=
      globalExtrasFromRecords (globalExtraRecordsWithIndex index x.decls) }

/-- Attach the whole-export unexpected-slot sweep to an already complete
overlay. The caller is responsible for having overlaid every declaration not
present in the source snapshot. -/
def SyntaxIndex.withGlobalExtras (x : Export) (index : SyntaxIndex) : SyntaxIndex :=
  { index with globalExtras :=
      globalExtrasFromRecords (globalExtraRecordsWithIndex index x.decls) }

/-- Restrict the expensive unexpected-slot sweep to selected diagnostic
owners before any template scans the complete final name array. Names from
unselected records remain visible because a selected owner's unexpected public
slot may be introduced anywhere in the final stream. This is exactly the
historical late violation filter, but avoids work for unrelated owners. -/
def globalExtrasFromRecordsFor (records : Array GlobalExtraRecord)
    (owners : Std.HashSet Name) : Array Violation :=
  globalExtrasFromRecords <| records.map fun record =>
    { record with templates := record.templates.filter fun template =>
        owners.contains template.owner }

/-- Convenience form for an in-memory export. Compact callers instead retain
the bound per-record summaries and reorder them with compact declaration
locators before calling `globalExtrasFromRecords`. -/
def compactGlobalExtrasWithIndex (index : SyntaxIndex) (records : Array EDecl) :
    Array Violation :=
  globalExtrasFromRecords (globalExtraRecordsWithIndex index records)

/-- Discover selected families whose owner records belong to one generated
island, using its overlay for transparent aliases and projection eligibility.
Declaration indices are island-local; statement checking never interprets
them as positions in the source export. -/
def statementFamiliesForRecordsWithIndex (island : Export) (index : SyntaxIndex)
    (owners : Std.HashSet Name) : Array Family := Id.run do
  let mut families : Array Family := #[]
  for ownerDecl in [0:island.decls.size] do
    let .induct types _ _ := island.decls[ownerDecl]! | continue
    let some root := types.head?.map (·.name) | continue
    unless owners.contains root do continue
    let some correspondence := correspondenceFor? index.normalizer
        (intrinsicProjectionFieldsWithIndex index) island.decls[ownerDecl]!
      | continue
    families := families.push
      { owner := root, modelRoot := Naming.modelName root,
        carrier := Naming.modelName root, ownerDecl, correspondence,
        decls := #[], names := #[] }
  return families

def checkFamiliesWithIndex (x : Export) (index : SyntaxIndex)
    (families : Array Family) (checkOrder : Bool) : Array Violation :=
  families.foldl (fun violations family =>
      violations ++ checkFamilyWithIndex x index family checkOrder) #[] ++
    index.globalExtras

private def checkFamilies (x : Export) (families : Array Family)
    (checkOrder : Bool) : Array Violation :=
  checkFamiliesWithIndex x (.ofExport x) families checkOrder

/-- Check order, independence, and every exact public declaration and statement,
and report the exact number of model families inspected.  All comparisons are
literal after positional universe alignment and the one simultaneous
declaration-name substitution. -/
def checkReport (x : Export) : Report :=
  let index := SyntaxIndex.ofExport x
  let families := discoverWithIndex x index
  { familiesChecked := families.size,
    violations := checkFamiliesWithIndex x index families true }

end InductiveModels.Check
