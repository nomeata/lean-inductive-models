import InductiveModels.Check.Index

/-!
# Name-only compact certificates

Once compact ordering succeeds, model records precede their owners and the
structural pass can release declarations and expression graphs.  A certificate
retains the names, owner-reference trace, and family-local violations captured
while the family was live, and [`compactOrderedReport`] finishes the report
from those alone.

That form still consumes an array of every record. Generation has no such
array — it emits a record and releases it — so [`CompactStream`] produces the
same report as a fold: each record is checked as it arrives and the pending
tables that made the answer possible are dropped at the record which declares
their root.
-/

open Lean

namespace InductiveModels.Check

/-! ## Compact output certificates

Once compact ordering succeeds, model records precede their owners. An owner
reference to a model name reinforces that order rather than forming a cycle,
so the exact ordered owner-reference trace is retained as well. The remaining
compact structural pass can therefore release declarations and expression graphs.
-/

/-- Name-only compact certificate captured while one family's source and model
declarations are live. `localViolations` excludes order/backreference checks
and the final stream-level extra-rule census. -/
structure CompactFamilyCertificate where
  owner : Name
  publicNames : Array Name
  /-- Exact `(original, public)` pairs used to reproduce source-order
  diagnostics after the source declarations themselves have been released. -/
  publicOwners : Array (Name × Name)
  ownerReferences : Array (Name × Name)
  localViolations : Array Violation
  recursors : Array (Name × Name × Nat)
  deriving Inhabited, Repr, BEq

private def notExtraRule : Violation → Bool
  | .extraRule .. => false
  | _ => true

/-- Capture one family through the exact syntax index used for its local
structural check. The recursor tuples are `(owner, model, validRuleCount)`. -/
def compactFamilyCertificateWithIndex (x : Export) (index : SyntaxIndex)
    (family : Family) : CompactFamilyCertificate :=
  { owner := family.owner
    publicNames := family.correspondence.publicNames
    publicOwners := family.correspondence.publicNames.filterMap fun publicName =>
      family.correspondence.originalOfPublic? publicName |>.map fun owner => (owner, publicName)
    ownerReferences := ownerReferenceCertificate x.decls[family.ownerDecl]!
    localViolations :=
      (checkFamilyWithIndex x index family false).filter notExtraRule
    recursors := family.correspondence.recursors.map fun pair =>
      (pair.owner, pair.model,
        (family.correspondence.iotas.filter (·.recursor == pair.owner)).size) }

/-- Bind selected family certificates to their owner records. Empty rows are
retained so this array can be permuted with declaration summaries and byte
locators without a separate owner/name lookup. -/
def compactFamilyCertificateRecordsWithIndex (x : Export) (index : SyntaxIndex)
    (families : Array Family) : Array (Array CompactFamilyCertificate) := Id.run do
  let mut records := Array.replicate x.decls.size #[]
  for family in families do
    if family.ownerDecl < records.size then
      records := records.modify family.ownerDecl (·.push
        (compactFamilyCertificateWithIndex x index family))
  return records

/-- Capture every currently discoverable family in owner-record order. This is
the full-export convenience form; compact generation captures source and island
families separately through `compactFamilyCertificateWithIndex`. -/
def compactFamilyCertificates (x : Export) : Array CompactFamilyCertificate :=
  let index := SyntaxIndex.ofSource x
  (discoverWithIndex x index).map (compactFamilyCertificateWithIndex x index)

/-- One final record's global-extra template and family certificates. Keeping
the fields bound makes it possible to reject a certificate attached to a row
other than its exact owner record. -/
structure CompactCheckRecord where
  owner : Option Name := none
  modelSlots : Array Name := #[]
  globalExtra : GlobalExtraRecord
  families : Array CompactFamilyCertificate := #[]
  deriving Inhabited, Repr, BEq

/-- Finish the structural report from final ordered names and family-local
certificates. The caller must already have proved compact dependency/model
ordering; that proof excludes the two order-only violation classes omitted by
the certificates.

This is the retained-row form, kept as the in-memory oracle an already ordered
export is compared against ([`compactOrderedCheckReport`]). Generation itself
does not build this array: it produces the same report as a fold over the
stream, through [`CompactStream`] below. -/
private def compactReport (records : Array CompactCheckRecord) :
    Except String Report := do
  let orderedGlobals := records.map (·.globalExtra)
  let orderedNames := orderedGlobals.flatMap (·.names)
  let mut declared : Std.HashSet Name := {}
  -- Every declared name is bound to the record that declares it.  The
  -- duplicate rejection in this same pass makes that binding single-valued, so
  -- the family-name union below can look a name up instead of re-walking every
  -- record.
  let mut declaringSlot : Std.HashMap Name Nat := {}
  for recordIndex in [:records.size] do
    let record := records[recordIndex]!
    for name in record.globalExtra.names do
      if declared.contains name then
        throw s!"duplicate compact declaration name {name}"
      declared := declared.insert name
      declaringSlot := declaringSlot.insert name recordIndex
  let ruleSlots := orderedNames.foldl (init :=
      ({} : Std.HashMap Name (Array (Name × Nat)))) fun slots name =>
    match iotaSlot? name with
    | none => slots
    | some (parent, ruleIndex) =>
      slots.insert parent ((slots.getD parent #[]).push (name, ruleIndex))
  let mut familiesChecked := 0
  let mut violations : Array Violation := #[]
  let mut certifiedOwners : Std.HashSet Name := {}
  for recordIndex in [:records.size] do
    let record := records[recordIndex]!
    if record.families.size > 1 then
      throw s!"compact owner record {record.owner} carries {record.families.size} family certificates"
    for family in record.families do
      unless record.owner == some family.owner do
        throw s!"compact family certificate for {family.owner} is not bound to its owner record"
      if certifiedOwners.contains family.owner then
        throw s!"duplicate compact family certificate for {family.owner}"
      certifiedOwners := certifiedOwners.insert family.owner
      unless family.publicNames.any declared.contains do continue
      familiesChecked := familiesChecked + 1
      -- `appendUnique` over each public slot's whole declaring record, without
      -- the quadratic membership scan and without revisiting a record already
      -- contributed by an earlier slot: a repeat contributes nothing new
      -- because record names are globally unique.
      let mut familyNames : Array Name := #[]
      let mut familyNameSet : Std.HashSet Name := {}
      let mut familyRecords : Std.HashSet Nat := {}
      for publicName in family.publicNames do
        if let some declIndex := declaringSlot[publicName]? then
          unless familyRecords.contains declIndex do
            familyRecords := familyRecords.insert declIndex
            for name in records[declIndex]!.globalExtra.names do
              unless familyNameSet.contains name do
                familyNameSet := familyNameSet.insert name
                familyNames := familyNames.push name
      if let some (owner, target) :=
          ownerBackreferenceFromCertificate? family.ownerReferences familyNames then
        violations := violations.push (.ownerBackreference owner target)
      violations := violations ++ family.localViolations
      for (owner, model, validRules) in family.recursors do
        for (name, ruleIndex) in ruleSlots.getD model #[] do
          if ruleIndex >= validRules || name != Naming.iotaName owner ruleIndex then
            violations := violations.push (.extraRule owner name)
    if record.modelSlots.any declared.contains && record.families.isEmpty then
      throw s!"compact owner record {record.owner} has declared model slots but no family certificate"
  violations := violations ++ globalExtrasFromRecords orderedGlobals
  return { familiesChecked, violations }

/-- Finish an already dependency/model-ordered compact output report. -/
def compactOrderedReport (records : Array CompactCheckRecord) : Except String Report :=
  compactReport records

/-! ## The same report, as a fold

[`compactReport`] is a pass over retained rows: it builds whole-stream name,
slot and record tables first and only then walks the families. The generation
loop has no such array — it sees one record at a time and releases it — so the
same report is produced here by [`CompactStream.push`], one record at a time,
and finished by [`CompactStream.finish`].

**Nothing is revisited.** Each record is charged for its own names, its own
family certificate and its own owner templates as it arrives, and the pending
tables that made those answers possible are dropped again at the record which
declares their root. What survives to the end is a name census (duplicate
rejection has no smaller witness), one small template per inductive owner, and
the violations themselves.

**The three axes that genuinely look forward**, and what each becomes:

* *A model slot declared after its owner.* Under compact order every model
  record precedes its owner, so at the owner this is a membership test against
  the names already seen. A slot the owner expects and the stream has not
  declared becomes a watch in `lateSlots`; the record that eventually declares
  it reports `modelNotBefore` there and then. This is the only class whose
  diagnostics can be emitted at a different position than the retained-row pass
  would place them, and it is exactly the class the pipeline rejects in the
  input before generation begins.
* *An unexpected metadata or projection slot declared after its owner.* This one
  is irreducibly deferred: `T._model.unitlike` is not part of any family's
  expected interface, so the model-order check above cannot see it. The owner's
  template is therefore kept in `deferredTemplates`, keyed by the owner it
  names, and later names are tested against it. That is a bounded per-owner
  map, not a retained record: the template is names, field indices and three
  booleans.
* *The relative order of global-extra diagnostics.* The retained-row pass emits
  them owner by owner after every family violation, so a deferred one has to
  land back at its owner's position. Each carries the
  [`GlobalExtraSlot`] it would have occupied and they are ordered once at
  `finish`. -/

/-- The parent of the last `_model` component of `name`, if it has one.

Every public model slot is `X._model` or `X._model.<suffix>` for an `X` the
owner record itself declares ([`InductiveModels.Naming`]), so this recovers
the declaration a slot-shaped name belongs to. The *last* component is the one
taken, which keeps a model of a name that already contains `_model` — the
generated implementation tags do — pointing at its own owner. -/
def modelSlotRoot? : Name → Option Name
  | .str parent suffix => if suffix == "_model" then some parent else modelSlotRoot? parent
  | .num parent _ => modelSlotRoot? parent
  | .anonymous => none

/-- The position one global-extra diagnostic occupies in the retained-row
sweep: its owner record, that record's template, the class of slot, and the
declaring name's ordinal in the flat name stream. A diagnostic discovered after
its owner record has passed is ordered by this and by nothing else. -/
structure GlobalExtraSlot where
  record : Nat
  template : Nat
  /-- `0` projections and rule K, `1` unit-like, `2` eta — the order in which
  one `.type` template reports its own slots. -/
  rank : Nat
  ordinal : Nat
  deriving Inhabited, Repr, BEq

def GlobalExtraSlot.before (left right : GlobalExtraSlot) : Bool :=
  if left.record != right.record then left.record < right.record
  else if left.template != right.template then left.template < right.template
  else if left.rank != right.rank then left.rank < right.rank
  else left.ordinal < right.ordinal

/-- Everything the compact structural report still needs to know once a record
has been consumed and released. -/
structure CompactStream where
  /-- The index the next record will take. -/
  recordIndex : Nat := 0
  /-- The flat ordinal the next declared name will take. -/
  nameOrdinal : Nat := 0
  familiesChecked : Nat := 0
  /-- Every declared name. Duplicate rejection has no smaller witness than the
  complete census, so this is the one table that necessarily spans the run. -/
  declared : Std.HashSet Name := {}
  /-- Owners whose family certificate has been consumed. -/
  certifiedOwners : Std.HashSet Name := {}
  /-- Family diagnostics, already in their final order. -/
  violations : Array Violation := #[]
  /-- Global-extra diagnostics with the position they occupy among themselves. -/
  globalExtras : Array (GlobalExtraSlot × Violation) := #[]
  /-- A slot-shaped name bound to the complete name list of the record which
  declared it, for the owner-backreference target set. Dropped at the record
  which declares the slot's root. -/
  slotRecords : Std.HashMap Name (Array Name) := {}
  /-- Root to the slot-shaped names recorded under it, so both tables above and
  below are dropped together. -/
  rootSlots : Std.HashMap Name (Array Name) := {}
  /-- `R._model` to its `iota_j` slots in stream order, for the extra-rule
  census. Dropped at the record which declares `R`. -/
  ruleSlots : Std.HashMap Name (Array (Name × Nat)) := {}
  /-- `T._model` to its projection slots and their flat ordinals in stream
  order. Dropped at the record which declares `T`. -/
  projectionSlots : Std.HashMap Name (Array (Name × Nat × Nat)) := {}
  /-- A public slot an owner expected and the stream had not declared, bound to
  the owners waiting for it and their records. -/
  lateSlots : Std.HashMap Name (Array (Name × Nat)) := {}
  /-- One owner's global-extra templates and their positions, retained because
  an unexpected slot may still be declared. -/
  deferredTemplates : Std.HashMap Name (Array (GlobalExtraTemplate × Nat × Nat)) := {}
  deriving Inhabited

/-- Charge one already-declared name against the owner templates whose records
have passed. This is the deferred half of the unexpected-slot sweep. -/
private def CompactStream.chargeDeferred (state : CompactStream) (name : Name)
    (ordinal : Nat) : CompactStream := Id.run do
  let some root := modelSlotRoot? name | return state
  let some templates := state.deferredTemplates[root]? | return state
  let mut globalExtras := state.globalExtras
  for (template, record, templateIndex) in templates do
    match template with
    | .type owner validFields allowsUnitlike allowsEta =>
      if let some (slotRoot, fieldIndex) := projectionSlotRoot? name then
        if slotRoot == Naming.modelName owner && !validFields.contains fieldIndex then
          globalExtras := globalExtras.push
            ({ record, template := templateIndex, rank := 0, ordinal },
              .extraProjection owner name)
      if !allowsUnitlike && name == Naming.unitlikeName owner then
        globalExtras := globalExtras.push
          ({ record, template := templateIndex, rank := 1, ordinal := 0 },
            .extraMetadata owner name .unitlike)
      if !allowsEta && name == Naming.etaName owner then
        globalExtras := globalExtras.push
          ({ record, template := templateIndex, rank := 2, ordinal := 0 },
            .extraMetadata owner name .eta)
    | .recursor owner allowsRuleK =>
      if !allowsRuleK && name == Naming.ruleKName owner then
        globalExtras := globalExtras.push
          ({ record, template := templateIndex, rank := 0, ordinal := 0 },
            .extraMetadata owner name .ruleK)
  return { state with globalExtras }

/-- Consume one final-order record: its names, its family certificate and its
owner templates, in that order. The record itself is not retained. -/
def CompactStream.push (state : CompactStream) (row : CompactCheckRecord) :
    Except String CompactStream := do
  let index := state.recordIndex
  let names := row.globalExtra.names
  let mut state := state
  -- **Names.** Duplicate rejection, the waiting model-order watches, and the
  -- slot tables the family and template passes below read back.
  for position in [:names.size] do
    let name := names[position]!
    if state.declared.contains name then
      throw s!"duplicate compact declaration name {name}"
    let ordinal := state.nameOrdinal
    let mut violations := state.violations
    for (owner, ownerRecord) in state.lateSlots.getD name #[] do
      violations := violations.push (.modelNotBefore owner name index ownerRecord)
    state := { state with
      declared := state.declared.insert name
      lateSlots := state.lateSlots.erase name
      violations
      nameOrdinal := ordinal + 1 }
    if let some root := modelSlotRoot? name then
      state := { state with
        slotRecords := state.slotRecords.insert name names
        rootSlots := state.rootSlots.insert root
          ((state.rootSlots.getD root #[]).push name) }
    if let some (parent, ruleIndex) := iotaSlot? name then
      state := { state with
        ruleSlots := state.ruleSlots.insert parent
          ((state.ruleSlots.getD parent #[]).push (name, ruleIndex)) }
    if let some (parent, fieldIndex) := projectionSlotRoot? name then
      state := { state with
        projectionSlots := state.projectionSlots.insert parent
          ((state.projectionSlots.getD parent #[]).push (name, fieldIndex, ordinal)) }
    state := state.chargeDeferred name ordinal
  -- **The family certificate**, bound to this exact record.
  if row.families.size > 1 then
    throw s!"compact owner record {row.owner} carries {row.families.size} family certificates"
  for family in row.families do
    unless row.owner == some family.owner do
      throw s!"compact family certificate for {family.owner} is not bound to its owner record"
    if state.certifiedOwners.contains family.owner then
      throw s!"duplicate compact family certificate for {family.owner}"
    state := { state with certifiedOwners := state.certifiedOwners.insert family.owner }
    -- **Model before owner.** A slot this record declares is already too late;
    -- a slot the stream has not reached becomes a watch, which is what makes
    -- the check survive without the owner's record.
    let ownPosition := names.foldl (init := (({} : Std.HashMap Name Nat), 0))
      (fun (positions, next) name =>
        (if positions.contains name then positions else positions.insert name next, next + 1))
      |>.1
    let mut visited : Std.HashSet Name := {}
    let mut late : Array (Nat × Name × Name) := #[]
    let mut lateSlots := state.lateSlots
    for (owner, publicName) in family.publicOwners do
      unless visited.contains publicName do
        visited := visited.insert publicName
        match ownPosition[publicName]?, state.declared.contains publicName with
        | some position, _ => late := late.push (position, owner, publicName)
        | none, true => pure ()
        | none, false =>
          lateSlots := lateSlots.insert publicName
            ((lateSlots.getD publicName #[]).push (owner, index))
    state := { state with lateSlots }
    unless family.publicNames.any state.declared.contains do continue
    let mut violations := state.violations
    for (_, owner, name) in late.qsort (fun left right => left.1 < right.1) do
      violations := violations.push (.modelNotBefore owner name index index)
    -- **The owner's backreference target set** is the names of every record
    -- which declared one of this family's public slots.
    let mut targets : Array Name := #[]
    let mut seen : Std.HashSet Name := {}
    for publicName in family.publicNames do
      for name in state.slotRecords.getD publicName #[] do
        unless seen.contains name do
          seen := seen.insert name
          targets := targets.push name
    if let some (owner, target) :=
        ownerBackreferenceFromCertificate? family.ownerReferences targets then
      violations := violations.push (.ownerBackreference owner target)
    violations := violations ++ family.localViolations
    for (owner, model, validRules) in family.recursors do
      for (name, ruleIndex) in state.ruleSlots.getD model #[] do
        if ruleIndex >= validRules || name != Naming.iotaName owner ruleIndex then
          violations := violations.push (.extraRule owner name)
    state := { state with violations, familiesChecked := state.familiesChecked + 1 }
  if row.modelSlots.any state.declared.contains && row.families.isEmpty then
    throw s!"compact owner record {row.owner} has declared model slots but no family certificate"
  -- **The owner's own unexpected-slot templates**, against everything declared
  -- so far, and then kept for whatever the stream declares later.
  let templates := row.globalExtra.templates
  for templateIndex in [:templates.size] do
    let template := templates[templateIndex]!
    let mut globalExtras := state.globalExtras
    let slot := fun (rank ordinal : Nat) =>
      ({ record := index, template := templateIndex, rank, ordinal } : GlobalExtraSlot)
    match template with
    | .type owner validFields allowsUnitlike allowsEta =>
      for (name, fieldIndex, ordinal) in
          state.projectionSlots.getD (Naming.modelName owner) #[] do
        unless validFields.contains fieldIndex do
          globalExtras := globalExtras.push (slot 0 ordinal, .extraProjection owner name)
      unless allowsUnitlike do
        let name := Naming.unitlikeName owner
        if state.declared.contains name then
          globalExtras := globalExtras.push
            (slot 1 0, .extraMetadata owner name .unitlike)
      unless allowsEta do
        let name := Naming.etaName owner
        if state.declared.contains name then
          globalExtras := globalExtras.push (slot 2 0, .extraMetadata owner name .eta)
    | .recursor owner allowsRuleK =>
      unless allowsRuleK do
        let name := Naming.ruleKName owner
        if state.declared.contains name then
          globalExtras := globalExtras.push (slot 0 0, .extraMetadata owner name .ruleK)
    state := { state with
      globalExtras
      deferredTemplates := state.deferredTemplates.insert template.owner
        ((state.deferredTemplates.getD template.owner #[]).push
          (template, index, templateIndex)) }
  -- **Release.** Every pending slot table entry rooted at a name this record
  -- declares has now been read for the last time: a family for that root is
  -- checked at this record and nowhere else, and anything declared under it
  -- later is the deferred sweep's business.
  for name in names do
    for slotName in state.rootSlots.getD name #[] do
      state := { state with slotRecords := state.slotRecords.erase slotName }
    state := { state with
      rootSlots := state.rootSlots.erase name
      ruleSlots := state.ruleSlots.erase (Naming.modelName name)
      projectionSlots := state.projectionSlots.erase (Naming.modelName name) }
  return { state with recordIndex := index + 1 }

/-- The global-extra diagnostics in the order the retained-row sweep produces
them, deferred ones included. -/
def CompactStream.orderedGlobalExtras (state : CompactStream) : Array Violation :=
  (state.globalExtras.qsort fun left right => GlobalExtraSlot.before left.1 right.1).map (·.2)

/-- The completed structural report: family diagnostics in record order, then
the unexpected-slot sweep. -/
def CompactStream.finish (state : CompactStream) : Report :=
  { familiesChecked := state.familiesChecked
    violations := state.violations ++ state.orderedGlobalExtras }

/-- Fold a complete record array through the stream. Generation has no such
array; this is the form a caller which already holds one — a test, or the
in-memory oracle below — uses to ask the streaming checker the same question. -/
def compactStreamedReport (records : Array CompactCheckRecord) :
    Except String Report := do
  let mut state : CompactStream := {}
  for row in records do
    state ← state.push row
  return state.finish

/-- The unexpected-slot sweep restricted to selected diagnostic owners. Every
diagnostic that sweep produces names the owner of the template which produced
it, so selecting owners here is exactly [`globalExtrasFromRecordsFor`]'s
template filter. -/
def CompactStream.globalExtrasFor (state : CompactStream)
    (owners : Std.HashSet Name) : Array Violation :=
  state.orderedGlobalExtras.filter fun violation => owners.contains violation.familyOwner

/-- The compact rows of an in-memory export, in its own record order. -/
def compactCheckRecords (x : Export) : Array CompactCheckRecord :=
  let index := SyntaxIndex.ofSource x
  let families := discoverWithIndex x index
  let familyRecords := compactFamilyCertificateRecordsWithIndex x index families
  let modelSlotRecords := families.foldl (init := Array.replicate x.decls.size #[])
    fun records family => records.set! family.ownerDecl family.correspondence.publicNames
  (globalExtraRecordsWithIndex index x.decls).mapIdx fun i globalExtra =>
    { owner := match x.decls[i]! with
        | .induct (type :: _) _ _ => some type.name
        | _ => none
      modelSlots := modelSlotRecords[i]!
      globalExtra, families := familyRecords[i]! }

/-- In-memory equivalence oracle for an already ordered export. -/
def compactOrderedCheckReport (x : Export) : Except String Report :=
  compactOrderedReport (compactCheckRecords x)

/-- The same oracle produced by the fold rather than by the retained rows.

On an already ordered export the two agree exactly: every model record precedes
its owner, so the streaming model-order watch fires nowhere, and each deferred
unexpected-slot diagnostic is ordered back into its owner's position. A
difference between them is a difference between the two implementations of one
report, which is the only reason both exist. -/
def compactStreamCheckReport (x : Export) : Except String Report :=
  compactStreamedReport (compactCheckRecords x)

end InductiveModels.Check
