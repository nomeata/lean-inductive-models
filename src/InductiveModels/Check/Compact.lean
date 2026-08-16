import InductiveModels.Check.Index

/-!
# Name-only compact certificates

Once compact ordering succeeds, model records precede their owners and the
structural pass can release declarations and expression graphs.  A certificate
retains the names, owner-reference trace, and family-local violations captured
while the family was live, and [`compactOrderedReport`] finishes the report
from those alone.
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

/-- Capture the frozen source-family template while its exact owner record is
live.  The singleton *record view* still contains the complete mutual block;
all declaration types, constructors, public-slot occurrences, transparent
definitions, and rule slots come from `index`. Rebasing only the record ordinal
therefore avoids retaining unrelated `EDecl` values without synthesizing or
splitting the owner. -/
def SyntaxIndex.sourceFamilyCertificatesForRecord (index : SyntaxIndex)
    (template : Export) (owner : EDecl) : Array CompactFamilyCertificate :=
  let root? := match owner with
    | .induct (type :: _) _ _ => some type.name
    | _ => none
  root?.elim #[] fun root =>
    let view := { template with decls := #[owner] }
    (index.sourceStatementFamilies root).filterMap fun family =>
      -- Match indexed discovery exactly: an expected family becomes an input
      -- family only when at least one exact public slot occurs in the source.
      if family.correspondence.publicNames.any index.names.contains then
        some (compactFamilyCertificateWithIndex view index { family with ownerDecl := 0 })
      else none

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
the certificates. -/
private def compactReport (records : Array CompactCheckRecord)
    (checkSourceOrder : Bool) : Except String Report := do
  let orderedGlobals := records.map (·.globalExtra)
  let orderedNames := orderedGlobals.flatMap (·.names)
  let mut declared : Std.HashSet Name := {}
  let mut declaringRecord : Std.HashMap Name (Array Name) := {}
  for recordIndex in [:records.size] do
    let record := records[recordIndex]!
    for name in record.globalExtra.names do
      if declared.contains name then
        throw s!"duplicate compact declaration name {name}"
      declared := declared.insert name
      declaringRecord := declaringRecord.insert name record.globalExtra.names
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
      if checkSourceOrder then
        for modelDecl in [:records.size] do
          unless modelDecl < recordIndex do
            for name in records[modelDecl]!.globalExtra.names do
              if let some (owner, _) := family.publicOwners.find? (fun pair => pair.2 == name) then
                violations := violations.push
                  (.modelNotBefore owner name modelDecl recordIndex)
      let familyNames := family.publicNames.foldl (init := #[]) fun names publicName =>
        appendUnique names (declaringRecord.getD publicName #[]).toList
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
  compactReport records false

/-- Finish the historical structural report for source records in their raw
order. Unlike [`compactOrderedReport`], this reproduces model-after-owner
diagnostics rather than assuming a proven compact order. -/
def compactSourceReport (records : Array CompactCheckRecord) : Except String Report :=
  compactReport records true

/-- In-memory equivalence oracle for an already ordered export. -/
def compactOrderedCheckReport (x : Export) : Except String Report :=
  let index := SyntaxIndex.ofSource x
  let families := discoverWithIndex x index
  let familyRecords := compactFamilyCertificateRecordsWithIndex x index families
  let modelSlotRecords := families.foldl (init := Array.replicate x.decls.size #[])
    fun records family => records.set! family.ownerDecl family.correspondence.publicNames
  compactOrderedReport <| (globalExtraRecordsWithIndex index x.decls).mapIdx fun i globalExtra =>
    { owner := match x.decls[i]! with
        | .induct (type :: _) _ _ => some type.name
        | _ => none
      modelSlots := modelSlotRecords[i]!
      globalExtra, families := familyRecords[i]! }

end InductiveModels.Check
