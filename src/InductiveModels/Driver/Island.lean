import InductiveModels.Driver.Types
import InductiveModels.Driver.Records
import InductiveModels.Driver.StructureModels

/-!
# One generated island: assembly, the kernel gate, and the close

The observer seam, the placement of a newly generated model at its emission
boundary, the three installed/source model entry points, and the two
environment gates an island passes — reinstallation in an owner-free
environment ([`checkGeneratedIn`]) and the persistence of the support it
splices ([`installGeneratedSupportIn`]) — ending at [`closeModelIsland`].

[`IslandObserver`] is deliberately parameterised in `α`: the driver names no
observation type, so a consumer of an island lives entirely outside `src/`.

[`appendModelRecords`] was file-private and is module-visible now because both
the composition tower and the filter place records with it.
-/

open Lean Meta

namespace InductiveModels

/-- **The island observer seam.** A callback from one exact source record and
the kernel-checked private [`InductiveModels.Iso`] built from it to whatever a
caller wants to observe about that pair. The driver never inspects the result:
it fixes no observation type, imports no module that defines one, and threads
the values it is handed straight back out.

The seam exists so that observation experiments stay off the production build.
A caller that wants one supplies the callback and names the type; production
supplies none, and the modules implementing an observer are not part of the
`lean-inductive-models` object closure at all. -/
abbrev IslandObserver (α : Type) := EDecl → Iso → MetaM α


/-- Place one newly generated model at its constructive emission boundary. A
source owner is not in the private forest yet, so its model appends and the
source callback follows it. A recursively generated owner is already present
inside a dependency-ordered parent segment; splice immediately before that
complete record, preserving every earlier support record the child may use. -/
def appendModelRecords (out records : Array EDecl) (owner : Name) : Array EDecl :=
  match out.findIdx? (fun declaration => declaration.names.contains owner) with
  | none => out ++ records
  | some ownerIndex =>
    out.extract 0 ownerIndex ++ records ++ out.extract ownerIndex out.size


/-- Installed-block adapter for the two generation routes which run after the
original inductive has been replayed. -/
def addInstalledUnitlikeTheorems (names : Array Name) (reserved : Std.HashSet Name)
    (is : Iso) : GenM Iso := do
  let .induct types constructors recursors ← indEDecl names
    | badShape s!"{names} did not read back as an inductive block"
  addUnitlikeTheorems types.toArray constructors.toArray recursors.toArray reserved is

/-- Installed-block adapter for all per-member structure metadata. -/
def addInstalledStructureModels (names : Array Name) (projections : Array EProjection)
    (reserved : Std.HashSet Name) (is : Iso) : GenM Iso := do
  let .induct types constructors recursors ← indEDecl names
    | badShape s!"{names} did not read back as an inductive block"
  addStructureModels types.toArray constructors.toArray recursors.toArray
    projections reserved is

/-- Exact source-owned adapter.  Unlike the installed adapter above, this
keeps the raw export spelling of the owner, constructor, and recursor records;
the optional normalizer is used only at the one kernel beta-normalization
boundary of projection-iota theorem binders. -/
def addSourceStructureModels (block : EDecl) (projections : Array EProjection)
    (normalizer : ExactNormalizationEnv) (reserved : Std.HashSet Name)
    (is : Iso) : GenM Iso := do
  let .induct types constructors recursors := block
    | badShape "source structure adapter did not receive an inductive block"
  addStructureModels types.toArray constructors.toArray recursors.toArray
    projections reserved is (some normalizer)


/-- Reinstall serialized generated records, with kernel checking, in an
arbitrary source-prefix environment.

Generation may use a separate analysis environment containing the owner.  A
successful public model must nevertheless install here, where the owner is
absent. This makes owner independence a kernel-checked invariant at the same
prefix where the island is constructively emitted. The returned environment is a fork;
the caller may discard it after streaming the records. -/
def checkGeneratedIn (base : Environment) (records : Array EDecl) :
    MetaM (Except String Environment) := do
  let mut checked := base
  let mut cursor := 0
  while cursor < records.size do
    let record := records[cursor]!
    if record matches .quot .. then
      -- Quotient is one kernel declaration but four consecutive export
      -- records. Validate and install it at the current checked prefix: that
      -- prefix may itself contain generated Eq, which the kernel declaration
      -- requires and an up-front scan against `base` cannot see.
      for name in [`Quot, `Quot.mk, `Quot.lift, `Quot.ind] do
        if checked.constants.contains name then
          return .error s!"generated quotient bundle would shadow existing {name}"
      unless cursor + 4 <= records.size do
        return .error "quotient declaration does not have four consecutive export records"
      let quotientEnv ← match checked.addDeclCore 0 0 .quotDecl none true with
        | .error exception =>
          return .error s!"cannot reconstruct quotient declaration: \
            {← (exception.toMessageData {}).toString}"
        | .ok next => pure next
      let some expected := installedQuotRecords? quotientEnv
        | return .error "kernel quotient declaration did not install its four constants"
      let actual := records.extract cursor (cursor + 4)
      unless actual == expected do
        return .error "quotient export bundle does not match the kernel declaration"
      checked := quotientEnv
      cursor := cursor + 4
      continue
    let some declaration := toDeclaration checked record | do
      return .error s!"{record.names}: cannot reconstruct a kernel declaration"
    match checked.addDeclCore 0 0 declaration none true with
    | .error exception =>
      return .error s!"{record.names}: \
        {← (exception.toMessageData {}).toString}"
    | .ok next =>
      checked := next
      for name in declaration.getNames do
        unless checked.constants.contains name do
          return .error s!"{name}: checked declaration was lost from the kernel environment"
    cursor := cursor + 1
  return .ok checked

/-- **One record of reusable shared support a model spliced**, as opposed to a
record of that model's own disposable implementation forest. The `Iso.spliced`
witness is essential: namespace shape alone must never call a public model such
as `Eq.Example._model` shared support. Local skeletons and per-model `funext`
are spliced too and are deliberately not shared: they belong to the one model
that built them. -/
def splicedSupportRecord (spliced : Std.HashSet Name) (record : EDecl) : Bool :=
  record.names.any spliced.contains &&
    (record.names.any persistentSupportRoot || record.names.all persistentSupportName)

/-- Persist the reusable subset of support explicitly recorded by an accepted
model island. Local skeletons and per-model `funext` remain disposable. -/
def generatedSupportRecords (records : Array EDecl) (models : Array PendingModel) :
    Array EDecl :=
  let spliced := models.foldl (init := ({} : Std.HashSet Name)) fun names model =>
    model.spliced.foldl (fun names name => names.insert name) names
  records.filter (splicedSupportRecord spliced)

def installGeneratedSupportIn (base : Environment) (records : Array EDecl)
    (models : Array PendingModel) :
    MetaM (Except String Environment) := do
  let mut main := base
  for record in generatedSupportRecords records models do
    let some declaration := toDeclaration main record | do
      if installedQuotRecord main record then continue
      return .error s!"{record.names}: cannot reconstruct shared support"
    -- Reusable support belongs to the construction view. The complete exact
    -- emitted island is checked once, separately, when generated checking is on.
    match main.addDeclCore 0 0 declaration none false with
    | .error exception =>
      return .error s!"{record.names}: {← (exception.toMessageData {}).toString}"
    | .ok next => main := next
  return .ok main

/-- **The island records a syntax index already carries.**

Generation writes its own canonical basis declaration at the first point one is
needed, and the input's own record for that name is dropped when the stream
reaches it ([`InductiveModels.canonicalBasisRecordMatches`]). The source syntax
index, however, was built from the whole input and still describes the record
that is about to be dropped, so overlaying the generated copy on top would be a
redeclaration — of the *same* declaration, since a record that is not the same
declaration rejects the run rather than being dropped. There is nothing to add,
so such a record is left out of the overlay.

The one gate is the fixed basis list: nothing outside it is ever both written
by generation and already indexed, because every other generated name goes
through the reserved-name guard. -/
def canonicalBasisAlreadyIndexed (index : Check.SyntaxIndex) (record : EDecl) : Bool :=
  record.names.any fun name => canonicalBasisNames.contains name && index.declares name

/-- Finalize one atomic generated forest. Generated records stay in generator
append order, and only fixed shared support is copied back into the persistent
construction environment. The caller may separately submit the exact returned
island to the generated kernel gate. -/
def closeModelIsland (template : Export) (main : Environment)
    (records : Array EDecl) (models : Array PendingModel) (owner : EDecl)
    (sourceSyntax : Check.SyntaxIndex) (generatedOwners : Std.HashSet Name)
    (sourceAliases : SourceReplayAliases := {}) :
    MetaM (Except String
      (Array EDecl × CompactIsland × Environment × Check.StatementReport)) := do
  -- Generation runs in the collision-free replay environment, so generated
  -- expressions can mention replay aliases.  Restore the exact source names
  -- before every syntax/output operation. The optional caller-side kernel
  -- gate converts the returned exact records back to their collision-safe
  -- build image.
  let exactRecords := records.map sourceAliases.exactRecord
  unless exactRecords.map sourceAliases.buildRecord == records do
    return .error "generated source-alias round trip changed a declaration"
  -- Round-trip equality alone cannot see an unregistered derived build name:
  -- both exactRecord and buildRecord would leave it unchanged.  The exhaustive
  -- record mapper must find no construction prefix after exactification, even
  -- when generated-declaration checking has been disabled by the caller.
  unless exactRecords.map sourceAliases.exactDerivedRecord == exactRecords do
    return .error "generated declaration retained an unregistered source replay alias"
  -- Generation appends every declaration in dependency order, behind the
  -- shared support each model spliced ([`InductiveModels.serialiseIso`]). The
  -- island is emitted exactly in that constructive order immediately before
  -- `owner`; no island or stream ordering pass runs here.
  let generated := exactRecords
  -- Statement correspondence is an export-syntax check, so it can run while
  -- the owner is still absent from the persistent replay environment. Source
  -- owners use family templates indexed once; generated owners use the island
  -- records plus an overlay carrying source transparent aliases and exact
  -- projection metadata. The final aggregate remains the equivalence oracle.
  let index ← match sourceSyntax.prependRecords
      (generated.filter (!canonicalBasisAlreadyIndexed sourceSyntax ·)) with
    | .ok index => pure index
    | .error message => return .error s!"cannot index generated island: {message}"
  let sourceRoot? : Option Name := match owner with
    | .induct (type :: _) _ _ => some type.name
    | _ => none
  let generatedOnlyOwners := sourceRoot?.elim generatedOwners generatedOwners.erase
  let generatedView := { template with decls := generated }
  -- Source-local checks need the complete atomic owner record (including all
  -- mutual members), not unrelated source values. Every cross-record syntax
  -- table and public-slot occurrence is already frozen in `sourceSyntax`.
  let ownerView := { template with decls := #[owner] }
  let generatedFamilies :=
    Check.statementFamiliesForRecordsWithIndex generatedView index generatedOnlyOwners
  let sourceFamilies := sourceRoot?.elim #[] fun root =>
    if generatedOwners.contains root then
      (sourceSyntax.sourceStatementFamilies root).map fun family =>
        { family with ownerDecl := 0 }
    else #[]
  let allFamilies := generatedFamilies ++ sourceFamilies
  let diagnosticOwners := allFamilies.foldl
    (fun result family => family.correspondence.diagnosticOwners.foldl
      (fun result owner => result.insert owner) result)
    ({} : Std.HashSet Name)
  let compactOwners := generated.foldl (init := ({} : Std.HashSet Name)) fun owners record =>
    match record with
    | .induct (type :: _) _ _ => owners.insert type.name
    | _ => owners
  let generatedFamilyRecords :=
    Check.compactFamilyCertificateRecordsWithIndex generatedView index generatedFamilies
  let sourceFamilyCertificates := sourceFamilies.map
    (Check.compactFamilyCertificateWithIndex ownerView index)
  let sourceGlobalExtra? := if sourceFamilies.isEmpty then none else
    (Check.globalExtraRecordsWithIndex index #[owner])[0]?
  let compact : CompactIsland :=
    { summaries := Order.summariesWithIndex generatedView index compactOwners
      globalExtras := Check.globalExtraRecordsWithIndex index generated
      families := generatedFamilyRecords
      sourceFamilies := sourceFamilyCertificates
      sourceGlobalExtra?
      diagnosticOwners }
  -- An owner this island reported as generated but for which family discovery
  -- produced nothing would be checked by nobody: both local reports would be
  -- built from an empty family array, so the island would report
  -- `statementsChecked = 0, violations = #[]` and be indistinguishable from one
  -- that compared clean. Only the summed run total is inspected downstream, and
  -- it cannot see one silent owner among hundreds of thousands. So require it
  -- here, per island: every owner this island claims to have modeled must have
  -- yielded a discovered family carrying at least one statement comparison.
  let uncompared := generatedOwners.toArray.filter fun owner =>
    !allFamilies.any fun family =>
      family.owner == owner && family.correspondence.statementCount > 0
  unless uncompared.isEmpty do
    let names := (uncompared.qsort (toString · < toString ·)).map toString
    return .error s!"generated owner produced no statement comparison: \
      {String.intercalate ", " names.toList}"
  let statementReport :=
    if generatedOwners.isEmpty then
      { statementsChecked := 0, violations := #[] }
    else
      let generatedReport :=
        Check.checkStatementFamiliesLocalWithIndex generatedView index generatedFamilies
      let sourceReport :=
        Check.checkStatementFamiliesLocalWithIndex ownerView index sourceFamilies
      let checkedCount := generatedReport.statementsChecked + sourceReport.statementsChecked
      let combinedViolations := generatedReport.violations ++ sourceReport.violations
      ({ statementsChecked := checkedCount, violations := combinedViolations } :
        Check.StatementReport)
  -- Drop the owner-local construction fork before reconstructing persistent
  -- support. The exact serialized records and compact splice witnesses above
  -- are the only state allowed to cross this boundary.
  setEnv main
  let replayGenerated := generated.map sourceAliases.buildRecord
  match ← installGeneratedSupportIn main replayGenerated models with
  | .error message => return .error message
  | .ok supported => return .ok (generated, compact, supported, statementReport)
