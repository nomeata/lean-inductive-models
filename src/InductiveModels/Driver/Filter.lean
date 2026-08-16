import InductiveModels.Driver.Tower
import InductiveModels.Driver.Census
import InductiveModels.Driver.Readiness

/-!
# The declaration-wise fold, and the six routes over it

`FilterState.feedSource` is the one-record logical transition and
`FilterState.finalize` consumes what it accumulated.  `runFilterCore` drives
them and stays private: the six public routes below are the only ways in, and
each of them fixes the retention mode its contract allows.
-/

open Lean Meta

namespace InductiveModels

/-! ## Declaration-wise filter state

Retained-input routes materialise a complete `Export`, while planned-input
routes decode one certified declaration at a time. The generation loop below
does not own its mutable state as local variables.
`FilterState.feedSource` is the one-record logical transition and
`FilterState.finalize` consumes only accumulated value-level certificates or
the compatibility retained output. This is the boundary a census/span reader
and declaration emitter drive without changing an
owner's pre-replay generation, source replay, post-replay generation, or atomic
island close. -/

/-- Observable, value-free boundary facts for one completed source transition.
This regression seam deliberately exposes neither `FilterState` nor a live
environment, so a test cannot mutate subsequent generation. -/
structure FilterSourceStep where
  sourceOrdinal : Nat
  rawOrdinal : Nat
  sourceNames : Array Name
  sourceIsInductive : Bool
  sourceInstalled : Bool
  generated : Array (Name × Nat)
  generatedRecords : Nat
  deriving Inhabited, Repr, BEq

/-- Output retention is explicit: compatibility callers may retain a complete
array, while production output streams and no-output mode retain only
value-level certificates. -/
private inductive RetentionMode where
  | fullOutput
  | compactDiscard
  | streamOutput

private def RetentionMode.isCompact : RetentionMode → Bool
  | .fullOutput => false
  | .compactDiscard => true
  | .streamOutput => true

private def RetentionMode.retainsOutput : RetentionMode → Bool
  | .fullOutput => true
  | .compactDiscard => false
  | .streamOutput => false

private def RetentionMode.streamsOutput : RetentionMode → Bool
  | .streamOutput => true
  | _ => false


private structure FilterContext (α : Type) where
  source : Export
  checkRecursors : Bool
  generation : Cli.Config
  retention : RetentionMode
  exactTransform : EDecl → EDecl
  sourceSyntax : Check.SyntaxIndex
  constructionSyntax : Check.SyntaxIndex
  constructionNormalizer : ExactNormalizationEnv
  sourceAliases : SourceReplayAliases
  sourceSummaries : Array Order.DeclSummary
  sourceGlobalExtras : Array Check.GlobalExtraRecord
  sourceFamilyRecords : Array (Array Check.CompactFamilyCertificate)
  rawOrdinals : Std.HashMap Name Nat
  reserved : Std.HashSet Name
  constructionReserved : Std.HashSet Name
  collectTrace : Bool := false
  observer? : Option (IslandObserver α) := none
  outputEmitter? : Option StreamOutputEmitter := none

/-- Cheap summary-first test for whether an exhaustive record rewrite can
change anything. `all` fields are bookkeeping rather than dependencies, so
they are the only constant-bearing fields not already covered by a summary. -/
private def sourceRecordUsesAliases (aliases : SourceReplayAliases)
    (summary : Order.DeclSummary) (declaration : EDecl) : Bool :=
  let bookkeepingUsesAlias := match declaration with
    | .defn _ _ _ _ _ _ all | .thm _ _ _ _ all | .opaq _ _ _ _ _ all =>
      all.any aliases.hasExact
    | .induct types _ recursors =>
      types.any (fun type => type.all.any aliases.hasExact) ||
        recursors.any (fun recursor => recursor.all.any aliases.hasExact)
    | _ => false
  summary.introduced.any aliases.hasExact ||
    summary.referenced.any aliases.hasExact || bookkeepingUsesAlias

/-! ### What the fold retains

Every field below is either a value-level verdict the run has to end with, or a
bound the fold cannot avoid. Nothing here is a view of the output: no source or
generated declaration outlives the transition that produced it, with the single
exception named in `legacyOut`. -/

private structure FilterState (α : Type) where
  mainEnv : Environment
  persistentSyntax : Check.SyntaxIndex
  /-- **The one place output declarations accumulate**, and only under
  [`RetentionMode.fullOutput`]: the compatibility entry points hand a complete
  `Array EDecl` back, and the final family-local statement aggregate they
  cross-check the per-island reports against is a whole-export pass by
  construction. Compact discard and declaration-wise output leave this empty,
  and `finalize` fails rather than returning quietly if they did not. -/
  legacyOut : Array EDecl := #[]
  report : Report := {}
  /-- The compact structural check, as far as the stream has been consumed.
  No output record — source or generated — outlives the transition that
  produced it, so this state and the locator schedule below are the only
  things the final report is built from. -/
  compactCheck : Check.CompactStream := {}
  /-- Where each emitted record came from, in emission order.  Two natural
  numbers per record and no payload; this is the plan's own schedule, not a
  retained view of the output. -/
  compactLocators : Array CompactLocator := #[]
  /-- Accepted generated islands so far, which is the island number the next
  one's locators carry. -/
  compactIslandCount : Nat := 0
  /-- Owners whose generated statement diagnostics the compact statement report
  selects. One name per generated owner, which is what `report.generated`
  already costs. -/
  diagnosticOwners : Std.HashSet Name := {}
  sourceOrdinal : Nat := 0
  islandStatements : Check.StatementReport :=
    { statementsChecked := 0, violations := #[] }
  invalidBasis : Std.HashSet Name := {}
  /-- Value-free boundary facts for the regression seam, and empty unless
  `collectTrace` asked for them. `runFilterCore` requires that seam to be a
  retained-output run, so a trace is never the largest thing a run is holding. -/
  sourceSteps : Array FilterSourceStep := #[]
  observations : Array α := #[]
  streamStats : StreamOutputStats := {}
  /-- **Source owners that arrived with a model family of their own**, in the
  order the stream reached them, with a set beside them so that recognising one
  already seen costs a lookup rather than a scan of every owner accepted so
  far. One name per input family and no record: an input which declares no
  model — every export straight out of `lean4export` — accumulates nothing
  here at all. `finalize` subtracts the owners the structural report faulted
  and hands the rest to the decline classifier. -/
  inputFamilyOwners : Array Name := #[]
  inputFamilyOwnerSet : Std.HashSet Name := {}
  /-- **The canonical basis names generation has written into the output.**
  Exactly the names whose input-owned record is dropped when the stream reaches
  it. This is a record of what was emitted and not a question about the
  environment: the input's own quotient bundle is four records binding four
  constants at the first of them, so "already in the environment" would drop
  the other three. -/
  canonicalBasisWritten : Std.HashSet Name := {}

private inductive FilterFeedResult (α : Type) where
  | next (state : FilterState α)
  /-- Preserve the completed trace without making the caller retain the whole
  previous state while `feedSource` appends to its accumulated arrays. -/
  | unreplayable (report : Report) (sourceSteps : Array FilterSourceStep)

/-- Consume one declaration from the raw-order logical source
stream.  Every mutable field which survives this call is explicit in
`FilterState`; `out`, `pending`, and the replay fork remain owner-local. -/
private def FilterState.feedSource (state : FilterState α) (context : FilterContext α)
    (d : EDecl) : MetaM (FilterFeedResult α) := do
  let x := context.source
  let generation := context.generation
  let retention := context.retention
  let compactMode := retention.isCompact
  let retainOutput := retention.retainsOutput
  let streamOutput := retention.streamsOutput
  let exactTransform := context.exactTransform
  let constructionNormalizer := context.constructionNormalizer
  let sourceAliases := context.sourceAliases
  let sourceSummaries := context.sourceSummaries
  let sourceOrdinal := state.sourceOrdinal
  let sourceSummary := sourceSummaries[sourceOrdinal]!
  let sourceUsesAlias := sourceRecordUsesAliases sourceAliases sourceSummary d
  let replayD := if sourceUsesAlias then sourceAliases.buildRecord d else d
  let sourceGlobalExtra := context.sourceGlobalExtras[sourceOrdinal]!
  let sourceFamilyRecord := context.sourceFamilyRecords[sourceOrdinal]!
  let rawOrdinals := context.rawOrdinals
  let reserved := context.constructionReserved
  let mut mainEnv := state.mainEnv
  let mut persistentSyntax := state.persistentSyntax
  let mut legacyOut := state.legacyOut
  let mut rep := state.report
  let mut compactCheck := state.compactCheck
  let mut compactLocators := state.compactLocators
  let mut compactIslandCount := state.compactIslandCount
  let mut diagnosticOwners := state.diagnosticOwners
  let mut islandStatements := state.islandStatements
  let mut invalidBasis := state.invalidBasis
  let mut sourceSteps := state.sourceSteps
  let mut observations := state.observations
  let mut streamStats := state.streamStats
  let mut inputFamilyOwners := state.inputFamilyOwners
  let mut inputFamilyOwnerSet := state.inputFamilyOwnerSet
  let mut canonicalBasisWritten := state.canonicalBasisWritten
  for family in sourceFamilyRecord do
    unless inputFamilyOwnerSet.contains family.owner do
      inputFamilyOwnerSet := inputFamilyOwnerSet.insert family.owner
      inputFamilyOwners := inputFamilyOwners.push family.owner
  -- Construction state is island-local. Nothing generated for an earlier
  -- owner remains in this buffer after that island has closed.
  let mut out : Array EDecl := #[]
  let mut pending : Array PendingModel := #[]
  let mut islandObservations : Array α := #[]
  let mut modeledSourceFamilies : Array Check.CompactFamilyCertificate := #[]
  let mut modeledSourceGlobalExtra? : Option Check.GlobalExtraRecord := none
  let mut streamIsland? : Option (Array EDecl) := none
  let basisRoot? := match replayD with
    | .induct types _ _ => types.findSome? fun type =>
        if inductiveBasis.contains type.name then some type.name else none
    | _ => none
  -- No model declaration is ever installed in `mainEnv`. All constructors
  -- below work in the ambient disposable fork; closing an inductive record
  -- restores this exact source prefix plus accepted reusable support.
  setEnv mainEnv
  -- **The one record class that is dropped rather than emitted.** A canonical
  -- basis name is already bound here exactly when generation wrote its own
  -- declaration at that name earlier in the stream; input names are unique and
  -- this record has not been replayed, so nothing else can have bound it.
  -- Dropping is only correct if this record is that same declaration, and that
  -- is asked here and nowhere else ([`InductiveModels.canonicalBasisRecordMatches`]).
  let dropCanonicalBasisRecord ←
    if replayD.names.any canonicalBasisWritten.contains then
      if ← canonicalBasisRecordMatches replayD then pure true
      else
        return .unreplayable
          { rep with unreplayable := some s!"{d.names}: generation already wrote the \
            canonical basis declaration at this name, and this input record is not that \
            declaration" }
          sourceSteps
    else pure false
  let mainBefore := mainEnv
  let mut replayedOwnerEnv? : Option Environment := none
  let reportedBefore := rep.generated.size
  let declinedBefore := rep.declined.size
  let exemptBefore := rep.exempt.size
  let splicedBefore := rep.spliced.size
  -- The model, if this is a nested declaration. Generated **before** the
  -- declaration is added: nothing in the model mentions `T`.
  if let .induct ts cs inputRecursors := replayD then
    -- **A mutual block whose members nest is one block, not several.** Lean
    -- specialises the whole block at once — `nest_mutual_both`'s `A`/`B`
    -- become four members with four recursors over one shared motive vector
    -- — so the model does too, under the first member's `_model` namespace
    -- and with one carrier per real member.
    if let t :: _ := ts then
      if generation.nested && ts.any (·.numNested > 0) &&
          basisRoot?.isNone && invalidBasis.isEmpty && !dropCanonicalBasisRecord then
        let all := ts.toArray.map (·.name)
        let ctorsOfMember := fun (n : Name) =>
          (cs.filter (·.induct == n)).toArray.map fun c => (c.name, c.type)
        let ptypes : Array PType := ts.toArray.map fun m =>
          { name := m.name, type := m.type, ctors := ctorsOfMember m.name }
        match plan (← getEnv) t.levelParams t.numParams ptypes with
        | .error e => rep := { rep with declined := rep.declined.push (t.name, e) }
        | .ok none => pure ()
        | .ok (some pl) =>
          let saved ← getEnv
          let ctors := all.map ctorsOfMember
          let mut result ← (do
            let is ← iso all t.levelParams t.numParams ctors inputRecursors.toArray
              pl reserved
            addStructureModels ts.toArray cs.toArray inputRecursors.toArray
              #[] reserved is).run
          if let .error (.nameLost _) := result then
            setEnv saved
            result ← (do
              let is ← iso all t.levelParams t.numParams ctors inputRecursors.toArray pl reserved
                (some (Naming.retryRoot t.name))
              addStructureModels ts.toArray cs.toArray inputRecursors.toArray
                #[] reserved is).run
          match result with
          | .error dec =>
            setEnv saved
            rep := rep.withDecline t.name dec "nested"
          | .ok is =>
            let serialised ← serialiseIso replayD is exactTransform context.observer?
            if let some observation := serialised.observation? then
              islandObservations := islandObservations.push observation
            let records := serialised.records
            let is := serialised.model
            out := appendModelRecords out records t.name
            rep := { rep with generated := rep.generated.push (t.name, is.decls.size) }
            unless is.spliced.isEmpty do
              rep := { rep with spliced := rep.spliced.push (t.name, is.spliced) }
            pending := pending.push { spliced := is.spliced }
            -- The model of the generated mutual block remains in this same
            -- atomic owner transition.
            if generation.mutualModels && is.members.size > 1 then
              let saved2 ← getEnv
              let (tys2, ctors2) ← blockOf is.members
              let composedRoot := is.members[0]!
              let exactBlock ← serialised.exactBlocks.require composedRoot
              let mut mutualResult ← (do
                let is2 ← mutualIso is.members is.levelParams t.numParams
                  tys2 ctors2 reserved (sourceBlock? := some exactBlock)
                addInstalledStructureModels is.members #[] reserved is2).run
              if let .error (.nameLost _) := mutualResult then
                setEnv saved2
                mutualResult ← (do
                  let is2 ← mutualIso is.members is.levelParams t.numParams
                    tys2 ctors2 reserved (some (Naming.retryRoot composedRoot))
                      (sourceBlock? := some exactBlock)
                  addInstalledStructureModels is.members #[] reserved is2).run
              match mutualResult with
              | .error dec =>
                setEnv saved2
                rep := rep.withDecline is.members[0]! dec "mutual"
              | .ok is2 =>
                let serialised2 ←
                  serialiseIso exactBlock is2 exactTransform context.observer?
                if let some observation := serialised2.observation? then
                  islandObservations := islandObservations.push observation
                let records := serialised2.records
                let is2 := serialised2.model
                out := appendModelRecords out records is.members[0]!
                rep := { rep with
                  generated := rep.generated.push (is.members[0]!, is2.decls.size) }
                pending := pending.push { spliced := is2.spliced }
                if generation.simple then
                  let st3 ← primCompose is2.members is2.levelParams
                    t.numParams reserved generation.basic serialised2.exactBlocks
                      (out, rep, pending, islandObservations) exactTransform
                      context.observer?
                  (out, rep, pending, islandObservations) ← pure st3
  -- Replay the source record between its pre-owner and post-owner generation
  -- phases.  An unreplayable source record terminates the complete machine and
  -- discards every private island, matching the historical loop return.
  if dropCanonicalBasisRecord then
    -- **This record's own declaration is already installed**, because
    -- generation wrote the canonical declaration at this name earlier and this
    -- record was proved above to be that declaration. Installing it again is
    -- installing the same declaration, which the kernel refuses by name, so
    -- the record replays as a no-op — the same answer `toDeclaration` gives
    -- the second `quot` record of one kernel quotient bundle — and it is not
    -- emitted either.
    replayedOwnerEnv? := some (← getEnv)
  else if let some dcl := toDeclaration (← getEnv) replayD then
    match (← getEnv).addDeclCore 0 0 dcl none false with
    | .ok e =>
      replayedOwnerEnv? := some e
      setEnv e
    | .error ex =>
      let msg ← (ex.toMessageData {}).toString
      return .unreplayable
        { rep with unreplayable := some s!"{d.names}: {sourceAliases.exactMessage msg}" }
        sourceSteps
  if sourceUsesAlias then
    let replayEnv ← getEnv
    for name in replayD.names do
      unless (replayEnv.find? name).isSome do
        throwError "source replay lost Meta visibility for {sourceAliases.exactName name} \
          while installing {d.names}"
    if let .induct types constructors recursors := replayD then
      let mismatches ← checkInductiveMetadata types constructors recursors
      unless mismatches.isEmpty do
        throwError "collision-safe inductive replay metadata differs for {d.names}: \
          {mismatches.toList.map sourceAliases.exactMessage}"
  -- **The exemption is a fact about the source declaration, not about where it
  -- ends up.** A dropped basis owner is reported exempt exactly as an emitted
  -- one is: the input declared it and this tool did not model it. For a dropped
  -- record the verdict can only be `.ok`, because the drop above already
  -- established that this record is the canonical declaration.
  if let some root := basisRoot? then
    match ← (validateBasisOwner root replayD).run with
    | .ok () =>
      if generation.modelsSimpleInput root then
        rep := { rep with
          exempt := rep.exempt.push (root, Decline.basisExempt.labelAs "prim") }
    | .error decline =>
      invalidBasis := invalidBasis.insert root
      rep := rep.withDecline root decline "prim"
  -- Plain mutual and direct-simple routes read recursor metadata installed by
  -- the replay above and therefore remain the post-owner half of this single
  -- transition.
  if let .induct ts cs _ := replayD then
    if let t :: _ := ts then
      if generation.mutualModels && ts.length > 1 && !ts.any (·.numNested > 0) &&
          basisRoot?.isNone && invalidBasis.isEmpty && !dropCanonicalBasisRecord then
        let all := ts.toArray.map (·.name)
        let ctors := all.map fun n =>
          (cs.filter (·.induct == n)).toArray.map fun c => (c.name, c.type)
        let tys := ts.toArray.map (·.type)
        let st3 ← genMutual all t.levelParams t.numParams tys ctors #[] reserved
          generation.simple generation.basic (out, rep, pending, islandObservations)
          (some replayD) exactTransform context.observer?
        (out, rep, pending, islandObservations) ← pure st3
      if generation.modelsSimpleInput t.name && ts.length == 1 && t.numNested == 0 &&
          basisRoot?.isNone && invalidBasis.isEmpty && !dropCanonicalBasisRecord then
        let ctors := (cs.filter (·.induct == t.name)).toArray.map fun c => (c.name, c.type)
        let st ← genPrim t.name t.levelParams t.numParams t.type ctors
          #[] reserved generation.basic (out, rep, pending, islandObservations)
          (some (replayD, constructionNormalizer)) exactTransform
          context.observer?
        (out, rep, pending, islandObservations) ← pure st
  if d matches .induct .. then
    let generated := out
    let islandModels := pending
    let islandAliases ← match sourceAliases.registerRecords generated with
      | .ok aliases => pure aliases
      | .error message => throwError
        "cannot register generated source replay aliases for {d.names}: \
            {sourceAliases.exactMessage message}"
    rep := { rep with
      generated := rep.generated.extract 0 reportedBefore ++
        (rep.generated.extract reportedBefore rep.generated.size).map fun (name, count) =>
          (islandAliases.exactName name, count)
      declined := rep.declined.extract 0 declinedBefore ++
        (rep.declined.extract declinedBefore rep.declined.size).map fun (name, reason) =>
          (islandAliases.exactName name, islandAliases.exactMessage reason)
      exempt := rep.exempt.extract 0 exemptBefore ++
        (rep.exempt.extract exemptBefore rep.exempt.size).map fun (name, reason) =>
          (islandAliases.exactName name, islandAliases.exactMessage reason)
      spliced := rep.spliced.extract 0 splicedBefore ++
        (rep.spliced.extract splicedBefore rep.spliced.size).map fun (name, names) =>
          (islandAliases.exactName name, names.map islandAliases.exactName) }
    let exactIslandModels := islandModels.map fun model =>
      { model with spliced := model.spliced.map islandAliases.exactName }
    rep := { rep with
      maxLivePendingModels := max rep.maxLivePendingModels islandModels.size
      maxLiveIslandRecords := max rep.maxLiveIslandRecords generated.size }
    let islandOwners := (rep.generated.extract reportedBefore rep.generated.size).foldl
      (fun owners entry => owners.insert entry.1) ({} : Std.HashSet Name)
    if generated.isEmpty && islandOwners.isEmpty then
      unless islandModels.isEmpty do
        throwError "empty generated island for {d.names} retained model witnesses"
      let ownerEnv := replayedOwnerEnv?.getD mainBefore
      mainEnv := ownerEnv
      setEnv ownerEnv
    else
      let (orderedGenerated, compact, mainWithSupport, statementReport) ← match
          ← closeModelIsland x mainBefore generated islandModels d persistentSyntax islandOwners
            islandAliases with
        | .ok result => pure result
        | .error message => throwError
            "owner-free generated declaration rejected for {d.names}: \
              {islandAliases.exactMessage message}"
      islandStatements :=
        { statementsChecked := islandStatements.statementsChecked +
            statementReport.statementsChecked
          violations := islandStatements.violations ++ statementReport.violations }
      unless compact.summaries.size == orderedGenerated.size &&
          compact.globalExtras.size == orderedGenerated.size &&
          compact.families.size == orderedGenerated.size do
        throwError "accepted island cardinality mismatch for {d.names}: \
          records={orderedGenerated.size}, summaries={compact.summaries.size}, \
          extras={compact.globalExtras.size}, families={compact.families.size}"
      if generation.typeCheckGenerated && rep.generatedKernelRejected.isNone then
        rep := { rep with generatedKernelChecks := rep.generatedKernelChecks + 1 }
        match ← checkGeneratedIn mainBefore (orderedGenerated.map islandAliases.buildRecord) with
        | .ok _ => pure ()
        | .error message =>
          rep := { rep with generatedKernelRejected := some (islandAliases.exactMessage message) }
      modeledSourceFamilies := compact.sourceFamilies
      modeledSourceGlobalExtra? := compact.sourceGlobalExtra?
      if compactMode then
        let islandNumber := compactIslandCount
        for localOrdinal in [:compact.summaries.size] do
          let summary := compact.summaries[localOrdinal]!
          compactCheck ← match compactCheck.push {
              owner := summary.owner
              modelSlots := summary.modelSlots
              globalExtra := compact.globalExtras[localOrdinal]!
              families := compact.families[localOrdinal]! } with
            | .ok next => pure next
            | .error message =>
              throwError "invalid compact output certificate: {message}"
          compactLocators := compactLocators.push (.generated islandNumber localOrdinal)
        compactIslandCount := compactIslandCount + 1
        for owner in compact.diagnosticOwners.toArray do
          diagnosticOwners := diagnosticOwners.insert owner
      if streamOutput && rep.generatedKernelRejected.isNone then
        streamIsland? := some orderedGenerated
      let persistentRecords := (generatedSupportRecords orderedGenerated exactIslandModels).filter
        (!canonicalBasisAlreadyIndexed persistentSyntax ·)
      persistentSyntax := ← match persistentSyntax.prependRecords persistentRecords with
        | .ok index => pure index
        | .error message => throwError
            "cannot index accepted persistent support for {d.names}: {message}"
      for record in orderedGenerated do
        for name in record.names do
          if canonicalBasisNames.contains name then
            canonicalBasisWritten := canonicalBasisWritten.insert name
      if retainOutput then legacyOut := legacyOut ++ orderedGenerated
      setEnv mainWithSupport
      if dropCanonicalBasisRecord then
        -- The owner-free island replay restores this record's own declaration
        -- together with the prefix; generation wrote it earlier and it is not
        -- installed a second time here either.
        mainEnv := mainWithSupport
      else if let some ownerDeclaration := toDeclaration mainWithSupport replayD then
        match mainWithSupport.addDeclCore 0 0 ownerDeclaration none false with
        | .ok env =>
          mainEnv := env
          setEnv env
        | .error exception =>
          let message ← (exception.toMessageData {}).toString
          return .unreplayable
            { rep with unreplayable := some s!"{d.names}: \
              {islandAliases.exactMessage message}" }
            sourceSteps
  else
    mainEnv ← getEnv
  -- **A dropped record leaves the output here.** Its declaration is already in
  -- the output, written by generation at the point it was first needed, so
  -- emitting this record too would bind the same constant twice.
  if retainOutput && !dropCanonicalBasisRecord then legacyOut := legacyOut.push d
  if compactMode && !dropCanonicalBasisRecord then
    let some firstName := d.names.head? | throwError "source declaration has no name"
    let some rawOrdinal := rawOrdinals[firstName]?
      | throwError "source declaration {firstName} lost its raw ordinal"
    compactCheck ← match compactCheck.push {
        owner := sourceSummary.owner
        modelSlots := sourceSummary.modelSlots
        globalExtra := modeledSourceGlobalExtra?.getD sourceGlobalExtra
        families := sourceFamilyRecord ++ modeledSourceFamilies } with
      | .ok next => pure next
      | .error message => throwError "invalid compact output certificate: {message}"
    compactLocators := compactLocators.push (.source rawOrdinal)
  if context.checkRecursors && !dropCanonicalBasisRecord then
    if let .induct _ _ rs := replayD then
      let (n, b) ← checkRecs rs
      rep := { rep with
        recChecked := rep.recChecked + n
        recMismatch := rep.recMismatch ++ b.map (fun name => sourceAliases.exactName name) }
  if context.collectTrace then
    let some firstName := d.names.head? | throwError "source declaration has no name"
    let some rawOrdinal := rawOrdinals[firstName]?
      | throwError "logical source declaration {firstName} lost its raw ordinal"
    sourceSteps := sourceSteps.push {
      sourceOrdinal
      rawOrdinal
      sourceNames := d.names.toArray
      sourceIsInductive := d matches .induct ..
      sourceInstalled := replayD.names.all mainEnv.constants.contains
      generated := rep.generated.extract reportedBefore rep.generated.size
      generatedRecords := out.size }
  if context.observer?.isSome then
    observations := observations ++ islandObservations
  if streamOutput && rep.generatedKernelRejected.isNone then
    let some emit := context.outputEmitter?
      | throwError "streaming output mode has no declaration emitter"
    if let some island := streamIsland? then
      emit (.generatedIsland island)
      streamStats := {
        streamStats with
        generatedRecords := streamStats.generatedRecords + island.size
        maxIslandRecords := max streamStats.maxIslandRecords island.size }
    unless dropCanonicalBasisRecord do
      emit (.source d)
      streamStats := { streamStats with sourceRecords := streamStats.sourceRecords + 1 }
  return .next {
    mainEnv, persistentSyntax, legacyOut, report := rep, compactCheck,
    compactLocators, compactIslandCount, diagnosticOwners,
    sourceOrdinal := sourceOrdinal + 1, islandStatements, invalidBasis,
    sourceSteps, observations, streamStats, inputFamilyOwners, inputFamilyOwnerSet,
    canonicalBasisWritten }

/-- Read out the verdicts once the logical source stream has been exhausted.

Nothing is checked here: the compact structural report was charged record by
record as the stream produced it, so this reads an accumulated value and never
walks a record array. The one exception is the retained-output compatibility
mode, whose whole point is that it kept the declarations. -/
private def FilterState.finalize (state : FilterState α) (context : FilterContext α) :
    MetaM (Array EDecl × Report × CompactPlan) := do
  let x := context.source
  let retention := context.retention
  let compactMode := retention.isCompact
  let retainOutput := retention.retainsOutput
  let sourceSyntax := context.sourceSyntax
  let reserved := context.reserved
  let legacyOut := state.legacyOut
  let islandStatements := state.islandStatements
  let mut rep := state.report
  -- Every record has already been charged against the structural check at the
  -- transition which emitted it.  Nothing is consumed here but the accumulated
  -- verdict.
  let compactCheckReport : Check.Report := if compactMode then
      state.compactCheck.finish
    else { familiesChecked := 0, violations := #[] }
  let compactStatementReport := if compactMode then
    ({ islandStatements with
      violations := islandStatements.violations ++
        state.compactCheck.globalExtrasFor state.diagnosticOwners } : Check.StatementReport)
  else islandStatements
  let statementReport ← if retainOutput then do
      let generatedOwners := rep.generated.foldl
        (fun owners entry => owners.insert entry.1) ({} : Std.HashSet Name)
      let finalExport := { x with decls := legacyOut }
      let finalFamilies := Check.statementFamiliesFor finalExport generatedOwners
      let generatedRecords := legacyOut.filter fun declaration =>
        declaration.names.any fun name => !reserved.contains name
      let finalIndex ← match sourceSyntax.prependRecords generatedRecords with
        | .error message => throwError "cannot index final generated records: {message}"
        | .ok index => pure (index.withGlobalExtras finalExport)
      let finalLocal :=
        Check.checkStatementFamiliesLocalWithIndex finalExport finalIndex finalFamilies
      unless islandStatements == finalLocal do
        throwError "per-island statement checks disagree with the final family-local aggregate: \
          islands={repr islandStatements}, aggregate={repr finalLocal}"
      let fullReport :=
        Check.checkStatementFamiliesWithIndex finalExport finalIndex finalFamilies
      pure fullReport
    else pure compactStatementReport
  rep := { rep with stmtChecked := statementReport.statementsChecked }
  rep := { rep with
    stmtErrors := statementReport.violations.map fun violation => violation.message }
  unless retainOutput || legacyOut.isEmpty do
    throwError "compact filter retained {legacyOut.size} cumulative declaration records"
  let compactPlan : CompactPlan := {
    declarations := state.compactLocators
    checkReport := compactCheckReport
    retainedGeneratedRecords := legacyOut.foldl (fun count declaration =>
      if declaration.names.any fun name => !reserved.contains name then count + 1 else count) 0
    streamStats := state.streamStats
    coveredInputOwners :=
      let invalidOwners := compactCheckReport.violations.foldl
        (fun owners violation => owners.insert violation.familyOwner)
        ({} : Std.HashSet Name)
      state.inputFamilyOwners.filter fun owner => !invalidOwners.contains owner }
  return (legacyOut, rep, compactPlan)

/-- Shared generation loop. Compact modes summarize every accepted island at
its close boundary; streaming emits and releases it, while the compatibility
full mode retains declarations. -/
private def runFilterCore (x : Export) (checkRecursors : Bool) (generation : Cli.Config)
    (retention : RetentionMode)
    (exactTransform : EDecl → EDecl := id) (collectTrace : Bool := false)
    (observer? : Option (IslandObserver α) := none)
    (outputEmitter? : Option StreamOutputEmitter := none) :
    MetaM (Array EDecl × Report × CompactPlan × Array FilterSourceStep ×
      Array α) := do
  -- **The two per-record accumulators that are not part of a verdict** — the
  -- observation array and the boundary trace — belong to the two regression
  -- seams, and both of those are retained-output entry points, which already
  -- hold every declaration. Asking for either from a compact or streaming run
  -- would introduce a whole-run accumulator into exactly the modes whose
  -- contract is that they have none, so it is refused rather than served.
  unless retention.retainsOutput || (!collectTrace && observer?.isNone) do
    throwError "declaration-wise generation has no whole-run trace or observation array"
  let sourceCensus := SourceCensus.ofSource x
  let plannedAliases ← match sourceCensus.replayAliases with
    | .ok aliases => pure aliases
    | .error message => throwError "cannot plan collision-safe source replay: {message}"
  let sourceAliases ← match sourceReplayInductiveDerivations
      sourceCensus.replayRoles plannedAliases with
    | .ok aliases => pure aliases
    | .error message => throwError "cannot derive collision-safe inductive replay: {message}"
  unless sourceAliases.isEmpty do
    for name in sourceCensus.replayRoles.quotients do
      if sourceAliases.hasExact name then
        throwError "normalized source-name collision moves quotient role {name}; \
          collision-safe quotient replay is not supported"
  let sourceOrder := Array.range sourceCensus.summaries.size
  -- Source records are consumed in their original stream order and no
  -- declaration is ever moved. An owner whose fixed *support* occurs later
  -- still declines at that owner; the one exception is the fixed basis, which
  -- generation writes at the first point it is needed and whose input-owned
  -- record is then dropped where it stands
  -- ([`InductiveModels.canonicalBasisRecordMatches`]).
  let mainEnv ← getEnv
  -- Reuse the immutable census products. Retained sources may still supply
  -- whole-export row caches; planned sources derive missing rows from each
  -- transient declaration at its logical transition.
  let sourceSyntax := sourceCensus.sourceSyntax
  let constructionSyntax ← if sourceAliases.isEmpty then pure sourceSyntax else do
    let mut exactRecords : Array EDecl := #[]
    let mut replayRecords : Array EDecl := #[]
    for ordinal in [:x.decls.size] do
      let declaration := x.decls[ordinal]!
      if sourceRecordUsesAliases sourceAliases sourceCensus.summaries[ordinal]! declaration then
        exactRecords := exactRecords.push declaration
        replayRecords := replayRecords.push (sourceAliases.buildRecord declaration)
    match sourceSyntax.withReplayRecords exactRecords replayRecords with
    | .ok index => pure index
    | .error message => throwError "cannot index collision-safe source replay: {message}"
  let constructionNormalizer := constructionSyntax.exactNormalizer
  let sourceSummaries := sourceCensus.summaries
  let sourceGlobalExtras := Check.globalExtraRecordsWithIndex sourceSyntax x.decls
  let sourceFamilyRecords := sourceCensus.familyCertificateRecords x
  let rawOrdinals := sourceCensus.rawOrdinals
  let reserved := sourceCensus.reserved
  let constructionReserved := reserved.fold (init := reserved) fun names name =>
    (sourceAliases.buildDerivedNames name).foldl (fun names build => names.insert build) names
  let context : FilterContext α := {
    source := x, checkRecursors, generation, retention, exactTransform,
    sourceSyntax, constructionSyntax, constructionNormalizer, sourceAliases,
    sourceSummaries, sourceGlobalExtras, sourceFamilyRecords,
    rawOrdinals, reserved, constructionReserved, collectTrace, observer?,
    outputEmitter? }
  let mut state : FilterState α :=
    { mainEnv := mainEnv, persistentSyntax := sourceSyntax }
  for rawOrdinal in sourceOrder do
    let some declaration := x.decls[rawOrdinal]?
      | throwError "source record {rawOrdinal} has no parsed payload"
    -- A `return` from a `for` loop preserves its mutable loop state. Move the
    -- real state out first so that `feedSource` owns its accumulated arrays;
    -- the placeholder is observed only by the loop machinery on an early
    -- return and is never part of the public result.
    let current := state
    state := { mainEnv, persistentSyntax := sourceSyntax }
    let feedResult ← current.feedSource context declaration
    match feedResult with
    | .next next => state := next
    | .unreplayable report sourceSteps =>
      return (x.decls, report, {}, sourceSteps, #[])
  let (decls, report, compact) ← state.finalize context
  return (decls, report, compact, state.sourceSteps, state.observations)

/-- **The filter.** -/
def runFilter (x : Export) (checkRecursors : Bool) (generation : Cli.Config) :
    MetaM (Array EDecl × Report) := do
  let (decls, report, _, _, _) ←
    runFilterCore (α := Unit) x checkRecursors generation .fullOutput
  return (decls, report)

/-- **The one entry point that observes islands at all.** The observer sees
every kernel-checked private model paired with the exact source record it was
built from, in emission order, and its results come back in that order.

The observation type is the caller's, not the driver's: `α` is opaque here, so
a module that defines one is imported by the caller and never by production.
Every other entry point supplies no observer, and then no observer runs — this
is not a best-effort hook that falls back to a default value. -/
def runFilterWithIslandObserver (x : Export) (checkRecursors : Bool)
    (generation : Cli.Config) (observe : IslandObserver α) :
    MetaM (Array EDecl × Report × Array α) := do
  let (decls, report, _, _, observations) ← runFilterCore x checkRecursors generation
    .fullOutput (observer? := some observe)
  return (decls, report, observations)

/-- Test-facing observer for the declaration-wise transition.  The generated
output and report are produced by the same core invocation as the snapshots;
ordinary production callers collect no snapshots. -/
def runFilterWithSourceTrace (x : Export) (checkRecursors : Bool)
    (generation : Cli.Config) : MetaM (Array EDecl × Report × Array FilterSourceStep) := do
  let (decls, report, _, steps, _) ←
    runFilterCore (α := Unit) x checkRecursors generation .fullOutput (collectTrace := true)
  return (decls, report, steps)

/-- Focused exact-syntax regression seam. The transform is applied only to
freshly serialized generated inductive records, before their immediate
composed consumer sees them; ordinary production callers use [`runFilter`]. -/
def runFilterWithExactBlockTransform (x : Export) (checkRecursors : Bool)
    (generation : Cli.Config) (transform : EDecl → EDecl) :
    MetaM (Array EDecl × Report) := do
  let (decls, report, _, _, _) ←
    runFilterCore (α := Unit) x checkRecursors generation .fullOutput transform
  return (decls, report)

/-- AST-dropping no-output generation. Accepted generated records are
summarized at island close, optionally kernel-checked according to the generated
gate, then discarded without opening a workspace or retaining a physical span. -/
def runFilterDiscarding (x : Export) (checkRecursors : Bool) (generation : Cli.Config) :
    MetaM (Report × CompactPlan) := do
  let (_, report, compact, _, _) ←
    runFilterCore (α := Unit) x checkRecursors generation .compactDiscard
  return (report, compact)

/-- Declaration-wise generated output. The callback sees a generated island
only after compact structural capture and its optional kernel gate, then sees
the corresponding exact source declaration. No output declaration is retained
after its callback returns. -/
def runFilterStreaming (x : Export) (checkRecursors : Bool)
    (generation : Cli.Config) (emit : StreamOutputEmitter) :
    MetaM (Report × CompactPlan) := do
  let (_, report, compact, _, _) ← runFilterCore (α := Unit) x checkRecursors generation
    .streamOutput (outputEmitter? := some emit)
  return (report, compact)
