import Modelgen.Simple
import Modelgen.Cli
import Modelgen.Naming
import Modelgen.Projection
import Modelgen.Check
import Modelgen.Order
import Modelgen.Spool

/-!
# The filter

`.ndjson` in, `.ndjson` out. Generation replays source declarations into its
analysis environment without checking their values; the independent
`--type-check-input` and `--type-check-output` gates request whole-stream kernel
verdicts. Every declaration this tool generates is always checked in an
owner-free environment before it can be emitted.

Beside each supported inductive the output carries that declaration's complete
public model family. Final ordering places every model record before its owner
and preserves the dependency constraints of the complete transformed export.
Input declarations themselves retain their exact exported records.

There are **three** constructions and they are separate files.
`src/Modelgen/Model.lean` specialises a nested declaration into a mutual block
and proves the export's recursors over it; `src/Modelgen/Mutual.lean` packs a
plain mutual block into an implementation tag and one auxiliary inductive;
`src/Modelgen/Simple.lean`
models a single inductive from the primitive basis. None is a degenerate case
of another, and this driver is the only thing that composes them.

## Why output is re-interned

Declaration records refer into one file-wide name, level, and expression arena.
After generation and ordering, [`Modelgen.Export.writeTo`] therefore serializes
the parsed snapshot as one self-contained arena. The writer streams record
lines rather than retaining the rendered file as one string.

## The free oracle

Lean's kernel builds the nested construction itself: given `Tree`'s
`inductDecl` it generates **both** `Tree.rec` and `Tree.rec_1`, at the shapes
the export declares. The optional internal recursor audit compares those
installed recursors with the export while replaying the file. The public
`--check` instead verifies the literal exported model interface.
-/

open Lean Meta

namespace Modelgen

/-- What one run did. -/
structure Report where
  generated : Array (Name × Nat) := #[]
  declined : Array (Name × String) := #[]
  /-- **The basis exemption, which is not a decline** ([`Modelgen.primBasis`]).
  `Eq`, `Nat`, `PSigma'`, and `PUnit` are the primitives
  the third construction is written in, so a run leaves them unmodelled *by
  definition*; counting them among the declines makes every coverage report
  a number it then had to walk back in the next sentence. Reported on their own
  lines and counted in their own row. -/
  exempt : Array (Name × String) := #[]
  /-- **Prelude constants the input did not declare and a model spliced in**,
  per declaration. `Eq`, the quotient and `Quot.sound` come out under Lean's
  own names and `funext` under the model's; `Modelgen.ensureEq` and
  `Modelgen.ensureFunext` say why the two are named differently. Printed,
  always: an insertion is a decision on record. -/
  spliced : Array (Name × Array Name) := #[]
  /-- Recursors whose replayed shape differs from the export's own. -/
  recMismatch : Array Name := #[]
  recChecked : Nat := 0
  /-- Public statements compared syntactically against the exact exported
  owner records, and the ones that did not match. -/
  stmtChecked : Nat := 0
  stmtErrors : Array String := #[]
  /-- Peak number of compact splice summaries retained inside one not-yet-closed
  generated island. `PendingModel` deliberately cannot retain an `Iso`. This
  is a retention invariant, not an output statistic. -/
  maxLivePendingModels : Nat := 0
  /-- Peak number of generated declaration records retained by one island
  before ordering, checking, and eventual staged serialization. -/
  maxLiveIslandRecords : Nat := 0
  /-- The input stopped replaying here: a declaration Lean's kernel will not
  load at all. The filter then becomes the identity, which is what a filter
  should be when it can do nothing. -/
  unreplayable : Option String := none
  deriving Inhabited, Repr, BEq

/-- Whether one reported decline still represents unsupported generation after
accounting for an existing or newly generated model. A noncanonical basis
owner is always unsupported: neither a model-shaped input family nor another
route may turn the reserved-name validation failure into success. -/
def declineIsUnsupported (alreadyCovered generated : Std.HashSet Name)
    (owner : Name) : Bool :=
  primBasis.contains owner ||
    (!alreadyCovered.contains owner && !generated.contains owner)

/-- The compact support-persistence witness retained until an island closes.
The complete `Iso` is needed only while composing and serializing a model;
retaining it here would keep every generated declaration and construction
expression alive until owner-free replay. -/
structure PendingModel where
  spliced : Array Name

/-- Value-free information captured while one accepted island's declarations
are still live. The arrays remain aligned with the island's checked record
order and therefore with a later `Spool.IslandCommit.declarations`. -/
structure CompactIsland where
  summaries : Array Order.DeclSummary
  globalExtras : Array Check.GlobalExtraRecord
  families : Array (Array Check.CompactFamilyCertificate)
  sourceFamilies : Array Check.CompactFamilyCertificate
  sourceGlobalExtra? : Option Check.GlobalExtraRecord
  diagnosticOwners : Std.HashSet Name

/-- One staged island after its generated expressions have been serialized.
The commit contains byte spans; `compact` contains names and dependency facts
only, so this value cannot retain the generated expression graph. -/
structure StagedIsland where
  compact : CompactIsland
  commit : Spool.IslandCommit

/-- Transaction endpoint for accepted generated islands. The Driver calls this
only after ordering, exact statement checking, owner-free kernel replay, and
support installation have all succeeded. -/
structure IslandSink where
  commit : Array EDecl → IO Spool.IslandCommit

/-- Adapt the append-only spool stage to the Driver sink interface. -/
def IslandSink.ofStage (stage : Spool.IslandStage) : IslandSink where
  commit records := do
    let cursor ← stage.cursor
    let prepared ← match Spool.prepareIsland cursor records with
      | .ok prepared => pure prepared
      | .error message => throw <| IO.userError message
    stage.commit prepared

/-- Origin of one declaration in the eventual compact record schedule. Source
indices address the parser certificate's declaration spans; generated indices
address an accepted island and its declaration span within that island. -/
inductive StagedLocator where
  | source (index : Nat)
  | generated (island declaration : Nat)
  deriving Inhabited, Repr, BEq

/-- Atomic value-free scheduling row. `summary` and `globalExtra` are captured
together with their byte locator and must always be permuted as one value. -/
structure StagedRecord where
  summary : Order.DeclSummary
  globalExtra : Check.GlobalExtraRecord
  families : Array Check.CompactFamilyCertificate := #[]
  /-- Syntax availability at certificate capture. Source payload can be
  recaptured with its current generated island while retaining a source byte
  locator and scheduling origin. -/
  checkIsland? : Option Nat := none
  locator : StagedLocator
  deriving Inhabited, Repr

private def compactAvailabilityError? (records : Array StagedRecord)
    (persistentSupportOrigins : Std.HashMap Name Nat) : Option String := Id.run do
  let mut generatedProviders : Std.HashMap Name Nat := {}
  for record in records do
    if let .island island := record.summary.origin then
      for name in record.summary.introduced do
        generatedProviders := generatedProviders.insert name island
  let availableAt := fun (origin : Option Nat) (name : Name) =>
    match generatedProviders[name]? with
    | none => true
    | some provider => match origin with
      | none => false
      | some consumer => provider == consumer ||
          (provider < consumer && persistentSupportOrigins[name]? == some provider)
  for record in records do
    let origin := record.checkIsland?.orElse fun _ => match record.summary.origin with
      | .source => none
      | .island island => some island
    if let some name := record.summary.referenced.toArray.find?
        (fun name => !availableAt origin name) then
      return some s!"compact syntax for {record.summary.introduced} references generated \
        provider {name} unavailable at its capture point"
    for family in record.families do
      if let some name := family.publicNames.find?
          (fun name => !availableAt family.captureIsland? name) then
        return some s!"compact family {family.owner} depends on generated public slot {name} \
          unavailable at its capture point"
  return none

/-- Emission-only shadow of the final transformed declaration stream. The
ordering/checking summaries have already been consumed: generated payloads are
addressed by island commits and `declarations` is the final compact order. -/
structure StagedPlan where
  islands : Array Spool.IslandCommit := #[]
  declarations : Array StagedLocator := #[]
  checkReport : Check.Report := { familiesChecked := 0, violations := #[] }
  /-- A semantic condition made AST-dropping unavailable. The private stage
  has not been published; callers must rerun the ordinary full-AST filter. -/
  unavailable? : Option String := none

/-- Physical declaration payload selected by one compact output row. -/
inductive StagedDeclarationSpan where
  | source (span : RawSpan)
  | generated (span : Spool.ByteSpan)
  deriving Inhabited, Repr, BEq

private def spansPartition (spans : Array Spool.ByteSpan) (size : UInt64) : Bool := Id.run do
  let mut endpoint : UInt64 := 0
  for span in spans do
    unless span.offset == endpoint do return false
    let some next := span.end? | return false
    unless next ≤ size do return false
    endpoint := next
  return endpoint == size

/-- Validate every compact/output axis before the first final byte is written.
This binds source raw ordinals, generated island spans, cursor publication, and
the final compact permutation without reparsing a staged export. -/
def StagedPlan.declarationSpans (plan : StagedPlan) (certificate : RawCertificate)
    (sourceSizes : RawSpoolSizes) (sourceDeclarationCount : Nat)
    (sealed : Spool.SealedIsland) :
    Except String (Array StagedDeclarationSpan) := do
  if let some why := plan.unavailable? then
    throw s!"staged plan is unavailable: {why}"
  discard <| certificate.validate sourceSizes sourceDeclarationCount
  let mut expectedCursor := Writer.Cursor.ofRaw certificate.cursor
  let mut generatedArenaSpans : Array Spool.ByteSpan := #[]
  let mut generatedDeclarationSpans : Array Spool.ByteSpan := #[]
  for island in plan.islands do
    unless island.before == expectedCursor do
      throw "staged island cursor chain has a gap or overlap"
    expectedCursor := island.after
    generatedArenaSpans := generatedArenaSpans ++ island.arenas
    generatedDeclarationSpans := generatedDeclarationSpans ++ island.declarations
  unless expectedCursor == sealed.cursor do
    throw "sealed cursor does not match staged island cursor chain"
  unless spansPartition generatedArenaSpans sealed.arenaSize do
    throw "generated arena spans do not partition the sealed spool"
  unless spansPartition generatedDeclarationSpans sealed.declarationSize do
    throw "generated declaration spans do not partition the sealed spool"

  let mut seenSource : Std.HashSet Nat := {}
  let mut seenGenerated : Std.HashSet (Nat × Nat) := {}
  let mut result : Array StagedDeclarationSpan := #[]
  for locator in plan.declarations do
    match locator with
    | .source ordinal =>
      let some span := certificate.declarations[ordinal]?
        | throw "staged source locator is outside the parser certificate"
      if seenSource.contains ordinal then throw "staged source locator is duplicated"
      seenSource := seenSource.insert ordinal
      result := result.push (.source span)
    | .generated island declaration =>
      let some artifact := plan.islands[island]?
        | throw "staged generated locator has an invalid island"
      let some span := artifact.declarations[declaration]?
        | throw "staged generated locator has an invalid declaration"
      let key := (island, declaration)
      if seenGenerated.contains key then throw "staged generated locator is duplicated"
      seenGenerated := seenGenerated.insert key
      result := result.push (.generated span)
  unless seenSource.size == certificate.declarations.size do
    throw "staged plan does not contain every source declaration"
  unless seenGenerated.size == generatedDeclarationSpans.size do
    throw "staged plan does not contain every generated declaration"
  return result

/-- The unique minor-premise position belonging to `constructorName` in a
mutual recursor telescope.  Each exported recursor record carries only its
own member's rules, while the installed mutual recursor consumes every
member's minors.  Reconstruct that order from `recursor.all`, retaining the
literal per-member rule order and ignoring the export's recursor-array order. -/
def recursorMinorIndex (constructors : Array ECtor) (recursors : Array ERec)
    (recursor : ERec) (constructorName : Name) : GenM Nat := do
  let mut rules : Array Name := #[]
  for member in recursor.all do
    for candidate in recursors do
      if candidate.all == recursor.all then
        for rule in candidate.rules do
          if constructors.any fun constructor =>
              constructor.name == rule.ctor && constructor.induct == member then
            rules := rules.push rule.ctor
  unless rules.size == recursor.numMinors do
    badShape s!"{recursor.name}'s mutual rule order has {rules.size} entries, expected {recursor.numMinors}"
  unless (rules.filter (· == constructorName)).size == 1 do
    badShape s!"{recursor.name} does not have exactly one rule for {constructorName}"
  let some index := rules.findIdx? (· == constructorName)
    | badShape s!"{recursor.name}'s mutual telescope has no rule for {constructorName}"
  return index

/-- Add the equality theorem for every member on which Lean's kernel enables
its unit-like shortcut.  The proof does not appeal to that shortcut: it runs
the model recursor twice, once for each side of the equality.  Constant
equality motives discharge the unrelated arms of a mutual/nested recursor. -/
def addUnitlikeTheorems (types : Array EIndType) (constructors : Array ECtor)
    (recursors : Array ERec) (reserved : Std.HashSet Name) (is : Iso) : GenM Iso := do
  let eligible := (Array.range types.size).filter fun k =>
    types[k]!.isKernelUnitlike constructors.toList
  if eligible.isEmpty then return is
  unless types.size == is.numAll && is.selfNames.size == is.numAll do
    badShape "the unit-like member table does not match the generated model"

  -- Collisions are tested at the emitted names.  A simple model built under an
  -- alias is renamed only when serialized, so its environment-local theorem
  -- name is derived separately from `selfNames` below.
  let publicTable := eligible.foldl (fun table k =>
    table.addMetadata .unitlike types[k]!.name) Naming.Table.empty
  let occupied := reserved.fold (fun names name => names.push name) #[]
  let census := publicTable.collisionCensus occupied
  if let some name := census.taken[0]? <|> census.duplicateRequirements[0]? then
    declineWith (.nameTaken name)

  let env ← getEnv
  let eqi ← match EqInfo.check env with
    | .ok eqi => pure eqi
    | .error message => badShape message
  let us := is.levelParams.map Level.param
  let mut out := is.decls
  let mut unitlikes := is.unitlikes

  for k in eligible do
    let type := types[k]!
    let [constructorName] := type.ctors
      | badShape s!"{type.name} changed shape while generating its unit-like theorem"
    unless constructors.any fun constructor =>
        constructor.name == constructorName && constructor.induct == type.name do
      badShape s!"{constructorName} has no constructor record"
    let some recursor := recursors.find? fun recursor =>
        recursor.rules.any (·.ctor == constructorName)
      | badShape s!"{type.name} has no corresponding exported recursor rule"
    let minorIndex ← recursorMinorIndex constructors recursors recursor constructorName
    let some motiveIndex := recursor.all.idxOf? type.name
      | badShape s!"{recursor.name} has no motive for {type.name}"
    unless recursor.numIndices == 0 do
      badShape s!"unit-like recursor {recursor.name} unexpectedly has indices"
    unless recursor.numMotives == recursor.all.length &&
        recursor.numMinors == constructors.size do
      badShape s!"{recursor.name} has an unexpected mutual telescope"

    let modelType := is.selfNames[k]!
    let some (_, modelConstructor) := is.ctors.find? (·.1 == constructorName)
      | badShape s!"{constructorName} has no model constructor"
    let modelRecursor := is.recs[k]!
    let theoremName := Name.str modelType "unitlike"
    if env.constants.contains theoremName then declineWith (.nameTaken theoremName)
    let typeInfo ← constInfo modelType
    let recInfo ← constInfo modelRecursor
    let recLevels ←
      if recInfo.levelParams.length == is.levelParams.length + 1 then
        pure (.zero :: us)
      else if recInfo.levelParams.length == is.levelParams.length then
        pure us
      else
        badShape s!"{modelRecursor} carries unexpected universe parameters"
    let recType := recInfo.type.instantiateLevelParams recInfo.levelParams recLevels
    let ctorInfo ← constInfo modelConstructor
    let ctorType := ctorInfo.type.instantiateLevelParams ctorInfo.levelParams us

    let declaration ← forallBoundedTelescope typeInfo.type (some type.numParams) fun ps _ => do
      let carrier := mkAppN (.const modelType us) ps
      let constructor ← do
        let ctorTail ← instForall ctorType ps
        unless numForalls ctorTail == 0 do
          badShape s!"unit-like constructor {modelConstructor} has fields"
        pure (mkAppN (.const modelConstructor us) ps)
      let eqcc := eqi.mk' (← ilevel carrier) carrier constructor constructor
      let refl := eqi.refl' (← ilevel carrier) carrier constructor
      let carrierLevel ← ilevel carrier

      let constantMotive := fun (domain proposition : Expr) =>
        forallTelescope domain fun binders _ => mkLambdaFVars binders proposition
      let applyRec := fun (targetMotive targetMinor major : Expr) => do
        let mut current ← instForall recType ps
        let mut args := ps
        for motive in [0:recursor.numMotives] do
          let .forallE _ domain body _ := current
            | badShape s!"{modelRecursor} has too few motive binders"
          let value ← if motive == motiveIndex then pure targetMotive
            else constantMotive domain eqcc
          args := args.push value
          current := body.instantiate1 value
        for minor in [0:recursor.numMinors] do
          let .forallE _ domain body _ := current
            | badShape s!"{modelRecursor} has too few minor binders"
          let value ← if minor == minorIndex then pure targetMinor
            else forallTelescope domain fun binders _ => mkLambdaFVars binders refl
          args := args.push value
          current := body.instantiate1 value
        let .forallE _ majorType _ _ := current
          | badShape s!"{modelRecursor} has no major premise"
        unless ← isDefEq majorType carrier do
          badShape s!"{modelRecursor}'s major premise is not {modelType}"
        pure (mkAppN (.const modelRecursor recLevels) (args.push major))

      let innerMotive ← withLocalDeclD `y carrier fun y =>
        mkLambdaFVars #[y] (eqi.mk' carrierLevel carrier constructor y)
      let innerMinor := refl
      let outerMinor ← withLocalDeclD `y carrier fun y => do
        mkLambdaFVars #[y] (← applyRec innerMotive innerMinor y)
      let outerMotive ← withLocalDeclD `x carrier fun x => do
        let body ← withLocalDeclD `y carrier fun y =>
          mkForallFVars #[y] (eqi.mk' carrierLevel carrier x y)
        mkLambdaFVars #[x] body

      let theoremType ← withLocalDeclD `x carrier fun x =>
        withLocalDeclD `y carrier fun y =>
          mkForallFVars (ps ++ #[x, y]) (eqi.mk' carrierLevel carrier x y)
      let theoremValue ← withLocalDeclD `x carrier fun x => do
        mkLambdaFVars (ps.push x) (← applyRec outerMotive outerMinor x)
      pure <| Declaration.thmDecl
        { name := theoremName, levelParams := is.levelParams
          type := theoremType, value := theoremValue }
    addChecked declaration
    out := out.push declaration
    unitlikes := unitlikes.push (k, theoremName)
  return { is with decls := out, unitlikes }

private partial def findConstructorApp? (targetConstructor : Name)
    (expression : Expr) : Option Expr :=
  if expression.getAppFn.isConstOf targetConstructor then some expression
  else match expression with
    | .app fn argument =>
      findConstructorApp? targetConstructor fn <|>
        findConstructorApp? targetConstructor argument
    | .lam _ type body _ | .forallE _ type body _ =>
      findConstructorApp? targetConstructor type <|>
        findConstructorApp? targetConstructor body
    | .letE _ type value body _ =>
      findConstructorApp? targetConstructor type <|>
        findConstructorApp? targetConstructor value <|>
        findConstructorApp? targetConstructor body
    | .mdata _ body => findConstructorApp? targetConstructor body
    | .proj _ _ struct => findConstructorApp? targetConstructor struct
    | _ => none

/-- Build the parameter/motive/minor prefix for one selected member of a
mutual model recursor.  The callback supplies the body of the selected minor;
all unrelated motives and minors receive inhabited propositional lifts. -/
private def structureRecursorPreArgumentsWith (eqi : EqInfo) (sourceRecursor : ERec)
    (modelRecursor targetConstructor : Name) (motiveIndex : Nat)
    (params : Array Expr) (carrier major targetMotive : Expr)
    (motiveLevel : Level) (recLevels : List Level)
    (selectedMinorBody : Array Expr → Expr → GenM Expr) :
    GenM (Array Expr) := do
  let modelRecursorInfo ← constInfo modelRecursor
  let recType := modelRecursorInfo.type.instantiateLevelParams
    modelRecursorInfo.levelParams recLevels
  let mut current ← instForall recType params
  let mut arguments := params
  let carrierLevel ← ilevel carrier
  let fillerProposition := eqi.mk' carrierLevel carrier major major
  -- Every motive of one mutual recursor lands in the same `Sort motiveLevel`.
  -- A bare equality inhabits `Prop`, which is not syntactically a term of
  -- `Type u` at a variable `u`; lift it through the primitive basis so the
  -- unrelated motives and minors have exactly the recursor's required sort.
  let fillerType := puliftT motiveLevel fillerProposition
  let fillerValue := puliftUp motiveLevel fillerProposition
    (eqi.refl' carrierLevel carrier major)
  let constantMotive := fun (domain proposition : Expr) =>
    forallTelescope domain fun binders _ => mkLambdaFVars binders proposition
  let selectedMinorIndex ← forallBoundedTelescope current (some sourceRecursor.numMotives)
      fun _ afterMotives =>
    forallBoundedTelescope afterMotives (some sourceRecursor.numMinors) fun minors _ => do
      let mut selected : Option Nat := none
      for i in [:minors.size] do
        if (findConstructorApp? targetConstructor (← inferType minors[i]!)).isSome then
          if selected.isSome then
            badShape s!"{modelRecursor} has several minors for {targetConstructor}"
          selected := some i
      let some index := selected
        | badShape s!"{modelRecursor} has no minor for {targetConstructor}"
      return index
  for motive in [0:sourceRecursor.numMotives] do
    let .forallE _ domain body _ := current
      | badShape s!"{modelRecursor} has too few motive binders"
    let value ← if motive == motiveIndex then pure targetMotive
      else constantMotive domain fillerType
    arguments := arguments.push value
    current := body.instantiate1 value
  for minorIndex in [0:sourceRecursor.numMinors] do
    let .forallE _ domain body _ := current
      | badShape s!"{modelRecursor} has too few minor binders"
    let value ← if minorIndex == selectedMinorIndex then
      forallTelescope domain fun binders conclusion => do
        mkLambdaFVars binders (← selectedMinorBody binders conclusion)
      else forallTelescope domain fun binders _ => mkLambdaFVars binders fillerValue
    arguments := arguments.push value
    current := body.instantiate1 value
  return arguments

/-- Build the recursor prefix selecting one intrinsic structure projection.
The selected minor is normalized with the already-generated lower field
projections and their literal reduction theorems. -/
def structureRecursorPreArguments (eqi : EqInfo) (sourceRecursor : ERec)
    (modelRecursor targetConstructor : Name) (motiveIndex : Nat)
    (params : Array Expr) (carrier major targetMotive : Expr) (targetFieldIndex : Nat)
    (numConstructorFields : Nat)
    (motiveLevel : Level) (recLevels modelLevels : List Level)
    (projectionModels : Array (Name × Nat × Name × Name)) (owner : Name) :
    GenM (Array Expr) :=
  structureRecursorPreArgumentsWith eqi sourceRecursor modelRecursor targetConstructor
    motiveIndex params carrier major targetMotive motiveLevel recLevels fun _ conclusion => do
        let some constructorApp := findConstructorApp? targetConstructor conclusion
          | badShape s!"{targetConstructor}'s selected minor has no constructor conclusion"
        let constructorArgs := constructorApp.getAppArgs
        unless constructorArgs.size >= params.size + numConstructorFields do
          badShape s!"{targetConstructor}'s selected minor has a short constructor application"
        let fields := constructorArgs.extract params.size (params.size + numConstructorFields)
        let majorType ← inferType constructorApp
        let ownerArguments := majorType.getAppArgs
        let indices := ownerArguments.extract params.size ownerArguments.size
        let mut normalizedFields : Array ProjectionField := #[]
        for fieldIndex in [:fields.size] do
          let value := fields[fieldIndex]!
          let type ← inferType value
          let level ← ilevel type
          let prior? := projectionModels.find? fun entry =>
            entry.1 == owner && entry.2.1 == fieldIndex
          let projected := match prior? with
            | some (_, _, projection, _) =>
              mkAppN (.const projection modelLevels) (params ++ indices ++ #[constructorApp])
            | none => value
          let iota? := prior?.map fun (_, _, _, iota) =>
            mkAppN (.const iota modelLevels) constructorArgs
          normalizedFields := normalizedFields.push
            { name := Name.mkSimple s!"field_{fieldIndex}", info := .default,
              value, type, level, projected, iota? }
        let normalized ← match ProjectionField.normalizeProjectionField eqi
            (Naming.projectionName owner targetFieldIndex) normalizedFields targetFieldIndex with
          | .ok value => pure value
          | .error message => badShape message
        pure normalized

/-- Build the recursor prefix used by a structure-eta proof.  The selected
minor is supplied exactly; unrelated arms are inhabited without assuming
anything about sibling field codomains. -/
private def structureEtaRecursorPreArguments (eqi : EqInfo) (sourceRecursor : ERec)
    (modelRecursor targetConstructor : Name) (motiveIndex : Nat)
    (params : Array Expr) (carrier major targetMotive targetMinor : Expr)
    (recLevels : List Level) : GenM (Array Expr) :=
  structureRecursorPreArgumentsWith eqi sourceRecursor modelRecursor targetConstructor
    motiveIndex params carrier major targetMotive .zero recLevels fun binders _ =>
      pure (targetMinor.beta binders)

private partial def projectionFieldEligibleM (ownerIsProp : Bool) (fieldIndex : Nat)
    (current : Expr) : MetaM Bool := do
  let current ← whnf current
  let .forallE name fieldType body info := current | return false
  unless ownerIsProp do
    if fieldIndex == 0 then return true
    return ← withLocalDecl name info fieldType fun value =>
      projectionFieldEligibleM false (fieldIndex - 1) (body.instantiate1 value)
  let fieldIsProp ← isProp fieldType
  if fieldIndex == 0 then return !ownerIsProp || fieldIsProp
  if ownerIsProp && body.hasLooseBVars && !fieldIsProp then return false
  withLocalDecl name info fieldType fun value =>
    projectionFieldEligibleM ownerIsProp (fieldIndex - 1) (body.instantiate1 value)

/-- Mirror the kernel's `infer_proj` field walk.  A Prop-valued owner may only
project proof fields, and may not cross an earlier data field on which the
remaining constructor telescope depends. -/
private def eligibleProjectionFieldsM (type : EIndType) (constructor : ECtor) : MetaM (Array Nat) := do
  let ownerIsProp ← isPropFormerType type.type
  forallBoundedTelescope constructor.type (some type.numParams) fun _ fieldsType => do
    let mut result := #[]
    for fieldIndex in [:constructor.numFields] do
      if ← projectionFieldEligibleM ownerIsProp fieldIndex fieldsType then
        result := result.push fieldIndex
    return result

/-- Add modeled primitive projections and their literal constructor rules for
every kernel structure-like member in a generated block.

This is a post-generator operation, not a simple-inductive special case.  A
non-recursive mutual block can have several structure-like members, and the
kernel predicate is per member.  For the selected member the recursor motive
is the projection codomain and its constructor minor selects the field.  Every
unrelated mutual motive is the inhabited constant lift of `self = self` into
the shared motive sort; thus no arbitrary inhabitant of an unrelated field
codomain is assumed. -/
def addProjectionModels (types : Array EIndType) (constructors : Array ECtor)
    (recursors : Array ERec) (_projections : Array EProjection)
    (reserved : Std.HashSet Name) (is : Iso) : GenM Iso := do
  let mut fields : Array (Name × Nat) := #[]
  for type in types do
    if let [constructorName] := type.ctors then
      if let some constructor := constructors.find? fun constructor =>
          constructor.name == constructorName && constructor.induct == type.name then
        for fieldIndex in ← eligibleProjectionFieldsM type constructor do
          fields := fields.push (type.name, fieldIndex)
  if fields.isEmpty then return is
  unless types.size == is.numAll && is.selfNames.size == is.numAll do
    badShape "the structure-member table does not match the generated model"

  let publicTable := fields.foldl (fun table field =>
    table.addProjection field.1 field.2) Naming.Table.empty
  let occupied := reserved.fold (fun names name => names.push name) #[]
  let census := publicTable.collisionCensus occupied
  if let some name := census.taken[0]? <|> census.duplicateRequirements[0]? then
    declineWith (.nameTaken name)

  -- Unselected mutual motives must still inhabit the selected projection's
  -- result sort. The internally derived tight-pair/PUnit lift carries the
  -- reflexive equality filler to that exact, possibly variable universe.
  let puliftDecls ← if recursors.any (·.numMotives > 1) then
    ensureExactSortLift reserved else pure #[]

  let env ← getEnv
  let eqi ← match EqInfo.check env with
    | .ok eqi => pure eqi
    | .error message => badShape message
  let us := is.levelParams.map Level.param
  let mut out := is.decls
  let mut spliced := is.spliced
  for declaration in puliftDecls do
    out := out.push declaration
    spliced := spliced ++ declaration.getNames.toArray
  let mut projectionModels := is.projections
  let mut aliases := is.aliases

  for (owner, fieldIndex) in fields do
    let some memberIndex := types.findIdx? (·.name == owner)
      | badShape s!"{owner} has no structure member"
    let type := types[memberIndex]!
    let [constructorName] := type.ctors
      | badShape s!"{type.name} does not have exactly one constructor"
    let some constructorIndex := constructors.findIdx? fun constructor =>
        constructor.name == constructorName && constructor.induct == type.name
      | badShape s!"{constructorName} has no constructor record"
    let constructor := constructors[constructorIndex]!
    -- Exported recursors are not required to follow the type array's order:
    -- Lean emits a wholly non-recursive mutual structure fixture's recursors
    -- in reverse member order.  The unique constructor rule is the exact,
    -- order-independent association.
    let some recursor := recursors.find? fun recursor =>
        recursor.rules.any (·.ctor == constructorName)
      | badShape s!"{type.name} has no corresponding exported recursor rule"
    let some motiveIndex := recursor.all.idxOf? type.name
      | badShape s!"{recursor.name} has no motive for {type.name}"
    unless fieldIndex < constructor.numFields do
      badShape s!"{type.name}'s field {fieldIndex} is outside {constructorName}'s telescope"

    let modelType := is.selfNames[memberIndex]!
    let some (_, modelConstructor) := is.ctors.find? (·.1 == constructorName)
      | badShape s!"{constructorName} has no model constructor"
    let modelRecursor := is.recs[memberIndex]!
    let publicProjection := Naming.projectionName type.name fieldIndex
    let publicRule := Naming.projectionIotaName type.name fieldIndex
    let (modelProjection, modelRule) :=
      if aliases.buildRoot?.isSome then
        let base := Name.str modelType s!"proj_{fieldIndex}"
        (base, Name.str base "iota")
      else
        (publicProjection, publicRule)
    if (← getEnv).constants.contains modelProjection then declineWith (.nameTaken publicProjection)
    if (← getEnv).constants.contains modelRule then declineWith (.nameTaken publicRule)
    let override? := is.projectionOverrides.find? fun entry =>
      entry.1 == type.name && entry.2.1 == fieldIndex

    let modelConstructorType := (← constInfo modelConstructor).type
    let modelTypeInfo ← constInfo modelType
    let modelRecursorInfo ← constInfo modelRecursor
    let ownerArity := type.numParams + type.numIndices
    let carrier := fun (arguments : Array Expr) => mkAppN (.const modelType us) arguments

    -- Read the selected field type from the modeled constructor telescope.
    -- Every earlier field variable is replaced by the intrinsic projection
    -- already emitted for that field, so dependent results mention no
    -- constructor-local variable outside their scope.
    let projectionType ← forallBoundedTelescope modelTypeInfo.type (some ownerArity)
        fun ownerArguments _ => do
      let params := ownerArguments.extract 0 type.numParams
      let fieldsType ← instantiateForall modelConstructorType params
      withLocalDeclD `self (carrier ownerArguments) fun self => do
        let mut current := fieldsType
        for earlier in [0:fieldIndex + 1] do
          let .forallE _ fieldType rest _ := current
            | badShape s!"{constructorName} has too few fields"
          if earlier == fieldIndex then
            return ← mkForallFVars (ownerArguments.push self) fieldType
          let some (_, _, earlierProjection, _) := projectionModels.find? fun entry =>
              entry.1 == type.name && entry.2.1 == earlier
            | badShape s!"{type.name}'s field {fieldIndex} precedes intrinsic field {earlier}"
          let selected := mkAppN (.const earlierProjection us) (ownerArguments.push self)
          current := rest.instantiate1 selected
        badShape s!"{constructorName} has no field {fieldIndex}"

    let value ← match override? with
      | some (_, _, value, _) => pure value
      | none => do
        forallBoundedTelescope projectionType (some (ownerArity + 1))
            fun arguments result => do
        let params := arguments.extract 0 type.numParams
        let indices := arguments.extract type.numParams ownerArity
        let self := arguments[ownerArity]!
        let targetMotive ← mkLambdaFVars (indices.push self) result
        let resultLevel ← ilevel result
        let recLevels ←
          if modelRecursorInfo.levelParams.length == is.levelParams.length + 1 then
            pure (resultLevel :: us)
          else if modelRecursorInfo.levelParams.length == is.levelParams.length then
            pure us
          else
            badShape s!"{modelRecursor} carries unexpected universe parameters"
        let pre ← structureRecursorPreArguments eqi recursor modelRecursor
          modelConstructor motiveIndex params (carrier (params ++ indices))
          self targetMotive fieldIndex constructor.numFields resultLevel recLevels us
          projectionModels type.name
        mkLambdaFVars arguments
          (mkAppN (.const modelRecursor recLevels) (pre ++ indices ++ #[self]))
    let definition := Declaration.defnDecl
      { name := modelProjection, levelParams := is.levelParams, type := projectionType,
        value, hints := .abbrev, safety := .safe }
    addChecked definition
    out := out.push definition

    let some (_, _, iotaTheorem) := is.iotas.find? fun (index, key, _) =>
        index == memberIndex && key == constructorName
      | badShape s!"{modelRecursor} has no iota theorem for {constructorName}"
    let rule ← forallBoundedTelescope modelConstructorType
        (some (type.numParams + constructor.numFields)) fun arguments _ => do
      let params := arguments.extract 0 type.numParams
      let fields := arguments.extract type.numParams arguments.size
      let major := mkAppN (.const modelConstructor us) arguments
      let majorType ← inferType major
      let majorArguments := majorType.getAppArgs
      unless majorArguments.size == ownerArity do
        badShape s!"{modelConstructor}'s result has {majorArguments.size} arguments, expected {ownerArity}"
      let indices := majorArguments.extract type.numParams ownerArity
      let lhs := mkAppN (.const modelProjection us) (params ++ indices ++ #[major])
      let mut normalizedFields : Array ProjectionField := #[]
      for index in [:fields.size] do
        let value := fields[index]!
        let fieldType ← inferType value
        let level ← getLevel fieldType
        let prior? := projectionModels.find? fun entry =>
          entry.1 == type.name && entry.2.1 == index
        let projected := if index == fieldIndex then lhs else match prior? with
          | some (_, _, projection, _) =>
            mkAppN (.const projection us) (params ++ indices ++ #[major])
          | none => value
        let iota? := prior?.map fun (_, _, _, iota) =>
          mkAppN (.const iota us) arguments
        normalizedFields := normalizedFields.push
          { name := Name.mkSimple s!"field_{index}", info := .default,
            value, type := fieldType, level, projected, iota? }
      let rhs ←
        if projectionIotaUsesLiteralField types type then
          pure fields[fieldIndex]!
        else
          match ProjectionField.normalizeProjectionField eqi
            publicProjection normalizedFields fieldIndex with
          | .ok value => pure value
          | .error message => badShape message
      let alpha ← inferType lhs
      let fieldLevel ← ilevel alpha
      let proof ← if projectionIotaUsesLiteralField types type then
          pure (eqi.refl' fieldLevel alpha lhs)
        else match override? with
        | some (_, _, _, proof) => pure (proof.beta arguments)
        | none => do
          let targetMotive ← forallBoundedTelescope
              (← instantiateForall projectionType params) (some (type.numIndices + 1))
              fun motiveArguments result => mkLambdaFVars motiveArguments result
          let recLevels ←
            if modelRecursorInfo.levelParams.length == is.levelParams.length + 1 then
              pure (fieldLevel :: us)
            else if modelRecursorInfo.levelParams.length == is.levelParams.length then
              pure us
            else
              badShape s!"{modelRecursor} carries unexpected universe parameters"
          let pre ← structureRecursorPreArguments eqi recursor modelRecursor
            modelConstructor motiveIndex params (carrier (params ++ indices))
            major targetMotive fieldIndex constructor.numFields fieldLevel recLevels us
            projectionModels type.name
          pure (mkAppN (.const iotaTheorem recLevels) (pre ++ fields))
      let type ← mkForallFVars arguments (eqi.mk' fieldLevel alpha lhs rhs)
      let value ← mkLambdaFVars arguments proof
      return Declaration.thmDecl
        { name := modelRule, levelParams := is.levelParams, type, value }
    addChecked rule
    out := out.push rule
    projectionModels := projectionModels.push (type.name, fieldIndex, modelProjection, modelRule)
    aliases := aliases.insert modelProjection publicProjection
    aliases := aliases.insert modelRule publicRule

  return { is with decls := out, projections := projectionModels, spliced, aliases := aliases }

/-- Add the literal structure-eta theorem for every non-propositional member
on which Lean's kernel enables structure eta.

The reconstruction uses the member's intrinsic modeled projections in
zero-based field order.  This interface is independent of whether the export
also contains named wrapper definitions for any fields. -/
def addStructureEtaTheorems (types : Array EIndType) (constructors : Array ECtor)
    (recursors : Array ERec) (reserved : Std.HashSet Name) (is : Iso) : GenM Iso := do
  let mut eligible : Array Nat := #[]
  for k in [0:types.size] do
    let type := types[k]!
    if type.isKernelStructureLike constructors.toList && !(← isPropFormerType type.type) then
      eligible := eligible.push k
  if eligible.isEmpty then return is
  unless types.size == is.numAll && is.selfNames.size == is.numAll do
    badShape "the structure-eta member table does not match the generated model"

  let publicTable := eligible.foldl (fun table k =>
    table.addMetadata .eta types[k]!.name) Naming.Table.empty
  let occupied := reserved.fold (fun names name => names.push name) #[]
  let census := publicTable.collisionCensus occupied
  if let some name := census.taken[0]? <|> census.duplicateRequirements[0]? then
    declineWith (.nameTaken name)

  -- A mutual recursor's unrelated motives need an inhabitant at the selected
  -- motive sort. The common adapter uses the derived tight-pair/PUnit lift.
  let puliftDecls ← if types.size > 1 then ensureExactSortLift reserved else pure #[]
  let env ← getEnv
  let eqi ← match EqInfo.check env with
    | .ok eqi => pure eqi
    | .error message => badShape message
  let us := is.levelParams.map Level.param
  let mut out := is.decls
  let mut spliced := is.spliced
  let mut etas := is.etas
  let mut aliases := is.aliases
  for declaration in puliftDecls do
    out := out.push declaration
    spliced := spliced ++ declaration.getNames.toArray

  for k in eligible do
    let type := types[k]!
    let [constructorName] := type.ctors
      | badShape s!"{type.name} changed shape while generating structure eta"
    let some constructor := constructors.find? fun constructor =>
        constructor.name == constructorName && constructor.induct == type.name
      | badShape s!"{constructorName} has no constructor record"
    let some recursor := recursors.find? fun recursor =>
        recursor.rules.any (·.ctor == constructorName)
      | badShape s!"{type.name} has no corresponding exported recursor rule"
    let some motiveIndex := recursor.all.idxOf? type.name
      | badShape s!"{recursor.name} has no motive for {type.name}"
    unless recursor.numIndices == 0 do
      badShape s!"structure recursor {recursor.name} unexpectedly has indices"
    unless recursor.numMotives == recursor.all.length &&
        recursor.numMinors == constructors.size do
      badShape s!"{recursor.name} has an unexpected mutual telescope"

    let modelType := is.selfNames[k]!
    let some (_, modelConstructor) := is.ctors.find? (·.1 == constructorName)
      | badShape s!"{constructorName} has no model constructor"
    let modelRecursor := is.recs[k]!
    let theoremName := Name.str modelType "eta"
    let publicName := Naming.etaName type.name
    if (← getEnv).constants.contains theoremName then declineWith (.nameTaken publicName)
    let typeInfo ← constInfo modelType
    let constructorInfo ← constInfo modelConstructor
    let recursorInfo ← constInfo modelRecursor
    let mut modelProjections : Array Name := #[]
    for fieldIndex in [0:constructor.numFields] do
      let some (_, _, modelProjection, _) := is.projections.find? fun entry =>
          entry.1 == type.name && entry.2.1 == fieldIndex
        | badShape s!"{type.name} has no intrinsic modeled projection for field {fieldIndex}"
      modelProjections := modelProjections.push modelProjection

    let declaration ← forallBoundedTelescope typeInfo.type (some type.numParams)
        fun params _ => do
      let carrier := mkAppN (.const modelType us) params
      let carrierLevel ← ilevel carrier
      let constructorTail ← instForall constructorInfo.type params
      withLocalDeclD `x carrier fun x => do
        let reconstruct := fun z =>
          mkAppN (.const modelConstructor us)
            (params ++ modelProjections.map fun projection =>
              mkAppN (.const projection us) (params.push z))
        let proposition := eqi.mk' carrierLevel carrier x (reconstruct x)
        let targetMotive ← withLocalDeclD `z carrier fun z =>
          mkLambdaFVars #[z] (eqi.mk' carrierLevel carrier z (reconstruct z))
        let targetMinor ← forallBoundedTelescope constructorTail
            (some constructor.numFields) fun fields _ => do
          let major := mkAppN (.const modelConstructor us) (params ++ fields)
          mkLambdaFVars fields (eqi.refl' carrierLevel carrier major)
        let recLevels ←
          if recursorInfo.levelParams.length == is.levelParams.length + 1 then
            pure (.zero :: us)
          else if recursorInfo.levelParams.length == is.levelParams.length then
            pure us
          else
            badShape s!"{modelRecursor} carries unexpected universe parameters"
        let pre ← structureEtaRecursorPreArguments eqi recursor modelRecursor
          modelConstructor motiveIndex params carrier x targetMotive targetMinor recLevels
        let proof := mkAppN (.const modelRecursor recLevels) (pre.push x)
        return Declaration.thmDecl
          { name := theoremName, levelParams := is.levelParams
            type := ← mkForallFVars (params.push x) proposition
            value := ← mkLambdaFVars (params.push x) proof }
    addChecked declaration
    out := out.push declaration
    etas := etas.push (k, theoremName)
    aliases := aliases.insert theoremName publicName
  return { is with decls := out, etas, spliced, aliases }

/-- Add all declaration-local structure metadata in dependency order. -/
def addStructureModels (types : Array EIndType) (constructors : Array ECtor)
    (recursors : Array ERec) (projections : Array EProjection)
    (reserved : Std.HashSet Name) (is : Iso) : GenM Iso := do
  let is ← addProjectionModels types constructors recursors projections reserved is
  let is ← addStructureEtaTheorems types constructors recursors reserved is
  addUnitlikeTheorems types constructors recursors reserved is

private abbrev FilterState := Array EDecl × Report × Array PendingModel

/-- Read one inductive block back out of the environment, including the
recursors the **kernel** generated for it. -/
def indEDecl (names : Array Name) : MetaM EDecl := do
  let env ← getEnv
  let mut ts : Array EIndType := #[]
  let mut cs : Array ECtor := #[]
  let mut rs : Array ERec := #[]
  for n in names do
    let some (.inductInfo iv) := env.constants.find? n | throwError "{n} is not an inductive"
    ts := ts.push
      { name := iv.name, levelParams := iv.levelParams, type := iv.type, all := iv.all
        ctors := iv.ctors, numParams := iv.numParams, numIndices := iv.numIndices
        numNested := iv.numNested, isRec := iv.isRec, isReflexive := iv.isReflexive
        isUnsafe := iv.isUnsafe }
    for cn in iv.ctors do
      let some (.ctorInfo cv) := env.constants.find? cn | throwError "{cn} is not a constructor"
      cs := cs.push
        { name := cv.name, levelParams := cv.levelParams, type := cv.type, cidx := cv.cidx
          numParams := cv.numParams, numFields := cv.numFields, induct := cv.induct
          isUnsafe := cv.isUnsafe }
  for n in names do
    if let some (.recInfo rv) := env.constants.find? (Name.str n "rec") then
      rs := rs.push
        { name := rv.name, levelParams := rv.levelParams, type := rv.type, all := rv.all
          numParams := rv.numParams, numIndices := rv.numIndices, numMotives := rv.numMotives
          numMinors := rv.numMinors, k := rv.k, isUnsafe := rv.isUnsafe
          rules := rv.rules.map fun r =>
            { ctor := r.ctor, nfields := r.nfields, rhs := r.rhs } }
  return .induct ts.toList cs.toList rs.toList

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

/-- Read the exact recursor records of a block generated inside this pass. -/
def recursorsOfNames (names : Array Name) : MetaM (Array ERec) := do
  let .induct _ _ recursors ← indEDecl names
    | throwError "{names} did not read back as an inductive block"
  return recursors.toArray

/-- A generated declaration as an export record. -/
def toEDecl : Declaration → MetaM EDecl
  | .defnDecl v =>
      return .defn v.name v.levelParams v.type v.value (hintsOf v.hints)
        (safetyTo v.safety) [v.name]
  | .thmDecl v => return .thm v.name v.levelParams v.type v.value [v.name]
  | .axiomDecl v => return .ax v.name v.levelParams v.type v.isUnsafe
  | .opaqueDecl v => return .opaq v.name v.levelParams v.type v.value v.isUnsafe [v.name]
  | .inductDecl _ _ ts _ => indEDecl (ts.toArray.map (·.name))
  | d => throwError "cannot serialise {d.getTopLevelNames}"

/-- The export's word for each of the four quotient records. Read off the
`QuotKind` the kernel stamped on the constant, so the record is recognised
**structurally** on the way back out, just as the monomorphizer's carried
built-ins recognise it on the way in. -/
def quotKindStr : QuotKind → String
  | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"

/-- Whether a quotient export record is exactly the part of the single kernel
`quotDecl` already installed in `env`.  This distinguishes the three covered
records of a valid four-record bundle from malformed or unrelated records. -/
def installedQuotRecord (env : Environment) : EDecl → Bool
  | .quot name levelParams type kind =>
    match env.constants.find? name with
    | some (.quotInfo info) => info.levelParams == levelParams && info.type == type &&
        quotKindStr info.kind == kind
    | _ => false
  | _ => false

/-- The exact four-record export spelling of the kernel quotient already
installed in `env`.  A quotient declaration is atomic to the kernel even
though lean4export represents it by four consecutive records. -/
def installedQuotRecords? (env : Environment) : Option (Array EDecl) := do
  let record (name : Name) : Option EDecl :=
    match env.constants.find? name with
    | some (.quotInfo info) =>
      some (.quot info.name info.levelParams info.type (quotKindStr info.kind))
    | _ => none
  let quot ← record `Quot
  let mk ← record `Quot.mk
  let lift ← record `Quot.lift
  let ind ← record `Quot.ind
  return #[quot, mk, lift, ind]

/-- Validate quotient records before replaying any generated declaration.

There is no meaningful per-record replay for a quotient: the first record
causes the kernel to install all four constants.  Consequently the only sound
serialized representation is one new, consecutive, canonically ordered
four-record bundle with every exported field equal to the kernel-minted
metadata.  In particular this rejects a lone first record, a reordered or
duplicated bundle, and malformed metadata on the first record rather than
letting the subsequent installed-name checks obscure it. -/
def checkGeneratedQuotRecords (base : Environment) (records : Array EDecl) :
    MetaM (Except String Unit) := do
  let positions := (Array.range records.size).filter fun i =>
    match records[i]! with | .quot .. => true | _ => false
  if positions.isEmpty then return .ok ()
  for name in [`Quot, `Quot.mk, `Quot.lift, `Quot.ind] do
    if base.constants.contains name then
      return .error s!"generated quotient bundle would shadow existing {name}"
  unless positions.size == 4 do
    return .error s!"quotient declaration has {positions.size} export records, expected 4"
  let first := positions[0]!
  unless positions == #[first, first + 1, first + 2, first + 3] do
    return .error "quotient export records are not one consecutive bundle"
  let quotientEnv ← match base.addDeclCore 0 .quotDecl none true with
    | .error exception =>
      return .error s!"cannot reconstruct quotient declaration: \
        {← (exception.toMessageData {}).toString}"
    | .ok next => pure next
  let some expected := installedQuotRecords? quotientEnv
    | return .error "kernel quotient declaration did not install its four constants"
  let actual := records.extract first (first + 4)
  unless actual == expected do
    return .error "quotient export bundle does not match the kernel declaration"
  return .ok ()

/-- A generated declaration as export records — **plural**, because
`Declaration.quotDecl` is one kernel declaration and four records. Everything
else is one record and goes through [`Modelgen.toEDecl`]. -/
def toEDecls (d : Declaration) : MetaM (Array EDecl) := do
  match d with
  | .quotDecl =>
    let env ← getEnv
    let some records := installedQuotRecords? env
      | throwError "the quotient declaration did not install its four constants"
    return records
  | _ => return #[← toEDecl d]

/-- Reinstall serialized generated records, with kernel checking, in an
arbitrary source-prefix environment.

Generation may use a separate analysis environment containing the owner.  A
successful public model must nevertheless install here, where the owner is
absent.  This makes owner independence a kernel-checked invariant instead of a
hope later imposed by record ordering.  The returned environment is a fork;
the caller may discard it after streaming the records. -/
def checkGeneratedIn (base : Environment) (records : Array EDecl) :
    MetaM (Except String Environment) := do
  match ← checkGeneratedQuotRecords base records with
  | .error message => return .error message
  | .ok () => pure ()
  let mut checked := base
  for record in records do
    let some declaration := toDeclaration checked record | do
      -- One `Declaration.quotDecl` installs all four exported quotient names.
      -- The remaining three records are therefore already represented, not
      -- failed reconstructions, once their exact constant is present.
      if installedQuotRecord checked record then continue
      return .error s!"{record.names}: cannot reconstruct a kernel declaration"
    match checked.addDeclCore 0 declaration none true with
    | .error exception =>
      return .error s!"{record.names}: \
        {← (exception.toMessageData {}).toString}"
    | .ok next =>
      checked := next
      for name in declaration.getNames do
        unless checked.constants.contains name do
          return .error s!"{name}: checked declaration was lost from the kernel environment"
  return .ok checked

/-- Persist the reusable subset of support explicitly recorded by an accepted
model island. The `Iso.spliced` witness is essential: namespace shape alone
must never copy a public model such as `Eq.Example._model` into the replay
environment. Local skeletons and per-model `funext` remain disposable. -/
def generatedSupportRecords (records : Array EDecl) (models : Array PendingModel) :
    Array EDecl :=
  let spliced := models.foldl (init := ({} : Std.HashSet Name)) fun names model =>
    model.spliced.foldl (fun names name => names.insert name) names
  records.filter fun record =>
    record.names.any spliced.contains &&
      (record.names.any persistentSupportRoot || record.names.all persistentSupportName)

def installGeneratedSupportIn (base : Environment) (records : Array EDecl)
    (models : Array PendingModel) :
    MetaM (Except String Environment) := do
  let mut main := base
  for record in generatedSupportRecords records models do
    let some declaration := toDeclaration main record | do
      if installedQuotRecord main record then continue
      return .error s!"{record.names}: cannot reconstruct shared support"
    match main.addDeclCore 0 declaration none true with
    | .error exception =>
      return .error s!"{record.names}: {← (exception.toMessageData {}).toString}"
    | .ok next => main := next
  return .ok main

/-- Finalize one atomic generated forest.  The source owner participates in
record ordering but is removed before checked replay, so the kernel sees every
exact serialized model declaration in the owner-free persistent environment.
Only fixed shared support is copied back. -/
def closeModelIsland (template : Export) (main : Environment)
    (records : Array EDecl) (models : Array PendingModel) (owner : EDecl)
    (sourceSyntax : Check.SyntaxIndex) (generatedOwners : Std.HashSet Name) :
    MetaM (Except String
      (Array EDecl × CompactIsland × Environment × Check.StatementReport)) := do
  let island := { template with decls := records.push owner }
  let ordered ← match Order.reorder island with
    | .ok ordered => pure ordered
    | .error error => return .error s!"cannot order generated island: {repr error}"
  let mut generated : Array EDecl := #[]
  let mut removedOwner := false
  for record in ordered.decls do
    if !removedOwner && record == owner then removedOwner := true
    else generated := generated.push record
  unless removedOwner do return .error s!"source owner {owner.names} disappeared from its island"
  -- Statement correspondence is an export-syntax check, so it can run while
  -- the owner is still absent from the persistent replay environment. Source
  -- owners use family templates indexed once; generated owners use the island
  -- records plus an overlay carrying source transparent aliases and exact
  -- projection metadata. The final aggregate remains the equivalence oracle.
  let index ← match sourceSyntax.prependRecords generated with
    | .ok index => pure index
    | .error message => return .error s!"cannot index generated island: {message}"
  let sourceRoot? : Option Name := match owner with
    | .induct (type :: _) _ _ => some type.name
    | _ => none
  let generatedOnlyOwners := sourceRoot?.elim generatedOwners generatedOwners.erase
  let generatedView := { template with decls := generated }
  let generatedFamilies :=
    Check.statementFamiliesForRecordsWithIndex generatedView index generatedOnlyOwners
  let sourceFamilies := sourceRoot?.elim #[] fun root =>
    if generatedOwners.contains root then sourceSyntax.sourceStatementFamilies root else #[]
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
    (Check.compactFamilyCertificateWithIndex template index)
  let sourceGlobalExtra? := if sourceFamilies.isEmpty then none else
    (Check.globalExtraRecordsWithIndex index #[owner])[0]?
  let compact : CompactIsland :=
    { summaries := Order.summariesWithIndex generatedView index compactOwners
      globalExtras := Check.globalExtraRecordsWithIndex index generated
      families := generatedFamilyRecords
      sourceFamilies := sourceFamilyCertificates
      sourceGlobalExtra?
      diagnosticOwners }
  let statementReport :=
    if generatedOwners.isEmpty then
      { statementsChecked := 0, violations := #[] }
    else
      let generatedReport :=
        Check.checkStatementFamiliesLocalWithIndex generatedView index generatedFamilies
      let sourceReport :=
        Check.checkStatementFamiliesLocalWithIndex template index sourceFamilies
      let checkedCount := generatedReport.statementsChecked + sourceReport.statementsChecked
      let combinedViolations := generatedReport.violations ++ sourceReport.violations
      ({ statementsChecked := checkedCount, violations := combinedViolations } :
        Check.StatementReport)
  -- Drop the construction fork before reconstructing any declaration.  The
  -- exact serialized records and compact splice witnesses above are the only
  -- state allowed to cross into owner-free checked replay.
  setEnv main
  match ← checkGeneratedIn main generated with
  | .error message => return .error message
  | .ok _ =>
    match ← installGeneratedSupportIn main generated models with
    | .error message => return .error message
    | .ok supported => return .ok (generated, compact, supported, statementReport)

/-- Source declarations which must be replayed before any owner that can need
them. This is deliberately wider than [`Modelgen.persistentSupportName`]:
When only the nested/mutual layers are selected, moving the full simple basis
would change independent source order for no reason. `False` is derived, not
support: preferring it could put its own model before a later input-owned
`Nat`, although that model needs `Nat`. -/
def scheduledSupportRecord (generation : Cli.Config) (declaration : EDecl) : Bool :=
  if generation.simple || generation.basic then
    declaration.names.any persistentSupportRoot || declaration.names.all persistentSupportName
  else if generation.nested || generation.mutualModels then
    declaration.names.any fun name =>
      name == `Eq || name == `PSigma' || (`PSigma').isPrefixOf name ||
        name == `PUnit || (`PUnit).isPrefixOf name
  else
    false

/-- Whether this input record reaches any enabled model-generation branch.

Support scheduling is global so that one fixed, dependency-closed support
class moves atomically ahead of every selected owner.  It must nevertheless be
inactive when the export has no selected owner: generation flags alone do not
justify moving independent source records. -/
def scheduledModelOwner (generation : Cli.Config) (reserved : Std.HashSet Name) : EDecl → Bool
  | .induct types _ _ =>
    match types with
    | [] => false
    | first :: _ =>
      !reserved.contains (Naming.modelName first.name) &&
        ((generation.nested && types.any (·.numNested > 0)) ||
          (generation.mutualModels && types.length > 1 && !types.any (·.numNested > 0)) ||
          (types.length == 1 && first.numNested == 0 &&
            generation.modelsSimpleInput first.name))
  | _ => false

/-- Dependency-order source records, hoisting the fixed support class exactly
when at least one input owner reaches an enabled generation branch. -/
def scheduleSource (x : Export) (generation : Cli.Config) : Except Order.Error Export :=
  let reserved := x.decls.foldl (fun names declaration =>
    declaration.names.foldl (·.insert ·) names) {}
  if x.decls.any (scheduledModelOwner generation reserved) then
    Order.reorderPrioritizing x (scheduledSupportRecord generation)
  else
    Order.reorder x

/-- Read a generated model back from the construction environment, register
every name Lean minted for its inductive blocks, and serialize through exact
alias lookups. The returned `Iso` carries the completed alias and splice
witnesses used for reporting and shared-support persistence. -/
def serialiseIso (is : Iso) : MetaM (Array EDecl × Iso) := do
  let mut records : Array EDecl := #[]
  for declaration in is.decls do
    records := records ++ (← toEDecls declaration)
  let names := records.flatMap fun record => record.names.toArray
  let aliases := is.aliases.register names
  let renamed := records.map (·.renameAliases aliases)
  let spliced := is.spliced.map fun name => aliases.exact name
  -- `Iso` continues to name declarations in the disposable construction
  -- environment. Only serialized records take exact aliases; the completed
  -- map therefore remains available while the exact output identities of
  -- spliced support are recorded for persistence and reporting.
  return (renamed, { is with aliases := aliases, spliced := spliced })

/-- The exact exported metadata of one inductive record must be what Lean's
kernel regenerated from that record's type-former and constructor inputs.

`Declaration.inductDecl` does not take the exported `InductiveVal`,
`ConstructorVal`, or `RecursorVal` metadata as input.  Merely adding the
reconstructed declaration therefore proves the constructor types are valid,
but does not validate fields such as constructor indices, recursion flags, or
recursor rule arities.  Compare every exported field here, including the fields
which are bookkeeping rather than kernel declaration inputs. -/
private def exportedRecursorRules (recursor : ERec) : List RecursorRule :=
  recursor.rules.map fun rule : ERecRule =>
    { ctor := rule.ctor, nfields := rule.nfields, rhs := rule.rhs }

private def recursorMetadataMatches (recursor : ERec) (actual : RecursorVal) : Bool :=
  actual.name == recursor.name && actual.levelParams == recursor.levelParams &&
    actual.type == recursor.type && actual.all == recursor.all &&
    actual.numParams == recursor.numParams && actual.numIndices == recursor.numIndices &&
    actual.numMotives == recursor.numMotives && actual.numMinors == recursor.numMinors &&
    actual.rules == exportedRecursorRules recursor && actual.k == recursor.k &&
    actual.isUnsafe == recursor.isUnsafe

private def metadataMismatch (name : Name) (kind field : String) : String :=
  s!"{name}: {kind} {field} differs from Lean's kernel"

def checkInductiveMetadata (types : List EIndType) (constructors : List ECtor)
    (recursors : List ERec) : MetaM (Array String) := do
  let env ← getEnv
  let mut mismatches : Array String := #[]
  for type in types do
    match env.constants.find? type.name with
    | some (.inductInfo actual) =>
      unless actual.name == type.name do
        mismatches := mismatches.push (metadataMismatch type.name "inductive" "name")
      unless actual.levelParams == type.levelParams do
        mismatches := mismatches.push (metadataMismatch type.name "inductive" "levelParams")
      unless actual.type == type.type do
        mismatches := mismatches.push (metadataMismatch type.name "inductive" "type")
      unless actual.all == type.all do
        mismatches := mismatches.push (metadataMismatch type.name "inductive" "all")
      unless actual.ctors == type.ctors do
        mismatches := mismatches.push (metadataMismatch type.name "inductive" "constructors")
      unless actual.numParams == type.numParams do
        mismatches := mismatches.push (metadataMismatch type.name "inductive" "numParams")
      unless actual.numIndices == type.numIndices do
        mismatches := mismatches.push (metadataMismatch type.name "inductive" "numIndices")
      unless actual.numNested == type.numNested do
        mismatches := mismatches.push (metadataMismatch type.name "inductive" "numNested")
      unless actual.isRec == type.isRec do
        mismatches := mismatches.push (metadataMismatch type.name "inductive" "isRec")
      unless actual.isReflexive == type.isReflexive do
        mismatches := mismatches.push (metadataMismatch type.name "inductive" "isReflexive")
      unless actual.isUnsafe == type.isUnsafe do
        mismatches := mismatches.push (metadataMismatch type.name "inductive" "isUnsafe")
    | some _ => mismatches := mismatches.push (metadataMismatch type.name "declaration" "kind")
    | none => mismatches := mismatches.push (metadataMismatch type.name "inductive" "presence")
  for constructor in constructors do
    match env.constants.find? constructor.name with
    | some (.ctorInfo actual) =>
      unless actual.name == constructor.name do
        mismatches := mismatches.push (metadataMismatch constructor.name "constructor" "name")
      unless actual.levelParams == constructor.levelParams do
        mismatches := mismatches.push
          (metadataMismatch constructor.name "constructor" "levelParams")
      unless actual.type == constructor.type do
        mismatches := mismatches.push (metadataMismatch constructor.name "constructor" "type")
      unless actual.induct == constructor.induct do
        mismatches := mismatches.push (metadataMismatch constructor.name "constructor" "induct")
      unless actual.cidx == constructor.cidx do
        mismatches := mismatches.push (metadataMismatch constructor.name "constructor" "cidx")
      unless actual.numParams == constructor.numParams do
        mismatches := mismatches.push
          (metadataMismatch constructor.name "constructor" "numParams")
      unless actual.numFields == constructor.numFields do
        mismatches := mismatches.push
          (metadataMismatch constructor.name "constructor" "numFields")
      unless actual.isUnsafe == constructor.isUnsafe do
        mismatches := mismatches.push
          (metadataMismatch constructor.name "constructor" "isUnsafe")
    | some _ =>
      mismatches := mismatches.push (metadataMismatch constructor.name "declaration" "kind")
    | none =>
      mismatches := mismatches.push (metadataMismatch constructor.name "constructor" "presence")
  for recursor in recursors do
    match env.constants.find? recursor.name with
    | some (.recInfo actual) =>
      unless actual.name == recursor.name do
        mismatches := mismatches.push (metadataMismatch recursor.name "recursor" "name")
      unless actual.levelParams == recursor.levelParams do
        mismatches := mismatches.push (metadataMismatch recursor.name "recursor" "levelParams")
      unless actual.type == recursor.type do
        mismatches := mismatches.push (metadataMismatch recursor.name "recursor" "type")
      unless actual.all == recursor.all do
        mismatches := mismatches.push (metadataMismatch recursor.name "recursor" "all")
      unless actual.numParams == recursor.numParams do
        mismatches := mismatches.push (metadataMismatch recursor.name "recursor" "numParams")
      unless actual.numIndices == recursor.numIndices do
        mismatches := mismatches.push (metadataMismatch recursor.name "recursor" "numIndices")
      unless actual.numMotives == recursor.numMotives do
        mismatches := mismatches.push (metadataMismatch recursor.name "recursor" "numMotives")
      unless actual.numMinors == recursor.numMinors do
        mismatches := mismatches.push (metadataMismatch recursor.name "recursor" "numMinors")
      unless actual.rules == exportedRecursorRules recursor do
        mismatches := mismatches.push (metadataMismatch recursor.name "recursor" "rules")
      unless actual.k == recursor.k do
        mismatches := mismatches.push (metadataMismatch recursor.name "recursor" "k")
      unless actual.isUnsafe == recursor.isUnsafe do
        mismatches := mismatches.push (metadataMismatch recursor.name "recursor" "isUnsafe")
    | some _ =>
      mismatches := mismatches.push (metadataMismatch recursor.name "declaration" "kind")
    | none =>
      mismatches := mismatches.push (metadataMismatch recursor.name "recursor" "presence")
  return mismatches

/-- Optional generation-time recursor audit retained for the library driver.
The whole-stream CLI gate additionally checks types and constructors above. -/
def checkRecs (recursors : List ERec) : MetaM (Nat × Array Name) := do
  let env ← getEnv
  let mut bad : Array Name := #[]
  for recursor in recursors do
    match env.constants.find? recursor.name with
    | some (.recInfo actual) =>
      unless recursorMetadataMatches recursor actual do bad := bad.push recursor.name
    | _ => bad := bad.push recursor.name
  return (recursors.length, bad)

private def insertConstantInfo (constants : Std.HashMap Name ConstantInfo)
    (info : ConstantInfo) : Except String (Std.HashMap Name ConstantInfo) := do
  if constants.contains info.name then
    throw s!"duplicate declaration {info.name}"
  return constants.insert info.name info

/-- Reconstruct the exact `ConstantInfo` map represented by an export.  Unlike
the kernel declaration assembled from an inductive record, this retains the
metadata which is not itself an input to kernel insertion, so it can be
compared with the values regenerated by Lean. -/
def Export.constantInfos (x : Export) : Except String (Std.HashMap Name ConstantInfo) := do
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for declaration in x.decls do
    match declaration with
    | .ax name levelParams type isUnsafe =>
      constants ← insertConstantInfo constants <| .axiomInfo
        { name, levelParams, type, isUnsafe }
    | .defn name levelParams type value hints safety all =>
      let some safety := safetyOf? safety
        | throw s!"unknown definition safety {safety}"
      constants ← insertConstantInfo constants <| .defnInfo
        { name, levelParams, type, value, hints := hintsTo hints, safety, all }
    | .thm name levelParams type value all =>
      constants ← insertConstantInfo constants <| .thmInfo
        { name, levelParams, type, value, all }
    | .opaq name levelParams type value isUnsafe all =>
      constants ← insertConstantInfo constants <| .opaqueInfo
        { name, levelParams, type, value, isUnsafe, all }
    | .quot name levelParams type kind =>
      let some kind := quotKindOf? kind
        | throw s!"unknown quotient kind {kind}"
      constants ← insertConstantInfo constants <| .quotInfo
        { name, levelParams, type, kind }
    | .induct types constructors recursors =>
      for type in types do
        constants ← insertConstantInfo constants <| .inductInfo
          { name := type.name, levelParams := type.levelParams, type := type.type
            all := type.all, ctors := type.ctors, numParams := type.numParams
            numIndices := type.numIndices, numNested := type.numNested, isRec := type.isRec
            isUnsafe := type.isUnsafe, isReflexive := type.isReflexive }
      for constructor in constructors do
        constants ← insertConstantInfo constants <| .ctorInfo
          { name := constructor.name, levelParams := constructor.levelParams
            type := constructor.type, induct := constructor.induct, cidx := constructor.cidx
            numParams := constructor.numParams, numFields := constructor.numFields
            isUnsafe := constructor.isUnsafe }
      for recursor in recursors do
        constants ← insertConstantInfo constants <| .recInfo
          { name := recursor.name, levelParams := recursor.levelParams, type := recursor.type
            all := recursor.all, numParams := recursor.numParams
            numIndices := recursor.numIndices, numMotives := recursor.numMotives
            numMinors := recursor.numMinors, rules := exportedRecursorRules recursor
            k := recursor.k, isUnsafe := recursor.isUnsafe }
  return constants

/-- Whether Lean Kernel Arena omits an entire export record from replay.

Unsafe and partial constants are intentionally outside the arena's verdict.
For an inductive record, however, one accidentally safe constructor or
recursor is enough to make the malformed block observable: the arena would
try to validate that safe constant and fail when its unsafe owner was absent. -/
private def kernelReplaySkipped : EDecl → Bool
  | .ax _ _ _ isUnsafe => isUnsafe
  | .defn _ _ _ _ _ safety _ =>
    match safetyOf? safety with
    | some .safe => false
    | _ => true
  | .thm .. => false
  | .opaq _ _ _ _ isUnsafe _ => isUnsafe
  | .quot name .. => name == `Quot.mk || name == `Quot.lift || name == `Quot.ind
  | .induct types constructors recursors =>
    !types.isEmpty && types.all (·.isUnsafe) && constructors.all (·.isUnsafe) &&
      recursors.all (·.isUnsafe)

/-- Constants used by the actual declaration submitted to the kernel.

Recursor terms and all exported inductive bookkeeping are outputs of kernel
insertion, not inputs to it.  They must therefore be compared afterwards, but
must not create false dependency cycles before insertion.  The explicit `Eq`
edge for the quotient matches the arena's patched replay implementation. -/
private def kernelInputReferences (declaration : EDecl) : Std.HashSet Name := Id.run do
  if kernelReplaySkipped declaration then return {}
  let mut roots : Array Expr := #[]
  match declaration with
  | .ax _ _ type _ => roots := roots.push type
  | .defn _ _ type value _ _ _ => roots := roots.push type |>.push value
  | .thm _ _ type value _ => roots := roots.push type |>.push value
  | .opaq _ _ type value _ _ =>
    roots := roots.push type |>.push value
  | .quot _ _ type _ =>
    roots := roots.push type
  | .induct types constructors _ =>
    for type in types do roots := roots.push type.type
    for constructor in constructors do roots := roots.push constructor.type
  let mut references := Order.expressionReferences roots
  if let .quot .. := declaration then references := references.insert `Eq
  return references

/-- DFS state for the private replay schedule: unseen, visiting, or finished. -/
private abbrev KernelReplayMarks := Array UInt8

/-- Visit one atomic export record and its declaration dependencies.

The public output order is deliberately untouched.  This private order exists
only so pure checker mode accepts arbitrary valid declaration ordering, while
one record containing a mutual/nested inductive remains indivisible. -/
private partial def visitKernelRecord (x : Export) (ownership : Std.HashMap Name Nat)
    (index : Nat) (marks : KernelReplayMarks) (order : Array Nat) :
    Except String (KernelReplayMarks × Array Nat) := do
  match marks[index]! with
  | 2 => return (marks, order)
  | 1 => throw s!"cyclic kernel declaration dependencies at record {index}: {x.decls[index]!.names}"
  | _ => pure ()
  let mut marks := marks.set! index 1
  let mut order := order
  for name in kernelInputReferences x.decls[index]! do
    if let some dependency := ownership[name]? then
      if dependency != index then
        (marks, order) ← visitKernelRecord x ownership dependency marks order
  marks := marks.set! index 2
  return (marks, order.push index)

/-- Stable input-independent dependency schedule for kernel replay.

Duplicate declaration names are malformed export data and are normally caught
by the parser.  Keep the same guard here for library callers constructing an
`Export` directly. -/
private def kernelReplayOrder (x : Export) : Except String (Array Nat) := do
  let mut ownership : Std.HashMap Name Nat := {}
  for index in [:x.decls.size] do
    for name in x.decls[index]!.names do
      if let some first := ownership[name]? then
        throw s!"duplicate declaration {name} in records {first} and {index}"
      ownership := ownership.insert name index
  let mut marks : KernelReplayMarks := Array.replicate x.decls.size 0
  let mut order : Array Nat := #[]
  for index in [:x.decls.size] do
    (marks, order) ← visitKernelRecord x ownership index marks order
  return order

private def findInductiveType (types : List EIndType) (name : Name) : Except String EIndType :=
  match types.find? (·.name == name) with
  | some type => .ok type
  | none => .error s!"inductive block names missing member {name}"

private def findConstructor (constructors : List ECtor) (name : Name) : Except String ECtor :=
  match constructors.find? (·.name == name) with
  | some constructor => .ok constructor
  | none => .error s!"inductive block names missing constructor {name}"

/-- Reconstruct exactly the declaration which the arena submits for one
active record.  In particular, `InductiveVal.all` and `InductiveVal.ctors`
control semantic member/constructor order; the enclosing record arrays are
only storage order. -/
private def kernelReplayDeclaration (declaration : EDecl) : Except String (Option Declaration) := do
  if kernelReplaySkipped declaration then return none
  match declaration with
  | .ax name levelParams type isUnsafe =>
    return some <| .axiomDecl { name, levelParams, type, isUnsafe }
  | .defn name levelParams type value hints safety all =>
    let some safety := safetyOf? safety | throw s!"unknown definition safety {safety}"
    return some <| .defnDecl
      { name, levelParams, type, value, hints := hintsTo hints, safety, all }
  | .thm name levelParams type value all =>
    return some <| .thmDecl { name, levelParams, type, value, all }
  | .opaq name levelParams type value isUnsafe all =>
    return some <| .opaqueDecl { name, levelParams, type, value, isUnsafe, all }
  | .quot .. => return some .quotDecl
  | .induct types constructors _ =>
    let first ← match types with
      | first :: _ => pure first
      | [] => throw "empty inductive declaration"
    let orderedTypes ← first.all.mapM (findInductiveType types)
    let inductiveTypes ← orderedTypes.mapM fun type => do
      let orderedConstructors ← type.ctors.mapM (findConstructor constructors)
      let ctors : List Constructor := orderedConstructors.map fun constructor =>
        { name := constructor.name, type := constructor.type }
      let inductiveType : InductiveType :=
        { name := type.name, type := type.type, ctors }
      return inductiveType
    -- Any active inductive record is replayed as safe, exactly as the arena:
    -- valid unsafe blocks are skipped above, while inconsistent unsafe flags
    -- are exposed by the metadata comparison below.
    return some <| .inductDecl first.levelParams first.numParams inductiveTypes false

/-- Replay grouped export records directly into a kernel environment.

Using `Lean.Environment.replay` here would split the constant map back into
individual records.  That loses the export's atomic grouping for nested
inductives and can fail to expose kernel-generated auxiliary recursors. -/
private def replayKernelRecords (base : Environment) (x : Export) (order : Array Nat) :
    MetaM (Except String Environment) := do
  let mut checked := base.toKernelEnv
  for index in order do
    let record := x.decls[index]!
    let declaration? ← match kernelReplayDeclaration record with
      | .ok declaration => pure declaration
      | .error message => return .error message
    let some declaration := declaration? | continue
    match checked.addDeclCore 0 declaration none with
    | .error exception =>
      return .error s!"{record.names}: {← (exception.toMessageData {}).toString}"
    | .ok next => checked := next
  return .ok (.ofKernelEnv checked)

/-- Submit a complete export to Lean's kernel and verify that its serialized
inductive, constructor, and recursor metadata agrees with what Lean regenerates.

This is the explicit whole-stream verdict gate used by the command line.  It
is separate from the mandatory checked construction of declarations generated
by this tool: disabling a CLI type-check gate never weakens model generation's
owner-free kernel replay. -/
def typeCheckExport (x : Export) : MetaM (Except String Unit) := do
  let base ← getEnv
  let constants ← match x.constantInfos with
    | .error message => return .error message
    | .ok constants => pure constants
  let order ← match kernelReplayOrder x with
    | .error message => return .error message
    | .ok order => pure order
  let checked ← match ← replayKernelRecords base x order with
    | .error message => return .error message
    | .ok checked => pure checked
  setEnv checked
  let mut mismatches : Array String := #[]
  for (_, expected) in constants do
    if expected.isUnsafe || expected.isPartial then continue
    match expected, checked.constants.find? expected.name with
    | .axiomInfo expected, some (.axiomInfo actual) =>
      unless actual == expected do
        mismatches := mismatches.push
          (metadataMismatch expected.name "axiom" "metadata")
    | .defnInfo expected, some (.defnInfo actual) =>
      unless actual == expected do
        mismatches := mismatches.push
          (metadataMismatch expected.name "definition" "metadata")
    | .thmInfo expected, some (.thmInfo actual) =>
      unless actual == expected do
        mismatches := mismatches.push
          (metadataMismatch expected.name "theorem" "metadata")
    | .opaqueInfo expected, some (.opaqueInfo actual) =>
      unless actual == expected do
        mismatches := mismatches.push
          (metadataMismatch expected.name "opaque declaration" "metadata")
    | .quotInfo _, _ | .inductInfo _, _ | .ctorInfo _, _ | .recInfo _, _ => pure ()
    | _, _ =>
      mismatches := mismatches.push
        (metadataMismatch expected.name "declaration" "kind or presence")
  for declaration in x.decls do
    if let .induct types constructors recursors := declaration then
      -- Lean Kernel Arena intentionally skips wholly unsafe blocks.  Every
      -- active block is fully present and all exported bookkeeping is checked.
      unless kernelReplaySkipped declaration do
        let bad ← checkInductiveMetadata types constructors recursors
        mismatches := mismatches ++ bad
  unless mismatches.isEmpty do
    return .error s!"serialized declaration metadata differs from Lean's kernel:\n  \
      {"\n  ".intercalate mismatches.toList}"
  return .ok ()

/-- **One installed inductive block, read back out of the environment** as the
member types and constructor lists [`Modelgen.mutualIso`] wants.

The block a nested declaration's model *is* — `T._model.0 … T._model.{n−1}` —
is not in the input, so there is no `EDecl` to take these off; it exists only in
the environment the generator just put it in. This is how the composition
hands the second construction its input. -/
def blockOf (names : Array Name) : MetaM (Array Expr × Array (Array (Name × Expr))) := do
  let env ← getEnv
  let mut tys : Array Expr := #[]
  let mut cs : Array (Array (Name × Expr)) := #[]
  for n in names do
    let some (.inductInfo iv) := env.constants.find? n | throwError "{n} is not an inductive"
    tys := tys.push iv.type
    let mut ct : Array (Name × Expr) := #[]
    for cn in iv.ctors do
      let some ci := env.constants.find? cn | throwError "{cn} is not declared"
      ct := ct.push (cn, ci.type)
    cs := cs.push ct
  return (tys, cs)

/-- **Can a model be written here?** — which is only ever a question about `Eq`.

`true` when the environment already has one, and when the input declares none
anywhere, because then the prelude splice supplies Lean's own. `false` in the one remaining
case: the input declares an `Eq` the replay has not reached yet, where a splice
is refused by the name guard and would be wrong anyway. -/
def eqReady (reserved : Std.HashSet Name) : MetaM Bool := do
  if (← getEnv).constants.contains `Eq then return true
  return !(reserved.contains `Eq || reserved.contains `Eq.refl)

/-- A plain mutual projection model additionally needs the tight-pair/PUnit
support that derives an inhabitant of each unrelated motive's exact universe.
If the input owns any part later in dependency order, wait for the complete
bundle; if it owns none, generation may splice the standard shapes. -/
def mutualReady (needsExactSortLift : Bool) (reserved : Std.HashSet Name) : MetaM Bool := do
  unless ← eqReady reserved do return false
  unless needsExactSortLift do return true
  let env ← getEnv
  for name in [`PSigma', `PSigma'.mk, `PSigma'.rec, `PSigma'.fst, `PSigma'.snd,
      `PSigma'.fst_mk, `PSigma'.snd_mk, `PSigma'.rec', `PSigma'.rec'_mk,
      `PUnit, `PUnit.unit, `PUnit.rec] do
    unless env.constants.contains name || !reserved.contains name do return false
  return true

private def hasIntrinsicProjectionFields (x : Export) (types : List EIndType)
    (constructors : List ECtor) : Bool :=
  types.any fun type =>
    !(x.intrinsicProjectionFieldsFor type constructors).isEmpty

private def isMutualBasisRecord (needsExactSortLift : Bool) (declaration : EDecl) : Bool :=
  declaration.names.any fun name =>
    name == `Eq || name == `Eq.refl ||
      (needsExactSortLift && (name == `PSigma' || (`PSigma').isPrefixOf name ||
        name == `PUnit || (`PUnit).isPrefixOf name))

/-- **Can a prim model be written here?** — [`Modelgen.eqReady`]'s question,
asked of every basis constant a prim model may splice: each must be already
installed or not declared by the input at all, else the model waits for the
input's own declaration to be replayed. -/
def primMissingBasis (reserved : Std.HashSet Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut missing := #[]
  for n in [`Eq, `Eq.refl, `Nat, `Nat.zero, `Nat.succ,
      `PSigma', `PSigma'.mk, `PSigma'.rec, `PSigma'.fst, `PSigma'.snd, `PSigma'.fst_mk,
      `PSigma'.snd_mk, `PSigma'.rec', `PSigma'.rec'_mk,
      `PUnit, `PUnit.unit, `PUnit.rec] do
    unless env.constants.contains n || !reserved.contains n do missing := missing.push n
  return missing

def primReady (reserved : Std.HashSet Name) : MetaM Bool := do
  return (← primMissingBasis reserved).isEmpty

/-- **The names beyond the basis that a prim model may splice** — the ones
[`Modelgen.primReady`] does not cover. Input-owned records for these names are
moved, with their dependency closure, ahead of selected owners by
[`Modelgen.scheduleSource`].

They form one post-scheduling readiness class:

* the quotient-side names deriving `funext` may splice
  ([`Modelgen.ensureFunext`]). A prim model reaches them on the singleton route
  and wherever a pad at a level `dsingOk` cannot build is discharged by
  transport — `PUnit`'s and the derived exact-sort lift's shapes.
* `Nonempty` and `Classical.choice`, which **arm G** splices and which the W
  core's fragment now also carries. An input that declares `Acc` before
  `Nonempty` — `test/fixtures/modelgen/w_core.ndjson`
  is one, since the fragment's `Acc` comes in through `WellFounded.fix` and its
  `Nonempty` only through `Classical.propDecidable` — used to lose `Acc`'s model
  to `prim model name taken (Nonempty)`. That is an uninstalled reserved-support
  name, not a generated name that was lost. -/
def lateSpliceNames : List Name :=
  [`Quot, `Quot.mk, `Quot.lift, `Quot.ind, `Quot.sound,
   `Nonempty, `Nonempty.intro, `Nonempty.rec, `Classical.choice]

/-- The exact logical interface the W fragment shares with the input.

`ensureWCore` refuses to splice any one of these when the input reserves it.
They form a separate atomic readiness class so a failed W construction reports
the complete Iff/propext prerequisite rather than conflating it with the
quotient/choice support used by non-W routes. `w_late_iff` pins that distinction. -/
def wLogicalLateNames : List Name := [`Iff, `Iff.intro, `Iff.rec, `propext]

/-- [`Modelgen.primReady`]'s question, asked of quotient/choice support after a
construction has actually encountered one of those names. It is not folded
into `primReady`: most simple models never use `funext` or choice. -/
def primLateReady (reserved : Std.HashSet Name) : MetaM Bool := do
  let env ← getEnv
  for n in lateSpliceNames do
    unless env.constants.contains n || !reserved.contains n do return false
  return true

/-- Atomic readiness for the exact Iff/propext interface shared by the W
fragment. Names the input does not reserve may be spliced; every name it does
reserve must be installed before the one retry. -/
def primWLogicalReady (reserved : Std.HashSet Name) : MetaM Bool := do
  let env ← getEnv
  for n in wLogicalLateNames do
    unless env.constants.contains n || !reserved.contains n do return false
  return true

/-- The atomic prerequisite class responsible for a support-name collision. -/
inductive PrimReadiness where
  | late
  | wLogical
  deriving Inhabited, BEq

def PrimReadiness.ready (readiness : PrimReadiness)
    (reserved : Std.HashSet Name) : MetaM Bool :=
  match readiness with
  | .late => primLateReady reserved
  | .wLogical => primWLogicalReady reserved

/-- Classify a support-name collision by its exact atomic prerequisite set.
Callers use this to distinguish a violated scheduling/closure invariant from a
genuine model-shape decline. -/
def Decline.lateReadiness? : Decline → Option PrimReadiness
  | .nameTaken n =>
    if lateSpliceNames.contains n then some .late
    else if wLogicalLateNames.contains n then some .wLogical
    else none
  | _ => none

/-- An exact public name generated by an earlier composed step is not part of
the input's `reserved` set.  Check those spellings before a collision-safe
retry so aliasing can never weaken `nameTaken`. -/
def exactPrimNameTaken? (tname : Name) (ctors : Array (Name × Expr))
    (_projections : Array EProjection) : MetaM (Option Name) := do
  let env ← getEnv
  let recursor := Name.str tname "rec"
  for n in #[Naming.modelName tname, Naming.modelName recursor] do
    if env.constants.contains n then return some n
  for (ctor, _) in ctors do
    let n := Naming.modelName ctor
    if env.constants.contains n then return some n
  for j in [0:ctors.size] do
    let n := Naming.iotaName recursor j
    if env.constants.contains n then return some n
  if let some (.recInfo info) := env.constants.find? recursor then
    if info.k then
      let n := Naming.ruleKName recursor
      if env.constants.contains n then return some n
  if let some (.inductInfo info) := env.constants.find? tname then
    if !info.isRec && info.numIndices == 0 && info.ctors.length == 1 &&
        !(← isPropFormerType info.type) then
      let n := Naming.etaName tname
      if env.constants.contains n then return some n
    if ctors.size == 1 then
      let ctorName := ctors[0]!.1
      let some (.ctorInfo ctorInfo) := env.constants.find? ctorName | return none
      let type : EIndType :=
        { name := info.name, levelParams := info.levelParams, type := info.type,
          all := info.all, ctors := info.ctors, numParams := info.numParams,
          numIndices := info.numIndices, numNested := info.numNested, isRec := info.isRec,
          isReflexive := info.isReflexive, isUnsafe := info.isUnsafe }
      let constructor : ECtor :=
        { name := ctorInfo.name, levelParams := ctorInfo.levelParams, type := ctorInfo.type,
          cidx := ctorInfo.cidx, numParams := ctorInfo.numParams,
          numFields := ctorInfo.numFields, induct := ctorInfo.induct,
          isUnsafe := ctorInfo.isUnsafe }
      for fieldIndex in ← eligibleProjectionFieldsM type constructor do
        for n in #[Naming.projectionName tname fieldIndex,
            Naming.projectionIotaName tname fieldIndex] do
          if env.constants.contains n then return some n
  return none

/-- One simple inductive's model from the primitives, generated and
accounted for — [`Modelgen.primIso`], selected by `--simple`. Shared by the
input's own simple inductives and the composition (the single inductives the
other two constructions emit).

`canWait` enables prerequisite classification: a collision at fixed support
([`Modelgen.Decline.lateReadiness?`]) returns its exact class in the second
component instead of recording a model-shape decline. Source owners have
already passed through [`Modelgen.scheduleSource`]; recursive splice closure
passes `false` because it must complete inside the same model island.

**And, with `basicModels`, models for whatever that model had to splice.**

The second half closes a structural hole rather than adding a convenience.
`ensurePrim` and friends put a spliced inductive into the environment and into
the output, and nothing ever ran the third construction over it — so layer 3
was **unable to model anything it introduced**, and no coverage figure could
show it, because a spliced declaration was never a candidate to begin with.
Earlier coverage figures therefore measured only declarations from the input.

Only *non-basis* splices are modelled: the four on
[`Modelgen.primBasis`] are the exemption that makes the construction
well-founded and must stay unmodelled. That is also what bounds the recursion
— a model's own splices are basis members or already present.

**Ordering is safe.** A spliced inductive is pushed to the output before the
model that needed it, and its own model is appended after; the export only
requires a declaration to precede its uses. -/
partial def genPrim (tname : Name) (lparams : List Name) (np : Nat) (ty : Expr)
    (ctors : Array (Name × Expr))
    (projections : Array EProjection)
    (reserved : Std.HashSet Name) (basicModels : Bool)
    (canWait : Bool)
    (st : FilterState) : MetaM (FilterState × Option PrimReadiness) := do
  let (out, rep, pending) := st
  let saved ← getEnv
  -- **The retry under an alias root**, and it is a retry rather than a
  -- decision taken up front on purpose: aliasing changes nothing about the
  -- output and everything about the risk, so it runs only where the collision
  -- has actually fired. Every declaration that models today takes exactly the
  -- path it took before, byte for byte.
  --
  -- The alias embeds the exact original below a public namespace.  This is
  -- injective even for distinct raw private names that normalize to the same
  -- user name, because `_private` is no longer the leading component.
  let aliasRoot : Name := Naming.retryRoot tname
  let mut root := tname
  let exactTaken ← exactPrimNameTaken? tname ctors projections
  let initial ← match exactTaken with
    | some n => pure (.error (.nameTaken n))
    | none => (do
        let is ← primIso tname root lparams np ty ctors reserved
        addInstalledStructureModels #[tname] projections reserved is).run
  let mut res := initial
  if let .error (.nameLost _) := res then
    setEnv saved
    root := aliasRoot
    res ← (do
      let is ← primIso tname root lparams np ty ctors reserved
      addInstalledStructureModels #[tname] projections reserved is).run
  match res with
  | .error dec =>
    setEnv saved
    if canWait then
      if let some readiness := dec.lateReadiness? then
        unless ← readiness.ready reserved do
          return ((out, rep, pending), some readiness)
    -- **Exempt is not declined.** A basis primitive is what the construction
    -- is written in, so its absence from the models is the thing that makes
    -- the construction well-founded rather than a shape it cannot reach; it
    -- gets its own row and is out of the decline count.
    if dec matches .basisExempt then
      return ((out, { rep with exempt := rep.exempt.push (tname, dec.labelAs "prim") },
        pending), none)
    return ((out, { rep with declined := rep.declined.push (tname, dec.labelAs "prim") },
      pending), none)
  | .ok is =>
    let (records, is) ← serialiseIso is
    let mut out := out
    out := out ++ records
    let mut rep := { rep with generated := rep.generated.push (tname, is.decls.size) }
    unless is.spliced.isEmpty do
      rep := { rep with spliced := rep.spliced.push (tname, is.spliced) }
    let mut st2 := (out, rep, pending.push { spliced := is.spliced })
    if basicModels then
      for n in is.spliced do
        if primBasis.contains n then continue
        let some (.inductInfo iv) := (← getEnv).constants.find? n | continue
        -- the block's own name only, and only a simple one
        unless iv.all == [n] && iv.numNested == 0 do continue
        -- Already modeled: the declaration-local carrier itself is the key.
        if (← getEnv).constants.contains (Naming.modelName n) then continue
        let mut cts : Array (Name × Expr) := #[]
        for cn in iv.ctors do
          if let some ci := (← getEnv).constants.find? cn then cts := cts.push (cn, ci.type)
        st2 :=
          (← genPrim n iv.levelParams iv.numParams iv.type cts #[] reserved
            basicModels false st2).1
    -- **A model may not leave an inductive it introduced unmodelled.** Arm C
    -- splices the index erasure of the family it is
    -- carving, so its output contains an inductive that was in nobody's
    -- input; if the descent above could not model it, emitting would put a
    -- additional unmodelled inductive in front of a consumer, which splice
    -- closure prevents.
    -- So the whole model is withdrawn and the declaration declines.
    --
    -- Checked **after** the descent and not predicted before it. A cheap test
    -- that says "this skeleton will model" is the shape of "skip is not
    -- pass": it reports success and leaves the hole open on the case it got
    -- wrong. This asks the environment.
    if basicModels then
      for n in is.requires do
        unless (← getEnv).constants.contains (Naming.modelName n) do
          -- **Withdraw everything**, and off `st` rather than off the locals:
          -- `out`, `rep` and `pending` have all been added to by the emission
          -- and the descent above, and returning any of those would leave the
          -- skeleton's records in the export with the model that needed them
          -- gone. `st` is the state as it stood before this declaration.
          setEnv saved
          -- **Carry the skeleton's own reason.** The descent recorded why it
          -- could not model it, and that entry is about to be discarded with
          -- the rest of the withdrawn state; a message that says only "the
          -- skeleton did not model" names where a value stopped rather than
          -- why, which is the defect class this repository has paid for most.
          let inner := (st2.2.1.declined.find? fun (m, _) => m == n).map (·.2)
          -- **"spliced inductive", not "spliced index erasure".** Arm C's
          -- skeleton was the only occupant when this was written; arm W's
          -- fragment is seventeen more, and none of them is an index
          -- erasure. A reason that misnames what stopped is the defect class
          -- this line already exists to avoid.
          let why := s!"prim model shape: the spliced inductive {n} did not model, so \
            emitting would leave an unmodelled inductive in front of a consumer \
            (the splice-closure rule) — {inner.getD "and the descent recorded no reason"}"
          return ((st.1, { st.2.1 with declined := st.2.1.declined.push (tname, why) },
            st.2.2), none)
    return (st2, none)

/-- **The composition's third step**: the implementation inductives a mutual
model just emitted — `T._model._impl.tag` and `T._model._impl.aux` — are
declarations of the output like any other, so the simple branch runs on them
too. The tag is a plain sum and models; the auxiliary is indexed and takes
arm C. Their own public carriers are the declaration-local names
`T._model._impl.tag._model` and `T._model._impl.aux._model`.

All input-owned prerequisite declarations are dependency-closed and scheduled
before model islands. Composition therefore completes in the same disposable
environment as the mutual model; retaining a job after its generated owner
would retain precisely the ownerful state this pass is designed to discard. -/
def primCompose (members : Array Name) (lparams : List Name) (np : Nat)
    (reserved : Std.HashSet Name) (basicModels : Bool)
    (st : FilterState) : MetaM FilterState := do
  let mut st := st
  -- Asked once, of the environment as it stands at the block: every member of
  -- one block is at the same point in the replay.
  let ready ← primReady reserved
  unless ready do
    throwError "composed simple model basis remained late after support scheduling: \
      {repr (← primMissingBasis reserved)}"
  for n in members do
    let some (.inductInfo iv) := (← getEnv).constants.find? n | continue
    let mut cts : Array (Name × Expr) := #[]
    for cn in iv.ctors do
      let some ci := (← getEnv).constants.find? cn | continue
      cts := cts.push (cn, ci.type)
    let (next, wait?) ←
      genPrim n lparams np iv.type cts #[] reserved basicModels true st
    if wait?.isSome then
      throwError "composed simple model prerequisite remained late after support scheduling"
    st := next
  return st

/-- One plain mutual block's model, generated and accounted for.

A separate function keeps the block path and the nested composition path on
one implementation. The basic layer controls the support closure of each
generated implementation tag and auxiliary model. -/
def genMutual (all : Array Name) (lparams : List Name) (np : Nat)
    (tys : Array Expr) (ctors : Array (Array (Name × Expr)))
    (projections : Array EProjection)
    (reserved : Std.HashSet Name) (simpleModels basicModels : Bool)
    (st : FilterState) : MetaM FilterState := do
  let (out, rep, pending) := st
  let saved ← getEnv
  let mut result ← (do
    let is ← mutualIso all lparams np tys ctors reserved
    addInstalledStructureModels all projections reserved is).run
  if let .error (.nameLost _) := result then
    setEnv saved
    result ← (do
      let is ← mutualIso all lparams np tys ctors reserved
        (some (Naming.retryRoot all[0]!))
      addInstalledStructureModels all projections reserved is).run
  match result with
  | .error dec =>
    setEnv saved
    return (out, { rep with declined := rep.declined.push (all[0]!, dec.labelAs "mutual") },
      pending)
  | .ok is =>
    let (records, is) ← serialiseIso is
    let mut out := out
    out := out ++ records
    let mut rep := { rep with generated := rep.generated.push (all[0]!, is.decls.size) }
    unless is.spliced.isEmpty do
      rep := { rep with spliced := rep.spliced.push (all[0]!, is.spliced) }
    let st := (out, rep, pending.push { spliced := is.spliced })
    if simpleModels then
      primCompose is.members is.levelParams np reserved basicModels st
    else
      return st

/-- Generation settings used by the aggregate fixture suite: nested and mutual
models remain enabled, while simple models and their bootstrap closure move
together. -/
def legacyGenerationConfig (primModels : Bool) : Cli.Config :=
  { simple := primModels, basic := primModels }

/-- Shared generation loop. With a sink, every accepted island is serialized
and compacted at its close boundary; the legacy declaration array remains for
the moment as an independent final-order/report oracle. -/
private def runFilterCore (x : Export) (checkRecursors : Bool) (generation : Cli.Config)
    (sink? : Option IslandSink) (retainOracle : Bool) :
    MetaM (Array EDecl × Report × StagedPlan) := do
  let scheduled ← match scheduleSource x generation with
    | .ok scheduled => pure scheduled
    | .error error => throwError "cannot schedule shared support: {repr error}"
  let mut mainEnv ← getEnv
  -- Built once. Each island overlays only its generated records, avoiding the
  -- former full-source declaration/constructor/rule/normalizer rebuild.
  let sourceSyntax := Check.SyntaxIndex.ofSource x
  let mut persistentSyntax := sourceSyntax
  let sourceSummaries := Order.summaries scheduled
  let sourceGlobalExtras := Check.globalExtraRecordsWithIndex sourceSyntax scheduled.decls
  let sourceFamilyRecords := Check.compactFamilyCertificateRecordsWithIndex
    scheduled sourceSyntax (Check.discover scheduled)
  let mut rawOrdinals : Std.HashMap Name Nat := {}
  for ordinal in [0:x.decls.size] do
    rawOrdinals := x.decls[ordinal]!.names.foldl
      (fun ordinals name => ordinals.insert name ordinal) rawOrdinals
  let mut legacyOut : Array EDecl := #[]
  let mut rep : Report := {}
  let mut staged : Array StagedIsland := #[]
  let mut stagedRecords : Array StagedRecord := #[]
  let mut scheduledOrdinal := 0
  let mut islandStatements : Check.StatementReport :=
    { statementsChecked := 0, violations := #[] }
  -- The declarations built inside the current model island. Besides staging
  -- exact generated names for support persistence, this keeps recursive
  -- splice closure and nested → mutual → simple composition atomic.
  -- A noncanonical declaration under a basis name makes generation
  -- unsupported for this stream. Support scheduling puts basis owners before
  -- their consumers; suppressing later islands prevents a weak, route-local
  -- prerequisite check from accidentally building against the wrong basis.
  let mut invalidBasis : Std.HashSet Name := {}
  -- Every name the input declares anywhere, so that a model cannot collide
  -- with one the file itself introduces *later*.
  let reserved : Std.HashSet Name :=
    x.decls.foldl (fun s d => d.names.foldl (·.insert ·) s) {}
  let mut persistentSupportOrigins : Std.HashMap Name Nat := {}
  for d in scheduled.decls do
    -- Construction state is island-local. Nothing generated for an earlier
    -- owner remains in this buffer after that island has closed.
    let mut out : Array EDecl := #[]
    let mut pending : Array PendingModel := #[]
    let mut modeledSourceFamilies : Array Check.CompactFamilyCertificate := #[]
    let mut modeledSourceGlobalExtra? : Option Check.GlobalExtraRecord := none
    let basisRoot? := match d with
      | .induct types _ _ => types.findSome? fun type =>
          if primBasis.contains type.name then some type.name else none
      | _ => none
    -- No model declaration is ever installed in `mainEnv`. All constructors
    -- below work in the ambient disposable fork; closing an inductive record
    -- restores this exact source prefix plus accepted reusable support.
    setEnv mainEnv
    let mainBefore := mainEnv
    let reportedBefore := rep.generated.size
    -- The model, if this is a nested declaration. Generated **before** the
    -- declaration is added: nothing in the model mentions `T`.
    if let .induct ts cs inputRecursors := d then
      -- **A mutual block whose members nest is one block, not several.** Lean
      -- specialises the whole block at once — `nest_mutual_both`'s `A`/`B`
      -- become four members with four recursors over one shared motive vector
      -- — so the model does too, under the first member's `_model` namespace
      -- and with one carrier per real member.
      if let t :: _ := ts then
        if generation.nested && ts.any (·.numNested > 0) &&
            basisRoot?.isNone && invalidBasis.isEmpty then
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
              rep := { rep with declined := rep.declined.push (t.name, dec.label) }
            | .ok is =>
              let (records, is) ← serialiseIso is
              out := out ++ records
              rep := { rep with generated := rep.generated.push (t.name, is.decls.size) }
              unless is.spliced.isEmpty do
                rep := { rep with spliced := rep.spliced.push (t.name, is.spliced) }
              pending := pending.push { spliced := is.spliced }
              -- ── the model of the model ────────────────────────────────────
              --
              -- **What has just been emitted is a `mutual … end` block**, and
              -- the second construction is the one that models exactly that.
              -- So it runs here, on `T._model.0 … T._model.{n−1}`, and the
              -- output carries a nested declaration's development twice over:
              -- the mutual model of `T`, and the *simple* model of that.
              --
              -- The block is still written — a model is emitted **beside** the
              -- thing it models and never in place of it — so what this
              -- buys is not that the output has no mutual block in it, but
              -- that **every** mutual block in the output has a model beside
              -- it, the ones this tool wrote included. A consumer that can add
              -- only a single inductive can now skip all of them.
              --
              -- **Here and not by re-running the filter.** The composition is
              -- one pass by construction; this is the composition boundary,
              -- and the prelude splice's
              -- idempotence is unaffected, because on an already-filtered
              -- input every name below is taken and the name guard declines.
              --
              -- `Eq` is certainly present: `Modelgen.iso` above went through
              -- `ensureEq`, which either found the input's or spliced Lean's.
              -- The composed step therefore satisfies its Eq prerequisite in
              -- this same island.
              if generation.mutualModels && is.members.size > 1 then
                let saved2 ← getEnv
                let (tys2, ctors2) ← blockOf is.members
                let composedRoot := is.members[0]!
                let mut mutualResult ← (do
                  let is2 ← mutualIso is.members is.levelParams t.numParams
                    tys2 ctors2 reserved
                  addInstalledStructureModels is.members #[] reserved is2).run
                if let .error (.nameLost _) := mutualResult then
                  setEnv saved2
                  mutualResult ← (do
                    let is2 ← mutualIso is.members is.levelParams t.numParams
                      tys2 ctors2 reserved (some (Naming.retryRoot composedRoot))
                    addInstalledStructureModels is.members #[] reserved is2).run
                match mutualResult with
                | .error dec =>
                  setEnv saved2
                  rep := { rep with
                    declined := rep.declined.push (is.members[0]!, dec.labelAs "mutual") }
                | .ok is2 =>
                  let (records, is2) ← serialiseIso is2
                  out := out ++ records
                  rep := { rep with
                    generated := rep.generated.push (is.members[0]!, is2.decls.size) }
                  pending := pending.push { spliced := is2.spliced }
                  -- ── the third step of the chain (`--simple`) ──────────────
                  -- The mutual model's own single inductives, modelled from
                  -- the primitives — nested → mutual → primitives, one pass.
                  if generation.simple then
                    let st3 ← primCompose is2.members is2.levelParams
                      t.numParams reserved generation.basic (out, rep, pending)
                    (out, rep, pending) ← pure st3
    -- Replay, unchecked: the input is trusted. Lean's kernel still runs the
    -- *inductive* elaboration, which is not skippable, so a deliberately
    -- ill-formed inductive stops the replay here. Nothing has been spliced yet
    -- when that happens, so the file passes through untouched.
    if let some dcl := toDeclaration (← getEnv) d then
      -- `Environment.addDeclCore` and not `Kernel.Environment.
      -- addDeclWithoutChecking`, even though the elaborator-side bookkeeping is
      -- unwanted here: `Environment.find?` — which `MetaM`'s `inferType` goes
      -- through — reads the *imported* half of the constant map and then the
      -- **async** map, so a constant added at the kernel level is invisible to
      -- it and the generator cannot so much as name `List.rec`. The price is
      -- one `panic!` from `AsyncConsts.add` on a large export where two private
      -- names from different modules normalise alike — normal in an export,
      -- which is many modules flattened into one file, and impossible during
      -- elaboration. It is not fatal: the entry is dropped from an index this
      -- tool never reads, so it does not affect model generation or checking.
      match (← getEnv).addDeclCore 0 dcl none false with
      | .ok e => setEnv e
      | .error ex =>
        let msg ← (ex.toMessageData {}).toString
        return (x.decls, { rep with unreplayable := some s!"{d.names}: {msg}" },
          { islands := #[], declarations := #[] })
    -- Basis exemption is granted only after the complete exported interface
    -- has been compared with one freshly minted by the kernel. The disposable
    -- alias environment used by the validator is never installed here.
    if let some root := basisRoot? then
      match ← (validateBasisOwner root d).run with
      | .ok () =>
        -- Preserve the report's route semantics: a valid basis owner is an
        -- exemption row only when simple generation selected it. Validation
        -- itself is unconditional, so an invalid unused owner still declines.
        if generation.modelsSimpleInput root then
          rep := { rep with
            exempt := rep.exempt.push (root, Decline.basisExempt.labelAs "prim") }
      | .error decline =>
        invalidBasis := invalidBasis.insert root
        rep := { rep with declined := rep.declined.push (root, decline.labelAs "prim") }
    -- **The model of a plain mutual block, and it is generated *after* the
    -- replay** where the nested one is generated before it. The reason is that
    -- there is nothing else to read the statements off: a nested declaration's
    -- model restates the recursors of the *specialised* block, which this tool
    -- builds itself, and a plain mutual block has no such second inductive —
    -- the implementation auxiliary's recursor is not `R_k.rec` at any
    -- renaming. So `Modelgen.mutualIso` reads the recursors Lean minted for the
    -- input's own block, which exist only once it is installed
    -- (`src/Modelgen/Mutual.lean`'s header).
    --
    -- The **records** still go out ahead of the declaration's whenever they
    -- can, because `out` has not been pushed yet.
    if let .induct ts cs _ := d then
      if let t :: _ := ts then
        -- **No "is this a block I wrote?" test here**, and that is deliberate.
        -- On this tool's own output the block `T._model.0 … T._model.{n−1}` is
        -- an input record like any other and does reach this branch — and
        -- declines, because every name its model would want is already in the
        -- file and the name guard says so. Idempotence is carried by the same
        -- mechanism that carries it for a nested declaration, which is
        -- one mechanism rather than two things to keep in step.
        if generation.mutualModels && ts.length > 1 && !ts.any (·.numNested > 0) &&
            basisRoot?.isNone && invalidBasis.isEmpty then
          let all := ts.toArray.map (·.name)
          let ctors := all.map fun n =>
            (cs.filter (·.induct == n)).toArray.map fun c => (c.name, c.type)
          let tys := ts.toArray.map (·.type)
          let mut needsExactSortLift := hasIntrinsicProjectionFields x ts cs
          unless needsExactSortLift do
            for type in ts do
              if type.isKernelStructureLike cs && !(← isPropFormerType type.type) then
                needsExactSortLift := true
          unless ← mutualReady needsExactSortLift reserved do
            throwError "plain mutual model prerequisites remained late after support scheduling"
          let st3 ← genMutual all t.levelParams t.numParams tys ctors #[] reserved
            generation.simple generation.basic (out, rep, pending)
          (out, rep, pending) ← pure st3
        -- ── a simple inductive (`--simple`) ──────────────────────────────
        -- Generated after replay because route construction reads the owner's
        -- installed recursor metadata. Acceptance later replays the serialized
        -- model owner-free, and statement correspondence uses export syntax.
        if generation.modelsSimpleInput t.name && ts.length == 1 && t.numNested == 0 &&
            basisRoot?.isNone && invalidBasis.isEmpty then
          let ctors := (cs.filter (·.induct == t.name)).toArray.map fun c => (c.name, c.type)
          -- Ask the selected route, rather than requiring the whole basis in
          -- advance. A reusable non-basis support declaration such as
          -- `Nonempty` may itself precede an independent input-owned ordinary
          -- `PSigma`, while its Church model does not mention
          -- that independent declaration at all.
          -- Any route that actually reaches a late splice still returns its
          -- exact readiness class below; fixed basis consumers are hoisted by
          -- `scheduledSupportRecord` before ordinary owners.
          let (st, wait?) ← genPrim t.name t.levelParams t.numParams t.type ctors
            #[] reserved generation.basic true (out, rep, pending)
          if wait?.isSome then
            throwError "simple model prerequisite remained late after support scheduling"
          (out, rep, pending) ← pure st
    if d matches .induct .. then
      let generated := out
      let islandModels := pending
      rep := { rep with
        maxLivePendingModels := max rep.maxLivePendingModels islandModels.size
        maxLiveIslandRecords := max rep.maxLiveIslandRecords generated.size }
      let islandOwners := (rep.generated.extract reportedBefore rep.generated.size).foldl
        (fun owners entry => owners.insert entry.1) ({} : Std.HashSet Name)
      let (orderedGenerated, compact, mainWithSupport, statementReport) ← match
          ← closeModelIsland x mainBefore generated islandModels d persistentSyntax islandOwners with
        | .ok result => pure result
        | .error message => throwError
            "owner-free generated declaration rejected for {d.names}: {message}"
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
      modeledSourceFamilies := compact.sourceFamilies
      modeledSourceGlobalExtra? := compact.sourceGlobalExtra?
      -- An inductive owner may legitimately produce no model under the active
      -- route configuration. It contributes no generated island; the spool
      -- transaction deliberately rejects empty commits.
      if let some sink := sink? then if !orderedGenerated.isEmpty then
        let commit ← sink.commit orderedGenerated
        unless orderedGenerated.size == commit.declarations.size do
          throwError "staged island cardinality mismatch for {d.names}: \
            records={orderedGenerated.size}, summaries={compact.summaries.size}, \
            extras={compact.globalExtras.size}, \
            spans={commit.declarations.size}"
        let islandNumber := staged.size
        let tagged := Order.tagIsland islandNumber compact.summaries
        for localOrdinal in [:tagged.size] do
          stagedRecords := stagedRecords.push {
            summary := tagged[localOrdinal]!
            globalExtra := compact.globalExtras[localOrdinal]!
            families := compact.families[localOrdinal]!.map (·.inIsland islandNumber)
            checkIsland? := some islandNumber
            locator := .generated islandNumber localOrdinal }
        staged := staged.push {
          compact := { compact with summaries := tagged }
          commit }
      let persistentRecords := generatedSupportRecords orderedGenerated islandModels
      if sink?.isSome && !orderedGenerated.isEmpty then
        let islandNumber := staged.size - 1
        for record in persistentRecords do
          for name in record.names do
            persistentSupportOrigins := persistentSupportOrigins.insert name islandNumber
      persistentSyntax := ← match persistentSyntax.prependRecords persistentRecords with
        | .ok index => pure index
        | .error message => throwError
            "cannot index accepted persistent support for {d.names}: {message}"
      if retainOracle then legacyOut := legacyOut ++ orderedGenerated
      setEnv mainWithSupport
      if let some ownerDeclaration := toDeclaration mainWithSupport d then
        match mainWithSupport.addDeclCore 0 ownerDeclaration none false with
        | .ok env =>
          mainEnv := env
          setEnv env
        | .error exception =>
          let message ← (exception.toMessageData {}).toString
          return (x.decls,
            { rep with unreplayable := some s!"{d.names}: {message}" },
            { islands := #[], declarations := #[] })
    else
      mainEnv ← getEnv
    legacyOut := legacyOut.push d
    if sink?.isSome then
      let some firstName := d.names.head? | throwError "source declaration has no name"
      let some rawOrdinal := rawOrdinals[firstName]?
        | throwError "scheduled source declaration {firstName} lost its raw ordinal"
      let modeledIsland? ← if modeledSourceFamilies.isEmpty then pure none else
        match staged.size with
        | 0 => throwError "modeled source family {d.names} has no committed generated island"
        | size + 1 => pure (some size)
      stagedRecords := stagedRecords.push {
        summary := sourceSummaries[scheduledOrdinal]!
        globalExtra := modeledSourceGlobalExtra?.getD sourceGlobalExtras[scheduledOrdinal]!
        families := sourceFamilyRecords[scheduledOrdinal]! ++
          (modeledSourceFamilies.map fun family =>
            modeledIsland?.elim family family.inIsland)
        checkIsland? := modeledIsland?
        locator := .source rawOrdinal }
    scheduledOrdinal := scheduledOrdinal + 1
    -- Statement correspondence is deliberately postponed until every emitted
    -- record is available.  It is an exact export-level comparison and does
    -- not consult this replay environment or the recursors the kernel minted
    -- for the owner.
    if checkRecursors then
      if let .induct _ _ rs := d then
        let (n, b) ← checkRecs rs
        rep := { rep with recChecked := rep.recChecked + n, recMismatch := rep.recMismatch ++ b }
  let stagedOrder ← if sink?.isSome then
      match Order.summaryRecordOrder (stagedRecords.map (·.summary)) with
      | .ok order => pure order
      | .error error => throwError "cannot compactly order staged records: {repr error}"
    else pure #[]
  let compactUnavailable? := if sink?.isSome then
      compactAvailabilityError? stagedRecords persistentSupportOrigins
    else none
  let compactCheckReport : Check.Report ← if sink?.isSome && compactUnavailable?.isNone then
      let orderedRecords := stagedOrder.map fun i =>
        { owner := stagedRecords[i]!.summary.owner
          modelSlots := stagedRecords[i]!.summary.modelSlots
          globalExtra := stagedRecords[i]!.globalExtra
          families := stagedRecords[i]!.families : Check.CompactCheckRecord }
      match Check.compactOrderedReport orderedRecords with
      | .ok report => pure report
      | .error message => throwError "invalid compact output certificate: {message}"
    else
      pure ({ familiesChecked := 0, violations := #[] } : Check.Report)
  let compactStatementReport := if sink?.isSome then
    let orderedGlobals := stagedOrder.map fun i => stagedRecords[i]!.globalExtra
    let diagnosticOwners := staged.foldl (init := ({} : Std.HashSet Name))
      fun owners island => island.compact.diagnosticOwners.toArray.foldl
        (fun owners owner => owners.insert owner) owners
    let compactGlobal := Check.globalExtrasFromRecordsFor orderedGlobals diagnosticOwners
    ({ islandStatements with
      violations := islandStatements.violations ++ compactGlobal } : Check.StatementReport)
  else islandStatements
  let statementReport ← if retainOracle then do
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
      if sink?.isSome then
        let fullOrder ← match Order.recordOrder finalExport with
          | .ok order => pure order
          | .error error => throwError "full oracle cannot order staged records: {repr error}"
        let compactNames := stagedOrder.map fun i => stagedRecords[i]!.summary.introduced
        let fullNames := fullOrder.map fun i => finalExport.decls[i]!.names.toArray
        unless compactNames == fullNames do
          throwError "compact staged order disagrees with full export: \
            compact={repr compactNames}, full={repr fullNames}"
        unless compactStatementReport == fullReport do
          throwError "compact staged statements disagree with full export: \
            compact={repr compactStatementReport}, full={repr fullReport}"
        let orderedExport := { finalExport with
          decls := fullOrder.map fun index => finalExport.decls[index]! }
        let fullCheckReport := Check.checkReport orderedExport
        if compactUnavailable?.isNone then
          unless compactCheckReport == fullCheckReport do
            throwError "compact output check disagrees with full export: \
              compact={repr compactCheckReport}, full={repr fullCheckReport}"
      pure fullReport
    else pure compactStatementReport
  rep := { rep with stmtChecked := statementReport.statementsChecked }
  rep := { rep with
    stmtErrors := statementReport.violations.map fun violation => violation.message }
  let emissionPlan : StagedPlan := {
    islands := staged.map (·.commit)
    declarations := stagedOrder.map fun index => stagedRecords[index]!.locator
    checkReport := compactCheckReport
    unavailable? := compactUnavailable? }
  return (legacyOut, rep, emissionPlan)

/-- **The filter.** -/
def runFilter (x : Export) (checkRecursors : Bool) (generation : Cli.Config) :
    MetaM (Array EDecl × Report) := do
  let (decls, report, _) ← runFilterCore x checkRecursors generation none true
  return (decls, report)

/-- Transitional staged oracle. Accepted islands are committed immediately,
but the full output remains live for the established final Order/Check oracle.
The returned plan has already discarded the compact checking summaries. -/
def runFilterWithIslandSink (x : Export) (checkRecursors : Bool) (generation : Cli.Config)
    (sink : IslandSink) : MetaM (Array EDecl × Report × StagedPlan) :=
  runFilterCore x checkRecursors generation (some sink) true

/-- AST-dropping staged generation. Accepted generated records are committed at
island close and never appended to a cumulative declaration array. The result
contains only ordered declaration locators and spool spans. -/
def runFilterStaged (x : Export) (checkRecursors : Bool) (generation : Cli.Config)
    (sink : IslandSink) : MetaM (Report × StagedPlan) := do
  let (_, report, plan) ← runFilterCore x checkRecursors generation (some sink) false
  return (report, plan)

end Modelgen
