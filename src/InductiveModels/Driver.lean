import InductiveModels.MutualOneLayer
import InductiveModels.Cli
import InductiveModels.Naming
import InductiveModels.Projection
import InductiveModels.Check
import InductiveModels.KernelCheck
import InductiveModels.FamilyAdapterShadow
import InductiveModels.Spool

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
`src/InductiveModels/Model.lean` specialises a nested declaration into a mutual block
and proves the export's recursors over it; `src/InductiveModels/Mutual.lean` packs a
plain mutual block into an implementation tag and one auxiliary inductive;
`src/InductiveModels/Simple.lean`
models a single inductive from the primitive basis. None is a degenerate case
of another, and this driver is the only thing that composes them.

## Why output is re-interned

Declaration records refer into one file-wide name, level, and expression arena.
After generation and ordering, [`InductiveModels.Export.writeTo`] therefore serializes
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

namespace InductiveModels

/-- The exact public type and universe binders of a generated declaration,
read from the construction result rather than from kernel-normalized metadata.
Proof construction may still use the installed declaration; only serialized
public statements cross this interface. -/
private structure GeneratedDeclInfo where
  levelParams : List Name
  type : Expr

private def generatedDeclInfo? (is : Iso) (name : Name) : Option GeneratedDeclInfo :=
  is.decls.findSome? fun declaration => match declaration with
    | .axiomDecl value =>
      if value.name == name then some { levelParams := value.levelParams, type := value.type }
      else none
    | .defnDecl value =>
      if value.name == name then some { levelParams := value.levelParams, type := value.type }
      else none
    | .thmDecl value =>
      if value.name == name then some { levelParams := value.levelParams, type := value.type }
      else none
    | .opaqueDecl value =>
      if value.name == name then some { levelParams := value.levelParams, type := value.type }
      else none
    | _ => none

private def generatedDeclInfo (is : Iso) (name : Name) : GenM GeneratedDeclInfo := do
  let some info := generatedDeclInfo? is name
    | badShape s!"generated declaration table has no public type for {name}"
  return info

private def instantiateForallsExact? (expression : Expr) (arguments : Array Expr) : Option Expr :=
  arguments.foldlM (fun expression argument => match expression with
    | .forallE _ _ body _ => some (body.instantiate1 argument)
    | _ => none) expression

/-- Apply the same deliberately bounded beta-only normalization as the exact
statement checker to the domains of a constructor telescope. -/
private partial def betaForallDomains (normalizer : ExactNormalizationEnv) : Expr → Expr
  | .forallE name domain body info =>
    .forallE name (normalizer.beta domain) (betaForallDomains normalizer body) info
  | body => body

/-- What one run did. -/
structure Report where
  generated : Array (Name × Nat) := #[]
  declined : Array (Name × String) := #[]
  /-- **The inductive-basis exemption, which is not a decline**
  ([`InductiveModels.inductiveBasis`]).
  `Eq`, `Nat`, `PSigma'`, and `PUnit` are the primitives
  the third construction is written in, so a run leaves them unmodelled *by
  definition*; counting them among the declines makes every coverage report
  a number it then had to walk back in the next sentence. Reported on their own
  lines and counted in their own row. -/
  exempt : Array (Name × String) := #[]
  /-- **Prelude constants the input did not declare and a model spliced in**,
  per declaration. `Eq`, the quotient and `Quot.sound` come out under Lean's
  own names and `funext` under the model's; `InductiveModels.ensureEq` and
  `InductiveModels.ensureFunext` say why the two are named differently. Printed,
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
  before ordering, checking, and either full output or compact discard. -/
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
  inductiveBasis.contains owner ||
    (!alreadyCovered.contains owner && !generated.contains owner)

/-- The compact support-persistence witness retained until an island closes.
The complete `Iso` is needed only while composing and serializing a model;
retaining it here would keep every generated declaration and construction
expression alive until owner-free replay. -/
structure PendingModel where
  spliced : Array Name

/-- Value-free information captured while one accepted island's declarations
are still live. The arrays remain aligned with the island's checked record
order and compact schedule rows. -/
structure CompactIsland where
  summaries : Array Order.DeclSummary
  globalExtras : Array Check.GlobalExtraRecord
  families : Array (Array Check.CompactFamilyCertificate)
  sourceFamilies : Array Check.CompactFamilyCertificate
  sourceGlobalExtra? : Option Check.GlobalExtraRecord
  diagnosticOwners : Std.HashSet Name

/-- Origin of one declaration in the eventual compact record schedule. Source
indices address exact input declarations; generated indices address an
accepted island and the declaration's position within that island. -/
inductive CompactLocator where
  | source (index : Nat)
  | generated (island declaration : Nat)
  deriving Inhabited, Repr, BEq

/-- Atomic value-free scheduling row. `summary` and `globalExtra` are captured
together with their logical locator and must always be permuted as one value. -/
structure CompactRecord where
  summary : Order.DeclSummary
  globalExtra : Check.GlobalExtraRecord
  families : Array Check.CompactFamilyCertificate := #[]
  /-- Syntax availability at certificate capture. Source payload can be
  recaptured with its current generated island while retaining its logical
  locator and scheduling origin. -/
  checkIsland? : Option Nat := none
  locator : CompactLocator
  deriving Inhabited, Repr

private def compactAvailabilityError? (records : Array CompactRecord)
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

/-- Value-only shadow of a compact generation pass, with no physical payloads
or generated declaration expressions. -/
structure CompactPlan where
  declarations : Array CompactLocator := #[]
  checkReport : Check.Report := { familiesChecked := 0, violations := #[] }
  unavailable? : Option String := none
  /-- A regression counter for the payload-retention contract. Compact discard
  never appends generated declarations to a cumulative output array. -/
  retainedGeneratedRecords : Nat := 0

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
  let census := publicTable.collisionCensusReserved reserved
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
    let typeInfo ← generatedDeclInfo is modelType
    let recInfo ← generatedDeclInfo is modelRecursor
    let recLevels ←
      if recInfo.levelParams.length == is.levelParams.length + 1 then
        pure (.zero :: us)
      else if recInfo.levelParams.length == is.levelParams.length then
        pure us
      else
        badShape s!"{modelRecursor} carries unexpected universe parameters"
    let recType := recInfo.type.instantiateLevelParams recInfo.levelParams recLevels
    let ctorInfo ← generatedDeclInfo is modelConstructor
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

private def phase1OneLayerProjectionCertificate (type : EIndType)
    (constructor : ECtor) (recursor : ERec) (is : Iso) : GenM Bool := do
  unless oneLayerProjectionFamily #[type] type ||
      indexedFibreOneLayerProjectionFamily #[type] type constructor recursor do return false
  let constructorName := constructor.name
  let some implementation := is.implementation? | return false
  let some publicModel := is.selfNames[0]? | return false
  let impl := Name.str publicModel "_impl"
  let expected : IsoInterface :=
    { selfNames := #[Name.str impl "self"]
      ctors := #[(constructorName, Name.str impl "ctor_0")]
      recs := #[Name.str impl "rec"]
      iotas := #[(0, constructorName, Name.str impl "rec_iota_0")] }
  unless implementation.selfNames == expected.selfNames &&
      implementation.ctors == expected.ctors &&
      implementation.recs == expected.recs &&
      implementation.iotas == expected.iotas do
    badShape s!"{type.name}'s phase-1 one-layer implementation certificate is malformed"
  for name in #[Name.str impl "roll", Name.str impl "unroll",
      Name.str impl "unroll_roll", Name.str impl "roll_unroll"] do
    let _ ← generatedDeclInfo is name
  return true

/-- Validate the simultaneous adapter as one complete owner/rule-keyed
certificate.  No member can opt into literal projection rules independently:
an absent, partial, duplicated, or malformed family fails closed. -/
private def mutualOneLayerProjectionCertificate (types : Array EIndType)
    (constructors : Array ECtor) (recursors : Array ERec) (type : EIndType)
    (constructorName : Name) (is : Iso) : GenM Bool := do
  let some certificate := is.familyImplementation? | return false
  let source := EDecl.induct types.toList constructors.toList recursors.toList
  let some changedMembers ← mutualOneLayerChangedMembers? source
    | badShape s!"{type.name}'s mutual one-layer certificate is outside the selected source shape"
  unless certificate.members.size == types.size && is.numAll == types.size &&
      is.selfNames.size == types.size && is.recs.size == types.size do
    badShape s!"{type.name}'s mutual one-layer family certificate is incomplete"
  let names : MutualFamilyNames :=
    { familyRoot := certificate.root
      tag := Name.str certificate.root "tag"
      aux := Name.str certificate.root "aux" }
  unless certificate.support == #[names.tag, names.aux] do
    badShape s!"{type.name}'s mutual one-layer support certificate is malformed"
  for name in certificate.support do
    unless is.decls.any fun declaration => declaration.getNames.contains name do
      badShape s!"{type.name}'s mutual one-layer support declaration {name} is absent"
  for memberIndex in [:types.size] do
    let sourceType := types[memberIndex]!
    let matching := certificate.members.filter fun member => member.owner == sourceType.name
    unless matching.size == 1 do
      badShape s!"{sourceType.name}'s mutual one-layer owner key is absent or duplicated"
    let member := matching[0]!
    let some (_, changed) := changedMembers.find? fun entry => entry.1 == sourceType.name
      | badShape s!"{sourceType.name}'s mutual one-layer source classification is incomplete"
    unless member.changed == changed && member.publicSelf == is.selfNames[memberIndex]! do
      badShape s!"{sourceType.name}'s mutual one-layer public member slot is malformed"
    let some sourceRecursor := recursors.find? fun recursor =>
        recursor.name == Name.str sourceType.name "rec"
      | badShape s!"{sourceType.name}'s exact mutual recursor record is absent"
    unless member.privateSelf == names.privateSelf sourceType.name &&
        member.privateRecursor == names.privateRecursor sourceType.name &&
        member.roll == names.roll sourceType.name &&
        member.unroll == names.unroll sourceType.name &&
        member.unrollRoll == names.unrollRoll sourceType.name &&
        member.rollUnroll == names.rollUnroll sourceType.name do
      badShape s!"{sourceType.name}'s mutual one-layer member names are malformed"
    let ownerConstructors := constructors.filter fun constructor =>
      constructor.induct == sourceType.name
    unless member.privateConstructors.size == ownerConstructors.size &&
        member.privateIotas.size == sourceRecursor.rules.length &&
        member.privateRules.size == sourceRecursor.rules.length do
      badShape s!"{sourceType.name}'s mutual one-layer constructor/rule certificate is incomplete"
    for constructor in ownerConstructors do
      let expected := names.privateConstructor sourceType.name constructor.name
      unless member.privateConstructors.filter (fun entry => entry.1 == constructor.name) ==
          #[(constructor.name, expected)] do
        badShape s!"{constructor.name}'s mutual one-layer constructor key is malformed"
      let _ ← generatedDeclInfo is expected
      let some (_, publicConstructor) := is.ctors.find? fun entry =>
          entry.1 == constructor.name
        | badShape s!"{constructor.name}'s mutual one-layer public constructor is absent"
      let _ ← generatedDeclInfo is publicConstructor
    for rule in sourceRecursor.rules do
      let expected := names.privateIota sourceType.name rule.ctor
      unless member.privateIotas.filter (fun entry =>
          entry.1 == sourceRecursor.name && entry.2.1 == rule.ctor) ==
          #[(sourceRecursor.name, rule.ctor, expected)] do
        badShape s!"{sourceRecursor.name}/{rule.ctor}'s mutual rule key is malformed"
      let _ ← generatedDeclInfo is expected
      let expectedRule := names.privateRule sourceType.name rule.ctor
      unless member.privateRules.filter (fun entry =>
          entry.1 == sourceRecursor.name && entry.2.1 == rule.ctor) ==
          #[(sourceRecursor.name, rule.ctor, expectedRule)] do
        badShape s!"{sourceRecursor.name}/{rule.ctor}'s mutual rule declaration is malformed"
      let _ ← generatedDeclInfo is expectedRule
    for name in #[member.publicSelf, member.privateSelf, member.privateRecursor,
        member.roll, member.unroll, member.unrollRoll, member.rollUnroll,
        is.recs[memberIndex]!] do
      let _ ← generatedDeclInfo is name
    for rule in sourceRecursor.rules do
      unless (is.iotas.filter fun entry =>
          entry.1 == memberIndex && entry.2.1 == rule.ctor).size == 1 do
        badShape s!"{sourceRecursor.name}/{rule.ctor}'s public rule key is absent or duplicated"
  let some member := certificate.members.find? fun member => member.owner == type.name
    | badShape s!"{type.name}'s mutual one-layer projection owner is absent"
  unless constructors.any fun constructor =>
      constructor.name == constructorName && constructor.induct == type.name do
    badShape s!"{constructorName}'s mutual one-layer projection constructor is absent"
  return member.changed

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
    (reserved : Std.HashSet Name) (is : Iso)
    (sourceNormalizer? : Option ExactNormalizationEnv := none) : GenM Iso := do
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
  let census := publicTable.collisionCensusReserved reserved
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
    let singletonOneLayer ←
      phase1OneLayerProjectionCertificate type constructor recursor is
    let mutualOneLayer ←
      mutualOneLayerProjectionCertificate types constructors recursors type constructorName is
    let phase1OneLayer := singletonOneLayer || mutualOneLayer
    let modelConstructorInfo ← generatedDeclInfo is modelConstructor
    let modelConstructorType := modelConstructorInfo.type
    let modelTypeInfo ← generatedDeclInfo is modelType
    let modelRecursorInfo ← generatedDeclInfo is modelRecursor
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
            let selfType ← mkForallFVars #[self] fieldType
            return (closeForallsExact? modelTypeInfo.type ownerArguments selfType).getD
              (← mkForallFVars ownerArguments selfType)
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
      let propositionLiteral := propositionProjectionIotaUsesLiteralField type
      let legacyLiteral := projectionIotaUsesLiteralField types type || propositionLiteral
      let rhs ←
        if legacyLiteral || phase1OneLayer then
          pure fields[fieldIndex]!
        else
          match ProjectionField.normalizeProjectionField eqi
            publicProjection normalizedFields fieldIndex with
          | .ok value => pure value
          | .error message => badShape message
      let some alpha := instantiateForallsExact? projectionType
          (params ++ indices ++ #[major])
        | badShape s!"{modelProjection}'s exact public type has the wrong arity"
      let fieldLevel ← ilevel alpha
      let proof ← match override? with
        | some (_, _, _, proof) => pure (proof.beta arguments)
        | none =>
          if legacyLiteral then
            pure (eqi.refl' fieldLevel alpha lhs)
          else do
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
      let body := eqi.mk' fieldLevel alpha lhs rhs
      let type ← match sourceNormalizer? with
        | some normalizer =>
          -- The selected one-layer public family is an exact source-name
          -- rewrite.  Its projection iota must retain even definitionally
          -- trivial source-authored binder syntax; the legacy structure
          -- routes continue to use their beta-only constructor telescope.
          let telescope := if phase1OneLayer || propositionLiteral then modelConstructorType
            else betaForallDomains normalizer modelConstructorType
          let fallback ← mkForallFVars arguments body
          pure ((closeForallsExact? telescope arguments body).getD fallback)
        | none => mkForallFVars arguments body
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
  let census := publicTable.collisionCensusReserved reserved
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
    let typeInfo ← generatedDeclInfo is modelType
    let constructorInfo ← generatedDeclInfo is modelConstructor
    let recursorInfo ← generatedDeclInfo is modelRecursor
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
    (reserved : Std.HashSet Name) (is : Iso)
    (sourceNormalizer? : Option ExactNormalizationEnv := none) : GenM Iso := do
  let is ← addProjectionModels types constructors recursors projections reserved is
    sourceNormalizer?
  let is ← addStructureEtaTheorems types constructors recursors reserved is
  addUnitlikeTheorems types constructors recursors reserved is

private abbrev ModelIslandState :=
  Array EDecl × Report × Array PendingModel × Array FamilyAdapter.ShadowObservation

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
**structurally** on the way back out. -/
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

/-- A generated declaration as export records — **plural**, because
`Declaration.quotDecl` is one kernel declaration and four records. Everything
else is one record and goes through [`InductiveModels.toEDecl`]. -/
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
      let quotientEnv ← match checked.addDeclCore 0 .quotDecl none true with
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
    match checked.addDeclCore 0 declaration none true with
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
    -- Reusable support belongs to the construction view. The complete exact
    -- emitted island is checked once, separately, when output checking is on.
    match main.addDeclCore 0 declaration none false with
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
    (sourceSyntax : Check.SyntaxIndex) (generatedOwners : Std.HashSet Name)
    (sourceAliases : SourceReplayAliases := {}) (typeCheckOutput : Bool := true) :
    MetaM (Except String
      (Array EDecl × CompactIsland × Environment × Check.StatementReport)) := do
  -- Generation runs in the collision-free replay environment, so generated
  -- expressions can mention replay aliases.  Restore the exact source names
  -- before every syntax/output operation.  Checked replay below converts the
  -- ordered result back in the opposite direction.
  let exactRecords := records.map sourceAliases.exactRecord
  unless exactRecords.map sourceAliases.buildRecord == records do
    return .error "generated source-alias round trip changed a declaration"
  -- Round-trip equality alone cannot see an unregistered derived build name:
  -- both exactRecord and buildRecord would leave it unchanged.  The exhaustive
  -- record mapper must find no construction prefix after exactification, even
  -- when output typechecking has been disabled by the caller.
  unless exactRecords.map sourceAliases.exactDerivedRecord == exactRecords do
    return .error "generated declaration retained an unregistered source replay alias"
  -- Generation appends every declaration in dependency order. The island is
  -- emitted exactly in that constructive order immediately before `owner`;
  -- no whole-island or whole-output ordering oracle is part of the route.
  let generated := exactRecords
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
  -- Drop the construction fork before reconstructing any declaration.  The
  -- exact serialized records and compact splice witnesses above are the only
  -- state allowed to cross into owner-free checked replay.
  setEnv main
  let replayGenerated := generated.map sourceAliases.buildRecord
  if typeCheckOutput then
    match ← checkGeneratedIn main replayGenerated with
    | .error message => return .error message
    | .ok _ => pure ()
  match ← installGeneratedSupportIn main replayGenerated models with
  | .error message => return .error message
  | .ok supported => return .ok (generated, compact, supported, statementReport)

/-- The exact quotient/choice interface that a prim model may splice after its
ordinary basis is ready.  These are source-scheduling names as well as the
readiness class used at the construction site below. -/
def lateSpliceNames : List Name :=
  [`Quot, `Quot.mk, `Quot.lift, `Quot.ind, `Quot.sound,
   `Nonempty, `Nonempty.intro, `Nonempty.rec, `Classical.choice]

/-- The exact logical interface shared with the fixed W fragment. -/
def wLogicalLateNames : List Name := [`Iff, `Iff.intro, `Iff.rec, `propext]

/-- The exact ordinary basis interface which can be input-owned.  Namespace
membership is intentionally insufficient: Mathlib contains hundreds of
unrelated later declarations such as `PUnit.le`, and preferring one of those
also prefers its complete dependency closure. -/
def scheduledPrimBasisNames : List Name :=
  [`Eq, `Eq.refl, `Eq.rec,
   `Nat, `Nat.zero, `Nat.succ, `Nat.rec,
   `PSigma', `PSigma'.mk, `PSigma'.rec, `PSigma'.fst, `PSigma'.snd,
   `PSigma'.fst_mk, `PSigma'.snd_mk, `PSigma'.rec', `PSigma'.rec'_mk,
   `PUnit, `PUnit.unit, `PUnit.rec]

/-- Source declarations which must be replayed before an unmodelled owner that
can need them.  Public core interfaces are selected by exact name.  The one
prefix exception is this tool's private `_wcore` namespace: its sentinel is
only sound when the complete fixed fragment has been replayed. -/
private def broadScheduledSupportRecord (declaration : EDecl) : Bool :=
  declaration.names.any fun name =>
    scheduledPrimBasisNames.contains name || lateSpliceNames.contains name ||
      wLogicalLateNames.contains name || wCoreRoot.isPrefixOf name

private def structuralScheduledSupportRecord (declaration : EDecl) : Bool :=
  declaration.names.any fun name =>
    [`Eq, `Eq.refl, `Eq.rec,
     `PSigma', `PSigma'.mk, `PSigma'.rec, `PSigma'.fst, `PSigma'.snd,
     `PSigma'.fst_mk, `PSigma'.snd_mk, `PSigma'.rec', `PSigma'.rec'_mk,
     `PUnit, `PUnit.unit, `PUnit.rec].contains name

def scheduledSupportRecord (generation : Cli.Config) (declaration : EDecl) : Bool :=
  if generation.simple || generation.basic then broadScheduledSupportRecord declaration
  else if generation.nested || generation.mutualModels then
    structuralScheduledSupportRecord declaration
  else false

/-- Whether this input record reaches any enabled model-generation branch.

This is the cheap scheduling pre-scan.  Fixed source support is relevant only
when an enabled branch has an owner whose public carrier is absent; basis and
fixed-support records are never such owners. -/
def scheduledModelOwner (generation : Cli.Config) (reserved : Std.HashSet Name) : EDecl → Bool
  | declaration@(.induct types _ _) =>
    match types with
    | [] => false
    | first :: _ =>
      !scheduledSupportRecord generation declaration &&
        !reserved.contains (Naming.modelName first.name) &&
        ((generation.nested && types.any (·.numNested > 0)) ||
          (generation.mutualModels && types.length > 1 && !types.any (·.numNested > 0)) ||
          (types.length == 1 && first.numNested == 0 &&
            generation.modelsSimpleInput first.name))
  | _ => false

/-- Independently classify the exact source owners for which generation lacks
the public carrier.  This repeats the enabled-branch cases instead of calling
[`scheduledModelOwner`], so the post-schedule certificate cannot certify a
pre-scan bug by reusing that pre-scan. -/
def generationMayAttemptOwner (generation : Cli.Config)
    (reserved : Std.HashSet Name) : EDecl → Bool
  | declaration@(.induct types _ _) =>
    match types with
    | [] => false
    | first :: _ =>
      !scheduledSupportRecord generation declaration &&
        !reserved.contains (Naming.modelName first.name) &&
        ((generation.nested && types.any (·.numNested > 0)) ||
          (generation.mutualModels && types.length > 1 && !types.any (·.numNested > 0)) ||
          (types.length == 1 && first.numNested == 0 &&
            generation.modelsSimpleInput first.name))
  | _ => false

/-- Whether any model-generation branch is enabled.  Kept local to the driver
so the library scheduler has the same boundary as the command-line driver. -/
def generationEnabled (generation : Cli.Config) : Bool :=
  generation.nested || generation.mutualModels || generation.simple || generation.basic

/-- Whether the source contains an actual late-support ordering hazard.

An absent public carrier is not sufficient: already-filtered files retain
permanently declined owners, and prioritizing support which already precedes
all of them changes independent byte order without enabling any construction.
Scan once in source order and request prioritization only when an exact
unmodelled candidate has already occurred before a later fixed-support record. -/
def sourceNeedsSupportScheduling (x : Export) (generation : Cli.Config)
    (reserved : Std.HashSet Name) : Bool := Id.run do
  let mut candidateSeen := false
  for declaration in x.decls do
    if scheduledModelOwner generation reserved declaration then
      candidateSeen := true
    if candidateSeen && scheduledSupportRecord generation declaration then
      return true
  return false

/-- Dependency-order source records.  Preserve ordinary stable order unless
an exact unmodelled owner precedes later source-owned support; only then hoist
the exact fixed interface and its dependency closure. -/
def scheduleSource (x : Export) (generation : Cli.Config) : Except Order.Error Export :=
  let reserved := x.decls.foldl (fun names declaration =>
    declaration.names.foldl (·.insert ·) names) {}
  if sourceNeedsSupportScheduling x generation reserved then
    Order.reorderPrioritizing x (scheduledSupportRecord generation)
  else
    Order.reorder x

/-- Certify the fixed-support scheduling invariant before constructing a
model.

Every selected owner outside the support class must follow every source record
in that class.  Support owners themselves are excluded: requiring `Eq` before
`Quot` and `Quot` before `Eq` would turn the atomic class into a cycle.  The
ordering pass already carries each support record's complete predecessor
closure; this check makes a regression in either selection or prioritization a
fail-fast internal error instead of eighteen unrelated model declines.

The owner classifier is intentionally [`generationMayAttemptOwner`], not
[`scheduledModelOwner`]: the scheduling pre-scan cannot certify itself. -/
def validateScheduledSupport (scheduled : Export) (generation : Cli.Config) : Except String Unit := do
  unless generationEnabled generation do return
  let reserved := scheduled.decls.foldl (fun names declaration =>
    declaration.names.foldl (·.insert ·) names) {}
  -- `every support index < ownerIndex` is equivalent to checking only the
  -- greatest support index.  Compute that witness once: the certificate stays
  -- exactly linear even on an export with many selected owners.
  let mut latestSupport? : Option (Nat × List Name) := none
  for supportIndex in [:scheduled.decls.size] do
    let support := scheduled.decls[supportIndex]!
    if scheduledSupportRecord generation support then
      latestSupport? := some (supportIndex, support.names)
  let some (supportIndex, supportNames) := latestSupport? | return
  for ownerIndex in [:scheduled.decls.size] do
    let owner := scheduled.decls[ownerIndex]!
    if scheduledSupportRecord generation owner then continue
    unless generationMayAttemptOwner generation reserved owner do continue
    unless supportIndex < ownerIndex do
      throw s!"latest fixed support {supportNames} remains at record {supportIndex} \
        after selected owner {owner.names} at record {ownerIndex}"

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

/-- Serialization result. `exactBlocks` and the compact generic-adapter shadow
are consumed inside the current island; neither is copied into output/report state. -/
structure SerialisedIso where
  records : Array EDecl
  exactBlocks : ExactGeneratedBlocks
  model : Iso
  adapterShadow? : Option FamilyAdapter.ShadowObservation

/-- Read a generated model back from the construction environment, register
every name Lean minted for its inductive blocks, and serialize through exact
alias lookups. The returned `Iso` carries the completed alias and splice
witnesses used for reporting and shared-support persistence. -/
def serialiseIso (source : EDecl) (is : Iso)
    (exactTransform : EDecl → EDecl := id) (observeAdapter : Bool := false) :
    MetaM SerialisedIso := do
  let adapterShadow? ← if observeAdapter then do
      let report ← FamilyAdapter.deriveShadowPlan source is
      pure (some (FamilyAdapter.ShadowReport.observe report))
    else do
      let _ ← FamilyAdapter.deriveShadowPlan source is
      pure none
  let mut rawRecords : Array EDecl := #[]
  for declaration in is.decls do
    rawRecords := rawRecords ++ (← toEDecls declaration)
  rawRecords := rawRecords.map fun record => match record with
    | .induct .. => exactTransform record
    | _ => record
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
  -- `Iso` continues to name declarations in the disposable construction
  -- environment. Only serialized records take exact aliases; the completed
  -- map therefore remains available while the exact output identities of
  -- spliced support are recorded for persistence and reporting.
  let model := { is with aliases := aliases, spliced := spliced }
  return {
    records := renamed
    exactBlocks := exactBlocks
    model := model
    adapterShadow? }

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

def checkInductiveMetadata (types : List EIndType) (constructors : List ECtor)
    (recursors : List ERec) : MetaM (Array String) := do
  return KernelCheck.checkInductiveMetadataIn (← getEnv) types constructors recursors

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

/-- **One installed inductive block, read back out of the environment** as the
member types and constructor lists [`InductiveModels.mutualIso`] wants.

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

private def hasIntrinsicProjectionFields (index : Check.SyntaxIndex) (types : List EIndType)
    (constructors : List ECtor) : Bool :=
  types.any fun type =>
    !(index.intrinsicProjectionFields type constructors).isEmpty

private def isMutualBasisRecord (needsExactSortLift : Bool) (declaration : EDecl) : Bool :=
  declaration.names.any fun name =>
    name == `Eq || name == `Eq.refl ||
      (needsExactSortLift && (name == `PSigma' || (`PSigma').isPrefixOf name ||
        name == `PUnit || (`PUnit).isPrefixOf name))

/-- **Can a prim model be written here?** — [`InductiveModels.eqReady`]'s question,
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

/- **The names beyond the basis that a prim model may splice** — the ones
[`InductiveModels.primReady`] does not cover. Input-owned records for these names are
moved, with their dependency closure, ahead of selected owners by
[`InductiveModels.scheduleSource`].

They form one post-scheduling readiness class:

* the quotient-side names deriving `funext` may splice
  ([`InductiveModels.ensureFunext`]). A prim model reaches them on the singleton route
  and wherever a pad at a level `dsingOk` cannot build is discharged by
  transport — `PUnit`'s and the derived exact-sort lift's shapes.
* `Nonempty` and `Classical.choice`, which **arm G** splices and which the W
  core's fragment now also carries. An input that declares `Acc` before
  `Nonempty` — `test/fixtures/inductive-models/w_core.ndjson`
  is one, since the fragment's `Acc` comes in through `WellFounded.fix` and its
  `Nonempty` only through `Classical.propDecidable` — used to lose `Acc`'s model
  to `prim model name taken (Nonempty)`. That is an uninstalled reserved-support
  name, not a generated name that was lost. -/
/- The exact logical interface the W fragment shares with the input.

`ensureWCore` refuses to splice any one of these when the input reserves it.
They form a separate atomic readiness class so a failed W construction reports
the complete Iff/propext prerequisite rather than conflating it with the
quotient/choice support used by non-W routes. `w_late_iff` pins that distinction. -/
/-- [`InductiveModels.primReady`]'s question, asked of quotient/choice support after a
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
accounted for — [`InductiveModels.primIso`], selected by `--simple`. Shared by the
input's own simple inductives and the composition (the single inductives the
other two constructions emit).

`canWait` enables prerequisite classification: a collision at fixed support
([`InductiveModels.Decline.lateReadiness?`]) returns its exact class in the second
component instead of recording a model-shape decline. Source owners have
already passed through [`InductiveModels.scheduleSource`]; recursive splice closure
passes `false` because it must complete inside the same model island.

**And, with `basicModels`, models for whatever that model had to splice.**

The second half closes a structural hole rather than adding a convenience.
`ensurePrim` and friends put a spliced inductive into the environment and into
the output, and nothing ever ran the third construction over it — so layer 3
was **unable to model anything it introduced**, and no coverage figure could
show it, because a spliced declaration was never a candidate to begin with.
Earlier coverage figures therefore measured only declarations from the input.

Only *non-basis* splices are modelled: the four on
[`InductiveModels.inductiveBasis`] are the exemption that makes the construction
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
    (st : ModelIslandState) (sourceBlock? : Option (EDecl × ExactNormalizationEnv) := none)
    (exactTransform : EDecl → EDecl := id)
    (selectPublicOneLayer : Bool := false)
    (collectAdapterShadows : Bool := false) :
    MetaM (ModelIslandState × Option PrimReadiness) := do
  let (out, rep, pending, adapterShadows) := st
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
  let sourceRecursor? := sourceBlock?.bind fun (block, _) => match block with
    | .induct _ _ recursors => recursors.find? (·.name == Name.str tname "rec")
    | _ => none
  let sourceType? := sourceBlock?.bind fun (block, _) => match block with
    | .induct types _ _ => types.find? (·.name == tname)
    | _ => none
  let sourceConstructor? := sourceBlock?.bind fun (block, _) => match block with
    | .induct _ constructors _ => constructors.find? (·.induct == tname)
    | _ => none
  let attachStructureModels := fun (is : Iso) => match sourceBlock? with
    | some (block, normalizer) =>
      addSourceStructureModels block projections normalizer reserved is
    | none => addInstalledStructureModels #[tname] projections reserved is
  let selectOneLayer ← if selectPublicOneLayer then
      phase1DirectTypeOneLayerEligible tname np ty ctors sourceRecursor?
    else pure false
  let selectIndexedFibre ← if selectPublicOneLayer && !selectOneLayer then
      match sourceType?, sourceConstructor?, sourceRecursor? with
      | some sourceType, some sourceConstructor, some sourceRecursor =>
        phase1IndexedFibreOneLayerEligible tname np ty ctors sourceType
          sourceConstructor sourceRecursor
      | _, _, _ => pure false
    else pure false
  let exactTaken ← exactPrimNameTaken? tname ctors projections
  let initial ← match exactTaken with
    | some n => pure (.error (.nameTaken n))
    | none => (do
        let is ← if selectOneLayer then
            let some sourceRecursor := sourceRecursor?
              | badShape s!"{tname}'s selected one-layer family has no exact recursor"
            let some sourceConstructor := ctors[0]?
              | badShape s!"{tname}'s selected one-layer family has no constructor"
            oneLayerIso tname root lparams np ty sourceConstructor sourceRecursor reserved
          else if selectIndexedFibre then
            let some sourceRecursor := sourceRecursor?
              | badShape s!"{tname}'s selected indexed fibre has no exact recursor"
            let some sourceConstructor := ctors[0]?
              | badShape s!"{tname}'s selected indexed fibre has no constructor"
            indexedFibreOneLayerIso tname root lparams np ty sourceConstructor sourceRecursor reserved
          else
            primIso tname root lparams np ty ctors reserved
              (sourceRecursor? := sourceRecursor?)
        attachStructureModels is).run
  let mut res := initial
  if let .error (.nameLost _) := res then
    setEnv saved
    root := aliasRoot
    res ← (do
      let is ← if selectOneLayer then
          let some sourceRecursor := sourceRecursor?
            | badShape s!"{tname}'s selected one-layer family has no exact recursor"
          let some sourceConstructor := ctors[0]?
            | badShape s!"{tname}'s selected one-layer family has no constructor"
          oneLayerIso tname root lparams np ty sourceConstructor sourceRecursor reserved
        else if selectIndexedFibre then
          let some sourceRecursor := sourceRecursor?
            | badShape s!"{tname}'s selected indexed fibre has no exact recursor"
          let some sourceConstructor := ctors[0]?
            | badShape s!"{tname}'s selected indexed fibre has no constructor"
          indexedFibreOneLayerIso tname root lparams np ty sourceConstructor sourceRecursor reserved
        else
          primIso tname root lparams np ty ctors reserved
            (sourceRecursor? := sourceRecursor?)
      attachStructureModels is).run
  match res with
  | .error dec =>
    setEnv saved
    if canWait then
      if let some readiness := dec.lateReadiness? then
        unless ← readiness.ready reserved do
          return ((out, rep, pending, adapterShadows), some readiness)
    -- **Exempt is not declined.** A basis primitive is what the construction
    -- is written in, so its absence from the models is the thing that makes
    -- the construction well-founded rather than a shape it cannot reach; it
    -- gets its own row and is out of the decline count.
    if dec matches .basisExempt then
      return ((out, { rep with exempt := rep.exempt.push (tname, dec.labelAs "prim") },
        pending, adapterShadows), none)
    return ((out, { rep with declined := rep.declined.push (tname, dec.labelAs "prim") },
      pending, adapterShadows), none)
  | .ok is =>
    let source ← match sourceBlock? with
      | some (block, _) => pure block
      | none => indEDecl #[tname]
    let serialised ← serialiseIso source is exactTransform collectAdapterShadows
    let records := serialised.records
    let is := serialised.model
    let mut out := out
    out := out ++ records
    let mut rep := { rep with generated := rep.generated.push (tname, is.decls.size) }
    unless is.spliced.isEmpty do
      rep := { rep with spliced := rep.spliced.push (tname, is.spliced) }
    let adapterShadows := serialised.adapterShadow?.elim adapterShadows adapterShadows.push
    let mut st2 := (out, rep, pending.push { spliced := is.spliced }, adapterShadows)
    if basicModels then
      for n in is.spliced do
        if inductiveBasis.contains n then continue
        let some (.inductInfo iv) := (← getEnv).constants.find? n | continue
        -- the block's own name only, and only a simple one
        unless iv.all == [n] && iv.numNested == 0 do continue
        -- Already modeled: the declaration-local carrier itself is the key.
        if (← getEnv).constants.contains (Naming.modelName n) then continue
        let mut cts : Array (Name × Expr) := #[]
        for cn in iv.ctors do
          if let some ci := (← getEnv).constants.find? cn then cts := cts.push (cn, ci.type)
        let exactBlock ← serialised.exactBlocks.require n
        -- Generated projection-iota closing uses only `ExactNormalizationEnv.beta`;
        -- that operation deliberately consults no named definition, so a
        -- one-block normalizer cannot lose persistent/source aliases.
        let normalizer := ({ metaLine := .null, decls := #[exactBlock] } : Export).exactNormalizationEnv
        st2 :=
          (← genPrim n iv.levelParams iv.numParams iv.type cts #[] reserved
            basicModels false st2 (some (exactBlock, normalizer)) exactTransform
            (collectAdapterShadows := collectAdapterShadows)).1
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
            st.2.2.1, st.2.2.2), none)
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
    (blocks : ExactGeneratedBlocks) (st : ModelIslandState)
    (exactTransform : EDecl → EDecl := id)
    (collectAdapterShadows : Bool := false) : MetaM ModelIslandState := do
  let mut st := st
  -- Asked once, of the environment as it stands at the block: every member of
  -- one block is at the same point in the replay.
  let ready ← primReady reserved
  unless ready do
    let owner := members[0]!
    let missing ← primMissingBasis reserved
    let (out, rep, pending, shadows) := st
    let declined := rep.declined.push
      (owner, s!"composed prim model prerequisites occur later in the input stream: \
        {repr missing}")
    return (out, { rep with declined }, pending, shadows)
  for n in members do
    let some (.inductInfo iv) := (← getEnv).constants.find? n | continue
    let mut cts : Array (Name × Expr) := #[]
    for cn in iv.ctors do
      let some ci := (← getEnv).constants.find? cn | continue
      cts := cts.push (cn, ci.type)
    let exactBlock ← blocks.require n
    let normalizer := ({ metaLine := .null, decls := #[exactBlock] } : Export).exactNormalizationEnv
    let (next, wait?) ←
      genPrim n lparams np iv.type cts #[] reserved basicModels true st
        (some (exactBlock, normalizer)) exactTransform
        (collectAdapterShadows := collectAdapterShadows)
    match wait? with
    | none => st := next
    | some _ =>
      let (out, rep, pending, shadows) := st
      let declined := rep.declined.push
        (n, "composed prim model prerequisite occurs later in the input stream")
      return (out, { rep with declined }, pending, shadows)
  return st

/-- One plain mutual block's model, generated and accounted for.

A separate function keeps the block path and the nested composition path on
one implementation. The basic layer controls the support closure of each
generated implementation tag and auxiliary model. -/
def genMutual (all : Array Name) (lparams : List Name) (np : Nat)
    (tys : Array Expr) (ctors : Array (Array (Name × Expr)))
    (projections : Array EProjection)
    (reserved : Std.HashSet Name) (simpleModels basicModels : Bool)
    (st : ModelIslandState) (sourceBlock? : Option EDecl := none)
    (exactTransform : EDecl → EDecl := id)
    (collectAdapterShadows : Bool := false) : MetaM ModelIslandState := do
  let (out, rep, pending, adapterShadows) := st
  let saved ← getEnv
  let generate := fun (buildRoot? : Option Name) => do
    let selected ← match sourceBlock? with
      | some source => mutualOneLayerEligible source
      | none => pure false
    if selected then
      let some source := sourceBlock?
        | badShape "selected mutual one-layer family has no exact source block"
      let is ← mutualOneLayerIso source reserved buildRoot?
      let normalizer := ({ metaLine := .null, decls := #[source] } : Export).exactNormalizationEnv
      addSourceStructureModels source projections normalizer reserved is
    else
      let is ← mutualIso all lparams np tys ctors reserved buildRoot?
        (sourceBlock? := sourceBlock?)
      addInstalledStructureModels all projections reserved is
  let mut result ← (generate none).run
  if let .error (.nameLost _) := result then
    setEnv saved
    result ← (generate (some (Naming.retryRoot all[0]!))).run
  match result with
  | .error dec =>
    setEnv saved
    return (out, { rep with declined := rep.declined.push (all[0]!, dec.labelAs "mutual") },
      pending, adapterShadows)
  | .ok is =>
    let source ← match sourceBlock? with
      | some block => pure block
      | none => indEDecl all
    let serialised ← serialiseIso source is exactTransform collectAdapterShadows
    let records := serialised.records
    let is := serialised.model
    let mut out := out
    out := out ++ records
    let mut rep := { rep with generated := rep.generated.push (all[0]!, is.decls.size) }
    unless is.spliced.isEmpty do
      rep := { rep with spliced := rep.spliced.push (all[0]!, is.spliced) }
    let adapterShadows := serialised.adapterShadow?.elim adapterShadows adapterShadows.push
    let st := (out, rep, pending.push { spliced := is.spliced }, adapterShadows)
    if simpleModels then
      primCompose is.members is.levelParams np reserved basicModels serialised.exactBlocks st
        exactTransform collectAdapterShadows
    else
      return st

/-- Generation settings used by the aggregate fixture suite: nested and mutual
models remain enabled, while simple models and their bootstrap closure move
together. -/
def legacyGenerationConfig (primModels : Bool) : Cli.Config :=
  { simple := primModels, basic := primModels }

/-! ## Declaration-wise filter state

The source scheduler still materialises a complete `Export` in this phase, but
the generation loop below no longer owns its mutable state as local variables.
`FilterState.feedSource` is the one-record logical transition and
`FilterState.finalize` consumes only its accumulated compact/output state.
This is the boundary a later census/span reader can drive without changing an
owner's pre-replay generation, source replay, post-replay generation, or atomic
island close. -/

/-- Observable, value-free boundary facts for one completed source transition.
This regression seam deliberately exposes neither `FilterState` nor a live
environment, so a test cannot mutate subsequent generation. -/
structure FilterSourceStep where
  scheduledOrdinal : Nat
  rawOrdinal : Nat
  sourceNames : Array Name
  sourceIsInductive : Bool
  sourceInstalled : Bool
  generated : Array (Name × Nat)
  generatedRecords : Nat
  deriving Inhabited, Repr, BEq

/-- Value-only comparison between declaration-wise exact kernel replay and the
historical batch oracle over the final reordered export.  `batchResult` is
always authoritative: a feed-order miss or differently ordered diagnostic
sets `usedFallback`. `streamedResult` remains observable only for A/B tests. -/
structure FilterKernelCheckShadow where
  streamedResult : Except String Unit
  batchResult : Except String Unit
  recordsPushed : Nat
  finalRecords : Nat
  usedFallback : Bool
  deriving Repr

private def sameKernelCheckResult (left right : Except String Unit) : Bool :=
  match left, right with
  | .ok (), .ok () => true
  | .error left, .error right => left == right
  | _, _ => false

/-- The diagnostic-order-preserving result of a full-oracle shadow run. -/
def FilterKernelCheckShadow.result (shadow : FilterKernelCheckShadow) : Except String Unit :=
  shadow.batchResult

/-- Environment-free result of direct compact kernel replay.  The checker has
already been sealed and its exact `Kernel.Environment` is unreachable.  A
`fallback?` means the chronological compact feed was not a complete final
schedule (for example, a generated provider appeared later); the eventual
caller must use the ordinary reordered batch oracle and its diagnostics. A
streamed rejection is represented only by a generic deferred error, never its
feed-order diagnostic. -/
structure CompactKernelCheckVerdict where
  result : Except String Unit
  recordsPushed : Nat
  scheduledRecords : Nat
  /-- Number of source transitions for which the direct route retained its
  cumulative construction environment.  The remaining source tail was
  checked and certified exactly without replaying it into Meta state. -/
  constructionTransitions : Nat
  fallback? : Option String := none
  deriving Repr

/-- Output retention is explicit: the full oracle retains declarations, while
the two compact no-output modes retain only value-level certificates. -/
private inductive RetentionMode where
  | fullOracle
  | compactDiscard
  | compactDirect

private def RetentionMode.isCompact : RetentionMode → Bool
  | .fullOracle => false
  | .compactDiscard | .compactDirect => true

private def RetentionMode.retainsOracle : RetentionMode → Bool
  | .fullOracle => true
  | .compactDiscard | .compactDirect => false

private def RetentionMode.checksKernelDirect : RetentionMode → Bool
  | .compactDirect => true
  | _ => false

/-- Value-free facts used by the planned scheduler after the source
declaration callback has returned.  `root?` and the three shape bits reproduce
the exact enabled-owner classification; the support bits preserve the two
configuration-dependent fixed interfaces. -/
structure SourceScheduleFact where
  root? : Option Name := none
  nestedOwner : Bool := false
  mutualOwner : Bool := false
  simpleOwner : Bool := false
  /-- This record owns any primitive inductive used to validate the simple
  construction basis.  Unlike `root?`, this ranges over every member of a
  mutual block. -/
  basisOwner : Bool := false
  /-- The exact output kernel checker deliberately omits this record.  The
  construction environment may still retain it for Meta visibility. -/
  kernelSkipped : Bool := false
  broadSupport : Bool := false
  structuralSupport : Bool := false
  deriving Inhabited, Repr, BEq

def SourceScheduleFact.ofDeclaration (declaration : EDecl) : SourceScheduleFact :=
  let (root?, nestedOwner, mutualOwner, simpleOwner, basisOwner) := match declaration with
    | .induct types _ _ => match types with
      | [] => (none, false, false, false, false)
      | first :: _ =>
        (some first.name, types.any (·.numNested > 0),
          types.length > 1 && !types.any (·.numNested > 0),
          types.length == 1 && first.numNested == 0,
          types.any fun type => inductiveBasis.contains type.name)
    | _ => (none, false, false, false, false)
  { root?, nestedOwner, mutualOwner, simpleOwner, basisOwner
    kernelSkipped := KernelCheck.metaOnlySkipped declaration
    broadSupport := broadScheduledSupportRecord declaration
    structuralSupport := structuralScheduledSupportRecord declaration }

def SourceScheduleFact.support (fact : SourceScheduleFact)
    (generation : Cli.Config) : Bool :=
  if generation.simple || generation.basic then fact.broadSupport
  else if generation.nested || generation.mutualModels then fact.structuralSupport
  else false

def SourceScheduleFact.modelOwner (fact : SourceScheduleFact)
    (generation : Cli.Config) (reserved : Std.HashSet Name) : Bool :=
  match fact.root? with
  | none => false
  | some root =>
    !fact.support generation && !reserved.contains (Naming.modelName root) &&
      ((generation.nested && fact.nestedOwner) ||
       (generation.mutualModels && fact.mutualOwner) ||
       (fact.simpleOwner && generation.modelsSimpleInput root))

/-- Whether this record can read or mutate cumulative construction state.

This is deliberately more conservative than [`SourceScheduleFact.modelOwner`]:
an occupied public carrier still reaches generation and reports `nameTaken`,
and every primitive-basis owner is validated even when it is exempt or
invalid. Recursive and composed generation remains inside the transition of
one of the three enabled owner shapes. -/
def SourceScheduleFact.constructionTouch (fact : SourceScheduleFact)
    (generation : Cli.Config) : Bool :=
  fact.basisOwner ||
    (generation.nested && fact.nestedOwner) ||
    (generation.mutualModels && fact.mutualOwner) ||
    (fact.simpleOwner && fact.root?.any generation.modelsSimpleInput)

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
records, and transparent definition values. Summaries, scheduling facts,
reserved names and raw ordinals do not retain complete `EDecl` values. -/
structure SourceCensus where
  sourceSyntax : Check.SyntaxIndex
  summaries : Array Order.DeclSummary
  scheduling : Array SourceScheduleFact
  reserved : Std.HashSet Name
  rawOrdinals : Std.HashMap Name Nat
  replayAliases : Except String SourceReplayAliases
  replayRoles : SourceReplayRoles
  private duplicate? : Option (Name × Nat × Nat)

/-- Single callback state for all raw-source products. -/
structure SourceCensus.Builder where
  private syntaxBuilder : Check.SyntaxIndex.Builder := {}
  private summaryBuilder : Order.SummaryBuilder := {}
  private scheduling : Array SourceScheduleFact := #[]
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
  | { syntaxBuilder, summaryBuilder, scheduling, reserved, rawOrdinals, duplicate?,
      replayRoles, nextOrdinal } =>
    let (duplicate?, _) := declaration.names.foldl
      (init := (duplicate?, ({} : Std.HashSet Name))) fun (duplicate?, seen) name =>
        let duplicate? := duplicate?.orElse fun _ =>
          if seen.contains name then some (name, nextOrdinal, nextOrdinal)
          else rawOrdinals[name]?.map fun first => (name, first, nextOrdinal)
        (duplicate?, seen.insert name)
    { syntaxBuilder := syntaxBuilder.push declaration
      summaryBuilder := summaryBuilder.push declaration
      scheduling := scheduling.push (.ofDeclaration declaration)
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
    scheduling := builder.scheduling
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

/-- Declaration-discarding parser result for the internal planned route.  The
raw certificate is not an eligibility promise: callers must still finish the
tee and construct a `PlannedSourceReader`. Generic raw composition requires a
canonical stream; the compact-direct CLI needs only a progressive arena and
falls back to the exact input snapshot when declaration replay is unsafe. -/
structure PlannedSourceInput where private mk ::
  envelope : ParsedEnvelope
  census : SourceCensus
  certificate : RawCertificate
  private provenance : Spool.SourceProvenance

private def parsePlannedSourceWithSink (stream : IO.FS.Stream) (sink : RawSink)
    (provenance : Spool.SourceProvenance)
    (allowDuplicateNames : Bool := false) :
    IO (Except String PlannedSourceInput) := do
  let builder ← IO.mkRef ({} : SourceCensus.Builder)
  let result ← parseStreamDiscardingDeclarations stream sink
    { emit := fun declaration => builder.modify (·.push declaration) }
    allowDuplicateNames
  match result with
  | .error error => return .error error
  | .ok (envelope, certificate) =>
    let census := (← builder.get).freeze
    unless census.summaries.size == envelope.declarationCount &&
        census.scheduling.size == envelope.declarationCount do
      return .error "planned source census cardinality disagrees with parser"
    return .ok (.mk envelope census certificate provenance)

def parsePlannedSourceWithTee (handle : IO.FS.Handle) (tee : Spool.ParseTee)
    (allowDuplicateNames : Bool := false) :
    IO (Except String PlannedSourceInput) :=
  parsePlannedSourceWithSink (IO.FS.Stream.ofHandle handle) tee.sink tee.sourceProvenance
    allowDuplicateNames

/-- Parse the compact-direct CLI input into a frozen census plus one exact raw
fallback snapshot and declaration spans. Generated output is not involved. -/
def parsePlannedSourceWithDirectTee (handle : IO.FS.Handle)
    (tee : Spool.DirectInputTee) (allowDuplicateNames : Bool := false) :
    IO (Except String PlannedSourceInput) :=
  parsePlannedSourceWithSink (IO.FS.Stream.ofHandle handle) tee.sink tee.sourceProvenance
    allowDuplicateNames

def parsePlannedSourceStreamWithDirectTee (stream : IO.FS.Stream)
    (tee : Spool.DirectInputTee) (allowDuplicateNames : Bool := false) :
    IO (Except String PlannedSourceInput) :=
  parsePlannedSourceWithSink stream tee.sink tee.sourceProvenance
    allowDuplicateNames

/-- Rebind declaration-local frozen summaries to a logical source order.
Every summary field except `ordinal` is a function of the declaration itself
and the source-wide owner-name table, so a permutation need not traverse its
expression graph again.  Validate the permutation here so future callers
cannot silently duplicate or omit one source record. -/
def SourceCensus.summariesForOrder (census : SourceCensus)
    (order : Array Nat) : Except String (Array Order.DeclSummary) := do
  unless order.size == census.summaries.size do
    throw "source summary order has the wrong number of records"
  let mut seen := Array.replicate census.summaries.size false
  let mut summaries : Array Order.DeclSummary := #[]
  for scheduledOrdinal in [:order.size] do
    let rawOrdinal := order[scheduledOrdinal]!
    unless rawOrdinal < census.summaries.size do
      throw s!"source summary order contains out-of-range record {rawOrdinal}"
    if seen[rawOrdinal]! then
      throw s!"source summary order repeats record {rawOrdinal}"
    seen := seen.set! rawOrdinal true
    summaries := summaries.push
      { census.summaries[rawOrdinal]! with ordinal := scheduledOrdinal }
  return summaries

/-- Rebind source-family certificates to a reordered declaration view without
interpreting the source index's raw record occurrences as view ordinals. -/
def SourceCensus.familyCertificateRecords (census : SourceCensus)
    (source view : Export) : Array (Array Check.CompactFamilyCertificate) := Id.run do
  let mut byOwner : Std.HashMap Name (Array Check.CompactFamilyCertificate) := {}
  for family in Check.discoverWithIndex source census.sourceSyntax do
    let certificate := Check.compactFamilyCertificateWithIndex source census.sourceSyntax family
    byOwner := byOwner.insert family.owner
      ((byOwner.getD family.owner #[]).push certificate)
  let mut rows := Array.replicate view.decls.size #[]
  for i in [0:view.decls.size] do
    if let .induct (type :: _) _ _ := view.decls[i]! then
      rows := rows.set! i (byOwner.getD type.name #[])
  return rows

/-- Produce today's exact dependency order from frozen summaries. -/
def SourceCensus.scheduleOrder (census : SourceCensus) (source : Export)
    (generation : Cli.Config) : Except Order.Error (Array Nat) := do
  let preferSupport := sourceNeedsSupportScheduling source generation census.reserved
  let summaries := if preferSupport then
      census.summaries.map fun summary =>
        { summary with support :=
            scheduledSupportRecord generation source.decls[summary.ordinal]! }
    else census.summaries
  Order.summaryRecordOrderPrioritizing summaries

/-- Exact support-hazard decision from callback facts only.  This is kept
separate from `sourceNeedsSupportScheduling` so the full-Export scheduler
remains an independent property oracle during migration. -/
def SourceCensus.needsPlannedSupportScheduling (census : SourceCensus)
    (generation : Cli.Config) : Bool := Id.run do
  let mut candidateSeen := false
  for fact in census.scheduling do
    if fact.modelOwner generation census.reserved then candidateSeen := true
    if candidateSeen && fact.support generation then return true
  return false

/-- Planned dependency order without a retained declaration array. -/
def SourceCensus.plannedScheduleOrder (census : SourceCensus)
    (generation : Cli.Config) : Except Order.Error (Array Nat) :=
  let preferSupport := census.needsPlannedSupportScheduling generation
  let summaries := if preferSupport then
      census.summaries.mapIdx fun ordinal summary =>
        { summary with support := census.scheduling[ordinal]!.support generation }
    else census.summaries
  Order.summaryRecordOrderPrioritizing summaries

/-- Recheck the post-schedule fixed-support invariant using only callback
facts. This mirrors, but does not call, the retained-Export certificate. -/
def SourceCensus.validatePlannedSupport (census : SourceCensus)
    (order : Array Nat) (generation : Cli.Config) : Except String Unit := do
  unless generationEnabled generation do return
  unless order.size == census.scheduling.size do
    throw "planned support order has the wrong number of records"
  let mut latestSupport? : Option (Nat × Array Name) := none
  for scheduledOrdinal in [:order.size] do
    let rawOrdinal := order[scheduledOrdinal]!
    unless rawOrdinal < census.scheduling.size do
      throw s!"planned support order contains out-of-range record {rawOrdinal}"
    if census.scheduling[rawOrdinal]!.support generation then
      latestSupport? := some (scheduledOrdinal, census.summaries[rawOrdinal]!.introduced)
  let some (supportIndex, supportNames) := latestSupport? | return
  for ownerIndex in [:order.size] do
    let rawOrdinal := order[ownerIndex]!
    let owner := census.scheduling[rawOrdinal]!
    if owner.support generation then continue
    unless owner.modelOwner generation census.reserved do continue
    unless supportIndex < ownerIndex do
      throw s!"latest fixed support {supportNames} remains at record {supportIndex} \
        after selected owner {census.summaries[rawOrdinal]!.introduced} at record {ownerIndex}"

/-- Produce today's complete scheduled `Export` from frozen summaries.  The
historical value-retaining scheduler remains as a property oracle; both use
the same owner-major/model-major stable graph algorithm. -/
def SourceCensus.schedule (census : SourceCensus) (source : Export)
    (generation : Cli.Config) : Except Order.Error Export := do
  let order ← census.scheduleOrder source generation
  return { source with decls := order.map fun ordinal => source.decls[ordinal]! }

/-- Exact source declarations installed ahead of their logical source turn.
The map is keyed by raw source ordinal so namespace similarity can never turn
an unrelated declaration into support. -/
private structure FutureSourceSupport where
  env : Environment
  records : Std.HashMap Nat EDecl

private def exactSupportBundleRecords? (source : Export) (names : Array Name) :
    Except String (Option (Array (Nat × EDecl))) := do
  let mut ordinals : Std.HashSet Nat := {}
  let mut anyPresent := false
  for name in names do
    let mut occurrences : Array Nat := #[]
    for ordinal in [:source.decls.size] do
      if source.decls[ordinal]!.names.contains name then
        occurrences := occurrences.push ordinal
    if !occurrences.isEmpty then anyPresent := true
    unless occurrences.size ≤ 1 do
      throw s!"future support name {name} is introduced more than once"
    if let some ordinal := occurrences[0]? then ordinals := ordinals.insert ordinal
  unless anyPresent do return none
  for name in names do
    unless source.decls.any (·.names.contains name) do
      throw s!"future support bundle containing {name} is incomplete"
  let mut records : Array (Nat × EDecl) := #[]
  for ordinal in [:source.decls.size] do
    if ordinals.contains ordinal then
      let declaration := source.decls[ordinal]!
      unless declaration.names.all names.contains do
        throw s!"future support record {declaration.names} also introduces an unaudited name"
      records := records.push (ordinal, declaration)
  return some records

private def installFutureRecords (env : Environment) (template : Export)
    (records : Array (Nat × EDecl)) : MetaM (Except String Environment) := do
  let bundle := { template with decls := records.map (·.2) }
  let ordered ← match Order.reorder bundle with
    | .ok ordered => pure ordered
    | .error error => return .error s!"cannot order future support bundle: {repr error}"
  checkGeneratedIn env ordered.decls

private def validateFutureBasis (env : Environment) (root : Name) (record : EDecl) :
    MetaM (Except String Unit) := do
  setEnv env
  match ← (validateBasisOwner root record).run with
  | .ok () => return .ok ()
  | .error decline => return .error decline.label

/-- Build the exact phase-one shadow ledger. Any partial, malformed, or
unsupported scheduled-support family makes the internal comparison mode use
the historical scheduler instead. This is deliberately narrower than
`scheduledSupportRecord`: no prefix or arbitrary future declaration is ever
preinstalled. -/
private def FutureSourceSupport.create (base : Environment) (source : Export)
    (generation : Cli.Config) : MetaM (Except String FutureSourceSupport) := do
  let eqNames : Array Name := #[`Eq, `Eq.refl, `Eq.rec]
  let natNames : Array Name := #[`Nat, `Nat.zero, `Nat.succ, `Nat.rec]
  let punitNames : Array Name := #[`PUnit, `PUnit.unit, `PUnit.rec]
  let psigmaNames : Array Name := #[`PSigma', `PSigma'.mk, `PSigma'.rec,
    `PSigma'.fst, `PSigma'.snd, `PSigma'.fst_mk, `PSigma'.snd_mk,
    `PSigma'.rec', `PSigma'.rec'_mk]
  let quotNames : Array Name := #[`Quot, `Quot.mk, `Quot.lift, `Quot.ind]
  let audited := (eqNames ++ natNames ++ punitNames ++ psigmaNames ++ quotNames).push `Quot.sound
  for declaration in source.decls do
    if scheduledSupportRecord generation declaration &&
        !declaration.names.all audited.contains then
      return .error s!"scheduled support {declaration.names} is outside the audited shadow set"
  let mut env := base
  let mut shadowed : Std.HashMap Nat EDecl := {}
  for (root, names) in #[( `Eq, eqNames), (`Nat, natNames),
      (`PUnit, punitNames), (`PSigma', psigmaNames)] do
    -- A canonical bundle outside the active route's scheduling class remains
    -- ordinary future source.  Preinstalling it would grant capabilities the
    -- historical scheduler deliberately leaves late (Nat for nested-only,
    -- and quotient support below).
    unless source.decls.any fun declaration =>
        scheduledSupportRecord generation declaration &&
          declaration.names.any names.contains do
      continue
    let records? ← match exactSupportBundleRecords? source names with
      | .ok records => pure records
      | .error error => return .error error
    if let some records := records? then
      let some (_, owner) := records.find? fun entry => entry.2.names.contains root
        | return .error s!"future support bundle {root} has no owner record"
      match ← validateFutureBasis env root owner with
      | .error error => return .error s!"future support {root} is not canonical: {error}"
      | .ok () => pure ()
      match ← installFutureRecords env source records with
      | .error error => return .error error
      | .ok next => env := next
      if root == `Eq then
        match EqInfo.check env with
        | .error error => return .error s!"future Eq is not canonical: {error}"
        | .ok _ => pure ()
      else if root == `Nat then
        match checkNat env with
        | .error error => return .error s!"future Nat is not canonical: {error}"
        | .ok () => pure ()
      else if root == `PUnit then
        match checkPUnit env with
        | .error error => return .error s!"future PUnit is not canonical: {error}"
        | .ok () => pure ()
      else
        setEnv env
        match ← (ensurePSigmaPrime {}).run with
        | .error decline => return .error s!"future PSigma' is not canonical: {decline.label}"
        | .ok added => unless added.isEmpty do
            return .error "future PSigma' bundle was incomplete"
      for (ordinal, record) in records do shadowed := shadowed.insert ordinal record
  let quotScheduled := source.decls.any fun declaration =>
    scheduledSupportRecord generation declaration &&
      declaration.names.any quotNames.contains
  let quotRecords? ← if quotScheduled then
    match exactSupportBundleRecords? source quotNames with
    | .ok records => pure records
    | .error error => return .error error
  else
    pure none
  if let some records := quotRecords? then
    let ordinals := records.map (·.1)
    unless ordinals.size == 4 && ordinals[1]! == ordinals[0]! + 1 &&
        ordinals[2]! == ordinals[1]! + 1 && ordinals[3]! == ordinals[2]! + 1 do
      return .error "future quotient is not one atomic four-record source bundle"
    match ← installFutureRecords env source records with
    | .error error => return .error error
    | .ok next => env := next
    let some expected := installedQuotRecords? env
      | return .error "future quotient did not install the kernel's four-record bundle"
    unless records.map (·.2) == expected do
      return .error "future quotient source records are not the kernel's exact bundle"
    for (ordinal, record) in records do shadowed := shadowed.insert ordinal record
  let soundRecords? ← if source.decls.any fun declaration =>
      scheduledSupportRecord generation declaration && declaration.names.contains `Quot.sound then
    match exactSupportBundleRecords? source #[`Quot.sound] with
    | .ok records => pure records
    | .error error => return .error error
  else
    pure none
  if let some records := soundRecords? then
    let #[entry] := records | return .error "future Quot.sound is not one source record"
    let .ax `Quot.sound levelParams _ false := entry.2
      | return .error "future Quot.sound is not a safe axiom"
    let [su] := levelParams | return .error "future Quot.sound has the wrong universe arity"
    match ← installFutureRecords env source records with
    | .error error => return .error error
    | .ok next => env := next
    let some info := env.constants.find? `Quot.sound
      | return .error "future Quot.sound disappeared after replay"
    let eqi ← match EqInfo.check env with
      | .ok eqi => pure eqi
      | .error error => return .error s!"future Quot.sound lacks canonical Eq: {error}"
    setEnv env
    unless ← isDefEq info.type (← quotSoundType eqi.eqN (.param su)) do
      return .error "future Quot.sound does not have Lean's statement"
    shadowed := shadowed.insert entry.1 entry.2
  return .ok { env, records := shadowed }

private structure FilterContext where
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
  /-- Construction-touch bits in scheduled source order.  These are frozen
  census facts, not retained declarations. -/
  sourceConstructionTouches : Array Bool
  /-- Exclusive scheduled-source cutoff for cumulative construction replay. -/
  constructionTransitions : Nat
  sourceGlobalExtras? : Option (Array Check.GlobalExtraRecord)
  sourceFamilyRecords? : Option (Array (Array Check.CompactFamilyCertificate))
  rawOrdinals : Std.HashMap Name Nat
  reserved : Std.HashSet Name
  constructionReserved : Std.HashSet Name
  kernelCheckBase? : Option Environment := none
  futureSupport? : Option FutureSourceSupport := none
  outputSourceOrder? : Option (Array Nat) := none
  collectTrace : Bool := false
  collectAdapterShadows : Bool := false
  sharedPrefixPhaseB : Bool := false

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

/-- Value-only observation of Phase A in the shared-prefix direct design.
`fallback?` makes the optimization unavailable without changing the ordinary
filter result.  The private preparation object below owns the actual shared
source environment and owner snapshots; this public seam cannot retain them. -/
structure SharedPrefixSourceObservation where
  sourceRecords : Nat
  ownerSnapshots : Nat
  metaOnlyRecords : Nat
  constructionTransitions : Nat
  fallback? : Option String := none
  deriving Inhabited, Repr, BEq

private structure SharedPrefixOwnerSnapshot where
  scheduledOrdinal : Nat
  rawOrdinal : Nat
  env : Environment

private inductive SharedPrefixSourceAccess where
  | retained (source : Export)
  | planned (reader : Spool.PlannedSourceReader)

private def SharedPrefixSourceAccess.read (access : SharedPrefixSourceAccess)
    (rawOrdinal : Nat) : MetaM (Except String EDecl) := match access with
  | .retained source => pure <| match source.decls[rawOrdinal]? with
    | some declaration => .ok declaration
    | none => .error s!"retained shared-prefix source ordinal {rawOrdinal} is out of range"
  | .planned reader => reader.read rawOrdinal

private structure SharedPrefixSourcePrepared where
  observation : SharedPrefixSourceObservation
  completedEnv : Environment
  snapshots : Array SharedPrefixOwnerSnapshot
  rows : Array CompactRecord
  context : FilterContext
  aliases : SourceReplayAliases
  metaOnlyNames : Std.HashSet Name
  sourceAccess : SharedPrefixSourceAccess

/-- Phase A: replay the collision-free source build image once, checking every
kernel-relevant record and retaining unchecked unsafe/partial records only for
Meta visibility.  Exact dependency roots certify that the latter are an
irrelevant extension.  Owner snapshots share the one persistent source prefix
and contain no generated declaration payload. -/
private def prepareSharedPrefixSourceCore (template : Export) (census : SourceCensus)
    (sourceAccess : SharedPrefixSourceAccess) (generation : Cli.Config) :
    MetaM (Except String SharedPrefixSourcePrepared) := do
  let plannedAliases ← match census.replayAliases with
    | .ok aliases => pure aliases
    | .error message => return .error s!"cannot plan collision-safe source replay: {message}"
  let aliases ← match sourceReplayInductiveDerivations census.replayRoles plannedAliases with
    | .ok aliases => pure aliases
    | .error message => return .error s!"cannot derive collision-safe inductive replay: {message}"
  unless aliases.isEmpty do
    for name in census.replayRoles.quotients do
      if aliases.hasExact name then
        return .error s!"normalized source-name collision moves quotient role {name}"
  let planned := sourceAccess matches .planned _
  let sourceOrder ← match if planned then census.plannedScheduleOrder generation else
      match sourceAccess with
      | .retained source => census.scheduleOrder source generation
      | .planned _ => unreachable! with
    | .ok order => pure order
    | .error error => return .error s!"cannot schedule shared support: {repr error}"
  let supportValidation := if planned then census.validatePlannedSupport sourceOrder generation
    else match sourceAccess with
      | .retained source =>
        let scheduled := { source with
          decls := sourceOrder.map fun ordinal => source.decls[ordinal]! }
        validateScheduledSupport scheduled generation
      | .planned _ => unreachable!
  match supportValidation with
  | .error message => return .error s!"invalid shared-support schedule: {message}"
  | .ok () => pure ()
  let sourceSummaries ← match census.summariesForOrder sourceOrder with
    | .ok summaries => pure summaries
    | .error message => return .error s!"cannot rebind frozen source summaries: {message}"
  let mut metaOnlyNames : Std.HashSet Name := {}
  let mut metaOnlyRecords := 0
  for rawOrdinal in [:census.scheduling.size] do
    if census.scheduling[rawOrdinal]!.kernelSkipped then
      metaOnlyRecords := metaOnlyRecords + 1
      for name in census.summaries[rawOrdinal]!.introduced do
        metaOnlyNames := metaOnlyNames.insert name
  let base ← getEnv
  let mut env := base
  let mut snapshots : Array SharedPrefixOwnerSnapshot := #[]
  let mut rows : Array CompactRecord := #[]
  let mut sourceGlobals : Array Check.GlobalExtraRecord := #[]
  let mut sourceFamilies : Array (Array Check.CompactFamilyCertificate) := #[]
  let mut constructionSyntax := census.sourceSyntax
  let mut constructionTransitions := 0
  let sourceConstructionTouches := sourceOrder.map fun rawOrdinal =>
    census.scheduling[rawOrdinal]!.constructionTouch generation
  for scheduledOrdinal in [:sourceOrder.size] do
    let rawOrdinal := sourceOrder[scheduledOrdinal]!
    let declaration ← match ← sourceAccess.read rawOrdinal with
      | .ok declaration => pure declaration
      | .error message =>
        return .error s!"cannot decode shared-prefix source record {rawOrdinal}: {message}"
    let fact := census.scheduling[rawOrdinal]!
    if fact.constructionTouch generation then
      constructionTransitions := scheduledOrdinal + 1
      snapshots := snapshots.push { scheduledOrdinal, rawOrdinal, env }
    let logicalDisposition ← match KernelCheck.replayDisposition declaration with
      | .error message => return .error message
      | .ok disposition => pure disposition
    unless (logicalDisposition matches .metaOnly) == fact.kernelSkipped do
      return .error s!"source replay classification disagrees for {declaration.names}"
    if !fact.kernelSkipped then
      if let some dependency := (KernelCheck.inputReferences declaration).toArray.find?
          metaOnlyNames.contains then
        return .error s!"checked source record {declaration.names} depends on \
          unchecked construction-only declaration {dependency}"
    let replay := aliases.buildRecord declaration
    unless aliases.exactRecord replay == declaration do
      return .error s!"source replay round trip changed {declaration.names}"
    unless aliases.exactDerivedRecord declaration == declaration do
      return .error s!"source declaration {declaration.names} contains a fresh build alias"
    if sourceRecordUsesAliases aliases census.summaries[rawOrdinal]! declaration then
      match constructionSyntax.withReplayRecords #[declaration] #[replay] with
      | .ok next => constructionSyntax := next
      | .error message =>
        return .error s!"cannot index collision-safe source replay: {message}"
    let buildDisposition ← match KernelCheck.replayDisposition replay with
      | .error message => return .error (aliases.exactMessage message)
      | .ok disposition => pure disposition
    unless (logicalDisposition matches .checked ..) == (buildDisposition matches .checked ..) &&
        (logicalDisposition matches .metaOnly) == (buildDisposition matches .metaOnly) &&
        (logicalDisposition matches .bundled) == (buildDisposition matches .bundled) do
      return .error s!"source replay classification changed under aliases for {declaration.names}"
    setEnv env
    let kernelDeclaration? ← match buildDisposition with
      | .checked kernelDeclaration => pure (some (kernelDeclaration, true))
      | .metaOnly => match toDeclaration env replay with
        | some kernelDeclaration => pure (some (kernelDeclaration, false))
        | none => return .error s!"construction-only source record {declaration.names} \
            could not be reconstructed for Meta visibility"
      | .bundled => pure none
    if let some (kernelDeclaration, doCheck) := kernelDeclaration? then
      match env.addDeclCore 0 kernelDeclaration none doCheck with
      | .error exception =>
        return .error s!"{declaration.names}: {aliases.exactMessage
          (← (exception.toMessageData {}).toString)}"
      | .ok next =>
        env := next
        setEnv next
    if buildDisposition matches .checked .. then
      let mismatches := KernelCheck.mappedMetadataMismatches env replay
      unless mismatches.isEmpty do
        return .error s!"source build-image metadata differs from Lean's kernel for \
          {declaration.names}: {mismatches.toList.map aliases.exactMessage}"
    if sourceRecordUsesAliases aliases sourceSummaries[scheduledOrdinal]! declaration then
      if let .induct types constructors recursors := replay then
        let mismatches ← checkInductiveMetadata types constructors recursors
        unless mismatches.isEmpty do
          return .error s!"collision-safe inductive replay metadata differs for \
            {declaration.names}: {mismatches.toList.map aliases.exactMessage}"
    if declaration matches .quot .. then
      let some installed := installedQuotRecords? env
        | return .error "source quotient bundle was not installed by its leading record"
      unless installed.contains declaration do
        return .error s!"source quotient record {declaration.names} differs from the kernel bundle"
    let some firstName := declaration.names.head?
      | return .error "shared-prefix source declaration has no name"
    let some certifiedRaw := census.rawOrdinals[firstName]?
      | return .error s!"shared-prefix source declaration {firstName} lost its raw ordinal"
    unless certifiedRaw == rawOrdinal do
      return .error s!"shared-prefix source declaration {firstName} changed raw ordinal"
    unless sourceSummaries[scheduledOrdinal]!.introduced == declaration.names.toArray do
      return .error s!"shared-prefix source row changed names for {declaration.names}"
    let globalExtra := (Check.globalExtraRecordsWithIndex census.sourceSyntax #[declaration])[0]!
    let families := census.sourceSyntax.sourceFamilyCertificatesForRecord template declaration
    sourceGlobals := sourceGlobals.push globalExtra
    sourceFamilies := sourceFamilies.push families
    rows := rows.push {
      summary := sourceSummaries[scheduledOrdinal]!
      globalExtra
      families
      locator := .source rawOrdinal }
  let constructionReserved := census.reserved.fold (init := census.reserved) fun names name =>
    (aliases.buildDerivedNames name).foldl (fun names build => names.insert build) names
  let context : FilterContext := {
    source := template
    checkRecursors := false
    generation
    retention := .compactDirect
    exactTransform := id
    sourceSyntax := census.sourceSyntax
    constructionSyntax
    constructionNormalizer := constructionSyntax.exactNormalizer
    sourceAliases := aliases
    sourceSummaries
    sourceConstructionTouches
    constructionTransitions
    sourceGlobalExtras? := some sourceGlobals
    sourceFamilyRecords? := some sourceFamilies
    rawOrdinals := census.rawOrdinals
    reserved := census.reserved
    constructionReserved
    kernelCheckBase? := some base
    sharedPrefixPhaseB := true }
  return .ok {
    observation := {
      sourceRecords := sourceOrder.size
      ownerSnapshots := snapshots.size
      metaOnlyRecords
      constructionTransitions }
    completedEnv := env
    snapshots
    rows
    context
    aliases
    metaOnlyNames
    sourceAccess }

private def prepareSharedPrefixSource (x : Export) (generation : Cli.Config) :
    MetaM (Except String SharedPrefixSourcePrepared) :=
  prepareSharedPrefixSourceCore x (SourceCensus.ofSource x) (.retained x) generation

/-- Test-facing Phase-A observer.  It always restores the invocation base and
returns only counts/fallback text; the shared environments remain private. -/
def observeSharedPrefixSource (x : Export) (generation : Cli.Config) :
    MetaM SharedPrefixSourceObservation := do
  let base ← getEnv
  let prepared ← try
    prepareSharedPrefixSource x generation
  finally
    setEnv base
  match prepared with
  | .ok prepared => return prepared.observation
  | .error message => return {
      sourceRecords := x.decls.size
      ownerSnapshots := 0
      metaOnlyRecords := 0
      constructionTransitions := 0
      fallback? := some message }

private structure FilterState where
  mainEnv : Environment
  persistentSyntax : Check.SyntaxIndex
  legacyOut : Array EDecl := #[]
  report : Report := {}
  compactIslands : Array CompactIsland := #[]
  compactRecords : Array CompactRecord := #[]
  scheduledOrdinal : Nat := 0
  islandStatements : Check.StatementReport :=
    { statementsChecked := 0, violations := #[] }
  invalidBasis : Std.HashSet Name := {}
  persistentSupportOrigins : Std.HashMap Name Nat := {}
  futureSupportRemaining : Std.HashMap Nat EDecl := {}
  emissionByRaw : Std.HashMap Nat (Array EDecl) := {}
  sourceSteps : Array FilterSourceStep := #[]
  kernelCheckState? : Option KernelCheck.State := none
  /-- Exact name rows captured atomically with direct compact pushes.  Names
  only: retaining this array cannot retain a declaration expression graph. -/
  kernelCheckRows : Array (Array Name) := #[]
  adapterShadows : Array FamilyAdapter.ShadowObservation := #[]
  /-- Phase-B-only exact support payload witnessed by accepted islands. No
  non-support generated declaration may enter this array. -/
  constructionSupportRecords : Array EDecl := #[]
  /-- Phase-B-only cumulative aliases for the completed output checker and
  exact witnessed-support replay. They include disposable generated names to
  keep the checker build image injective, but must never affect construction,
  readiness, `nameTaken`, or report spelling. -/
  sharedPrefixAliases? : Option SourceReplayAliases := none
  sharedPrefixMetaOnlyNames : Std.HashSet Name := {}

private inductive FilterFeedResult where
  | next (state : FilterState)
  /-- Preserve the completed trace without making the caller retain the whole
  previous state while `feedSource` appends to its accumulated arrays. -/
  | unreplayable (report : Report) (sourceSteps : Array FilterSourceStep)

/-- Consume a source record after the final possible construction transition.
The cumulative construction environment has already been replaced by the
exact invocation base.  Frozen syntax products supply the same compact row;
the live exact declaration is bound directly to that row and immediately
released after the incremental kernel push. -/
private def FilterState.feedSourceExactTail (state : FilterState)
    (context : FilterContext) (d : EDecl) : MetaM FilterState := do
  unless context.retention.checksKernelDirect do
    throwError "exact-only source tail selected outside direct retention"
  let scheduledOrdinal := state.scheduledOrdinal
  if context.sourceConstructionTouches[scheduledOrdinal]! then
    throwError "construction-touching source record reached the exact-only tail"
  let sourceSummary := context.sourceSummaries[scheduledOrdinal]!
  let sourceGlobalExtra := match context.sourceGlobalExtras?.bind (·[scheduledOrdinal]?) with
    | some record => record
    | none => (Check.globalExtraRecordsWithIndex context.sourceSyntax #[d])[0]!
  let sourceFamilyRecord := match context.sourceFamilyRecords?.bind (·[scheduledOrdinal]?) with
    | some records => records
    | none => context.sourceSyntax.sourceFamilyCertificatesForRecord context.source d
  let some firstName := d.names.head? | throwError "source declaration has no name"
  let some rawOrdinal := context.rawOrdinals[firstName]?
    | throwError "scheduled source declaration {firstName} lost its raw ordinal"
  let row : CompactRecord := {
    summary := sourceSummary
    globalExtra := sourceGlobalExtra
    families := sourceFamilyRecord
    checkIsland? := none
    locator := .source rawOrdinal }
  let some checker := state.kernelCheckState?
    | throwError "compact direct exact tail lost its exact kernel checker"
  let checker ← checker.pushBound d row.summary.introduced
  return { state with
    compactRecords := state.compactRecords.push row
    scheduledOrdinal := scheduledOrdinal + 1
    kernelCheckState? := some checker
    kernelCheckRows := state.kernelCheckRows.push row.summary.introduced }

/-- Consume one declaration from the already dependency-ordered logical source
stream.  Every mutable field which survives this call is explicit in
`FilterState`; `out`, `pending`, and the replay fork remain owner-local. -/
private def FilterState.feedSource (state : FilterState) (context : FilterContext)
    (d : EDecl) : MetaM FilterFeedResult := do
  let x := context.source
  let generation := context.generation
  let retention := context.retention
  let compactMode := retention.isCompact
  let retainOracle := retention.retainsOracle
  let exactTransform := context.exactTransform
  let sourceSyntax := context.sourceSyntax
  let constructionSyntax := context.constructionSyntax
  let constructionNormalizer := context.constructionNormalizer
  -- Each transition must use the same source-only alias view as the ordinary
  -- construction path. Phase B keeps a separate cumulative table solely for
  -- checker mapping and witnessed-support replay into historical snapshots.
  let sourceAliases := context.sourceAliases
  let sourceSummaries := context.sourceSummaries
  let scheduledOrdinal := state.scheduledOrdinal
  let sourceSummary := sourceSummaries[scheduledOrdinal]!
  let sourceUsesAlias := sourceRecordUsesAliases sourceAliases sourceSummary d
  let replayD := if sourceUsesAlias then sourceAliases.buildRecord d else d
  let sourceGlobalExtra := match context.sourceGlobalExtras?.bind (·[scheduledOrdinal]?) with
    | some record => record
    | none => (Check.globalExtraRecordsWithIndex sourceSyntax #[d])[0]!
  let sourceFamilyRecord := match context.sourceFamilyRecords?.bind (·[scheduledOrdinal]?) with
    | some records => records
    | none => sourceSyntax.sourceFamilyCertificatesForRecord x d
  let rawOrdinals := context.rawOrdinals
  let reserved := context.constructionReserved
  let mut mainEnv := state.mainEnv
  let mut persistentSyntax := state.persistentSyntax
  let mut legacyOut := state.legacyOut
  let mut rep := state.report
  let mut compactIslands := state.compactIslands
  let mut compactRecords := state.compactRecords
  let mut islandStatements := state.islandStatements
  let mut invalidBasis := state.invalidBasis
  let mut persistentSupportOrigins := state.persistentSupportOrigins
  let mut futureSupportRemaining := state.futureSupportRemaining
  let mut emissionByRaw := state.emissionByRaw
  let mut sourceSteps := state.sourceSteps
  let mut kernelCheckState? := state.kernelCheckState?
  let mut kernelCheckRows := state.kernelCheckRows
  let mut adapterShadows := state.adapterShadows
  let mut constructionSupportRecords := state.constructionSupportRecords
  let mut sharedPrefixAliases? := state.sharedPrefixAliases?
  let mut sharedPrefixMetaOnlyNames := state.sharedPrefixMetaOnlyNames
  let emissionStart := legacyOut.size
  -- Construction state is island-local. Nothing generated for an earlier
  -- owner remains in this buffer after that island has closed.
  let mut out : Array EDecl := #[]
  let mut pending : Array PendingModel := #[]
  let mut islandAdapterShadows : Array FamilyAdapter.ShadowObservation := #[]
  let mut modeledSourceFamilies : Array Check.CompactFamilyCertificate := #[]
  let mut modeledSourceGlobalExtra? : Option Check.GlobalExtraRecord := none
  let basisRoot? := match replayD with
    | .induct types _ _ => types.findSome? fun type =>
        if inductiveBasis.contains type.name then some type.name else none
    | _ => none
  -- No model declaration is ever installed in `mainEnv`. All constructors
  -- below work in the ambient disposable fork; closing an inductive record
  -- restores this exact source prefix plus accepted reusable support.
  setEnv mainEnv
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
            let serialised ← serialiseIso replayD is exactTransform context.collectAdapterShadows
            if let some shadow := serialised.adapterShadow? then
              islandAdapterShadows := islandAdapterShadows.push shadow
            let records := serialised.records
            let is := serialised.model
            out := out ++ records
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
                rep := { rep with
                  declined := rep.declined.push (is.members[0]!, dec.labelAs "mutual") }
              | .ok is2 =>
                let serialised2 ←
                  serialiseIso exactBlock is2 exactTransform context.collectAdapterShadows
                if let some shadow := serialised2.adapterShadow? then
                  islandAdapterShadows := islandAdapterShadows.push shadow
                let records := serialised2.records
                let is2 := serialised2.model
                out := out ++ records
                rep := { rep with
                  generated := rep.generated.push (is.members[0]!, is2.decls.size) }
                pending := pending.push { spliced := is2.spliced }
                if generation.simple then
                  let st3 ← primCompose is2.members is2.levelParams
                    t.numParams reserved generation.basic serialised2.exactBlocks
                      (out, rep, pending, islandAdapterShadows) exactTransform
                      context.collectAdapterShadows
                  (out, rep, pending, islandAdapterShadows) ← pure st3
  -- Replay the source record between its pre-owner and post-owner generation
  -- phases.  An unreplayable source record terminates the complete machine and
  -- discards every private island, matching the historical loop return.
  -- Raw ordinals are an obligation only for the shadow emission ledger.  The
  -- ordinary full path historically accepts declaration records with no
  -- introduced names (notably an empty `.induct` record), and must not become
  -- stricter merely because the internal shadow mode shares this transition.
  let rawSourceOrdinal? ← if context.outputSourceOrder?.isSome then do
    let some firstSourceName := d.names.head?
      | throwError "shadow source declaration has no name"
    let some rawSourceOrdinal := rawOrdinals[firstSourceName]?
      | throwError "logical source declaration {firstSourceName} lost its raw ordinal"
    pure (some rawSourceOrdinal)
  else
    pure none
  let shadowedSource ← match rawSourceOrdinal? with
  | some rawSourceOrdinal => match futureSupportRemaining[rawSourceOrdinal]? with
    | some expected =>
      unless d == expected do
        throwError "future support source record {rawSourceOrdinal} changed before discharge"
      futureSupportRemaining := futureSupportRemaining.erase rawSourceOrdinal
      replayedOwnerEnv? := some (← getEnv)
      pure true
    | none => pure false
  | none => pure false
  unless shadowedSource do
    if let some dcl := toDeclaration (← getEnv) replayD then
      match (← getEnv).addDeclCore 0 dcl none false with
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
  if let some root := basisRoot? then
    match ← (validateBasisOwner root replayD).run with
    | .ok () =>
      if generation.modelsSimpleInput root then
        rep := { rep with
          exempt := rep.exempt.push (root, Decline.basisExempt.labelAs "prim") }
    | .error decline =>
      invalidBasis := invalidBasis.insert root
      rep := { rep with declined := rep.declined.push (root, decline.labelAs "prim") }
  -- Plain mutual and direct-simple routes read recursor metadata installed by
  -- the replay above and therefore remain the post-owner half of this single
  -- transition.
  if let .induct ts cs _ := replayD then
    if let t :: _ := ts then
      if generation.mutualModels && ts.length > 1 && !ts.any (·.numNested > 0) &&
          basisRoot?.isNone && invalidBasis.isEmpty then
        let all := ts.toArray.map (·.name)
        let ctors := all.map fun n =>
          (cs.filter (·.induct == n)).toArray.map fun c => (c.name, c.type)
        let tys := ts.toArray.map (·.type)
        let mut needsExactSortLift := hasIntrinsicProjectionFields constructionSyntax ts cs
        unless needsExactSortLift do
          for type in ts do
            if type.isKernelStructureLike cs && !(← isPropFormerType type.type) then
              needsExactSortLift := true
        if ← mutualReady needsExactSortLift reserved then
          let st3 ← genMutual all t.levelParams t.numParams tys ctors #[] reserved
            generation.simple generation.basic (out, rep, pending, islandAdapterShadows)
            (some replayD) exactTransform context.collectAdapterShadows
          (out, rep, pending, islandAdapterShadows) ← pure st3
        else
          let declined := rep.declined.push
            (t.name, "mutual model prerequisite occurs later in the input stream")
          rep := { rep with declined }
      if generation.modelsSimpleInput t.name && ts.length == 1 && t.numNested == 0 &&
          basisRoot?.isNone && invalidBasis.isEmpty then
        let ctors := (cs.filter (·.induct == t.name)).toArray.map fun c => (c.name, c.type)
        let (st, wait?) ← genPrim t.name t.levelParams t.numParams t.type ctors
          #[] reserved generation.basic true (out, rep, pending, islandAdapterShadows)
          (some (replayD, constructionNormalizer)) exactTransform true
          context.collectAdapterShadows
        match wait? with
        | none => (out, rep, pending, islandAdapterShadows) ← pure st
        | some _ =>
          let declined := rep.declined.push
            (t.name, "prim model prerequisite occurs later in the input stream")
          rep := { rep with declined }
  if d matches .induct .. then
    let generated := out
    let islandModels := pending
    let islandAliases ← match sourceAliases.registerRecords generated with
      | .ok aliases => pure aliases
      | .error message => throwError
        "cannot register generated source replay aliases for {d.names}: \
            {sourceAliases.exactMessage message}"
    if context.sharedPrefixPhaseB then
      -- The checker/support view is global across islands, unlike the local
      -- construction view above. Register the complete live island directly
      -- against that cumulative table so its build image remains injective
      -- with every prior generated declaration, including disposable ones.
      -- This table is never exposed to generation, readiness, or nameTaken.
      sharedPrefixAliases? := some (← match
          (sharedPrefixAliases?.getD context.sourceAliases).registerRecords generated with
        | .ok aliases => pure aliases
        | .error message => throwError
          "cannot retain cumulative generated replay aliases for {d.names}: \
            {islandAliases.exactMessage message}")
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
            islandAliases generation.typeCheckOutput with
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
      unless compactMode do
        if let some checker := kernelCheckState? then
          let mut checker := checker
          for localOrdinal in [:orderedGenerated.size] do
            checker ← checker.pushBound orderedGenerated[localOrdinal]!
              compact.summaries[localOrdinal]!.introduced
          kernelCheckState? := some checker
      modeledSourceFamilies := compact.sourceFamilies
      modeledSourceGlobalExtra? := compact.sourceGlobalExtra?
      if compactMode then
        let islandNumber := compactIslands.size
        let tagged := Order.tagIsland islandNumber compact.summaries
        let compact := { compact with summaries := tagged }
        for localOrdinal in [:tagged.size] do
          let row : CompactRecord := {
            summary := tagged[localOrdinal]!
            globalExtra := compact.globalExtras[localOrdinal]!
            families := compact.families[localOrdinal]!.map (·.inIsland islandNumber)
            checkIsland? := some islandNumber
            locator := .generated islandNumber localOrdinal }
          if let some checker := kernelCheckState? then
            let exact := orderedGenerated[localOrdinal]!
            if context.sharedPrefixPhaseB then
              let checkerAliases := sharedPrefixAliases?.getD islandAliases
              let build := checkerAliases.buildRecord exact
              unless checkerAliases.exactRecord build == exact do
                throwError "generated replay round trip changed {exact.names}"
              unless checkerAliases.exactDerivedRecord exact == exact do
                throwError "generated declaration {exact.names} contains a fresh build alias"
              let exactDisposition ← match KernelCheck.replayDisposition exact with
                | .ok disposition => pure disposition
                | .error message => throwError message
              let buildDisposition ← match KernelCheck.replayDisposition build with
                | .ok disposition => pure disposition
                | .error message => throwError (checkerAliases.exactMessage message)
              unless (exactDisposition matches .checked ..) ==
                    (buildDisposition matches .checked ..) &&
                  (exactDisposition matches .metaOnly) ==
                    (buildDisposition matches .metaOnly) &&
                  (exactDisposition matches .bundled) ==
                    (buildDisposition matches .bundled) do
                throwError "generated replay classification changed under aliases for \
                  {exact.names}"
              match exactDisposition with
              | .metaOnly =>
                -- Preserve the ordinary output checker's unsafe/partial skip
                -- semantics, but make the extra Meta visibility irrelevant to
                -- every later checked generated record.
                for name in exact.names do
                  sharedPrefixMetaOnlyNames := sharedPrefixMetaOnlyNames.insert name
              | .checked _ =>
                if let some dependency := (KernelCheck.inputReferences exact).toArray.find?
                    sharedPrefixMetaOnlyNames.contains then
                  throwError "checked generated record {exact.names} depends on unchecked \
                    construction-only declaration {dependency}"
              | .bundled =>
                -- Quot.mk/lift/ind have no independent replay step: the
                -- leading checked Quot record installs the exact bundle.
                pure ()
            kernelCheckState? := some (← if context.sharedPrefixPhaseB then
              checker.pushMappedBound exact
                ((sharedPrefixAliases?.getD islandAliases).buildRecord exact)
                row.summary.introduced
            else
              checker.pushBound exact row.summary.introduced)
            kernelCheckRows := kernelCheckRows.push row.summary.introduced
          compactRecords := compactRecords.push row
        compactIslands := compactIslands.push compact
      let persistentRecords := generatedSupportRecords orderedGenerated exactIslandModels
      if context.sharedPrefixPhaseB then
        constructionSupportRecords := constructionSupportRecords ++ persistentRecords
      if compactMode then
        let islandNumber := compactIslands.size - 1
        for record in persistentRecords do
          for name in record.names do
            persistentSupportOrigins := persistentSupportOrigins.insert name islandNumber
      persistentSyntax := ← match persistentSyntax.prependRecords persistentRecords with
        | .ok index => pure index
        | .error message => throwError
            "cannot index accepted persistent support for {d.names}: {message}"
      if retainOracle then legacyOut := legacyOut ++ orderedGenerated
      setEnv mainWithSupport
      if let some ownerDeclaration := toDeclaration mainWithSupport replayD then
        match mainWithSupport.addDeclCore 0 ownerDeclaration none false with
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
  unless compactMode do
    if let some checker := kernelCheckState? then
      kernelCheckState? := some (← checker.pushBound d sourceSummary.introduced)
  if retainOracle then legacyOut := legacyOut.push d
  if retainOracle && context.outputSourceOrder?.isSome then
    let some rawSourceOrdinal := rawSourceOrdinal?
      | throwError "shadow source declaration has no raw ordinal"
    emissionByRaw := emissionByRaw.insert rawSourceOrdinal
      (legacyOut.extract emissionStart legacyOut.size)
  if compactMode then
    let some firstName := d.names.head? | throwError "source declaration has no name"
    let some rawOrdinal := rawOrdinals[firstName]?
      | throwError "scheduled source declaration {firstName} lost its raw ordinal"
    let modeledIsland? ← if modeledSourceFamilies.isEmpty then pure none else
      match compactIslands.size with
      | 0 => throwError "modeled source family {d.names} has no committed generated island"
      | size + 1 => pure (some size)
    let row : CompactRecord := {
      summary := sourceSummaries[scheduledOrdinal]!
      globalExtra := modeledSourceGlobalExtra?.getD sourceGlobalExtra
      families := sourceFamilyRecord ++
        (modeledSourceFamilies.map fun family =>
          modeledIsland?.elim family family.inIsland)
      checkIsland? := modeledIsland?
      locator := .source rawOrdinal }
    if let some checker := kernelCheckState? then
      unless context.sharedPrefixPhaseB do
        kernelCheckState? := some (← checker.pushBound d row.summary.introduced)
        kernelCheckRows := kernelCheckRows.push row.summary.introduced
    compactRecords := compactRecords.push row
  if context.checkRecursors then
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
      scheduledOrdinal
      rawOrdinal
      sourceNames := d.names.toArray
      sourceIsInductive := d matches .induct ..
      sourceInstalled := replayD.names.all mainEnv.constants.contains
      generated := rep.generated.extract reportedBefore rep.generated.size
      generatedRecords := out.size }
  if context.collectAdapterShadows then
    adapterShadows := adapterShadows ++ islandAdapterShadows
  return .next {
    mainEnv, persistentSyntax, legacyOut, report := rep, compactIslands, compactRecords,
    scheduledOrdinal := scheduledOrdinal + 1, islandStatements, invalidBasis,
    persistentSupportOrigins, futureSupportRemaining, emissionByRaw, sourceSteps,
    kernelCheckState?, kernelCheckRows, adapterShadows,
    constructionSupportRecords, sharedPrefixAliases?, sharedPrefixMetaOnlyNames }

/-- Payload-free handoff from logical generation to compact finalization.  It
contains neither an `Environment`, `Kernel.Environment`, `EDecl`, sink, writer,
nor spool commit. The private constructor keeps that retention claim local to
the consuming seal below. -/
private structure CompactDirectSealed where
  report : Report
  compactIslands : Array CompactIsland
  compactRecords : Array CompactRecord
  islandStatements : Check.StatementReport
  persistentSupportOrigins : Std.HashMap Name Nat
  kernelVerdict : KernelCheck.Verdict
  constructionTransitions : Nat

/-- Consume the complete direct state at the last expression-bearing boundary.
Every exact record was already submitted through `pushBound`.  This function
binds the feed rows to the compact rows, seals away `Kernel.Environment`, and
resets Meta state to the invocation base before returning value-only data. -/
private def FilterState.sealCompactDirect (state : FilterState) (context : FilterContext) :
    MetaM CompactDirectSealed := do
  unless context.retention.checksKernelDirect do
    throwError "compact direct seal selected outside direct retention"
  unless state.futureSupportRemaining.isEmpty do
    throwError "future support shadow retained undischarged source records"
  unless state.legacyOut.isEmpty do
    throwError "compact direct checker retained {state.legacyOut.size} declaration records"
  unless state.scheduledOrdinal == context.sourceSummaries.size do
    throwError "compact direct source schedule consumed {state.scheduledOrdinal} of \
      {context.sourceSummaries.size} rows"
  let compactRows := state.compactRecords.map (·.summary.introduced)
  unless state.kernelCheckRows == compactRows do
    throwError "compact direct kernel rows differ from compact rows: \
      kernel={repr state.kernelCheckRows}, compact={repr compactRows}"
  let sourceRows := state.compactRecords.foldl (init := 0) fun count record =>
    match record.locator with
    | .source _ => count + 1
    | .generated .. => count
  unless sourceRows == state.scheduledOrdinal do
    throwError "compact direct retained {sourceRows} source rows for \
      {state.scheduledOrdinal} transitions"
  let some checker := state.kernelCheckState?
    | throwError "compact direct state lost its exact kernel checker"
  let kernelVerdict := checker.seal
  unless kernelVerdict.recordsPushed == state.compactRecords.size do
    throwError "compact direct kernel consumed {kernelVerdict.recordsPushed} records, \
      but retained {state.compactRecords.size} compact rows"
  let some base := context.kernelCheckBase?
    | throwError "compact direct state lost its exact base environment"
  -- No later compact operation may observe construction declarations. The
  -- returned structure cannot retain either this Lean environment or the
  -- checker's exact kernel environment.
  setEnv base
  return {
    report := state.report
    compactIslands := state.compactIslands
    compactRecords := state.compactRecords
    islandStatements := state.islandStatements
    persistentSupportOrigins := state.persistentSupportOrigins
    kernelVerdict
    constructionTransitions := context.constructionTransitions }

/-- Finish ordering and structural checks from the value-only direct handoff. -/
private def CompactDirectSealed.finalize (sealed : CompactDirectSealed) :
    MetaM (Report × CompactPlan × CompactKernelCheckVerdict) := do
  let compactOrder ← match Order.summaryRecordOrder (sealed.compactRecords.map (·.summary)) with
    | .ok order => pure order
    | .error error => throwError "cannot compactly order direct records: {repr error}"
  let mut scheduled : Std.HashSet Nat := {}
  for index in compactOrder do
    unless index < sealed.compactRecords.size do
      throwError "compact direct schedule index {index} exceeds \
        {sealed.compactRecords.size} rows"
    if scheduled.contains index then
      throwError "compact direct schedule repeats row {index}"
    scheduled := scheduled.insert index
  unless scheduled.size == sealed.compactRecords.size do
    throwError "compact direct schedule covers {scheduled.size} of \
      {sealed.compactRecords.size} rows"
  let orderedRecords := compactOrder.map fun i =>
    { owner := sealed.compactRecords[i]!.summary.owner
      modelSlots := sealed.compactRecords[i]!.summary.modelSlots
      globalExtra := sealed.compactRecords[i]!.globalExtra
      families := sealed.compactRecords[i]!.families : Check.CompactCheckRecord }
  let compactCheckReport ← match Check.compactOrderedReport orderedRecords with
    | .ok report => pure report
    | .error message => throwError "invalid compact direct output certificate: {message}"
  let compactUnavailable? :=
    compactAvailabilityError? sealed.compactRecords sealed.persistentSupportOrigins
  let orderedGlobals := compactOrder.map fun i => sealed.compactRecords[i]!.globalExtra
  let diagnosticOwners := sealed.compactIslands.foldl (init := ({} : Std.HashSet Name))
    fun owners island => island.diagnosticOwners.toArray.foldl
      (fun owners owner => owners.insert owner) owners
  let compactGlobal := Check.globalExtrasFromRecordsFor orderedGlobals diagnosticOwners
  let statementReport : Check.StatementReport :=
    { sealed.islandStatements with
      violations := sealed.islandStatements.violations ++ compactGlobal }
  let rep := { sealed.report with
    stmtChecked := statementReport.statementsChecked
    stmtErrors := statementReport.violations.map fun violation => violation.message }
  let declarations := compactOrder.map fun index => sealed.compactRecords[index]!.locator
  unless declarations.size == sealed.kernelVerdict.recordsPushed do
    throwError "compact direct final schedule has {declarations.size} rows after checking \
      {sealed.kernelVerdict.recordsPushed} exact records"
  let compactPlan : CompactPlan := {
    declarations
    checkReport := compactCheckReport
    unavailable? := compactUnavailable?
    retainedGeneratedRecords := 0 }
  let (deferredResult, kernelFallback?) := match sealed.kernelVerdict.result with
    | .ok () => (.ok (), compactUnavailable?)
    | .error _ =>
      let fallback := compactUnavailable?.getD
        "direct kernel rejection requires the final reordered batch diagnostic"
      (.error fallback, some fallback)
  let kernelVerdict : CompactKernelCheckVerdict := {
    result := deferredResult
    recordsPushed := sealed.kernelVerdict.recordsPushed
    scheduledRecords := declarations.size
    constructionTransitions := sealed.constructionTransitions
    fallback? := kernelFallback? }
  return (rep, compactPlan, kernelVerdict)

/-- Complete compact ordering and checking after the logical source stream has
been exhausted.  No source `EDecl` is consumed here. -/
private def FilterState.finalize (state : FilterState) (context : FilterContext) :
    MetaM (Array EDecl × Report × CompactPlan × Option FilterKernelCheckShadow) := do
  let x := context.source
  let retention := context.retention
  let compactMode := retention.isCompact
  let retainOracle := retention.retainsOracle
  let sourceSyntax := context.sourceSyntax
  let reserved := context.reserved
  let legacyOut ← match context.outputSourceOrder? with
    | none => pure state.legacyOut
    | some order => do
      let mut reordered : Array EDecl := #[]
      for rawOrdinal in order do
        let some records := state.emissionByRaw[rawOrdinal]?
          | throwError "source emission order lost raw record {rawOrdinal}"
        reordered := reordered ++ records
      pure reordered
  let compactIslands := state.compactIslands
  let compactRecords := state.compactRecords
  let islandStatements := state.islandStatements
  let persistentSupportOrigins := state.persistentSupportOrigins
  unless state.futureSupportRemaining.isEmpty do
    throwError "future support shadow retained undischarged source records"
  let mut rep := state.report
  let compactOrder := if compactMode then Array.range compactRecords.size else #[]
  let compactCheckReport : Check.Report ← if compactMode then
      let orderedRecords := compactOrder.map fun i =>
        { owner := compactRecords[i]!.summary.owner
          modelSlots := compactRecords[i]!.summary.modelSlots
          globalExtra := compactRecords[i]!.globalExtra
          families := compactRecords[i]!.families : Check.CompactCheckRecord }
      match Check.compactSourceReport orderedRecords with
      | .ok report => pure report
      | .error message => throwError "invalid compact output certificate: {message}"
    else
      pure ({ familiesChecked := 0, violations := #[] } : Check.Report)
  let compactUnavailable? : Option String := none
  let compactStatementReport := if compactMode then
    let orderedGlobals := compactOrder.map fun i => compactRecords[i]!.globalExtra
    let diagnosticOwners := compactIslands.foldl (init := ({} : Std.HashSet Name))
      fun owners island => island.diagnosticOwners.toArray.foldl
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
      if compactMode then
        let fullOrder ← match Order.recordOrder finalExport with
          | .ok order => pure order
          | .error error => throwError "full oracle cannot order compact records: {repr error}"
        let compactNames := compactOrder.map fun i => compactRecords[i]!.summary.introduced
        let fullNames := fullOrder.map fun i => finalExport.decls[i]!.names.toArray
        unless compactNames == fullNames do
          throwError "compact order disagrees with full export: \
            compact={repr compactNames}, full={repr fullNames}"
        unless compactStatementReport == fullReport do
          throwError "compact statements disagree with full export: \
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
  unless retainOracle || legacyOut.isEmpty do
    throwError "compact filter retained {legacyOut.size} cumulative declaration records"
  let declarations := compactOrder.map fun index => compactRecords[index]!.locator
  let compactPlan : CompactPlan := {
    declarations
    checkReport := compactCheckReport
    unavailable? := compactUnavailable?
    retainedGeneratedRecords := legacyOut.foldl (fun count declaration =>
      if declaration.names.any fun name => !reserved.contains name then count + 1 else count) 0 }
  let kernelCheckShadow? ← match state.kernelCheckState? with
    | none => pure none
    | some checker => do
      let streamed := checker.seal
      unless streamed.recordsPushed == legacyOut.size do
        throwError "kernel-check shadow consumed {streamed.recordsPushed} records, \
          but the final full oracle retained {legacyOut.size}"
      let finalExport := { x with decls := legacyOut }
      let orderedExport ← match Order.reorder finalExport with
        | .ok ordered => pure ordered
        | .error error => throwError "kernel-check full oracle cannot order final export: {repr error}"
      let saved ← getEnv
      let some kernelCheckBase := context.kernelCheckBase?
        | throwError "kernel-check shadow lost its exact base environment"
      let batchResult ← try
        setEnv kernelCheckBase
        typeCheckExport orderedExport
      finally
        setEnv saved
      pure (some {
        streamedResult := streamed.result
        batchResult
        recordsPushed := streamed.recordsPushed
        finalRecords := orderedExport.decls.size
        usedFallback := !sameKernelCheckResult streamed.result batchResult })
  return (legacyOut, rep, compactPlan, kernelCheckShadow?)

/-- Shared generation loop. Compact modes summarize every accepted island at
its close boundary; oracle mode retains the historical full declaration array
for actual output and exact A/B comparison. -/
private def runFilterCore (x : Export) (checkRecursors : Bool) (generation : Cli.Config)
    (retention : RetentionMode)
    (exactTransform : EDecl → EDecl := id) (collectTrace : Bool := false)
    (plannedSource? : Option Spool.PlannedSourceReader := none)
    (sourceOrder? : Option (Array Nat) := none)
    (futureSupport? : Option FutureSourceSupport := none)
    (outputSourceOrder? : Option (Array Nat) := none)
    (sourceCensus? : Option SourceCensus := none)
    (kernelCheckShadow : Bool := false)
    (collectAdapterShadows : Bool := false) :
    MetaM (Array EDecl × Report × CompactPlan × Array FilterSourceStep ×
      Option FilterKernelCheckShadow × Option CompactKernelCheckVerdict ×
      Array FamilyAdapter.ShadowObservation) := do
  let plannedCensus := sourceCensus?.isSome
  let sourceCensus := sourceCensus?.getD (SourceCensus.ofSource x)
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
  let sourceOrder ← match sourceOrder? with
    | some order => pure order
    | none => pure (Array.range sourceCensus.summaries.size)
  let scheduled := if plannedCensus then x else
    { x with decls := sourceOrder.map fun ordinal => x.decls[ordinal]! }
  -- Source records are consumed in their original stream order. A model
  -- owner whose fixed support occurs later declines at that owner; the normal
  -- route never moves input declarations or preinstalls future support.
  let fallbackEnv ← getEnv
  let mainEnv := futureSupport?.map (·.env) |>.getD fallbackEnv
  -- Reuse the immutable census products. Retained sources may still supply
  -- whole-export row caches; planned sources derive missing rows from each
  -- transient declaration at its logical transition.
  let sourceSyntax := sourceCensus.sourceSyntax
  let constructionSyntax ← if sourceAliases.isEmpty then pure sourceSyntax else do
    if plannedCensus then
      let some reader := plannedSource?
        | throwError "planned source census has no declaration reader"
      let mut index := sourceSyntax
      for ordinal in [:sourceCensus.summaries.size] do
        let declaration ← match ← reader.read ordinal with
          | .ok declaration => pure declaration
          | .error message =>
            throwError "cannot decode planned source record {ordinal}: {message}"
        if sourceRecordUsesAliases sourceAliases sourceCensus.summaries[ordinal]! declaration then
          match index.withReplayRecords #[declaration]
              #[sourceAliases.buildRecord declaration] with
          | .ok next => index := next
          | .error message =>
            throwError "cannot index collision-safe source replay: {message}"
      pure index
    else
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
  let sourceSummaries ← match sourceCensus.summariesForOrder sourceOrder with
    | .ok summaries => pure summaries
    | .error error => throwError "cannot rebind frozen source summaries: {error}"
  let sourceGlobalExtras? := if plannedCensus then none else
    some (Check.globalExtraRecordsWithIndex sourceSyntax scheduled.decls)
  let sourceFamilyRecords? := if plannedCensus then none else
    some (sourceCensus.familyCertificateRecords x scheduled)
  let rawOrdinals := sourceCensus.rawOrdinals
  let reserved := sourceCensus.reserved
  let sourceConstructionTouches := sourceOrder.map fun rawOrdinal =>
    sourceCensus.scheduling[rawOrdinal]!.constructionTouch generation
  let constructionCutoffEnabled :=
    retention.checksKernelDirect && !checkRecursors && !collectTrace &&
      !collectAdapterShadows && futureSupport?.isNone
  let constructionTransitions := if constructionCutoffEnabled then Id.run do
      let mut cutoff := 0
      for ordinal in [:sourceConstructionTouches.size] do
        if sourceConstructionTouches[ordinal]! then cutoff := ordinal + 1
      return cutoff
    else sourceOrder.size
  let constructionReserved := reserved.fold (init := reserved) fun names name =>
    (sourceAliases.buildDerivedNames name).foldl (fun names build => names.insert build) names
  let context : FilterContext := {
    source := x, checkRecursors, generation, retention, exactTransform,
    sourceSyntax, constructionSyntax, constructionNormalizer, sourceAliases,
    sourceSummaries, sourceConstructionTouches, constructionTransitions,
    sourceGlobalExtras?, sourceFamilyRecords?,
    rawOrdinals, reserved, constructionReserved,
    kernelCheckBase? := if kernelCheckShadow || retention.checksKernelDirect then
      some fallbackEnv else none,
    futureSupport?, outputSourceOrder?, collectTrace, collectAdapterShadows }
  let initialFutureSupport := futureSupport?.map (·.records) |>.getD
    ({} : Std.HashMap Nat EDecl)
  let mut state : FilterState :=
    { mainEnv := mainEnv
      persistentSyntax := sourceSyntax
      futureSupportRemaining := initialFutureSupport
      kernelCheckState? := if kernelCheckShadow || retention.checksKernelDirect then
        some (KernelCheck.State.create fallbackEnv) else none }
  if retention.checksKernelDirect && constructionTransitions == 0 then
    state := { state with mainEnv := fallbackEnv }
    setEnv fallbackEnv
  for rawOrdinal in sourceOrder do
    let declaration ← match plannedSource? with
      | none => match x.decls[rawOrdinal]? with
        | some oracle => pure oracle
        | none => throwError "source record {rawOrdinal} has neither retained nor planned payload"
      | some reader => do
        match ← reader.read rawOrdinal with
        | .error error => throwError "cannot decode planned source record {rawOrdinal}: {error}"
        | .ok declaration =>
          if let some oracle := x.decls[rawOrdinal]? then
            unless declaration == oracle do
              throwError "planned source record {rawOrdinal} differs from the validated parse"
          pure declaration
    -- A `return` from a `for` loop preserves its mutable loop state. Move the
    -- real state out first so that `feedSource` owns its accumulated arrays;
    -- the placeholder is observed only by the loop machinery on an early
    -- return and is never part of the public result.
    let current := state
    state := { mainEnv, persistentSyntax := sourceSyntax }
    let feedResult ← if retention.checksKernelDirect &&
        current.scheduledOrdinal >= constructionTransitions then
      pure (.next (← current.feedSourceExactTail context declaration))
    else
      current.feedSource context declaration
    match feedResult with
    | .next next =>
      if retention.checksKernelDirect &&
          next.scheduledOrdinal == constructionTransitions then
        state := { next with mainEnv := fallbackEnv }
        setEnv fallbackEnv
      else
        state := next
    | .unreplayable report sourceSteps =>
      if retention.checksKernelDirect then
        let some base := context.kernelCheckBase?
          | throwError "unreplayable compact direct state lost its exact base environment"
        setEnv base
        return (#[], report, {}, sourceSteps, none, none, #[])
      return (x.decls, report, {}, sourceSteps, none, none, #[])
  if retention.checksKernelDirect then
    let sourceSteps := state.sourceSteps
    let some base := context.kernelCheckBase?
      | throwError "compact direct finalization lost its exact base environment"
    let sealed ← try
      state.sealCompactDirect context
    finally
      -- Validation errors must not strand construction declarations in the
      -- caller's Meta state either.
      setEnv base
    let (report, compact, kernelVerdict) ← sealed.finalize
    return (#[], report, compact, sourceSteps, none, some kernelVerdict, #[])
  let (decls, report, compact, kernelCheckShadow?) ← state.finalize context
  return (decls, report, compact, state.sourceSteps, kernelCheckShadow?, none,
    state.adapterShadows)

/-- **The filter.** -/
def runFilter (x : Export) (checkRecursors : Bool) (generation : Cli.Config) :
    MetaM (Array EDecl × Report) := do
  let (decls, report, _, _, _, _, _) ←
    runFilterCore x checkRecursors generation .fullOracle
  return (decls, report)

/-- Test-facing observer for generic family-adapter shadow validation. The
ordinary filter still derives and validates every plan, but retains none of
these compact observations and emits no trace or log output. -/
def runFilterWithFamilyAdapterShadow (x : Export) (checkRecursors : Bool)
    (generation : Cli.Config) :
    MetaM (Array EDecl × Report × Array FamilyAdapter.ShadowObservation) := do
  let (decls, report, _, _, _, _, shadows) ← runFilterCore x checkRecursors generation
    .fullOracle (collectAdapterShadows := true)
  return (decls, report, shadows)

/-- Test-facing full-output oracle with an exact declaration-wise kernel
shadow.  The ordinary filter and CLI do not select this path.  Each completed
transition feeds exact generated values and the exact source value; final
comparison uses the batch checker over the reordered full export and preserves
its result on any mismatch. An ordinary unreplayable source result has no final
stream to seal, so it returns its unchanged output/report with `none`. -/
def runFilterWithKernelCheckShadow (x : Export) (checkRecursors : Bool)
    (generation : Cli.Config) :
    MetaM (Array EDecl × Report × Option FilterKernelCheckShadow) := do
  let (decls, report, _, _, shadow?, _, _) ← runFilterCore x checkRecursors generation
    .fullOracle (kernelCheckShadow := true)
  return (decls, report, shadow?)

/-- Internal phase-one A/B path for replacing support-priority execution.
Only a complete exact [`FutureSourceSupport`] ledger selects it; every
unsupported or malformed source shape runs the historical scheduler unchanged.
Logical processing uses ordinary dependency order, while the returned export
is put through the existing stable support-priority order so this phase changes
neither bytes nor report ordering. -/
def runFilterWithFutureSourceSupportShadow (x : Export) (checkRecursors : Bool)
    (generation : Cli.Config) : MetaM (Array EDecl × Report × Bool) := do
  -- The shadow ledger and output reconstruction are intentionally keyed by a
  -- declaration's first introduced name.  Nameless records are valid on the
  -- historical path, so they make this phase-one optimization unavailable
  -- rather than becoming a new input restriction after another record selects
  -- future support.
  if x.decls.any (·.names.isEmpty) then
    let (decls, report) ← runFilter x checkRecursors generation
    return (decls, report, false)
  let census := SourceCensus.ofSource x
  let aliases ← match census.replayAliases with
    | .ok aliases => pure aliases
    | .error message => throwError "cannot plan collision-safe source replay: {message}"
  unless aliases.isEmpty do
    -- The phase-one shadow preinstalls exact future source declarations, so
    -- it cannot share the collision-safe replay view yet.  Fall back before
    -- certification mutates any environment; the ordinary path is alias-aware.
    let (decls, report) ← runFilter x checkRecursors generation
    return (decls, report, false)
  unless sourceNeedsSupportScheduling x generation census.reserved do
    let (decls, report) ← runFilter x checkRecursors generation
    return (decls, report, false)
  let base ← getEnv
  let shadowResult ← try
    FutureSourceSupport.create base x generation
  finally
    -- Certification temporarily installs the exact future source bundle in
    -- Meta state.  No ordering or fallback failure may expose that private
    -- environment to the caller.
    setEnv base
  let .ok shadow := shadowResult | do
    let (decls, report) ← runFilter x checkRecursors generation
    return (decls, report, false)
  unless !shadow.records.isEmpty do
    let (decls, report) ← runFilter x checkRecursors generation
    return (decls, report, false)
  let ordinaryOrder ← match Order.summaryRecordOrder census.summaries with
    | .ok order => pure order
    | .error error => throwError "cannot ordinarily order source shadow: {repr error}"
  let outputOrder ← match census.scheduleOrder x generation with
    | .ok order => pure order
    | .error error => throwError "cannot retain support-priority output order: {repr error}"
  let (decls, report, _, _, _, _, _) ←
    runFilterCore x checkRecursors generation .fullOracle
    (sourceOrder? := some ordinaryOrder) (futureSupport? := some shadow)
      (outputSourceOrder? := some outputOrder)
  return (decls, report, true)

/-- Test-facing observer for the declaration-wise transition.  The generated
output and report are produced by the same core invocation as the snapshots;
ordinary production callers collect no snapshots. -/
def runFilterWithSourceTrace (x : Export) (checkRecursors : Bool)
    (generation : Cli.Config) : MetaM (Array EDecl × Report × Array FilterSourceStep) := do
  let (decls, report, _, steps, _, _, _) ←
    runFilterCore x checkRecursors generation .fullOracle (collectTrace := true)
  return (decls, report, steps)

/-- Focused exact-syntax regression seam. The transform is applied only to
freshly serialized generated inductive records, before their immediate
composed consumer sees them; ordinary production callers use [`runFilter`]. -/
def runFilterWithExactBlockTransform (x : Export) (checkRecursors : Bool)
    (generation : Cli.Config) (transform : EDecl → EDecl) :
    MetaM (Array EDecl × Report) := do
  let (decls, report, _, _, _, _, _) ←
    runFilterCore x checkRecursors generation .fullOracle transform
  return (decls, report)

/-- Direct compact kernel path used by generated no-output checking. Exact
generated and source records are consumed only while their compact rows are
live; the returned report, plan, and optional deferred verdict contain no
declaration, environment, writer, sink, or spool payload. An unreplayable
source encountered while construction is live terminates like the ordinary
filter and returns `none`. A rejection in the exact-only tail returns a
deferred fallback so the ordinary replay can recover its generation report and
diagnostic without keeping construction state alive speculatively. -/
def runFilterDirectChecking (x : Export) (checkRecursors : Bool)
    (generation : Cli.Config) :
    MetaM (Report × CompactPlan × Option CompactKernelCheckVerdict) := do
  let (_, report, compact, _, _, kernelVerdict?, _) ←
    runFilterCore x checkRecursors generation .compactDirect
  return (report, compact, kernelVerdict?)

/-- Value-only test observation for the complete two-phase shared-prefix
prototype. `selected` means Phase B consumed the private source snapshots;
otherwise the returned filter result came from the ordinary direct fallback. -/
structure SharedPrefixDirectObservation where
  selected : Bool
  source : SharedPrefixSourceObservation
  retainedSupportRecords : Nat := 0
  ownerSnapshotsConsumed : Nat := 0
  pendingOwnerSnapshotsAtSeal : Nat := 0
  fallback? : Option String := none
  deriving Inhabited, Repr, BEq

private def installSharedPrefixSupport (base : Environment)
    (records : Array EDecl) (aliases : SourceReplayAliases) :
    MetaM (Except String Environment) :=
  -- `records` is exactly the witnessed persistent subset selected at island
  -- close. Every member already passed the exact/build classification and
  -- no-leak audits before entering the Phase-B state.
  checkGeneratedIn base (records.map aliases.buildRecord)

/-- Release the preceding owner's construction environment before rebuilding
the witnessed support view over the next historical source snapshot. -/
private def prepareSharedPrefixOwnerState (state : FilterState) (base : Environment)
    (snapshot : SharedPrefixOwnerSnapshot) (aliases : SourceReplayAliases) :
    MetaM (FilterState × Environment) := do
  let state := { state with mainEnv := base }
  -- `feedSource` also installed the preceding owner in the ambient Meta state.
  -- Drop that independent root before rebuilding support over the next
  -- historical snapshot, not merely before the following feed.
  setEnv base
  let installed ← match ← installSharedPrefixSupport snapshot.env
      state.constructionSupportRecords aliases with
    | .ok env => pure env
    | .error message => throwError "cannot replay witnessed construction support: {message}"
  return (state, installed)

/-- Consume the dynamic Phase-B state into one historical owner transition.
Keeping this call boundary linear lets the RC compiler pass the sole
`FilterState` reference to `feedSource`; in particular, its staged arrays do
not acquire a copy-on-write sibling while generation appends to them. -/
private def feedSharedPrefixOwner (state : FilterState) (context : FilterContext)
    (installed : Environment) (snapshot : SharedPrefixOwnerSnapshot)
    (declaration : EDecl) : MetaM (FilterState × Array CompactRecord) := do
  unless state.compactRecords.isEmpty && state.kernelCheckRows.isEmpty do
    throwError "shared-prefix owner transition retained rows from an earlier owner"
  setEnv installed
  match ← ({ state with
      mainEnv := installed
      scheduledOrdinal := snapshot.scheduledOrdinal }).feedSource context declaration with
  | .unreplayable report _ =>
    throwError "shared-prefix owner replay became unreplayable: {report.unreplayable}"
  | .next next =>
    let chunk := next.compactRecords
    unless chunk.any fun row => row.locator == .source snapshot.rawOrdinal do
      throwError "shared-prefix owner transition lost source row {snapshot.rawOrdinal}"
    -- The historical row array is owned by `chunks`; it is not also carried
    -- through the next mutating owner transition. The checker itself retains
    -- its cumulative kernel state, while final name rows are rebuilt below.
    return ({ next with compactRecords := #[], kernelCheckRows := #[] }, chunk)

private def runSharedPrefixPhaseB (prepared : SharedPrefixSourcePrepared)
    (failAfterOwners? : Option Nat := none) :
    MetaM (Report × CompactPlan × Option CompactKernelCheckVerdict × Nat × Nat × Nat) := do
  let ⟨_, completedEnv, snapshots, sourceRows, context, aliases, metaOnlyNames,
    sourceAccess⟩ := prepared
  let mut chunks := sourceRows.map fun row => #[row]
  let some base := context.kernelCheckBase?
    | throwError "shared-prefix source preparation lost its invocation base"
  let mut state : FilterState := {
    mainEnv := base
    persistentSyntax := context.sourceSyntax
    kernelCheckState? := some
      (KernelCheck.State.createCheckedPrefix completedEnv
        (sourceRows.map (·.summary.introduced)))
    sharedPrefixAliases? := some aliases
    sharedPrefixMetaOnlyNames := metaOnlyNames }
  -- Reverse once, then remove each root before running its transition.  The
  -- original array is consumed by this function, so at most the unvisited
  -- shared prefixes plus the current snapshot remain rooted during Phase B.
  let snapshotCount := snapshots.size
  let mut pendingSnapshots := snapshots.reverse
  let mut ownerSnapshotsConsumed := 0
  for _ in [:snapshotCount] do
    let some snapshot := pendingSnapshots.back?
      | throwError "shared-prefix owner snapshot stack ended early"
    pendingSnapshots := pendingSnapshots.pop
    ownerSnapshotsConsumed := ownerSnapshotsConsumed + 1
    let aliases := state.sharedPrefixAliases?.getD aliases
    let (withoutPriorOwner, installed) ←
      prepareSharedPrefixOwnerState state base snapshot aliases
    let declaration ← match ← sourceAccess.read snapshot.rawOrdinal with
      | .ok declaration => pure declaration
      | .error message => throwError
        "cannot reread shared-prefix owner {snapshot.rawOrdinal}: {message}"
    let (next, chunk) ←
      feedSharedPrefixOwner withoutPriorOwner context installed snapshot declaration
    chunks := chunks.set! snapshot.scheduledOrdinal chunk
    state := next
    if failAfterOwners? == some ownerSnapshotsConsumed then
      throwError "injected shared-prefix failure after owner {ownerSnapshotsConsumed}"
  unless pendingSnapshots.isEmpty do
    throwError "shared-prefix owner snapshot stack retained unconsumed roots"
  -- The last owner has no following preparation call to clear the ambient
  -- Meta root. Release it before assembling the value-only compact result.
  setEnv base
  let mut compactRecords : Array CompactRecord := #[]
  for chunk in chunks do compactRecords := compactRecords ++ chunk
  let kernelCheckRows := compactRecords.map (·.summary.introduced)
  let retainedSupportRecords := state.constructionSupportRecords.size
  state := { state with
    mainEnv := base
    compactRecords
    scheduledOrdinal := sourceRows.size
    kernelCheckRows }
  let sealed ← try
    state.sealCompactDirect context
  finally
    setEnv base
  let (report, compact, verdict) ← sealed.finalize
  return (report, compact, some verdict, retainedSupportRecords,
    ownerSnapshotsConsumed, pendingSnapshots.size)

/-- Opt-in test-facing two-phase direct path. Phase A owns one checked source
build image plus structurally shared pre-owner snapshots; Phase B buffers no
non-support generated record across owner transitions. Any unavailable audit
or prototype invariant restores the base and returns the authoritative current
direct implementation instead. `failAfterOwners?` is a regression-only fault
injection for fallback-state parity. Main never selects this observer. -/
def runFilterDirectCheckingSharedPrefix (x : Export) (generation : Cli.Config)
    (failAfterOwners? : Option Nat := none) :
    MetaM ((Report × CompactPlan × Option CompactKernelCheckVerdict) ×
      SharedPrefixDirectObservation) := do
  let base ← getEnv
  let levelCallsBefore ← LevelAlgebra.levelCalls.get
  let levelEscapesBefore ← LevelAlgebra.levelEscapes.get
  let restoreLevelCounters : MetaM Unit := do
    LevelAlgebra.levelCalls.set levelCallsBefore
    LevelAlgebra.levelEscapes.set levelEscapesBefore
  let preparation : Except String SharedPrefixSourcePrepared ← try
    prepareSharedPrefixSource x generation
  catch error =>
    pure (.error (← error.toMessageData.toString))
  finally
    setEnv base
  let .ok prepared := preparation | do
    let .error message := preparation | unreachable!
    restoreLevelCounters
    let result ← runFilterDirectChecking x false generation
    return (result, {
      selected := false
      source := {
        sourceRecords := x.decls.size
        ownerSnapshots := 0
        metaOnlyRecords := 0
        constructionTransitions := 0
        fallback? := some message }
      fallback? := some message })
  let sourceObservation := prepared.observation
  let phase : Except String
      (Report × CompactPlan × Option CompactKernelCheckVerdict × Nat × Nat × Nat) ← try
    pure (Except.ok (← runSharedPrefixPhaseB prepared failAfterOwners?))
  catch error =>
    pure (Except.error (← error.toMessageData.toString))
  match phase with
  | Except.ok (report, compact, verdict?, retainedSupportRecords,
      ownerSnapshotsConsumed, pendingOwnerSnapshotsAtSeal) =>
    return ((report, compact, verdict?), {
      selected := true
      source := sourceObservation
      retainedSupportRecords
      ownerSnapshotsConsumed
      pendingOwnerSnapshotsAtSeal })
  | Except.error message =>
    setEnv base
    restoreLevelCounters
    let result ← runFilterDirectChecking x false generation
    return (result, {
      selected := false
      source := sourceObservation
      fallback? := some message })

/-- AST-dropping no-output generation. Accepted generated records are checked
and summarized at island close, then discarded without opening a workspace or
retaining any physical span. -/
def runFilterDiscarding (x : Export) (checkRecursors : Bool) (generation : Cli.Config) :
    MetaM (Report × CompactPlan) := do
  let (_, report, compact, _, _, _, _) ←
    runFilterCore x checkRecursors generation .compactDiscard
  return (report, compact)

/-- Phase-three declaration-span driver.  The complete parsed export remains
the validation/census oracle in this tranche; each separately decoded source
record is nevertheless the value consumed by `feedSource`, and compact mode
does not retain it after that transition. -/
def runFilterDiscardingPlanned (x : Export) (reader : Spool.PlannedSourceReader)
    (checkRecursors : Bool) (generation : Cli.Config) : MetaM (Report × CompactPlan) := do
  let (_, report, compact, _, _, _, _) ←
    runFilterCore x checkRecursors generation .compactDiscard (plannedSource? := some reader)
  return (report, compact)

private def validatePlannedSource (input : PlannedSourceInput)
    (reader : Spool.PlannedSourceReader) : IO (Except String Unit) := do
  unless ← reader.matchesSource input.provenance do
    return .error "planned source census and reader have different raw provenance"
  unless input.envelope.retainedDeclarations == 0 do
    return .error "planned source parser retained complete declaration values"
  unless input.envelope.declarationCount == input.census.summaries.size &&
      input.envelope.declarationCount == input.census.scheduling.size &&
      input.envelope.declarationCount == reader.size do
    return .error "planned source parser/census/reader cardinalities disagree"
  return .ok ()

/-- Reproduce the ordinary whole-source structural report from the frozen
syntax index and one transient declaration value at a time. The retained rows
contain names and compact certificates only. -/
def checkPlannedSource (input : PlannedSourceInput)
    (reader : Spool.PlannedSourceReader) : IO (Except String Check.Report) := do
  if let .error message ← validatePlannedSource input reader then
    return .error message
  let template := input.envelope.template
  let index := input.census.sourceSyntax
  let mut records : Array Check.CompactCheckRecord := #[]
  for ordinal in [:reader.size] do
    let declaration ← match ← reader.read ordinal with
      | .ok declaration => pure declaration
      | .error message => return .error message
    let families := index.sourceFamilyCertificatesForRecord template declaration
    let globalExtra := (Check.globalExtraRecordsWithIndex index #[declaration])[0]!
    records := records.push {
      owner := match declaration with
        | .induct (type :: _) _ _ => some type.name
        | _ => none
      modelSlots := families.flatMap (·.publicNames)
      globalExtra
      families }
  return Check.compactSourceReport records

/-- Materialize the exact parsed source only for a compatibility fallback.
The ordinary successful compact-direct route never calls this function. -/
def materializePlannedSource (input : PlannedSourceInput)
    (reader : Spool.PlannedSourceReader) : IO (Except String Export) := do
  if let .error message ← validatePlannedSource input reader then
    return .error message
  let mut declarations : Array EDecl := #[]
  for ordinal in [:reader.size] do
    match ← reader.read ordinal with
    | .error message => return .error message
    | .ok declaration => declarations := declarations.push declaration
  return .ok { input.envelope.template with decls := declarations }

/-- Declaration-discarding compact-direct checker. Exact source values are
decoded into the kernel environment only while their feed transition is live;
the construction environment receives only the prefix through its last
possible consumer. No generated logical output is serialized. -/
def runFilterDirectCheckingPlannedCensus (input : PlannedSourceInput)
    (reader : Spool.PlannedSourceReader) (checkRecursors : Bool)
    (generation : Cli.Config) :
    MetaM (Report × CompactPlan × Option CompactKernelCheckVerdict) := do
  if let .error message ← validatePlannedSource input reader then
    throwError message
  let (_, report, compact, _, _, kernelVerdict?, _) ←
    runFilterCore input.envelope.template checkRecursors generation .compactDirect
      (plannedSource? := some reader) (sourceCensus? := some input.census)
  return (report, compact, kernelVerdict?)

/-- Planned-census counterpart of [`runFilterDirectCheckingSharedPrefix`].
Phase A reads each scheduled source declaration once from the completed arena,
and Phase B rereads only captured owner ordinals. The retained template has no
declarations; unavailability reruns the existing authoritative planned direct
path rather than materializing an `Export`. Main selects this seam only for
eligible generated `--no-output --type-check-output` invocations. -/
def runFilterDirectCheckingSharedPrefixPlannedCensus (input : PlannedSourceInput)
    (reader : Spool.PlannedSourceReader) (generation : Cli.Config)
    (failAfterOwners? : Option Nat := none) :
    MetaM ((Report × CompactPlan × Option CompactKernelCheckVerdict) ×
      SharedPrefixDirectObservation) := do
  if let .error message ← validatePlannedSource input reader then
    throwError message
  let base ← getEnv
  let levelCallsBefore ← LevelAlgebra.levelCalls.get
  let levelEscapesBefore ← LevelAlgebra.levelEscapes.get
  let restoreLevelCounters : MetaM Unit := do
    LevelAlgebra.levelCalls.set levelCallsBefore
    LevelAlgebra.levelEscapes.set levelEscapesBefore
  let preparation : Except String SharedPrefixSourcePrepared ← try
    prepareSharedPrefixSourceCore input.envelope.template input.census
      (.planned reader) generation
  catch error =>
    pure (.error (← error.toMessageData.toString))
  finally
    setEnv base
  let .ok prepared := preparation | do
    let .error message := preparation | unreachable!
    restoreLevelCounters
    let result ← runFilterDirectCheckingPlannedCensus input reader false generation
    return (result, {
      selected := false
      source := {
        sourceRecords := input.envelope.declarationCount
        ownerSnapshots := 0
        metaOnlyRecords := 0
        constructionTransitions := 0
        fallback? := some message }
      fallback? := some message })
  let sourceObservation := prepared.observation
  let phase : Except String
      (Report × CompactPlan × Option CompactKernelCheckVerdict × Nat × Nat × Nat) ← try
    pure (Except.ok (← runSharedPrefixPhaseB prepared failAfterOwners?))
  catch error =>
    pure (Except.error (← error.toMessageData.toString))
  match phase with
  | Except.ok (report, compact, verdict?, retainedSupportRecords,
      ownerSnapshotsConsumed, pendingOwnerSnapshotsAtSeal) =>
    return ((report, compact, verdict?), {
      selected := true
      source := sourceObservation
      retainedSupportRecords
      ownerSnapshotsConsumed
      pendingOwnerSnapshotsAtSeal })
  | Except.error message =>
    setEnv base
    restoreLevelCounters
    let result ← runFilterDirectCheckingPlannedCensus input reader false generation
    return (result, {
      selected := false
      source := sourceObservation
      fallback? := some message })

/-- Phase-four internal route: the parser has released its complete source
declaration array, and scheduled replay decodes exactly one certified raw
record for each `FilterState.feedSource` transition.  Main does not select this
path yet; the retained full parser/filter remains its independent fallback and
property oracle. -/
def runFilterDiscardingPlannedCensus (input : PlannedSourceInput)
    (reader : Spool.PlannedSourceReader) (checkRecursors : Bool)
    (generation : Cli.Config) : MetaM (Report × CompactPlan) := do
  if let .error message ← validatePlannedSource input reader then
    throwError message
  let (_, report, compact, _, _, _, _) ← runFilterCore input.envelope.template
    checkRecursors generation .compactDiscard (plannedSource? := some reader)
    (sourceCensus? := some input.census)
  return (report, compact)

end InductiveModels
