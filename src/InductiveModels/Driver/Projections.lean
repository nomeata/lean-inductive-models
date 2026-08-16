import InductiveModels.Driver.StructureRecursor
import InductiveModels.Driver.NestedField

/-!
# Modeled primitive projections and their literal constructor rules

The largest single route in the driver: for every eligible field of a
structure-like member it emits the projection, its iota rule, and — for a
nested owner — the definitional selector built in
[`InductiveModels.Driver.NestedField`].

The two bounded expression helpers and the recursor level list at the head of
this module are used only from here.
-/

open Lean Meta

namespace InductiveModels

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


/-- A model recursor's level list at a selected motive sort: the motive
universe in front of the model's own when the recursor carries one, and the
model's own alone when its block eliminates only into `Prop` and Lean minted
none. -/
private def recursorLevels (recursor : Name) (recursorLevelParams modelLevelParams : List Name)
    (motiveLevel : Level) (modelLevels : List Level) : GenM (List Level) :=
  if recursorLevelParams.length == modelLevelParams.length + 1 then
    pure (motiveLevel :: modelLevels)
  else if recursorLevelParams.length == modelLevelParams.length then
    pure modelLevels
  else
    badShape s!"{recursor} carries unexpected universe parameters"


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
    ensureExactSortLift else pure #[]

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
    -- **An empty carrier owes no field back, and that is a decision rather
    -- than a fallback.**  The route that built the model states here that
    -- `T._model.self p⃗` is [`InductiveModels.emptyAt`] at this level — arm E,
    -- whose property is that every constructor of the owner has a *bare*
    -- recursive field, so no constructor can be applied and the type is empty
    -- at every instantiation of its sort.  Where that holds, both halves of
    -- the projection contract are elimination of the major and nothing else:
    -- the selector eliminates its `self` at the intrinsic codomain, and the
    -- rule `proj_j (mk f⃗) = f_j` eliminates the modeled constructor
    -- application, which δβ-reduces to one of the `f⃗` and inhabits the empty
    -- carrier.  Both are total; neither is attempted-and-repaired, and if the
    -- claim were false the kernel would refuse the two declarations below
    -- rather than any other route being tried.
    --
    -- This cannot be a `projectionOverrides` entry.  An override supplies a
    -- closed value, and the codomain these two need — field `j`'s type with
    -- each earlier field replaced by *its* modeled projection at this major —
    -- is assembled a few lines below out of names this module owns and no
    -- route can see.  The route states the carrier; this module states the
    -- codomain; the elimination is the only thing that has to know both.
    let emptyCarrier? := (is.emptyCarriers.find? (·.1 == type.name)).map (·.2)
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

    -- The nested rung's own selector, and the one place generation and
    -- checking have to agree about it.  `projectionIotaUsesLiteralField` reads
    -- the serialized nesting metadata, which the block's existence is
    -- equivalent to: a member with a nested occurrence reaches no other
    -- construction ([`InductiveModels.FilterState.feedSource`] keeps the
    -- plain-mutual and direct-simple routes off it), and no other construction
    -- produces a container record.  Disagreement is a construction fault, not
    -- an input's shortcoming, so it fails closed here rather than reaching the
    -- kernel as a mis-stated rule.
    let nestedBlock? := nestedProjectionBlock? is memberIndex
    let blockConstructor := nestedBlock?.map fun block =>
      Name.str block.member (lastStr constructorName)
    let nestedPacking ← match nestedBlock?, blockConstructor with
      | some block, some blockConstructor =>
        nestedFieldPacking block blockConstructor us type.numParams constructor.numFields
      | _, _ => pure #[]

    -- Read the selected field type from the modeled constructor telescope.
    -- An earlier field variable the rest of the telescope still names is
    -- replaced by the intrinsic projection already emitted for that field, so
    -- dependent results mention no constructor-local variable outside their
    -- scope.
    --
    -- **The walk drops a binder exactly where the kernel drops it.**
    -- `infer_proj` forms `proj i self` only when the body under field `i`'s
    -- binder has a loose occurrence of it, and only *there* does it require
    -- field `i` to be projectable in the first place — a Prop-valued owner's
    -- data field is skipped, not refused, when nothing later names it.
    -- `eligibleProjectionFieldsM` mirrors that walk, so such an owner's later
    -- proof field is projectable while its data field has no projection at
    -- all; substituting here regardless demanded one and raised an internal
    -- error on a kernel-accepted declaration.
    --
    -- Under the loose-occurrence test the lookup below is a real invariant:
    -- a field the remaining telescope names is one the eligibility walk
    -- required to be a proposition, hence eligible itself, and this loop
    -- emits fields in index order.
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
            -- `ownerArguments` was opened from this very expression, so closing
            -- over it is total: `forallBoundedTelescope` binds the leading `∀`s
            -- left to right and never binds more than there are, and
            -- `closeForallsExact?` walks the same expression with the same
            -- instantiation. It can only answer `none` if the walk runs out of
            -- `∀`s first, which would mean the telescope opened a binder that
            -- is not syntactically there — `modelTypeInfo.type` is a generated
            -- model type former's declared type, built by `mkForallFVars` over
            -- params and indices, so its leading `ownerArity` binders are
            -- written. This is the same statement the other eight call sites
            -- make, and it fails the same way rather than quietly rebuilding
            -- the type from the local context and losing the exact binder
            -- syntax the retention exists for.
            let some projectionType :=
                closeForallsExact? modelTypeInfo.type ownerArguments selfType
              | badShape s!"{modelType}'s public type does not open as \
                {ownerArguments.size} written binders"
            return projectionType
          if rest.hasLooseBVar 0 then
            let some (_, _, earlierProjection, _) := projectionModels.find? fun entry =>
                entry.1 == type.name && entry.2.1 == earlier
              | badShape s!"{type.name}'s field {fieldIndex} precedes intrinsic field {earlier}"
            let selected := mkAppN (.const earlierProjection us) (ownerArguments.push self)
            current := rest.instantiate1 selected
          else
            current := rest.lowerLooseBVars 1 1
        badShape s!"{constructorName} has no field {fieldIndex}"

    -- Both selectors eliminate the same major at the same motive; they differ
    -- in *which* recursor does it and in what its selected minor has in hand.
    let value ← match override?, emptyCarrier? with
      | some (_, _, value, _), _ => pure value
      | none, some (carrierLevel, descent) =>
        forallBoundedTelescope projectionType (some (ownerArity + 1))
            fun arguments result => do
          let params := arguments.extract 0 type.numParams
          let self := arguments[ownerArity]!
          mkLambdaFVars arguments
            (← emptyAtElim eqi (← ilevel result) carrierLevel result
              (descent.beta (params.push self)))
      | none, none => do
        forallBoundedTelescope projectionType (some (ownerArity + 1))
            fun arguments result => do
        let params := arguments.extract 0 type.numParams
        let indices := arguments.extract type.numParams ownerArity
        let self := arguments[ownerArity]!
        let targetMotive ← mkLambdaFVars (indices.push self) result
        let resultLevel ← ilevel result
        let (selector, recLevels, pre) ← match nestedBlock?, blockConstructor with
          | some block, some blockConstructor => do
            let selector := Name.str block.member "rec"
            let .recInfo blockRecursor ← constInfo selector
              | badShape s!"{selector} is not the nested block's own recursor"
            let recLevels ← recursorLevels selector blockRecursor.levelParams
              is.levelParams resultLevel us
            -- The block's minor binds the block's own field telescope, so the
            -- selected field arrives packed and comes back through its
            -- container.
            let pre ← structureRecursorPreArgumentsWith eqi
              blockRecursor.numMotives blockRecursor.numMinors
              selector blockConstructor block.memberIndex params
              (carrier (params ++ indices)) self targetMotive resultLevel recLevels
              fun binders _ => do
                let some field := binders[fieldIndex]?
                  | badShape s!"{blockConstructor}'s minor has no field {fieldIndex}"
                let some packed? := nestedPacking[fieldIndex]?
                  | badShape s!"{blockConstructor} has no packing for field {fieldIndex}"
                nestedSourceField us params packed? field
            pure (selector, recLevels, pre)
          | _, _ => do
            let recLevels ← recursorLevels modelRecursor modelRecursorInfo.levelParams
              is.levelParams resultLevel us
            let pre ← structureRecursorPreArguments eqi recursor modelRecursor
              modelConstructor motiveIndex params (carrier (params ++ indices))
              self targetMotive fieldIndex constructor.numFields resultLevel recLevels us
              projectionModels type.name
            pure (modelRecursor, recLevels, pre)
        mkLambdaFVars arguments
          (mkAppN (.const selector recLevels) (pre ++ indices ++ #[self]))
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
      let propositionLiteral := propositionProjectionIotaUsesLiteralField type
      let legacyLiteral := projectionIotaUsesLiteralField types type || propositionLiteral
      unless nestedBlock?.isSome == types.any (·.numNested > 0) do
        badShape s!"{type.name}'s nested block and its serialized nesting metadata disagree"
      if nestedBlock?.isSome && !legacyLiteral then
        badShape s!"{type.name}'s nested selector reduces definitionally but its \
          projection rules are not on the literal contract"
      -- The right-hand side is the constructor field binder on every route,
      -- with no route left to choose between.  Lean's positivity and nesting
      -- rules leave no spelling of a constructor field type that reads a
      -- recursive or nested occurrence's *value* at all
      -- (`test/fixtures/inductive-models/nested_value_dependency.lean` writes
      -- out every attempt and the kernel rejects each one), so every field a
      -- later field can depend on is non-recursive — but non-recursive is not
      -- the same as definitionally selected, which is what the guard below
      -- asks.  The predicates above survive only where they still decide
      -- something: the nested-selector agreement gate here, the proof below,
      -- and the exact binder telescope of the closed statement.
      let rhs := fields[fieldIndex]!
      let some alpha := instantiateForallsExact? projectionType
          (params ++ indices ++ #[major])
        | badShape s!"{modelProjection}'s exact public type has the wrong arity"
      let fieldLevel ← ilevel alpha
      -- **The one precondition the literal contract still has.**  `alpha` is
      -- the kernel's intrinsic codomain for this projection: field
      -- `fieldIndex`'s type with every earlier field replaced by that field's
      -- own modeled projection at this major.  `rhs` is the constructor's own
      -- binder, at the field's declared type.  For a field that names no
      -- earlier one the two are the same expression and there is nothing to
      -- ask.  For a dependent field they agree exactly when each earlier
      -- projection in its dependency closure *selects* its field — reduces to
      -- it — on the modeled constructor.
      --
      -- Every construction that reaches a field definitionally satisfies this:
      -- the literal routes above by δι on the carrier's own selectors, the
      -- direct/one-layer overrides by their reflexive projections, the nested
      -- rung by the block's primitive ι rule, the carved indexed routes by
      -- unfolding onto the layer underneath, and **arm W** by
      -- [`InductiveModels.wStoredFieldRead`] — `_wcore.WT.root`, the label's
      -- two `PSigma'` projections and the data tower, none of which is
      -- `WT.Wrec`.  Its children keep `WT.Wrec` and nothing can depend on one.
      --
      -- **What is left is a real question and not a formality.**  A route may
      -- state that its carrier is empty and answer every projection by
      -- eliminating the major (the `emptyCarrier?` branch below): that
      -- elimination is total but it is not a *selector*, so at such an owner
      -- `proj_j (mk f⃗)` does not reduce to `f_j` and a dependent field's two
      -- sides stay at different types.  A transported right-hand side used to
      -- bridge them and is no longer part of the contract
      -- (`test/ProjectionTransportCensusTest.lean`), so the owner declines
      -- rather than emitting a proposition the kernel refuses.
      unless ← isDefEq alpha (← inferType rhs) do
        declineWith (.projectionCodomain type.name fieldIndex)
      let proof ← match override?, nestedBlock? with
        | some (_, _, _, proof), _ => pure (proof.beta arguments)
        | none, some block => do
          let some packed? := nestedPacking[fieldIndex]?
            | badShape s!"{constructorName} has no packing entry for field {fieldIndex}"
          nestedProjectionProof eqi block us params packed? fieldLevel alpha lhs
            fields[fieldIndex]!
        | none, none =>
          if let some (carrierLevel, descent) := emptyCarrier? then
            -- The major is `T._model.mk p⃗ f⃗`, which the route's own descent
            -- takes back to the emptiness its carrier ends in — the bare
            -- recursive field itself where nothing is stored, and the tower's
            -- `snd` chain past the stored fields where something is.
            -- Eliminating that proves this equation — and every other
            -- proposition — with no appeal to how the selector above computes.
            emptyAtElim eqi .zero carrierLevel (eqi.mk' fieldLevel alpha lhs rhs)
              (descent.beta (params.push major))
          else if legacyLiteral then
            pure (eqi.refl' fieldLevel alpha lhs)
          else do
          let targetMotive ← forallBoundedTelescope
              (← instantiateForall projectionType params) (some (type.numIndices + 1))
              fun motiveArguments result => mkLambdaFVars motiveArguments result
          let recLevels ← recursorLevels modelRecursor modelRecursorInfo.levelParams
            is.levelParams fieldLevel us
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
          --
          -- Total, and hard-failing for the same reason as the eight other
          -- call sites. `arguments` was opened from `modelConstructorType` by
          -- `forallBoundedTelescope`, which binds its leading `∀`s left to
          -- right and no more of them than are there; `betaForallDomains`
          -- rewrites domains only and leaves the `∀`-spine's length and order
          -- exactly as it found them, so both branches hand
          -- `closeForallsExact?` a telescope with the spine the values came
          -- from. Falling back to `mkForallFVars` here would silently drop the
          -- retention this branch exists for — the ι statement would come out
          -- elaborator-normalised, and the statement checker would compare a
          -- shape nobody asked for — so the retention either happens or the
          -- run says it could not.
          let some retained := closeForallsExact? telescope arguments body
            | badShape s!"{modelConstructor}'s exact constructor telescope does not open as \
              {arguments.size} written binders"
          pure retained
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
