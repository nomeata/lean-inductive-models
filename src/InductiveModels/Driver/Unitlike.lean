import InductiveModels.Driver.GeneratedInfo

/-!
# The unit-like equality theorem

Lean's kernel gives a unit-like inductive a definitional shortcut.  The model
does not appeal to it: the theorem is proved by running the model recursor
once for each side of the equality, so the minor-premise position of a
constructor in a mutual telescope has to be reconstructed first
([`recursorMinorIndex`]).
-/

open Lean Meta

namespace InductiveModels

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
  let normalizer := ExactNormalizationEnv.ofEnvironment (← getEnv)
  let eligible := (Array.range types.size).filter fun k =>
    types[k]!.isKernelUnitlike constructors.toList normalizer
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
