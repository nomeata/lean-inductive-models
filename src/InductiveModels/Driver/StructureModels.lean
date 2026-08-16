import InductiveModels.Driver.Unitlike
import InductiveModels.Driver.Projections

/-!
# The structure-like additions, and the roof over them

The literal structure-eta theorem and its recursor prefix, and
[`addStructureModels`], the one composition of the three additions
([`addUnitlikeTheorems`], [`addProjectionModels`], [`addStructureEtaTheorems`])
that every generation route calls.
-/

open Lean Meta

namespace InductiveModels

/-- Build the recursor prefix used by a structure-eta proof.  The selected
minor is supplied exactly; unrelated arms are inhabited without assuming
anything about sibling field codomains. -/
private def structureEtaRecursorPreArguments (eqi : EqInfo) (sourceRecursor : ERec)
    (modelRecursor targetConstructor : Name) (motiveIndex : Nat)
    (params : Array Expr) (carrier major targetMotive targetMinor : Expr)
    (recLevels : List Level) : GenM (Array Expr) :=
  structureRecursorPreArgumentsWith eqi sourceRecursor.numMotives sourceRecursor.numMinors
    modelRecursor targetConstructor
    motiveIndex params carrier major targetMotive .zero recLevels fun binders _ =>
      pure (targetMinor.beta binders)


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
  let puliftDecls ← if types.size > 1 then ensureExactSortLift else pure #[]
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
