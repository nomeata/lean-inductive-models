import InductiveModels.Simple.Kit

/-!
# The recursor prefix a structure-like proof runs on

A one-constructor member's model recursor applied to everything up to and
including the selected minor, with the minor's body supplied by the caller.
[`structureRecursorPreArguments`] is the projection route's entry point;
[`structureRecursorPreArgumentsWith`] is the shared body, module-visible
because the eta route and the projection route both build on it.
-/

open Lean Meta

namespace InductiveModels

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
all unrelated motives and minors receive inhabited propositional lifts.

The motive and minor counts are arguments rather than read off a source
recursor record: the nested rung's projections eliminate with the *block's*
own recursor, whose motive vector covers the specialised containers as well as
the export's own members and which no source record describes. -/
def structureRecursorPreArgumentsWith (eqi : EqInfo)
    (numMotives numMinors : Nat)
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
  let selectedMinorIndex ← forallBoundedTelescope current (some numMotives)
      fun _ afterMotives =>
    forallBoundedTelescope afterMotives (some numMinors) fun minors _ => do
      let mut selected : Option Nat := none
      for i in [:minors.size] do
        if (findConstructorApp? targetConstructor (← inferType minors[i]!)).isSome then
          if selected.isSome then
            badShape s!"{modelRecursor} has several minors for {targetConstructor}"
          selected := some i
      let some index := selected
        | badShape s!"{modelRecursor} has no minor for {targetConstructor}"
      return index
  for motive in [0:numMotives] do
    let .forallE _ domain body _ := current
      | badShape s!"{modelRecursor} has too few motive binders"
    let value ← if motive == motiveIndex then pure targetMotive
      else constantMotive domain fillerType
    arguments := arguments.push value
    current := body.instantiate1 value
  for minorIndex in [0:numMinors] do
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
  structureRecursorPreArgumentsWith eqi sourceRecursor.numMotives sourceRecursor.numMinors
    modelRecursor targetConstructor
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
