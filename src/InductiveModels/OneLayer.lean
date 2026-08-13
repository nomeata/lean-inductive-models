import InductiveModels.Simple

/-!
# One-layer public carriers

The first production tranche keeps the existing simple encoding as a private
fixpoint `M` and exposes one constructor layer `P = F M`.  This module builds
that boundary independently of the public constructor/recursor adapter, so the
carrier plumbing can be source-checked without changing output selection.
-/

open Lean Meta

namespace InductiveModels

/-- Names internal to one private/public one-layer equivalence. -/
structure OneLayerNames where
  publicNames : PrimInterfaceNames
  implementation : PrimInterfaceNames
  roll : Name
  unroll : Name
  unrollRoll : Name
  rollUnroll : Name
  deriving Inhabited

def OneLayerNames.forBuild (tname root : Name)
    (constructors : Array (Name × Expr)) : OneLayerNames :=
  let publicNames := PrimInterfaceNames.standard tname root constructors
  let implementation := PrimInterfaceNames.oneLayerImplementation root constructors
  { publicNames, implementation
    roll := Name.str implementation.impl "roll"
    unroll := Name.str implementation.impl "unroll"
    unrollRoll := Name.str implementation.impl "unroll_roll"
    rollUnroll := Name.str implementation.impl "roll_unroll" }

/-- The checked carrier boundary, before the public declaration family is
attached.  `storageFields` are represented structurally in the generated
definitions and are therefore not retained here. -/
structure OneLayerBase where
  declarations : Array Declaration
  spliced : Array Name
  names : OneLayerNames
  implementationNames : IsoInterface
  deriving Inhabited

/-- Public constructor and intrinsic-projection implementation, before the
public recursor family is attached. -/
structure OneLayerPublicFields where
  declarations : Array Declaration
  spliced : Array Name
  projectionOverrides : Array (Name × Nat × Expr × Expr)
  fx? : Option Name
  deriving Inhabited

private def generatedType (name : Name) : GenM Expr := do
  let some info := (← getEnv).constants.find? name
    | badShape s!"generated declaration {name} is absent"
  return info.type

private def exactCarrierLevel (memberTy : Expr) (np : Nat) : GenM Level :=
  forallBoundedTelescope memberTy (some np) fun _ result => match result with
    | .sort level => pure level
    | _ => badShape "a one-layer owner does not end in a sort"

private def ensureFresh (reserved : Std.HashSet Name) (name : Name) : GenM Unit := do
  if reserved.contains name || (← getEnv).constants.contains name then
    declineWith (.nameTaken name)

/-- Map the unique bare recursive occurrence in a direct or infinitary field.
The field's own Π binders are retained literally; only the terminal carrier
application moves through `operation`. -/
partial def mapOneLayerOccurrence (owner : Name) (np : Nat) (operation : Name)
    (levels : List Level) (type value : Expr) : GenM Expr := do
  match headNorm type with
  | .forallE name domain body info =>
    withLocalDecl name info domain fun argument => do
      let mapped ← mapOneLayerOccurrence owner np operation levels
        (body.instantiate1 argument) (mkApp value argument)
      mkLambdaFVars #[argument] mapped
  | terminal =>
    let some arguments ← ownerAppArgs? owner np 0 terminal
      | badShape s!"a one-layer recursive field does not end in {owner}"
    pure (mkAppN (.const operation levels)
      (arguments.extract 0 np |>.push value))

/-- Pointwise section/retraction proof for one direct or infinitary recursive
field.  A direct occurrence uses no `funext`; each explicit field binder uses
exactly one application of the supplied theorem. -/
partial def oneLayerOccurrenceRoundTrip (owner intermediate : Name) (np : Nat)
    (first second theoremName : Name) (fx? : Option Name) (levels : List Level)
    (type value : Expr) : GenM Expr := do
  match headNorm type with
  | .forallE name domain body info =>
    withLocalDecl name info domain fun argument => do
      let resultType := body.instantiate1 argument
      let applied := mkApp value argument
      let point ← oneLayerOccurrenceRoundTrip owner intermediate np first second theoremName fx?
        levels resultType applied
      let once ← mapOneLayerOccurrence owner np first levels type value
      let twiceType ← inferType once
      let twice ← mapOneLayerOccurrence intermediate np second levels twiceType once
      funextUp fx? #[argument] 1 twice value point
  | terminal =>
    let some arguments ← ownerAppArgs? owner np 0 terminal
      | badShape s!"a one-layer recursive field does not end in {owner}"
    pure (mkAppN (.const theoremName levels) (arguments.extract 0 np |>.push value))

/-- Build `P`, `roll : P → M`, and `unroll : M → P` over an already checked
private simple implementation.  No caller selects this helper until the two
round trips and complete public family have also been built.

The layer is the existing exact-sort field tower over the private constructor
telescope.  Consequently ordinary/dependent fields retain their literal
syntax, while direct and infinitary recursive fields store private `M` values.
-/
def buildOneLayerBase (tname root : Name) (lparams : List Name) (np : Nat)
    (memberTy : Expr) (sourceConstructor : Name × Expr)
    (reserved : Std.HashSet Name) (implementationIso : Iso) : GenM OneLayerBase := do
  let names := OneLayerNames.forBuild tname root #[sourceConstructor]
  unless implementationIso.selfNames == #[names.implementation.self] &&
      implementationIso.ctors == #[(sourceConstructor.1, names.implementation.ctors[0]!)] &&
      implementationIso.recs == #[names.implementation.recursor] &&
      implementationIso.iotas.map (fun (_, _, name) => name) == names.implementation.iotas do
    badShape s!"{tname}'s private simple interface does not match its one-layer name plan"
  for name in #[names.publicNames.self, names.publicNames.ctors[0]!, names.publicNames.recursor,
      names.publicNames.iotas[0]!, names.roll, names.unroll, names.unrollRoll,
      names.rollUnroll] do
    ensureFresh reserved name

  let us := lparams.map Level.param
  let level ← exactCarrierLevel memberTy np
  let privateTable := modelTable (← getEnv) #[tname] implementationIso
  let privateConstructorType := restore privateTable sourceConstructor.2
  let publicSelfName := names.publicNames.self
  let publicConstructorName := names.publicNames.ctors[0]!
  let publicRecursorName := names.publicNames.recursor
  let publicModel : Iso := { implementationIso with
      selfNames := #[publicSelfName]
      ctors := #[(sourceConstructor.1, publicConstructorName)]
      recs := #[publicRecursorName], iotas := #[] }
  let publicTable := modelTable (← getEnv) #[tname] publicModel
  let publicSelfType := restore publicTable memberTy

  -- Establish the exact carrier level before installing any extra support.
  forallBoundedTelescope memberTy (some np) fun parameters _ => do
    let telescope ← instForall privateConstructorType parameters
    let fieldCount := numForalls telescope
    forallBoundedTelescope telescope (some fieldCount) fun fields _ => do
      if let some actual ← wTowerLevelOf level fields then
        badShape s!"{tname}'s one-layer field tower inhabits Sort {actual}, not Sort {level}"

  let support ← ensureExactSortLift reserved
  let mut declarations := support
  let spliced := support.flatMap (·.getNames.toArray)

  let publicSelfValue ← forallBoundedTelescope memberTy (some np) fun parameters _ => do
    let telescope ← instForall privateConstructorType parameters
    let fieldCount := numForalls telescope
    forallBoundedTelescope telescope (some fieldCount) fun fields _ => do
      mkLambdaFVars parameters (← wTowerTyOf level fields)
  let publicSelfHints ← hintsFor publicSelfValue
  let publicSelf := Declaration.defnDecl
    { name := names.publicNames.self, levelParams := lparams, type := publicSelfType
      value := publicSelfValue, hints := publicSelfHints, safety := .safe }
  addChecked publicSelf
  declarations := declarations.push publicSelf

  let privateSelfAt := fun (parameters : Array Expr) =>
    mkAppN (.const names.implementation.self us) parameters
  let publicSelfAt := fun (parameters : Array Expr) =>
    mkAppN (.const names.publicNames.self us) parameters

  let rollType ← forallBoundedTelescope memberTy (some np) fun parameters _ =>
    withLocalDeclD `layer (publicSelfAt parameters) fun layer =>
      mkForallFVars (parameters.push layer) (privateSelfAt parameters)
  let rollValue ← forallBoundedTelescope memberTy (some np) fun parameters _ => do
    let telescope ← instForall privateConstructorType parameters
    let fieldCount := numForalls telescope
    forallBoundedTelescope telescope (some fieldCount) fun fields _ =>
      withLocalDeclD `layer (publicSelfAt parameters) fun layer => do
        let values ← wTowerProjsOf level fields layer
        mkLambdaFVars (parameters.push layer)
          (mkAppN (.const names.implementation.ctors[0]! us) (parameters ++ values))
  let roll := Declaration.defnDecl
    { name := names.roll, levelParams := lparams, type := rollType, value := rollValue
      hints := ← hintsFor rollValue, safety := .safe }
  addChecked roll
  declarations := declarations.push roll

  let implementationRecursorType ← generatedType names.implementation.recursor
  let implementationRecursorInfo ← match (← getEnv).constants.find?
      names.implementation.recursor with
    | some (.defnInfo info) => pure info
    | _ => badShape s!"{names.implementation.recursor} is not a generated definition"
  let recLevels :=
    if implementationRecursorInfo.levelParams.length == lparams.length + 1 then
      level :: us
    else us
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error message => badShape s!"{tname}'s one-layer equivalence needs Eq ({message})"
  let unrollPlan := fun (parameters : Array Expr) => do
    let motive ← withLocalDeclD `value (privateSelfAt parameters) fun value =>
      mkLambdaFVars #[value] (publicSelfAt parameters)
    let afterParameters ← instantiateForall implementationRecursorType parameters
    let .forallE _ _ afterMotive _ := afterParameters
      | badShape s!"{names.implementation.recursor} has no motive"
    let .forallE _ minorType _ _ := afterMotive.instantiate1 motive
      | badShape s!"{names.implementation.recursor} has no minor"
    let privateConstructorTelescope ← instForall privateConstructorType parameters
    let fieldCount := numForalls privateConstructorTelescope
    let minor ← forallBoundedTelescope minorType (some (numForalls minorType))
        fun binders _ => do
      unless binders.size >= fieldCount do
        badShape s!"{names.implementation.recursor}'s minor omits constructor fields"
      let fields := binders.extract 0 fieldCount
      mkLambdaFVars binders (← wTowerMkOf level fields fields)
    pure (motive, minor, fieldCount)
  let unrollType ← forallBoundedTelescope memberTy (some np) fun parameters _ =>
    withLocalDeclD `value (privateSelfAt parameters) fun value =>
      mkForallFVars (parameters.push value) (publicSelfAt parameters)
  let unrollValue ← forallBoundedTelescope memberTy (some np) fun parameters _ => do
    let (motive, minor, _) ← unrollPlan parameters
    withLocalDeclD `value (privateSelfAt parameters) fun value =>
      mkLambdaFVars (parameters.push value)
        (mkAppN (.const names.implementation.recursor recLevels)
          (parameters ++ #[motive, minor, value]))
  let unroll := Declaration.defnDecl
    { name := names.unroll, levelParams := lparams, type := unrollType, value := unrollValue
      hints := ← hintsFor unrollValue, safety := .safe }
  addChecked unroll
  declarations := declarations.push unroll

  let unrollRollType ← forallBoundedTelescope memberTy (some np) fun parameters _ =>
    withLocalDeclD `layer (publicSelfAt parameters) fun layer => do
      let lhs := mkAppN (.const names.unroll us)
        (parameters ++ #[mkAppN (.const names.roll us) (parameters ++ #[layer])])
      mkForallFVars (parameters.push layer)
        (eqi.mk' level (publicSelfAt parameters) lhs layer)
  let unrollRollValue ← forallBoundedTelescope memberTy (some np) fun parameters _ => do
    let telescope ← instForall privateConstructorType parameters
    let fieldCount := numForalls telescope
    forallBoundedTelescope telescope (some fieldCount) fun fields _ =>
      withLocalDeclD `layer (publicSelfAt parameters) fun layer => do
        let values ← wTowerProjsOf level fields layer
        let (motive, minor, _) ← unrollPlan parameters
        let proof := mkAppN (.const names.implementation.iotas[0]! recLevels)
          (parameters ++ #[motive, minor] ++ values)
        mkLambdaFVars (parameters.push layer) proof
  let unrollRoll := Declaration.thmDecl
    { name := names.unrollRoll, levelParams := lparams, type := unrollRollType
      value := unrollRollValue }
  addChecked unrollRoll
  declarations := declarations.push unrollRoll

  let rollUnrollType ← forallBoundedTelescope memberTy (some np) fun parameters _ =>
    withLocalDeclD `value (privateSelfAt parameters) fun value => do
      let unrolled := mkAppN (.const names.unroll us) (parameters ++ #[value])
      let lhs := mkAppN (.const names.roll us) (parameters ++ #[unrolled])
      mkForallFVars (parameters.push value)
        (eqi.mk' level (privateSelfAt parameters) lhs value)
  let rollUnrollValue ← forallBoundedTelescope memberTy (some np) fun parameters _ => do
    let motive ← withLocalDeclD `value (privateSelfAt parameters) fun value => do
      let unrolled := mkAppN (.const names.unroll us) (parameters ++ #[value])
      let lhs := mkAppN (.const names.roll us) (parameters ++ #[unrolled])
      mkLambdaFVars #[value] (eqi.mk' level (privateSelfAt parameters) lhs value)
    let afterParameters ← instantiateForall implementationRecursorType parameters
    let .forallE _ _ afterMotive _ := afterParameters
      | badShape s!"{names.implementation.recursor} has no motive"
    let .forallE _ minorType _ _ := afterMotive.instantiate1 motive
      | badShape s!"{names.implementation.recursor} has no minor"
    let telescope ← instForall privateConstructorType parameters
    let fieldCount := numForalls telescope
    let minor ← forallBoundedTelescope minorType (some (numForalls minorType))
        fun binders _ => do
      let fields := binders.extract 0 fieldCount
      let (unrollMotive, unrollMinor, _) ← unrollPlan parameters
      let layerEquality := mkAppN (.const names.implementation.iotas[0]! recLevels)
        (parameters ++ #[unrollMotive, unrollMinor] ++ fields)
      let layer := publicSelfAt parameters
      let privateCarrier := privateSelfAt parameters
      let source := mkAppN (.const names.unroll us)
        (parameters ++ #[mkAppN (.const names.implementation.ctors[0]! us)
          (parameters ++ fields)])
      let target ← wTowerMkOf level fields fields
      let rollAt := fun value => mkAppN (.const names.roll us) (parameters ++ #[value])
      let proof ← transportAlong eqi .zero level layer source target layerEquality
        (eqi.refl' level privateCarrier (rollAt source)) fun value =>
          pure (eqi.mk' level privateCarrier (rollAt source) (rollAt value))
      mkLambdaFVars binders proof
    withLocalDeclD `value (privateSelfAt parameters) fun value =>
      mkLambdaFVars (parameters.push value)
        (mkAppN (.const names.implementation.recursor recLevels)
          (parameters ++ #[motive, minor, value]))
  let rollUnroll := Declaration.thmDecl
    { name := names.rollUnroll, levelParams := lparams, type := rollUnrollType
      value := rollUnrollValue }
  addChecked rollUnroll
  declarations := declarations.push rollUnroll

  let implementationNames := implementationIso.publicInterface
  return { declarations, spliced, names, implementationNames }

/-- Attach the exact public constructor and direct layer projections.
Recursive constructor inputs are mapped into the private fixpoint with `roll`;
recursive projections map back with `unroll`.  Their public iota RHS is still
the literal source field, while the proof override is pointwise
`unroll_roll` (and therefore need not be reflexivity). -/
def buildOneLayerPublicFields (tname : Name) (lparams : List Name) (np : Nat)
    (memberTy : Expr) (sourceConstructor : Name × Expr)
    (reserved : Std.HashSet Name) (implementationIso : Iso)
    (base : OneLayerBase) : GenM OneLayerPublicFields := do
  let names := base.names
  let us := lparams.map Level.param
  let privateTable := modelTable (← getEnv) #[tname] implementationIso
  let publicIso : Iso := { implementationIso with
    selfNames := #[names.publicNames.self]
    ctors := #[(sourceConstructor.1, names.publicNames.ctors[0]!)]
    recs := #[names.publicNames.recursor]
    iotas := #[] }
  let publicTable := modelTable (← getEnv) #[tname] publicIso
  let privateConstructorType := restore privateTable sourceConstructor.2
  let publicConstructorType := restore publicTable sourceConstructor.2
  let level ← exactCarrierLevel memberTy np
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error message => badShape s!"{tname}'s one-layer fields need Eq ({message})"

  let fieldShape ← forallBoundedTelescope memberTy (some np) fun parameters _ => do
    let telescope ← instForall publicConstructorType parameters
    classifyCtor names.publicNames.self (numForalls telescope) telescope
  let needsFunext := fieldShape.any fun field => field.rec?.any (· > 0)
  let (fx?, funextDeclarations) ← if needsFunext then do
      let (name, declarations) ← ensureFunext names.implementation.impl eqi reserved
      pure (some name, declarations)
    else pure (none, #[])
  let mut declarations := funextDeclarations
  let spliced := funextDeclarations.flatMap (·.getNames.toArray)

  let constructorValue ← forallBoundedTelescope memberTy (some np) fun parameters _ => do
    let publicTelescope ← instForall publicConstructorType parameters
    let privateTelescope ← instForall privateConstructorType parameters
    let fieldCount := numForalls publicTelescope
    forallBoundedTelescope publicTelescope (some fieldCount) fun publicFields _ =>
      forallBoundedTelescope privateTelescope (some fieldCount) fun privateFields _ => do
        let mut stored : Array Expr := #[]
        for index in [0:fieldCount] do
          let value ← if fieldShape[index]!.rec?.isSome then
              mapOneLayerOccurrence names.publicNames.self np names.roll us
                (← inferType publicFields[index]!) publicFields[index]!
            else pure publicFields[index]!
          stored := stored.push value
        mkLambdaFVars (parameters ++ publicFields)
          (← wTowerMkOf level privateFields stored)
  let constructorHints ← hintsFor constructorValue
  let constructor := Declaration.defnDecl
    { name := names.publicNames.ctors[0]!, levelParams := lparams
      type := publicConstructorType, value := constructorValue
      hints := constructorHints, safety := .safe }
  addChecked constructor
  declarations := declarations.push constructor

  let mut overrides : Array (Name × Nat × Expr × Expr) := #[]
  for fieldIndex in [0:fieldShape.size] do
    let selector ← forallBoundedTelescope memberTy (some np) fun parameters _ => do
      let privateTelescope ← instForall privateConstructorType parameters
      let fieldCount := numForalls privateTelescope
      forallBoundedTelescope privateTelescope (some fieldCount) fun privateFields _ =>
        withLocalDeclD `layer
            (mkAppN (.const names.publicNames.self us) parameters) fun layer => do
          let fields ← wTowerProjsOf level privateFields layer
          let value ← if fieldShape[fieldIndex]!.rec?.isSome then
              mapOneLayerOccurrence names.implementation.self np names.unroll us
                (← inferType fields[fieldIndex]!) fields[fieldIndex]!
            else pure fields[fieldIndex]!
          mkLambdaFVars (parameters.push layer) value
    let proof ← forallBoundedTelescope memberTy (some np) fun parameters _ => do
      let publicTelescope ← instForall publicConstructorType parameters
      let fieldCount := numForalls publicTelescope
      forallBoundedTelescope publicTelescope (some fieldCount) fun publicFields _ => do
        let selected := publicFields[fieldIndex]!
        let equality ← if fieldShape[fieldIndex]!.rec?.isSome then
            oneLayerOccurrenceRoundTrip names.publicNames.self names.implementation.self np
              names.roll names.unroll names.unrollRoll fx? us
              (← inferType selected) selected
          else
            let type ← inferType selected
            pure (eqi.refl' (← ilevel type) type selected)
        mkLambdaFVars (parameters ++ publicFields) equality
    overrides := overrides.push (tname, fieldIndex, selector, proof)

  return { declarations, spliced, projectionOverrides := overrides, fx? }

end InductiveModels
