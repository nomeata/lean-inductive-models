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

/-! ## The two fixed-arity lemmas the compatibility construction is built from

A one-layer ι rule has to move `n` public recursive fields from
`unrollField (rollField p)` back to `p`, one equality elimination each, while
the private constructor, the private computation and every private induction
hypothesis stay fixed.  Writing that as a *lemma* would need `n` independent
field universes, so there is no n-ary statement to write; the generator
**constructs** the proof instead, from these two statements and nothing else.

Both quantify the transported path rather than fixing it.  That is the whole
trick: after the last field has been eliminated the remaining path proves an
equation between two syntactically equal endpoints, and definitional proof
irrelevance plus `Eq`'s K-like reduction collapse the transport to the
identity — so the base case is `Eq.refl` and no path bookkeeping survives.
-/

/-- **One recursive field's equality induction.**  `layer` is the public
constructor with every other field held fixed and `result` the public minor at
the same hole; `roundTrip` is that field's `unroll_roll`.  Exactly one field
universe occurs, which is what makes the construction n-ary: the generator
applies this once per recursive field instead of asking for a lemma with `n`
of them. -/
theorem oneLayerFieldStep {P : Sort u} {C : P → Sort v} {A : Sort w}
    (source : P) (value : C source)
    (layer : A → P) (result : (x : A) → C (layer x))
    (before after : A) (roundTrip : before = after)
    (previous : ∀ path : source = layer before,
      Eq.mp (congrArg C path) value = result before) :
    ∀ path : source = layer after,
      Eq.mp (congrArg C path) value = result after :=
  Eq.rec (motive := fun after _ =>
      ∀ path : source = layer after,
        Eq.mp (congrArg C path) value = result after)
    previous roundTrip

/-- **The base of that chain.**  Transporting back along *any* proof of the
reversed constructor agreement undoes the transport along it: the two proofs of
one equation are definitionally equal, so the eliminated path is reflexivity.
At zero recursive fields this lemma is the whole compatibility proof. -/
theorem oneLayerTransportCancel {P : Sort u} {C : P → Sort v}
    (source target : P) (equality : source = target) (value : C source) :
    ∀ inverse : target = source,
      Eq.mp (congrArg C inverse) (Eq.mp (congrArg C equality) value) = value :=
  Eq.rec (motive := fun target equality =>
      ∀ inverse : target = source,
        Eq.mp (congrArg C inverse) (Eq.mp (congrArg C equality) value) = value)
    (fun _ => rfl) equality

/-- The pointwise induction hypothesis presented by the public recursor is the
private recursive result.  Equality induction holds the private computation
fixed; proof irrelevance identifies the remaining section witness with
reflexivity in the base case. -/
theorem oneLayerIHCompatibility
    {M P : Type u} {C : P → Sort v}
    (roll : P → M) (unroll : M → P)
    (unrollRoll : ∀ p, unroll (roll p) = p)
    (rollUnroll : ∀ q, roll (unroll q) = q)
    (core : ∀ q, C (unroll q)) :
    let publicRec : ∀ p, C p := fun p =>
      Eq.mp (congrArg C (unrollRoll p)) (core (roll p))
    ∀ q, publicRec (unroll q) = core q := by
  intro publicRec q
  unfold publicRec
  let h := rollUnroll q
  let base := core (roll (unroll q))
  have transported :
      Eq.mp (congrArg C (congrArg unroll h)) base = core q := by
    exact Eq.rec (motive := fun q' h' =>
      Eq.mp (congrArg C (congrArg unroll h')) base = core q') rfl h
  have witnesses : unrollRoll (unroll q) = congrArg unroll h :=
    rfl
  rw [witnesses]
  exact transported

/-! The filter replaces its elaboration environment with the input export, so
tool declarations are deliberately unavailable while models are generated.
Capture the closed oracle proof as data when this module is elaborated; the
generator instantiates and inlines this expression, never its declaration
name. -/

private partial def quoteLevelValue : Level → Expr
  | .zero => mkConst ``Level.zero
  | .succ level => mkApp (mkConst ``Level.succ) (quoteLevelValue level)
  | .max first second => mkApp2 (mkConst ``Level.max)
      (quoteLevelValue first) (quoteLevelValue second)
  | .imax first second => mkApp2 (mkConst ``Level.imax)
      (quoteLevelValue first) (quoteLevelValue second)
  | .param name => mkApp (mkConst ``Level.param) (toExpr name)
  | .mvar _ => panic! "a closed theorem contains a universe metavariable"

private def quoteBinderInfoValue : BinderInfo → Expr
  | .default => mkConst ``BinderInfo.default
  | .implicit => mkConst ``BinderInfo.implicit
  | .strictImplicit => mkConst ``BinderInfo.strictImplicit
  | .instImplicit => mkConst ``BinderInfo.instImplicit

private def quoteLevelListValue : List Level → Expr
  | [] => mkApp (mkConst ``List.nil [0]) (mkConst ``Level)
  | level :: levels => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Level)
      (quoteLevelValue level) (quoteLevelListValue levels)

private partial def quoteClosedExprValue : Expr → Expr
  | .bvar index => mkApp (mkConst ``Expr.bvar) (toExpr index)
  | .fvar _ => panic! "a closed theorem contains a free variable"
  | .mvar _ => panic! "a closed theorem contains a metavariable"
  | .sort level => mkApp (mkConst ``Expr.sort) (quoteLevelValue level)
  | .const name levels => mkApp2 (mkConst ``Expr.const) (toExpr name)
      (quoteLevelListValue levels)
  | .app function argument => mkApp2 (mkConst ``Expr.app)
      (quoteClosedExprValue function) (quoteClosedExprValue argument)
  | .lam name type body info => mkApp4 (mkConst ``Expr.lam) (toExpr name)
      (quoteClosedExprValue type) (quoteClosedExprValue body) (quoteBinderInfoValue info)
  | .forallE name type body info => mkApp4 (mkConst ``Expr.forallE) (toExpr name)
      (quoteClosedExprValue type) (quoteClosedExprValue body) (quoteBinderInfoValue info)
  | .letE name type value body nondep => mkAppN (mkConst ``Expr.letE) #[toExpr name,
      quoteClosedExprValue type, quoteClosedExprValue value,
      quoteClosedExprValue body, toExpr nondep]
  | .lit literal => mkApp (mkConst ``Expr.lit) (toExpr literal)
  | .mdata _ body => quoteClosedExprValue body
  | .proj typeName index subject => mkApp3 (mkConst ``Expr.proj) (toExpr typeName)
      (toExpr index) (quoteClosedExprValue subject)

private partial def inlineCompatibilityConstants (expression : Expr) : MetaM Expr := do
  let function := expression.getAppFn
  let arguments := expression.getAppArgs
  if let .const name levels := function then
    unless name == ``Eq || name == ``Eq.refl || name == ``Eq.rec do
      match ← getConstInfo name with
      | .defnInfo info => do
          return ← inlineCompatibilityConstants <|
            mkAppN (info.value.instantiateLevelParams info.levelParams levels) arguments
      | .thmInfo info => do
          return ← inlineCompatibilityConstants <|
            mkAppN (info.value.instantiateLevelParams info.levelParams levels) arguments
      | _ => pure ()
  match expression with
  | .app function argument => do
      return Expr.app (← inlineCompatibilityConstants function)
        (← inlineCompatibilityConstants argument)
  | .lam name type body info => do
      return Expr.lam name (← inlineCompatibilityConstants type)
        (← inlineCompatibilityConstants body) info
  | .forallE name type body info => do
      return Expr.forallE name (← inlineCompatibilityConstants type)
        (← inlineCompatibilityConstants body) info
  | .letE name type value body nondep => do
      return Expr.letE name (← inlineCompatibilityConstants type)
        (← inlineCompatibilityConstants value) (← inlineCompatibilityConstants body) nondep
  | .mdata data body => do
      return Expr.mdata data (← inlineCompatibilityConstants body)
  | .proj typeName index subject => do
      return Expr.proj typeName index (← inlineCompatibilityConstants subject)
  | other => return other

/-- Read one closed oracle theorem as data: inline every constant it names
until nothing but `Eq`, `Eq.refl` and `Eq.rec` is left.  A theorem that keeps
any other constant is refused here rather than silently exported. -/
private def inlinedOracleValue (name : Name) (universes : List Name) : MetaM Expr := do
  let .thmInfo theoremInfo ← getConstInfo name
    | throwError "{name} is not a theorem"
  let value ← inlineCompatibilityConstants theoremInfo.value
  let extra := value.getUsedConstants.filter fun used =>
    used != ``Eq && used != ``Eq.refl && used != ``Eq.rec
  unless extra.isEmpty do
    throwError "embedded {name} proof retains {extra}"
  let parameters := (collectLevelParams {} value).params
  unless parameters.size == universes.length && universes.all parameters.contains do
    throwError "embedded {name} proof has universes {parameters}, expected {universes}"
  return value

open Elab Term in
elab "oneLayerFieldStepProof%" : term => do
  return quoteClosedExprValue (← inlinedOracleValue ``oneLayerFieldStep [`u, `v, `w])

open Elab Term in
elab "oneLayerTransportCancelProof%" : term => do
  return quoteClosedExprValue (← inlinedOracleValue ``oneLayerTransportCancel [`u, `v])

open Elab Term in
elab "oneLayerIHCompatibilityProof%" : term => do
  return quoteClosedExprValue (← inlinedOracleValue ``oneLayerIHCompatibility [`u, `v])

private def oneLayerFieldStepProof : Expr := oneLayerFieldStepProof%
private def oneLayerTransportCancelProof : Expr := oneLayerTransportCancelProof%
private def oneLayerIHCompatibilityProof : Expr := oneLayerIHCompatibilityProof%

private partial def firstDifferencePath? (actual expected : Expr)
    (path : String := "root") : Option String :=
  if actual == expected then none else
  match actual, expected with
  | .app af aa, .app ef ea =>
    firstDifferencePath? af ef s!"{path}.fn" <|>
      firstDifferencePath? aa ea s!"{path}.arg"
  | .lam _ ad ab ai, .lam _ ed eb ei
  | .forallE _ ad ab ai, .forallE _ ed eb ei =>
    if ai != ei then some s!"{path}.binderInfo" else
    firstDifferencePath? ad ed s!"{path}.domain" <|>
      firstDifferencePath? ab eb s!"{path}.body"
  | .letE _ aty av ab an, .letE _ ety ev eb en =>
    if an != en then some s!"{path}.letKind" else
    firstDifferencePath? aty ety s!"{path}.type" <|>
      firstDifferencePath? av ev s!"{path}.value" <|>
      firstDifferencePath? ab eb s!"{path}.body"
  | .mdata _ ab, .mdata _ eb => firstDifferencePath? ab eb s!"{path}.mdata"
  | .proj an ai av, .proj en ei ev =>
    if an != en || ai != ei then some s!"{path}.projection" else
      firstDifferencePath? av ev s!"{path}.subject"
  | _, _ => some path

/-- [`oneLayerFieldStep`]'s embedded proof at the public carrier's, the
motive's and this field's universes.  The three are supplied by *name*, so a
later edit to the proof term cannot silently permute them. -/
def oneLayerFieldStepAt (carrier motive field : Level) : Expr :=
  oneLayerFieldStepProof.instantiateLevelParams [`u, `v, `w] [carrier, motive, field]

/-- [`oneLayerTransportCancel`]'s embedded proof, likewise. -/
def oneLayerTransportCancelAt (carrier motive : Level) : Expr :=
  oneLayerTransportCancelProof.instantiateLevelParams [`u, `v] [carrier, motive]

/-- Validate a completed compatibility proof: no metavariables, no reference to
the tool-side oracle declarations, kernel-checked, and definitionally the
expected statement.  The construction that builds the proof is n-ary, so this
is the one place the result is confronted with the exact source statement. -/
def checkOneLayerCompatibility (what : String) (proof expected : Expr) :
    MetaM (Except String Expr) := do
  let proof ← instantiateMVars proof
  let actual ← inferType proof
  unless ← withTransparency .all <| isDefEq actual expected do
    return .error s!"{what} result differs at \
      {(firstDifferencePath? actual expected).getD "definitionally unequal subterm"}: \
      {actual}, expected {expected}"
  let proof ← instantiateMVars proof
  if proof.hasExprMVar || proof.hasLevelMVar then
    return .error s!"{what} proof retains metavariables"
  let oracles := proof.getUsedConstants.filter fun name =>
    name == ``oneLayerFieldStep || name == ``oneLayerTransportCancel ||
      name == ``oneLayerIHCompatibility
  unless oracles.isEmpty do
    return .error s!"{what} proof refers to the tool-side oracle declarations {oracles}"
  check proof
  return .ok proof

def applyOneLayerIHCompatibility (levels : List Level) (arguments : Array Expr)
    (expected : Expr) : MetaM (Except String Expr) := do
  unless arguments.size == 9 do
    return .error s!"one-layer IH compatibility needs 9 arguments, got {arguments.size}"
  unless levels.length == 2 do
    return .error s!"one-layer IH compatibility needs 2 universes, got {levels.length}"
  let template := oneLayerIHCompatibilityProof.instantiateLevelParams [`u, `v] levels
  let proof ← instantiateMVars (mkAppN template arguments)
  let actual ← inferType proof
  unless ← isDefEq actual expected do
    return .error s!"IH compatibility result has type {actual}, expected {expected}"
  let proof ← instantiateMVars proof
  if proof.hasExprMVar || proof.hasLevelMVar then
    return .error "IH compatibility proof retains metavariables"
  check proof
  return .ok proof

/-- Count fully applied occurrences of one recursor constant.  Once a local
replacement function is supplied, applications of that function are treated
as atomic: its body deliberately contains the installed recursor that it
replaces, and must not be mistaken for untouched source syntax. -/
private partial def recursorApplicationCount (target : Name) (protected? : Option Expr)
    (expression : Expr) : Nat :=
  if protected?.any fun protectedExpression => expression.getAppFn == protectedExpression then
    0
  else if expression.getAppFn.constName? == some target then
    expression.getAppArgs.foldl
      (fun total argument => total + recursorApplicationCount target protected? argument) 1
  else
    match expression with
    | .app function argument =>
      recursorApplicationCount target protected? function +
        recursorApplicationCount target protected? argument
    | .lam _ type body _ | .forallE _ type body _ =>
      recursorApplicationCount target protected? type +
        recursorApplicationCount target protected? body
    | .letE _ type value body _ =>
      recursorApplicationCount target protected? type +
        recursorApplicationCount target protected? value +
        recursorApplicationCount target protected? body
    | .mdata _ body => recursorApplicationCount target protected? body
    | .proj _ _ subject => recursorApplicationCount target protected? subject
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => 0

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

/-- Rename an exact source face into the public one-layer interface without
rebuilding its constant applications.  In particular, the universe argument
syntax on every occurrence (and every `Expr.proj.typeName`) remains exactly as
the exporter supplied it; installed declarations remain the separate proof
and layout oracle. -/
private def exactOneLayerPublicSource (tname sourceConstructor sourceRecursor : Name)
    (names : OneLayerNames) (expression : Expr) : Expr :=
  mapConstsE (fun name =>
    if name == tname then some names.publicNames.self
    else if name == sourceConstructor then some names.publicNames.ctors[0]!
    else if name == sourceRecursor then some names.publicNames.recursor
    else none) expression

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

structure OneLayerPublicRecursor where
  declarations : Array Declaration
  recursorName : Name
  iotas : Array (Nat × Name × Name)
  deriving Inhabited

/-- The induction-hypothesis telescope associated with one direct or
infinitary recursive field.  The field's binders are retained literally and
the terminal recursive value is observed through `result`. -/
private partial def oneLayerHypothesisType (owner : Name) (np : Nat)
    (result fieldType field : Expr) : GenM Expr := do
  match headNorm fieldType with
  | .forallE name domain body info =>
    withLocalDecl name info domain fun argument => do
      let tail ← oneLayerHypothesisType owner np result
        (body.instantiate1 argument) (mkApp field argument)
      mkForallFVars #[argument] tail
  | terminal =>
    let some _ ← ownerAppArgs? owner np 0 terminal
      | badShape s!"a one-layer induction hypothesis does not end in {owner}"
    pure (mkApp result field)

/-- Apply a recursor pointwise through one direct or infinitary recursive
field, preserving the exact field binders. -/
private partial def oneLayerHypothesisValue (owner : Name) (np : Nat)
    (recursor fieldType field : Expr) : GenM Expr := do
  match headNorm fieldType with
  | .forallE name domain body info =>
    withLocalDecl name info domain fun argument => do
      let tail ← oneLayerHypothesisValue owner np recursor
        (body.instantiate1 argument) (mkApp field argument)
      mkLambdaFVars #[argument] tail
  | terminal =>
    let some _ ← ownerAppArgs? owner np 0 terminal
      | badShape s!"a one-layer recursive field does not end in {owner}"
    pure (mkApp recursor field)

private structure OneLayerUnrollPlan where
  motive : Expr
  minor : Expr
  fieldCount : Nat

private def oneLayerUnrollPlan (names : OneLayerNames) (level : Level)
    (levels : List Level) (parameters : Array Expr)
    (privateConstructorType privateRecursorType : Expr) :
    GenM OneLayerUnrollPlan := do
  let privateSelf := mkAppN (.const names.implementation.self levels) parameters
  let publicSelf := mkAppN (.const names.publicNames.self levels) parameters
  let motive ← withLocalDeclD `value privateSelf fun value =>
    mkLambdaFVars #[value] publicSelf
  let afterParameters ← instantiateForall privateRecursorType parameters
  let .forallE _ _ afterMotive _ := afterParameters
    | badShape s!"{names.implementation.recursor} has no motive"
  let .forallE _ minorType _ _ := afterMotive.instantiate1 motive
    | badShape s!"{names.implementation.recursor} has no minor"
  let privateConstructorTelescope ← instForall privateConstructorType parameters
  let fieldCount := numForalls privateConstructorTelescope
  let minor ← forallBoundedTelescope minorType (some (numForalls minorType))
      fun binders _ => do
    let fields := binders.extract 0 fieldCount
    mkLambdaFVars binders (← wTowerMkOf level fields fields)
  return { motive, minor, fieldCount }

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

/-- A retry builds below an alias root, but the serialized certificate lands
at these exact names.  Check them before generation so aliasing cannot turn a
reserved exact helper into a late duplicate or replay failure. -/
private def ensureExactOneLayerRetryFresh (tname : Name)
    (sourceConstructor : Name × Expr) (reserved : Std.HashSet Name) : GenM Unit := do
  let exact := OneLayerNames.forBuild tname tname #[sourceConstructor]
  for name in #[exact.implementation.self, exact.implementation.ctors[0]!,
      exact.implementation.recursor, exact.implementation.iotas[0]!,
      exact.roll, exact.unroll, exact.unrollRoll, exact.rollUnroll] do
    ensureFresh reserved name

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

private def oneLayerTowerValue (stage : String) (level : Level) (carrier : Expr)
    (values : Array Expr) : GenM Expr := do
  let rec build (index : Nat) (current : Expr) : GenM Expr := do
    if index < values.size then
      let current ← withTransparency .all <| whnf current
      let .const name _ := current.getAppFn
        | badShape "a one-layer carrier layer is not a PSigma'"
      unless name == `PSigma' do badShape "a one-layer carrier layer is not a PSigma'"
      let arguments := current.getAppArgs
      unless arguments.size == 2 do badShape "a one-layer PSigma' has malformed arguments"
      let alpha := arguments[0]!
      let beta := arguments[1]!
      unless ← isDefEq (← inferType values[index]!) alpha do
        badShape s!"{stage}: a one-layer storage value {index} has type {← inferType values[index]!}, expected {alpha}; values={values}"
      let tail ← build (index + 1) (mkApp beta values[index]!)
      return psigmaMk (← ilevel alpha) level alpha beta values[index]! tail
    unless ← withTransparency .all <| isDefEq current (unitAt level) do
      badShape "a one-layer carrier does not terminate in PUnit"
    return unitAtCanon level
  build 0 carrier

private def oneLayerCongrChain (eqi : EqInfo) (v : Level) (α : Expr)
    (mkStep : Array Expr → GenM Expr) (ga gb pfs : Array Expr)
    (changed : Array Bool) : GenM Expr := do
  let n := ga.size
  unless gb.size == n && pfs.size == n && changed.size == n do
    badShape "a one-layer congruence certificate has inconsistent cardinalities"
  let mixed := fun (j : Nat) => (Array.range n).map fun m => if m < j then gb[m]! else ga[m]!
  let base ← mkStep ga
  let mut acc := eqi.refl' v α base
  for j in [0:n] do
    if !changed[j]! then
      unless ga[j]! == gb[j]! do
        badShape s!"an unchanged one-layer field {j} was rewritten"
      continue
    let .fvar fieldId := gb[j]!
      | badShape s!"a changed one-layer field {j} is not a constructor-local variable"
    for later in [j + 1:n] do
      if (← inferType gb[later]!).containsFVar fieldId then
        badShape s!"a changed one-layer field {j} occurs in later field {later}"
    let A ← ityp ga[j]!
    let ℓA ← ilevel A
    let atA ← mkStep ((mixed j).set! j ga[j]!)
    let famAt := fun (x : Expr) => mkStep ((mixed j).set! j x)
    let factor ← transportAlong eqi .zero ℓA A ga[j]! gb[j]! pfs[j]!
      (eqi.refl' v α atA) fun z => do
        let atZ ← famAt z
        pure (eqi.mk' v α atA atZ)
    let before ← mkStep (mixed j)
    let after ← mkStep (mixed (j + 1))
    acc ← transOf eqi v α base before after acc factor
  return acc

/-- Public constructor fields obtained from private fields, and the equation
identifying the rebuilt public constructor with `unroll` of the private one. -/
private def oneLayerConstructorAgreement (stage : String) (np : Nat)
    (names : OneLayerNames) (eqi : EqInfo) (fx? : Option Name)
    (levels recLevels : List Level) (level : Level) (parameters privateFields : Array Expr)
    (fieldShape : Array PField) (privateConstructorType privateRecursorType : Expr) :
    GenM (Array Expr × Expr) := do
  let mut publicFields : Array Expr := #[]
  let mut storedFields : Array Expr := #[]
  let mut proofs : Array Expr := #[]
  let mut changed : Array Bool := #[]
  for index in [0:privateFields.size] do
    let field := privateFields[index]!
    if fieldShape[index]!.rec?.isSome then
      let publicField ← mapOneLayerOccurrence names.implementation.self np names.unroll
        levels (← inferType field) field
      let stored ← mapOneLayerOccurrence names.publicNames.self np names.roll
        levels (← inferType publicField) publicField
      let proof ← oneLayerOccurrenceRoundTrip names.implementation.self names.publicNames.self np
        names.unroll names.roll names.rollUnroll fx? levels (← inferType field) field
      publicFields := publicFields.push publicField
      storedFields := storedFields.push stored
      proofs := proofs.push proof
      changed := changed.push true
    else
      publicFields := publicFields.push field
      storedFields := storedFields.push field
      let type ← inferType field
      proofs := proofs.push (eqi.refl' (← ilevel type) type field)
      changed := changed.push false
  let publicCarrier := mkAppN (.const names.publicNames.self levels) parameters
  let mkStep := oneLayerTowerValue stage level publicCarrier
  let stored ← mkStep privateFields
  let rebuilt ← mkStep storedFields
  let storageEquality ← oneLayerCongrChain eqi level publicCarrier
    mkStep storedFields privateFields proofs changed
  if storageEquality.hasExprMVar || storageEquality.hasLevelMVar then do
    let goals ← getMVars storageEquality
    badShape s!"one-layer storage equality retained metavariables: {repr goals}"
  let plan ← oneLayerUnrollPlan names level levels parameters
    privateConstructorType privateRecursorType
  let unrollEquality := mkAppN (.const names.implementation.iotas[0]! recLevels)
    (parameters ++ #[plan.motive, plan.minor] ++ privateFields)
  let privateMajor := mkAppN (.const names.implementation.ctors[0]! levels)
    (parameters ++ privateFields)
  let unrolledMajor := mkAppN (.const names.unroll levels) (parameters.push privateMajor)
  let reverse ← symmOf eqi level publicCarrier unrolledMajor stored unrollEquality
  let agreement ← transOf eqi level publicCarrier rebuilt stored unrolledMajor
    storageEquality reverse
  if agreement.hasExprMVar || agreement.hasLevelMVar then do
    let goals ← getMVars agreement
    badShape s!"one-layer constructor agreement retained metavariables: {repr goals}"
  return (publicFields, agreement)

private partial def oneLayerHypothesisAgreement (owner : Name) (np : Nat)
    (eqi : EqInfo) (fx? : Option Name) (names : OneLayerNames)
    (levels : List Level) (parameters : Array Expr)
    (publicMotive privateRec publicRec fieldType field : Expr) : GenM Expr := do
  match headNorm fieldType with
  | .forallE name domain body info =>
    withLocalDecl name info domain fun argument => do
      let point ← oneLayerHypothesisAgreement owner np eqi fx? names levels parameters
        publicMotive privateRec publicRec (body.instantiate1 argument) (mkApp field argument)
      let privateResult ← oneLayerHypothesisValue owner np privateRec fieldType field
      let publicField ← mapOneLayerOccurrence names.implementation.self np names.unroll
        levels fieldType field
      let publicResult ← oneLayerHypothesisValue names.publicNames.self np publicRec
        (← inferType publicField) publicField
      funextUp fx? #[argument] 1 publicResult privateResult point
  | terminal =>
    let some _ ← ownerAppArgs? owner np 0 terminal
      | badShape s!"a one-layer induction hypothesis does not end in {owner}"
    let publicValue := mkAppN (.const names.unroll levels) (parameters.push field)
    let lhs := mkApp publicRec publicValue
    let rhs := mkApp privateRec field
    let type ← inferType rhs
    let proposition := eqi.mk' (← ilevel type) type lhs rhs
    let privateCarrier := mkAppN (.const names.implementation.self levels) parameters
    let publicCarrier := mkAppN (.const names.publicNames.self levels) parameters
    let carrierLevel ← ilevel privateCarrier
    let some carrierUniverse := carrierLevel.normalize.dec
      | badShape "a phase-1 one-layer carrier is not in Type"
    let arguments := #[privateCarrier, publicCarrier, publicMotive,
      mkAppN (.const names.roll levels) parameters,
      mkAppN (.const names.unroll levels) parameters,
      mkAppN (.const names.unrollRoll levels) parameters,
      mkAppN (.const names.rollUnroll levels) parameters,
      privateRec, field]
    match ← applyOneLayerIHCompatibility [carrierUniverse, ← ilevel type]
        arguments proposition with
    | .ok proof => pure proof
    | .error message => badShape s!"one-layer IH compatibility failed: {message}"

private structure OneLayerRecursorPlan where
  privateMotive : Expr
  privateMinor : Expr
  core : Expr
  /-- The implementation iota proposition after fixing the public motive and
  private minor, but before applying constructor fields.  This is the single
  syntax authority used by the public compatibility proof. -/
  coreIotaProposition : Expr
  publicRec : Expr
  recLevels : List Level

/-- The exact primitive normal form of `Eq.mp (congrArg family equality)
base`.  The embedded compatibility theorem elaborates to this two-`Eq.rec`
term; sharing the construction prevents the public recursor declaration and
its proof oracle from choosing merely propositionally equal transports. -/
private def transportOneLayerMotiveAlong (eqi : EqInfo) (v ℓ : Level)
    (α a b equality base : Expr) (family : Expr → GenM Expr) : GenM Expr := do
  let source ← family a
  let target ← family b
  let congrMotive ← withLocalDeclD `z α fun z =>
    withLocalDeclD `hz (eqi.mk' ℓ α a z) fun hz => do
      let target ← family z
      mkLambdaFVars #[z, hz] (eqi.mk' (.succ v) (.sort v) source target)
  let congruence := eqi.recAt .zero ℓ α a congrMotive
    (eqi.refl' (.succ v) (.sort v) source) b equality
  let castMotive ← withLocalDeclD `target (.sort v) fun targetType =>
    withLocalDeclD `h (eqi.mk' (.succ v) (.sort v) source targetType) fun h =>
      mkLambdaFVars #[targetType, h] targetType
  return eqi.recAt v (.succ v) (.sort v) source castMotive base target congruence

/-- An `Eq.trans` chain with one `congrArg` per slot, over a family whose step
is monadic.  This is [`InductiveModels.congrChain`] at a `GenM` step, which the
induction-hypothesis congruence below needs because its step builds a
transport. -/
private def oneLayerSlotChain (eqi : EqInfo) (v : Level) (α : Expr)
    (mkStep : Array Expr → GenM Expr) (before after proofs : Array Expr) :
    GenM Expr := do
  let n := before.size
  unless after.size == n && proofs.size == n do
    badShape "a one-layer slot chain has inconsistent cardinalities"
  let mixed := fun (j : Nat) => (Array.range n).map fun m =>
    if m < j then after[m]! else before[m]!
  let base ← mkStep before
  let mut acc := eqi.refl' v α base
  for j in [0:n] do
    let slotType ← ityp before[j]!
    let slotLevel ← ilevel slotType
    let famAt := fun (x : Expr) => mkStep ((mixed j).set! j x)
    let atBefore ← famAt before[j]!
    let factor ← transportAlong eqi .zero slotLevel slotType before[j]! after[j]! proofs[j]!
      (eqi.refl' v α atBefore) fun z => do pure (eqi.mk' v α atBefore (← famAt z))
    acc ← transOf eqi v α base (← mkStep (mixed j)) (← mkStep (mixed (j + 1))) acc factor
  return acc

/-- **The compatibility proof for one one-layer ι rule, at any number of
recursive fields.**

The route's public recursor is `publicRec p = Eq.mp (congrArg C (unroll_roll p))
(core (roll p))`, and `roll (publicCtor p⃗)` is *definitionally* the private
constructor at the rolled fields `q⃗`.  So the rule to prove reads

```text
Eq.mp (congrArg C hout) (core (privateCtor q⃗))  =  minor p⃗ (publicIH⃗ p⃗)
```

and it is assembled in two halves.

**The bridge** rewrites the left transport's payload.  The private ι rule says
`core (privateCtor q⃗) = Eq.mp (congrArg C agreement) (minor m⃗ (privateIH⃗ q⃗))`
where `mᵢ = unrollFieldᵢ qᵢ`; one `congrArg` per field replaces each private
induction hypothesis by the public one at `mᵢ`, and the whole congruence is
lifted through the agreement transport.  What is left is the *same* minor the
goal names, but at `m⃗` rather than at `p⃗`.

**The chain** closes that gap, one field at a time.  It starts at
[`oneLayerTransportCancel`] — which is already the complete proof when there
are no recursive fields — and applies [`oneLayerFieldStep`] once per field,
each time replacing `mᵢ` by `pᵢ` along that field's `unroll_roll`.  Because
both lemmas quantify the transported path instead of fixing it, each step
eliminates exactly one field equation and nothing accumulates: the path is
supplied only at the end, as the major's own `unroll_roll`.

There is no arity anywhere in this: `n = 0`, `1`, `2` and `n > 2` are the same
loop, and the caller passes the field data as arrays. -/
def oneLayerNaryCompatibility (eqi : EqInfo) (carrierLevel motiveLevel : Level)
    (publicCarrier publicMotive unrolledMajor agreement : Expr)
    (coreAtPrivate coreIota roundTripMajor : Expr)
    (fieldTypes sources targets roundTrips privateIHs ihAgreements : Array Expr)
    (layerAt : Array Expr → GenM Expr)
    (minorAt : Array Expr → Array Expr → GenM Expr)
    (publicIHAt : Nat → Expr → GenM Expr) : GenM Expr := do
  let n := fieldTypes.size
  unless sources.size == n && targets.size == n && roundTrips.size == n &&
      privateIHs.size == n && ihAgreements.size == n do
    badShape "a one-layer compatibility construction has inconsistent field cardinalities"
  let mixed := fun (j : Nat) => (Array.range n).map fun i =>
    if i < j then targets[i]! else sources[i]!
  let publicMotiveAt := fun (value : Expr) => pure (mkApp publicMotive value)
  -- The minor at the unrolled fields, with the public induction hypotheses …
  let sourceFields := mixed 0
  let sourceLayer ← layerAt sourceFields
  let sourceAlpha := mkApp publicMotive sourceLayer
  let publicIHsAtSource ← (Array.range n).mapM fun i => publicIHAt i sourceFields[i]!
  let publicBase ← minorAt sourceFields publicIHsAtSource
  -- … and the same minor with the private ones, which is what the private ι
  -- rule actually produces.
  let privateBase ← minorAt sourceFields privateIHs
  let alongAgreement := fun (base : Expr) =>
    transportOneLayerMotiveAlong eqi motiveLevel carrierLevel publicCarrier
      sourceLayer unrolledMajor agreement base publicMotiveAt
  let value ← alongAgreement publicBase
  let privateValue ← alongAgreement privateBase
  let unrolledAlpha := mkApp publicMotive unrolledMajor
  -- The bridge: one `congrArg` per induction hypothesis, lifted through the
  -- constructor agreement, composed after the private ι rule.
  let ihChain ← oneLayerSlotChain eqi motiveLevel sourceAlpha
    (fun ihs => minorAt sourceFields ihs) privateIHs publicIHsAtSource
    (← (Array.range n).mapM fun i => do
      let hypothesisType ← ityp privateIHs[i]!
      symmOf eqi (← ilevel hypothesisType) hypothesisType
        publicIHsAtSource[i]! privateIHs[i]! ihAgreements[i]!)
  let liftedChain ← transportAlong eqi .zero motiveLevel sourceAlpha
    privateBase publicBase ihChain
    (eqi.refl' motiveLevel unrolledAlpha privateValue)
    fun z => do pure (eqi.mk' motiveLevel unrolledAlpha privateValue (← alongAgreement z))
  let bridge ← transOf eqi motiveLevel unrolledAlpha coreAtPrivate privateValue value
    coreIota liftedChain
  -- The chain: `cancel` once, then one `step` per recursive field.
  let mut chain := mkAppN (oneLayerTransportCancelAt carrierLevel motiveLevel)
    #[publicCarrier, publicMotive, sourceLayer, unrolledMajor, agreement, publicBase]
  for j in [0:n] do
    let fieldType := fieldTypes[j]!
    let fieldLevel ← ilevel fieldType
    let layer ← withLocalDeclD `field fieldType fun hole => do
      mkLambdaFVars #[hole] (← layerAt ((mixed j).set! j hole))
    let result ← withLocalDeclD `field fieldType fun hole => do
      let values := (mixed j).set! j hole
      let hypotheses ← (Array.range n).mapM fun i => publicIHAt i values[i]!
      mkLambdaFVars #[hole] (← minorAt values hypotheses)
    chain := mkAppN (oneLayerFieldStepAt carrierLevel motiveLevel fieldLevel)
      #[publicCarrier, publicMotive, fieldType, unrolledMajor, value, layer, result,
        sources[j]!, targets[j]!, roundTrips[j]!, chain]
  let chained := mkApp chain roundTripMajor
  -- Both halves live under the major's own round trip.
  let publicMajor ← layerAt (mixed n)
  let majorAlpha := mkApp publicMotive publicMajor
  let alongMajor := fun (base : Expr) =>
    transportOneLayerMotiveAlong eqi motiveLevel carrierLevel publicCarrier
      unrolledMajor publicMajor roundTripMajor base publicMotiveAt
  let recursorSide ← alongMajor coreAtPrivate
  let bridgedSide ← alongMajor value
  let liftedBridge ← transportAlong eqi .zero motiveLevel unrolledAlpha
    coreAtPrivate value bridge (eqi.refl' motiveLevel majorAlpha recursorSide)
    fun z => do pure (eqi.mk' motiveLevel majorAlpha recursorSide (← alongMajor z))
  let targetFields := mixed n
  let publicResult ← minorAt targetFields
    (← (Array.range n).mapM fun i => publicIHAt i targetFields[i]!)
  transOf eqi motiveLevel majorAlpha recursorSide bridgedSide publicResult
    liftedBridge chained

/-- The private recursion shared by the public recursor definition and its
compatibility proof.  Factoring it keeps the theorem arguments literally
identical to the declaration body rather than reconstructing an equivalent
minor after the declaration has been installed. -/
private def oneLayerRecursorPlan (_tname : Name) (lparams : List Name) (np : Nat)
    (parameters : Array Expr) (publicMotive publicMinor : Expr)
    (motiveLevel level : Level) (privateConstructorType privateRecursorType : Expr)
    (privateRecursorInfo : DefinitionVal) (fieldShape : Array PField)
    (eqi : EqInfo) (base : OneLayerBase) (publicFields : OneLayerPublicFields) :
    GenM OneLayerRecursorPlan := do
  let names := base.names
  let us := lparams.map Level.param
  let privateCarrier := mkAppN (.const names.implementation.self us) parameters
  let publicCarrier := mkAppN (.const names.publicNames.self us) parameters
  let privateMotive ← withLocalDeclD `value privateCarrier fun value =>
    mkLambdaFVars #[value]
      (mkApp publicMotive (mkAppN (.const names.unroll us) (parameters.push value)))
  let afterParameters ← instantiateForall privateRecursorType parameters
  let .forallE _ _ afterMotive _ := afterParameters
    | badShape s!"{names.implementation.recursor} has no motive"
  let .forallE _ privateMinorType _ _ := afterMotive.instantiate1 privateMotive
    | badShape s!"{names.implementation.recursor} has no minor"
  let privateTelescope ← instForall privateConstructorType parameters
  let fieldCount := numForalls privateTelescope
  let privateMinor ← forallBoundedTelescope privateMinorType
      (some (numForalls privateMinorType)) fun binders _ => do
    let privateFields := binders.extract 0 fieldCount
    let hypotheses := binders.extract fieldCount binders.size
    let layerRecLevels :=
      if privateRecursorInfo.levelParams.length == lparams.length + 1 then
        level :: us
      else us
    let (mappedFields, agreement) ← oneLayerConstructorAgreement "private minor" np names eqi
      publicFields.fx? us layerRecLevels level parameters privateFields fieldShape
      privateConstructorType privateRecursorType
    let targetMajor := mkAppN (.const names.unroll us)
      (parameters.push (mkAppN (.const names.implementation.ctors[0]! us)
        (parameters ++ privateFields)))
    let publicResult := mkAppN publicMinor (mappedFields ++ hypotheses)
    let proof ← transportOneLayerMotiveAlong eqi motiveLevel level publicCarrier
      (mkAppN (.const names.publicNames.ctors[0]! us) (parameters ++ mappedFields))
      targetMajor agreement publicResult fun value => pure (mkApp publicMotive value)
    mkLambdaFVars binders proof
  let recLevels :=
    if privateRecursorInfo.levelParams.length == lparams.length + 1 then
      motiveLevel :: us
    else us
  let core ← withLocalDeclD `value privateCarrier fun value =>
    mkLambdaFVars #[value] (mkAppN (.const names.implementation.recursor recLevels)
      (parameters ++ #[privateMotive, privateMinor, value]))
  let coreIotaProof := mkAppN (.const names.implementation.iotas[0]! recLevels)
    (parameters ++ #[privateMotive, privateMinor])
  let coreIotaProposition ← inferType coreIotaProof
  let publicRec ← withLocalDeclD `value publicCarrier fun value => do
    let privateMajor := mkAppN (.const names.roll us) (parameters.push value)
    let privateResult := mkApp core privateMajor
    let roundTrip := mkAppN (.const names.unrollRoll us) (parameters.push value)
    let body ← transportOneLayerMotiveAlong eqi motiveLevel level publicCarrier
      (mkAppN (.const names.unroll us) (parameters.push privateMajor)) value
      roundTrip privateResult fun result => pure (mkApp publicMotive result)
    mkLambdaFVars #[value] body
  return { privateMotive, privateMinor, core, coreIotaProposition, publicRec, recLevels }

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
  if root != tname then
    ensureExactOneLayerRetryFresh tname sourceConstructor reserved
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
  let sourceRecursorName := Name.str tname "rec"
  let publicSelfType := exactOneLayerPublicSource tname sourceConstructor.1
    sourceRecursorName names memberTy

  -- Establish the exact carrier level before installing any extra support.
  forallBoundedTelescope memberTy (some np) fun parameters _ => do
    let telescope ← instForall privateConstructorType parameters
    let fieldCount := numForalls telescope
    forallBoundedTelescope telescope (some fieldCount) fun fields _ => do
      if let some actual ← wTowerLevelOf level fields then
        badShape s!"{tname}'s one-layer field tower inhabits Sort {actual}, not Sort {level}"

  let support ← ensureExactSortLift
  let mut declarations := support
  let spliced := support.flatMap (·.getNames.toArray)

  let publicSelfValue ← forallBoundedTelescope memberTy (some np) fun parameters _ => do
    let telescope ← instForall privateConstructorType parameters
    let fieldCount := numForalls telescope
    forallBoundedTelescope telescope (some fieldCount) fun fields _ => do
      mkLambdaFVars parameters (← wTowerTyOf level fields)
  let publicSelf := Declaration.defnDecl
    { name := names.publicNames.self, levelParams := lparams, type := publicSelfType
      value := publicSelfValue, hints := .abbrev, safety := .safe }
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
  let unrollPlan := fun (parameters : Array Expr) =>
    oneLayerUnrollPlan names level us parameters privateConstructorType implementationRecursorType
  let unrollType ← forallBoundedTelescope memberTy (some np) fun parameters _ =>
    withLocalDeclD `value (privateSelfAt parameters) fun value =>
      mkForallFVars (parameters.push value) (publicSelfAt parameters)
  let unrollValue ← forallBoundedTelescope memberTy (some np) fun parameters _ => do
    let plan ← unrollPlan parameters
    withLocalDeclD `value (privateSelfAt parameters) fun value =>
      mkLambdaFVars (parameters.push value)
        (mkAppN (.const names.implementation.recursor recLevels)
          (parameters ++ #[plan.motive, plan.minor, value]))
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
        let plan ← unrollPlan parameters
        let proof := mkAppN (.const names.implementation.iotas[0]! recLevels)
          (parameters ++ #[plan.motive, plan.minor] ++ values)
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
      let plan ← unrollPlan parameters
      let layerEquality := mkAppN (.const names.implementation.iotas[0]! recLevels)
        (parameters ++ #[plan.motive, plan.minor] ++ fields)
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
      let equalityRecLevels :=
        if implementationRecursorInfo.levelParams.length == lparams.length + 1 then
          .zero :: us
        else us
      mkLambdaFVars (parameters.push value)
        (mkAppN (.const names.implementation.recursor equalityRecLevels)
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
  let privateConstructorType := restore privateTable sourceConstructor.2
  let publicConstructorType := exactOneLayerPublicSource tname sourceConstructor.1
    (Name.str tname "rec") names sourceConstructor.2
  let constructorValueType := publicConstructorType
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
    let fieldCount := numForalls publicTelescope
    forallBoundedTelescope publicTelescope (some fieldCount) fun publicFields _ => do
      let mut stored : Array Expr := #[]
      for index in [0:fieldCount] do
        let value ← if fieldShape[index]!.rec?.isSome then do
            let type ← inferType publicFields[index]!
            mapOneLayerOccurrence names.publicNames.self np names.roll us
              type publicFields[index]!
          else pure publicFields[index]!
        stored := stored.push value
      let expectedResult := mkAppN (.const names.publicNames.self us) parameters
      let value ← oneLayerTowerValue "public constructor" level expectedResult stored
      let actualResult ← inferType value
      unless ← withTransparency .all <| isDefEq actualResult expectedResult do
        badShape s!"{names.publicNames.ctors[0]!}'s concrete layer type {actualResult} does not inhabit {expectedResult}, which unfolds to {← withTransparency .all <| whnf expectedResult}"
      mkLambdaFVars (parameters ++ publicFields) value
  let constructorHints ← hintsFor constructorValue
  let constructor := Declaration.defnDecl
    { name := names.publicNames.ctors[0]!, levelParams := lparams
      type := constructorValueType, value := constructorValue
      hints := constructorHints, safety := .safe }
  if constructorValue.hasExprMVar || constructorValue.hasLevelMVar then do
    let goals ← getMVars constructorValue
    badShape s!"one-layer public constructor retained metavariables: {repr goals}"
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

/-- Build the exact public recursor over `P` from the private recursor over
`M`.  The private motive observes `unroll m`; the private minor maps recursive
fields pointwise through `unroll` and transports the public minor result along
the constructor agreement.  The final result transports along `unroll_roll`.
-/
def buildOneLayerPublicRecursor (tname : Name) (lparams : List Name) (np : Nat)
    (memberTy : Expr) (sourceConstructor : Name × Expr) (sourceRecursor : ERec)
    (implementationIso : Iso) (base : OneLayerBase) (publicFields : OneLayerPublicFields) :
    GenM OneLayerPublicRecursor := do
  let names := base.names
  let us := lparams.map Level.param
  let privateTable := modelTable (← getEnv) #[tname] implementationIso
  let privateConstructorType := restore privateTable sourceConstructor.2
  let publicConstructorType := exactOneLayerPublicSource tname sourceConstructor.1
    sourceRecursor.name names sourceConstructor.2
  let privateRecursorType ← generatedType names.implementation.recursor
  let publicRecursorType := exactOneLayerPublicSource tname sourceConstructor.1
    sourceRecursor.name names sourceRecursor.type
  let level ← exactCarrierLevel memberTy np
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error message => badShape s!"{tname}'s one-layer recursor needs Eq ({message})"
  let some (.defnInfo privateRecursorInfo) := (← getEnv).constants.find?
      names.implementation.recursor
    | badShape s!"{names.implementation.recursor} is not a generated definition"
  let publicRecLevels := sourceRecursor.levelParams.map Level.param
  let fieldShape ← forallBoundedTelescope memberTy (some np) fun parameters _ => do
    let telescope ← instForall publicConstructorType parameters
    classifyCtor names.publicNames.self (numForalls telescope) telescope

  let recursorValue ← forallBoundedTelescope publicRecursorType (some (np + 3))
      fun publicBinders _ => do
    let parameters := publicBinders.extract 0 np
    let publicMotive := publicBinders[np]!
    let publicMinor := publicBinders[np + 1]!
    let publicMajor := publicBinders[publicBinders.size - 1]!
    let motiveLevel ← ilevel (mkApp publicMotive publicMajor)
    let plan ← oneLayerRecursorPlan tname lparams np parameters publicMotive publicMinor
      motiveLevel level privateConstructorType privateRecursorType privateRecursorInfo
      fieldShape eqi base publicFields
    let body := mkApp plan.publicRec publicMajor
    mkLambdaFVars publicBinders body
  let recursorHints ← hintsFor recursorValue
  let recursor := Declaration.defnDecl
    { name := names.publicNames.recursor, levelParams := sourceRecursor.levelParams
      type := publicRecursorType, value := recursorValue
      hints := recursorHints, safety := .safe }
  addChecked recursor

  let publicRecursorName := names.publicNames.recursor
  let sourceRule ← match sourceRecursor.rules[0]? with
    | some rule => pure rule
    | none => badShape s!"{sourceRecursor.name} has no rule for {sourceConstructor.1}"
  unless sourceRule.ctor == sourceConstructor.1 do
    badShape s!"{sourceRecursor.name}'s rule is for {sourceRule.ctor}, not {sourceConstructor.1}"
  let iota ← forallBoundedTelescope publicRecursorType (some (np + 2)) fun pre _ => do
    let parameters := pre.extract 0 np
    let motive := pre[np]!
    let constructorTelescope ← instForall publicConstructorType parameters
    let fieldCount := numForalls constructorTelescope
    forallBoundedTelescope constructorTelescope (some fieldCount) fun fields _ => do
      let major := mkAppN (.const names.publicNames.ctors[0]! us) (parameters ++ fields)
      let lhs := mkAppN (.const names.publicNames.recursor publicRecLevels) (pre.push major)
      let rhs := (exactOneLayerPublicSource tname sourceConstructor.1 sourceRecursor.name
        names sourceRule.rhs).beta (pre ++ fields)
      let alpha := mkApp motive major
      let equalityLevel := if sourceRecursor.levelParams.length == lparams.length + 1 then
          sourceRecursor.levelParams.head?.map Level.param |>.getD .zero
        else .zero
      let proposition := eqi.mk' equalityLevel alpha lhs rhs
      let some exactFields := exactRecursorFieldTelescope? sourceRecursor 0 pre
        | badShape s!"{sourceRecursor.name}'s exported rule has no exact field telescope"
      let exactFields := exactOneLayerPublicSource tname sourceConstructor.1
        sourceRecursor.name names exactFields
      let some fieldsType := closeForallsExact? exactFields fields proposition
        | badShape s!"{sourceConstructor.1}'s exact field telescope is too short"
      let some theoremType := closeForallsExact? publicRecursorType pre fieldsType
        | badShape s!"{sourceRecursor.name}'s exact prefix is too short"
      let recursiveFields := (Array.range fields.size).filter fun index =>
        fieldShape[index]!.rec?.isSome
      let plan ← oneLayerRecursorPlan tname lparams np parameters motive pre[np + 1]!
        (← ilevel alpha) level privateConstructorType privateRecursorType privateRecursorInfo
        fieldShape eqi base publicFields
      let publicRec := plan.publicRec
      let motiveLevel ← ilevel alpha
      -- `q⃗`: every recursive field rolled into the private carrier, and `m⃗`:
      -- the same fields unrolled again.  Both are pointwise through the
      -- field's own binders, so an infinitary field is no different here.
      let mut storedFields := fields
      for index in recursiveFields do
        storedFields := storedFields.set! index (← mapOneLayerOccurrence
          names.publicNames.self np names.roll us (← inferType fields[index]!) fields[index]!)
      let mut unrolledFields := fields
      for index in recursiveFields do
        unrolledFields := unrolledFields.set! index (← mapOneLayerOccurrence
          names.implementation.self np names.unroll us
          (← inferType storedFields[index]!) storedFields[index]!)
      let privateMajor := mkAppN (.const names.implementation.ctors[0]! us)
        (parameters ++ storedFields)
      let rolledMajor := mkAppN (.const names.roll us) (parameters.push major)
      unless ← isDefEq rolledMajor privateMajor do
        badShape s!"{names.publicNames.ctors[0]!}'s roll compatibility is not definitional"
      let layerRecLevels :=
        if privateRecursorInfo.levelParams.length == lparams.length + 1 then
          level :: us
        else us
      -- Both the layer congruence and the private ι rule are read at *fresh*
      -- locals in the recursive slots and applied at `q⃗` afterwards: the
      -- congruence reads its independence invariant off the slots themselves,
      -- and the ι rule's exact statement is compared where no substitution has
      -- had a chance to reassociate it.  This is also how the private minor
      -- built the copy the private ι rule carries.
      let privateFieldTypes ← recursiveFields.mapM fun index =>
        inferType storedFields[index]!
      let storedRecursive := recursiveFields.map fun index => storedFields[index]!
      let holeTypes := privateFieldTypes.map fun type => (`q, type)
      let atHoles := fun (values : Array Expr) => Id.run do
        let mut holeFields := storedFields
        for slot in [0:recursiveFields.size] do
          holeFields := holeFields.set! recursiveFields[slot]! values[slot]!
        return holeFields
      let agreementFamily ← withLocalsD holeTypes 0 #[] fun holes => do
        let (_, proof) ← oneLayerConstructorAgreement "public iota" np names eqi
          publicFields.fx? us layerRecLevels level parameters (atHoles holes) fieldShape
          privateConstructorType privateRecursorType
        mkLambdaFVars holes proof
      let coreIotaFamily ← withLocalsD holeTypes 0 #[] fun holes => do
        let holeFields := atHoles holes
        let rule := mkAppN (.const names.implementation.iotas[0]! plan.recLevels)
          (parameters ++ #[plan.privateMotive, plan.privateMinor] ++ holeFields)
        unless (← inferType rule) ==
            (← instantiateForall plan.coreIotaProposition holeFields) do
          badShape s!"{names.implementation.iotas[0]!}'s exact instantiated rule changed syntax"
        mkLambdaFVars holes rule
      let agreement := agreementFamily.beta storedRecursive
      let coreIota := coreIotaFamily.beta storedRecursive
      let fieldTypes ← recursiveFields.mapM fun index => inferType fields[index]!
      let sources := recursiveFields.map fun index => unrolledFields[index]!
      let targets := recursiveFields.map fun index => fields[index]!
      let roundTrips ← recursiveFields.mapM fun index => do
        oneLayerOccurrenceRoundTrip names.publicNames.self names.implementation.self np
          names.roll names.unroll names.unrollRoll publicFields.fx? us
          (← inferType fields[index]!) fields[index]!
      let privateIHs ← recursiveFields.mapM fun index => do
        oneLayerHypothesisValue names.implementation.self np plan.core
          (← inferType storedFields[index]!) storedFields[index]!
      let ihAgreements ← recursiveFields.mapM fun index => do
        oneLayerHypothesisAgreement names.implementation.self np eqi publicFields.fx?
          names us parameters motive plan.core publicRec
          (← inferType storedFields[index]!) storedFields[index]!
      let substitute := fun (values : Array Expr) => Id.run do
        let mut result := fields
        for slot in [0:recursiveFields.size] do
          result := result.set! recursiveFields[slot]! values[slot]!
        return result
      let layerAt := fun (values : Array Expr) =>
        pure (mkAppN (.const names.publicNames.ctors[0]! us) (parameters ++ substitute values))
      let minorAt := fun (values hypotheses : Array Expr) =>
        pure (mkAppN pre[np + 1]! (substitute values ++ hypotheses))
      let publicIHAt := fun (_ : Nat) (value : Expr) => do
        oneLayerHypothesisValue names.publicNames.self np publicRec (← inferType value) value
      -- The exported rule is restored with the public declaration table, so
      -- its recursive hypotheses still call the installed public recursor.
      -- The compatibility proof is built before that declaration is unfolded:
      -- replace only calls with this exact parameter/motive/minor prefix by the
      -- local recursor body used on the left-hand side.
      let localRhs := rhs.replace fun subexpression => Id.run do
        let .const name _ := subexpression.getAppFn | return none
        unless name == names.publicNames.recursor do return none
        let arguments := subexpression.getAppArgs
        unless arguments.size == pre.size + 1 do return none
        for index in [:pre.size] do
          unless arguments[index]! == pre[index]! do return none
        return some (mkApp publicRec arguments[pre.size]!)
      let sourceCalls := recursorApplicationCount names.publicNames.recursor none rhs
      unless sourceCalls == recursiveFields.size do
        badShape s!"{names.publicNames.iotas[0]!}'s source rule has {sourceCalls} recursive \
          public calls, expected {recursiveFields.size}"
      let unmatchedCalls := recursorApplicationCount names.publicNames.recursor
        (some publicRec) localRhs
      unless unmatchedCalls == 0 do
        badShape s!"{names.publicNames.iotas[0]!}'s source rule retains {unmatchedCalls} \
          unmatched public recursor calls"
      let theoremLhs ← layerAt targets
      let theoremRhs ← minorAt targets
        (← (Array.range recursiveFields.size).mapM fun slot =>
          publicIHAt slot targets[slot]!)
      unless ← withTransparency .all <| isDefEq (mkApp publicRec theoremLhs)
          (mkApp publicRec major) do
        badShape s!"{names.publicNames.iotas[0]!}'s local constructor does not match its \
          exact source major"
      unless ← withTransparency .all <| isDefEq theoremRhs localRhs do
        badShape s!"{names.publicNames.iotas[0]!}'s local minor does not match its exact \
          source rule"
      let proof ← oneLayerNaryCompatibility eqi level motiveLevel
        (mkAppN (.const names.publicNames.self us) parameters) motive
        (mkAppN (.const names.unroll us) (parameters.push privateMajor)) agreement
        (mkApp plan.core privateMajor) coreIota
        (mkAppN (.const names.unrollRoll us) (parameters.push major))
        fieldTypes sources targets roundTrips privateIHs ihAgreements
        layerAt minorAt publicIHAt
      -- Type inference beta-reduces the local constructor/minor/IH arguments,
      -- so the already-checked exact source forms are the expected result while
      -- the same stored `publicRec` remains opaque on both sides.
      let localProposition := eqi.mk' equalityLevel alpha (mkApp publicRec major) localRhs
      let proof ← match ← checkOneLayerCompatibility
          s!"{names.publicNames.iotas[0]!}'s compatibility" proof localProposition with
        | .ok proof => pure proof
        | .error message => badShape message
      let actual ← inferType proof
      unless ← withTransparency .all <| isDefEq actual proposition do
        badShape s!"{names.publicNames.iotas[0]!}'s local compatibility proof does not unfold \
          to its public statement: {actual} != {proposition}"
      pure <| Declaration.thmDecl
        { name := names.publicNames.iotas[0]!, levelParams := sourceRecursor.levelParams
          type := theoremType, value := ← mkLambdaFVars (pre ++ fields) proof }
  addChecked iota
  let declarations := #[recursor, iota]
  let iotas : Array (Nat × Name × Name) :=
    #[(0, sourceConstructor.1, names.publicNames.iotas[0]!)]
  return { declarations, recursorName := publicRecursorName, iotas }

/-- Build the selected first production one-layer family.  The ordinary simple
generator remains the private recursion oracle; only this adapter's exact
source-shaped interface is published to correspondence and serialization. -/
def oneLayerIso (tname root : Name) (lparams : List Name) (np : Nat)
    (memberTy : Expr) (sourceConstructor : Name × Expr) (sourceRecursor : ERec)
    (reserved : Std.HashSet Name) : GenM Iso := do
  if sourceRecursor.k then
    badShape s!"{tname}'s recursive one-layer recursor unexpectedly carries rule K"
  let names := OneLayerNames.forBuild tname root #[sourceConstructor]
  let implementation ← primIsoWithInterface tname root lparams np memberTy
    #[sourceConstructor] reserved (sourceRecursor? := some sourceRecursor)
    (interface? := some names.implementation)
  let base ← buildOneLayerBase tname root lparams np memberTy sourceConstructor
    reserved implementation
  let fields ← buildOneLayerPublicFields tname lparams np memberTy sourceConstructor
    reserved implementation base
  let recursor ← buildOneLayerPublicRecursor tname lparams np memberTy sourceConstructor
    sourceRecursor implementation base fields
  let declarations := implementation.decls ++ base.declarations ++ fields.declarations ++
    recursor.declarations
  let mut aliases := if root == tname then Naming.AliasMap.empty else
    Naming.AliasMap.forRetry names.publicNames.model (Naming.modelName tname)
      (declarations.flatMap (·.getNames.toArray))
  if root != tname then
    aliases := aliases.insert names.publicNames.ctors[0]!
      (Naming.modelName sourceConstructor.1)
    aliases := aliases.insert names.publicNames.recursor
      (Naming.modelName sourceRecursor.name)
    aliases := aliases.insert names.publicNames.iotas[0]!
      (Naming.iotaName sourceRecursor.name 0)
  return { implementation with
    decls := declarations
    selfNames := #[names.publicNames.self]
    ctors := #[(sourceConstructor.1, names.publicNames.ctors[0]!)]
    recs := #[recursor.recursorName]
    iotas := recursor.iotas
    implementation? := some base.implementationNames
    ruleKs := #[]
    projectionOverrides := fields.projectionOverrides
    spliced := implementation.spliced ++ base.spliced ++ fields.spliced
    aliases }

private def etaAliasValue (levelParams : List Name) (source : Name)
    (type : Expr) : GenM Expr :=
  forallTelescope type fun arguments _ =>
    mkLambdaFVars arguments
      (mkAppN (.const source (levelParams.map Level.param)) arguments)

private def renameOneLayerCertificateNames (mapping : Array (Name × Name))
    (type : Expr) : Expr :=
  mapConstsE (fun name => mapping.findSome? fun (source, target) =>
    if name == source then some target else none) type

/-- Add the short, exact private/public certificate around the already checked
indexed fibre implementation.  Arm C remains the semantic implementation of
`P p i = Σ layer, resultIndex layer = i`; these declarations expose its two
interfaces and their identity equivalence without rebuilding or normalizing a
single public statement. -/
def indexedFibreOneLayerIso (tname root : Name) (lparams : List Name)
    (np : Nat) (memberTy : Expr)
    (sourceConstructor : Name × Expr) (sourceRecursor : ERec)
    (reserved : Std.HashSet Name) : GenM Iso := do
  if root != tname then
    ensureExactOneLayerRetryFresh tname sourceConstructor reserved
  let publicIso ← primIso tname root lparams np
    memberTy #[sourceConstructor] reserved
    (sourceRecursor? := some sourceRecursor)
  let names := OneLayerNames.forBuild tname root #[sourceConstructor]
  unless publicIso.selfNames == #[names.publicNames.self] &&
      publicIso.ctors == #[(sourceConstructor.1, names.publicNames.ctors[0]!)] &&
      publicIso.recs == #[names.publicNames.recursor] &&
      publicIso.iotas.map (fun (_, _, name) => name) == names.publicNames.iotas do
    badShape s!"{tname}'s indexed public fibre does not match its name plan"
  for name in #[names.implementation.self, names.implementation.ctors[0]!,
      names.implementation.recursor, names.implementation.iotas[0]!,
      names.roll, names.unroll, names.unrollRoll, names.rollUnroll] do
    ensureFresh reserved name
  let mapping := #[(names.publicNames.self, names.implementation.self),
    (names.publicNames.ctors[0]!, names.implementation.ctors[0]!),
    (names.publicNames.recursor, names.implementation.recursor),
    (names.publicNames.iotas[0]!, names.implementation.iotas[0]!)]
  let rename := renameOneLayerCertificateNames mapping
  let declaration := fun (name source : Name) (levelParams : List Name)
      (type : Expr) => do
    let value ← etaAliasValue levelParams source type
    pure <| Declaration.defnDecl
      { name, levelParams, type, value, hints := .abbrev, safety := .safe }
  let makeTheorem := fun (name source : Name) (levelParams : List Name)
      (type : Expr) => do
    let value ← etaAliasValue levelParams source type
    pure <| Declaration.thmDecl { name, levelParams, type, value }
  let publicSelfType ← generatedType names.publicNames.self
  let publicCtorType ← generatedType names.publicNames.ctors[0]!
  let publicRecType ← generatedType names.publicNames.recursor
  let publicIotaType ← generatedType names.publicNames.iotas[0]!
  let privateSelf ← declaration names.implementation.self names.publicNames.self
    lparams publicSelfType
  addChecked privateSelf
  let privateCtor ← declaration names.implementation.ctors[0]!
    names.publicNames.ctors[0]! lparams (rename publicCtorType)
  addChecked privateCtor
  let privateRec ← declaration names.implementation.recursor names.publicNames.recursor
    sourceRecursor.levelParams (rename publicRecType)
  addChecked privateRec
  let privateIota ← makeTheorem names.implementation.iotas[0]!
    names.publicNames.iotas[0]! sourceRecursor.levelParams (rename publicIotaType)
  addChecked privateIota
  let us := lparams.map Level.param
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error message => badShape s!"{tname}'s indexed fibre needs Eq ({message})"
  let ownerType ← generatedType names.publicNames.self
  let arity := numForalls ownerType
  let equivalenceType ← forallBoundedTelescope ownerType (some arity) fun arguments _ =>
    withLocalDeclD `value (mkAppN (.const names.publicNames.self us) arguments) fun value =>
      mkForallFVars (arguments.push value)
        (mkAppN (.const names.implementation.self us) arguments)
  let rollValue ← forallTelescope equivalenceType fun arguments _ =>
    mkLambdaFVars arguments arguments.back!
  let roll := Declaration.defnDecl
    { name := names.roll, levelParams := lparams, type := equivalenceType,
      value := rollValue, hints := .abbrev, safety := .safe }
  addChecked roll
  let inverseType ← forallBoundedTelescope ownerType (some arity) fun arguments _ =>
    withLocalDeclD `value (mkAppN (.const names.implementation.self us) arguments) fun value =>
      mkForallFVars (arguments.push value)
        (mkAppN (.const names.publicNames.self us) arguments)
  let unrollValue ← forallTelescope inverseType fun arguments _ =>
    mkLambdaFVars arguments arguments.back!
  let unroll := Declaration.defnDecl
    { name := names.unroll, levelParams := lparams, type := inverseType,
      value := unrollValue, hints := .abbrev, safety := .safe }
  addChecked unroll
  let law := fun (name : Name) (publicFirst : Bool) => do
    let carrierName := if publicFirst then names.publicNames.self else names.implementation.self
    let first := if publicFirst then names.roll else names.unroll
    let second := if publicFirst then names.unroll else names.roll
    let type ← forallBoundedTelescope ownerType (some arity) fun arguments _ =>
      withLocalDeclD `value (mkAppN (.const carrierName us) arguments) fun value => do
        let lhs := mkAppN (.const second us)
          (arguments.push (mkAppN (.const first us) (arguments.push value)))
        let carrier := mkAppN (.const carrierName us) arguments
        mkForallFVars (arguments.push value)
          (eqi.mk' (← ilevel carrier) carrier lhs value)
    let value ← forallTelescope type fun arguments result => do
      let #[alpha, lhs, _] := result.getAppArgs
        | badShape s!"{name}'s indexed fibre law is not an equality"
      mkLambdaFVars arguments
        (eqi.refl' (← ilevel alpha) alpha lhs)
    pure <| Declaration.thmDecl { name, levelParams := lparams, type, value }
  let unrollRoll ← law names.unrollRoll true
  addChecked unrollRoll
  let rollUnroll ← law names.rollUnroll false
  addChecked rollUnroll
  let certificate := #[privateSelf, privateCtor, privateRec, privateIota,
    roll, unroll, unrollRoll, rollUnroll]
  let aliases := publicIso.aliases.register
    (certificate.flatMap (·.getNames.toArray))
  return { publicIso with
    decls := publicIso.decls ++ certificate
    aliases
    implementation? := some
      { selfNames := #[names.implementation.self]
        ctors := #[(sourceConstructor.1, names.implementation.ctors[0]!)]
        recs := #[names.implementation.recursor]
        iotas := #[(0, sourceConstructor.1, names.implementation.iotas[0]!)] } }

end InductiveModels
