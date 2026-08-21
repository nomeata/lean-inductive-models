import InductiveModels.Simple

/-!
# One-layer certificates

A one-layer family publishes a public carrier `P`, a private carrier `M` and
an equivalence `roll`/`unroll` between them with both round trips proved, so a
consumer can read the public interface without seeing the encoding underneath.

Two routes still emit that certificate.  The **indexed fibre** adapter at the
bottom of this module wraps arm C's own public family: its `roll`/`unroll` are
the identity and its laws are reflexivity, so the certificate costs eight
aliases and no transport.  The **plain mutual** adapter
(`InductiveModels.MutualOneLayer`) rebuilds a real layer over the tag/aux
encoding, and the compatibility construction below is what proves its ι rules.

There is no adapter for an *unindexed* single-block owner.  One was built and
removed: the simple construction already publishes that owner's carrier,
constructor, recursor, ι rules and intrinsic projections at the exact source
syntax, so a private fixpoint with a rolled layer over it bought nothing and
cost one `Eq.rec` transport per recursive field (and a `funext` splice per
function-typed one) in every ι rule it published.
-/

open Lean Meta

namespace InductiveModels

/-! ## The two fixed-arity lemmas the compatibility construction is built from

A rebuilt one-layer ι rule has to move `n` public recursive fields from
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

private def generatedType (name : Name) : GenM Expr := do
  let some info := (← getEnv).constants.find? name
    | badShape s!"generated declaration {name} is absent"
  return info.type

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
loop, and the caller passes the field data as arrays.

**No caller can reach a step that does not collapse.**  The plain mutual
adapter is the only route that reaches this construction, and it installs each
member's `unroll_roll` as a declaration of type `unroll (roll value) = value`
whose value is the private family's ι rule — an `Eq.refl`, always, by that
family's own design.  A member whose round trip is only propositional therefore
publishes a certificate its kernel gate rejects, so every `roundTrips` entry and
the `roundTripMajor` handed in below prove equations between definitionally
equal endpoints, and proof irrelevance identifies them all with `Eq.refl`.
Measured over the whole corpus: every ι rule published through here is accepted
with `Eq.refl` in place of this entire construction — chain, bridge and all.
The arity is untested because it is unreachable, not because a fixture is
missing; see `test/fixtures/inductive-models/mutual_one_layer_boundary.lean`. -/
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
