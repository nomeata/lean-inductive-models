import InductiveModels.Check.Violation
import InductiveModels.Check.Family
import InductiveModels.Plan
import InductiveModels.Projection

/-!
# Declaration-type views and one-layer interface certificates

The type-bearing view of the public constants an export record introduces,
its kind and safety checks, and the two recognizers for the first-tranche
private/public one-layer boundary.  A partial certificate prefix is malformed
rather than a request to reinterpret the family as legacy output.
-/

open Lean

namespace InductiveModels.Check

/-- The type-bearing view of one public constant introduced by an export
record.  Values are intentionally absent: this tranche checks the interface,
not how a model implements it. -/
structure DeclType where
  name : Name
  levelParams : List Name
  type : Expr
  kind : DeclarationKind
  safety? : Option String := none
  deriving Inhabited

def declTypes : EDecl → Array DeclType
  | .ax name levelParams type _ =>
      #[{ name, levelParams, type, kind := .axiom }]
  | .defn name levelParams type _ _ safety _ =>
      #[{ name, levelParams, type, kind := .defn, safety? := some safety }]
  | .thm name levelParams type .. =>
      #[{ name, levelParams, type, kind := .thm }]
  | .opaq name levelParams type .. =>
      #[{ name, levelParams, type, kind := .opaq }]
  | .quot name levelParams type _ =>
      #[{ name, levelParams, type, kind := .quotient }]
  | .induct types ctors recursors =>
      types.toArray.map (fun type =>
        { name := type.name, levelParams := type.levelParams, type := type.type,
          kind := .induct }) ++
      ctors.toArray.map (fun ctor =>
        { name := ctor.name, levelParams := ctor.levelParams, type := ctor.type,
          kind := .ctor }) ++
      recursors.toArray.map (fun recursor =>
        { name := recursor.name, levelParams := recursor.levelParams, type := recursor.type,
          kind := .recursor })

abbrev DeclarationTypes := Lean.PersistentHashMap Name (Array DeclType)

def declarationTypes (x : Export) : DeclarationTypes := Id.run do
  let mut declarations : DeclarationTypes := {}
  for declaration in x.decls do
    for info in declTypes declaration do
      declarations := declarations.insert info.name
        ((declarations.findD info.name #[]).push info)
  return declarations

def checkImplementationDecl (owner : Name) (declaration : DeclType) : Array Violation :=
  if declaration.kind != .defn then
    #[.declarationKind owner declaration.name .defn declaration.kind]
  else if declaration.safety? != some "safe" then
    #[.declarationSafety owner declaration.name (declaration.safety?.getD "<missing>")]
  else
    #[]

def checkTheoremDecl (owner : Name) (declaration : DeclType) : Array Violation :=
  if declaration.kind == .thm then #[]
  else #[.declarationKind owner declaration.name .thm declaration.kind]

/-- Kind-check a proof slot without duplicating its missing/duplicate diagnostics,
which remain the responsibility of the slot's exact statement checker. -/
def checkTheoremSlot (declarations : DeclarationTypes) (owner name : Name) :
    Array Violation :=
  match declarations.findD name #[] with
  | #[declaration] => checkTheoremDecl owner declaration
  | _ => #[]

inductive Phase1OneLayerCertificate where
  | absent
  | valid
  | malformed (slot : Name)

private def rewriteCertificateNames (mapping : Array (Name × Name)) (type : Expr) : Expr :=
  type.replace fun expression => match expression with
    | .const name levels => mapping.findSome? fun (source, target) =>
        if name == source then some (.const target levels) else none
    | _ => none

/-- Recognize the complete first-tranche private/public interface from the
serialized declarations.  Names alone do not select the new contract: every
private public-facing type, both directions of the equivalence, and both laws
must be uniquely present and exact.  A partial prefix is malformed rather
than a request to reinterpret the family as legacy output. -/
def phase1OneLayerCertificate (declarations : DeclarationTypes)
    (ownerType : EIndType) (constructors : Array ECtor) (recursors : Array ERec)
    (family : Family) :
    Phase1OneLayerCertificate := Id.run do
  let publicCarrierName := Naming.modelName ownerType.name
  let impl := Name.str publicCarrierName "_impl"
  let privateCarrierName := Name.str impl "self"
  let privateConstructorName := Name.str impl "ctor_0"
  let privateRecursorName := Name.str impl "rec"
  let privateIotaName := Name.str impl "rec_iota_0"
  let rollName := Name.str impl "roll"
  let unrollName := Name.str impl "unroll"
  let unrollRollName := Name.str impl "unroll_roll"
  let rollUnrollName := Name.str impl "roll_unroll"
  let certificateNames := #[privateCarrierName, privateConstructorName,
    privateRecursorName, privateIotaName, rollName, unrollName,
    unrollRollName, rollUnrollName]
  unless certificateNames.any declarations.contains do return .absent
  let some sourceConstructor := constructors.find? fun constructor =>
      constructor.induct == ownerType.name && ownerType.ctors.contains constructor.name
    | return .malformed privateConstructorName
  let some sourceRecursor := recursors.find? fun recursor =>
      recursor.all.contains ownerType.name &&
        recursor.rules.any (·.ctor == sourceConstructor.name)
    | return .malformed privateRecursorName
  unless indexedFibreOneLayerProjectionFamily ownerType sourceConstructor
      sourceRecursor do
    return .malformed privateCarrierName
  let some constructorPair := family.correspondence.constructors[0]?
    | return .malformed privateConstructorName
  let some recursorPair := family.correspondence.recursors[0]?
    | return .malformed privateRecursorName
  let some iota := family.correspondence.iotas[0]?
    | return .malformed privateIotaName
  let unique := fun name => match declarations.findD name #[] with
    | #[declaration] => some declaration
    | _ => none
  let some publicCarrier := unique publicCarrierName | return .malformed publicCarrierName
  let some publicConstructor := unique constructorPair.model
    | return .malformed constructorPair.model
  let some publicRecursor := unique recursorPair.model
    | return .malformed recursorPair.model
  let some publicIota := unique iota.name | return .malformed iota.name
  let some privateCarrier := unique privateCarrierName | return .malformed privateCarrierName
  let some privateConstructor := unique privateConstructorName
    | return .malformed privateConstructorName
  let some privateRecursor := unique privateRecursorName | return .malformed privateRecursorName
  let some privateIota := unique privateIotaName | return .malformed privateIotaName
  let some roll := unique rollName | return .malformed rollName
  let some unroll := unique unrollName | return .malformed unrollName
  let some unrollRoll := unique unrollRollName | return .malformed unrollRollName
  let some rollUnroll := unique rollUnrollName | return .malformed rollUnrollName
  unless publicCarrier.name == publicCarrierName do return .malformed publicCarrierName
  unless privateCarrier.kind == .defn && privateCarrier.safety? == some "safe" do
    return .malformed privateCarrierName
  unless privateConstructor.kind == .defn && privateConstructor.safety? == some "safe" do
    return .malformed privateConstructorName
  unless privateRecursor.kind == .defn && privateRecursor.safety? == some "safe" do
    return .malformed privateRecursorName
  unless privateIota.kind == .thm do return .malformed privateIotaName
  unless roll.kind == .defn && roll.safety? == some "safe" do return .malformed rollName
  unless unroll.kind == .defn && unroll.safety? == some "safe" do return .malformed unrollName
  unless unrollRoll.kind == .thm do return .malformed unrollRollName
  unless rollUnroll.kind == .thm do return .malformed rollUnrollName
  unless #[privateCarrier, privateConstructor, roll, unroll, unrollRoll, rollUnroll].all
      (·.levelParams == publicCarrier.levelParams) &&
      privateRecursor.levelParams == publicRecursor.levelParams &&
      privateIota.levelParams == publicIota.levelParams do
    return .malformed (Name.str privateCarrierName "levels")
  let mapping := #[(publicCarrierName, privateCarrierName),
    (constructorPair.model, privateConstructorName),
    (recursorPair.model, privateRecursorName), (iota.name, privateIotaName)]
  unless privateCarrier.type == publicCarrier.type do
    return .malformed (Name.str privateCarrierName "type")
  unless privateConstructor.type == rewriteCertificateNames mapping publicConstructor.type do
    return .malformed privateConstructorName
  unless privateRecursor.type == rewriteCertificateNames mapping publicRecursor.type do
    return .malformed privateRecursorName
  unless privateIota.type == rewriteCertificateNames mapping publicIota.type do
    return .malformed privateIotaName
  let (parameters, result) := openForalls
    ((`_check.oneLayerCertificate).append ownerType.name) publicCarrier.type
  unless parameters.size == ownerType.numParams + ownerType.numIndices do
    return .malformed publicCarrierName
  let .sort carrierLevel := result | return .malformed publicCarrierName
  let levels := publicCarrier.levelParams.map Level.param
  let parameterValues := parameters.map (fun binder => binder.value)
  let publicCarrierType := mkAppN (.const publicCarrierName levels) parameterValues
  let privateCarrierType := mkAppN (.const privateCarrierName levels) parameterValues
  let publicValue : OpenBinder :=
    { name := `public, type := publicCarrierType, info := .default
      value := mkFVar (FVarId.mk ((`_check.oneLayerPublic).append ownerType.name)) }
  let privateValue : OpenBinder :=
    { name := `private, type := privateCarrierType, info := .default
      value := mkFVar (FVarId.mk ((`_check.oneLayerPrivate).append ownerType.name)) }
  let expectedRoll := closeForalls (parameters.push publicValue) privateCarrierType
  let expectedUnroll := closeForalls (parameters.push privateValue) publicCarrierType
  unless roll.type == expectedRoll do return .malformed rollName
  unless unroll.type == expectedUnroll do return .malformed unrollName
  let rollApp := mkAppN (.const rollName levels) (parameterValues.push publicValue.value)
  let unrollRollApp := mkAppN (.const unrollName levels) (parameterValues.push rollApp)
  let unrollRollBody := mkAppN (.const ``Eq [carrierLevel])
    #[publicCarrierType, unrollRollApp, publicValue.value]
  unless unrollRoll.type == closeForalls (parameters.push publicValue) unrollRollBody do
    return .malformed unrollRollName
  let unrollApp := mkAppN (.const unrollName levels) (parameterValues.push privateValue.value)
  let rollUnrollApp := mkAppN (.const rollName levels) (parameterValues.push unrollApp)
  let rollUnrollBody := mkAppN (.const ``Eq [carrierLevel])
    #[privateCarrierType, rollUnrollApp, privateValue.value]
  unless rollUnroll.type == closeForalls (parameters.push privateValue) rollUnrollBody do
    return .malformed rollUnrollName
  return .valid

/-- Recognize the complete serialized simultaneous family boundary.  The
family root comes from the first source owner, but every member, constructor,
and rule slot is recovered by its source owner/key.  Seeing any prefix commits
the checker to validating the whole certificate; a partial family is never
interpreted as legacy mutual output. -/
def phase1MutualOneLayerCertificate (declarations : DeclarationTypes)
    (ownerTypes : Array EIndType) (constructors : Array ECtor) (recursors : Array ERec)
    (normalizer : ExactNormalizationEnv) (family : Family) : Phase1OneLayerCertificate := Id.run do
  let some first := ownerTypes[0]? | return .absent
  let root := Name.str (Naming.modelName first.name) "_impl"
  let support := #[Name.str root "tag", Name.str root "aux"]
  let memberRoot := fun owner => Name.str root (lastStr owner)
  let privateSelf := fun owner => Name.str (memberRoot owner) "self"
  let privateRecursor := fun owner => Name.str (memberRoot owner) "rec"
  let privateConstructor := fun owner constructor =>
    Name.str (Name.str (memberRoot owner) "ctor") (lastStr constructor)
  let privateIota := fun owner constructor =>
    Name.str (Name.str (memberRoot owner) "rec_iota") (lastStr constructor)
  let privateRule := fun owner constructor =>
    Name.str (Name.str (memberRoot owner) "rule") (lastStr constructor)
  let roll := fun owner => Name.str (memberRoot owner) "roll"
  let unroll := fun owner => Name.str (memberRoot owner) "unroll"
  let unrollRoll := fun owner => Name.str (memberRoot owner) "unroll_roll"
  let rollUnroll := fun owner => Name.str (memberRoot owner) "roll_unroll"
  -- `tag` and `aux` are shared with every legacy mutual encoding.  Only a
  -- member-local adapter slot commits the stream to this new certificate.
  let mut certificateNames : Array Name := #[]
  for ownerType in ownerTypes do
    certificateNames := certificateNames ++ #[privateSelf ownerType.name,
      privateRecursor ownerType.name, roll ownerType.name, unroll ownerType.name,
      unrollRoll ownerType.name, rollUnroll ownerType.name]
    for constructor in constructors do
      if constructor.induct == ownerType.name then
        certificateNames := certificateNames.push
          (privateConstructor ownerType.name constructor.name)
    if let some recursor := recursors.find? fun recursor =>
        recursor.name == Name.str ownerType.name "rec" then
      for rule in recursor.rules do
        certificateNames := certificateNames ++ #[privateIota ownerType.name rule.ctor,
          privateRule ownerType.name rule.ctor]
  unless certificateNames.any declarations.contains do return .absent
  unless ownerTypes.size ≥ 2 do return .malformed root
  let all := ownerTypes.map (·.name)
  unless ownerTypes.all fun ownerType =>
      ownerType.all.toArray == all && ownerType.numIndices == 0 && ownerType.numNested == 0 &&
        ownerType.isRec && !ownerType.isUnsafe && ownerType.numParams == first.numParams do
    return .malformed root
  let mut anyChanged := false
  let mut edges : Array (Name × Name) := #[]
  for ownerType in ownerTypes do
    let (_, carrierResult) := openForalls
      ((`_check.mutualOneLayerShape).append ownerType.name) ownerType.type
    let .sort carrierLevel := carrierResult | return .malformed (privateSelf ownerType.name)
    unless carrierLevel.normalize.isNeverZero do
      return .malformed (privateSelf ownerType.name)
    let ownerConstructors := constructors.filter (·.induct == ownerType.name)
    unless ownerConstructors.size == ownerType.ctors.length do
      return .malformed (privateSelf ownerType.name)
    let mut changed := false
    for constructor in ownerConstructors do
      let (binders, _) := openForalls
        ((`_check.mutualOneLayerFields).append constructor.name) constructor.type
      unless binders.size == constructor.numParams + constructor.numFields do
        return .malformed (privateConstructor ownerType.name constructor.name)
      let fields := binders.extract constructor.numParams binders.size
      let fieldTypes := fields.map (·.type)
      let fieldValues := fields.map (·.value)
      -- No count of recursive fields is asked: the generator proves a rule
      -- with as many equality eliminations as the constructor has recursive
      -- fields.  What is still required of them is independence, checked one
      -- field at a time immediately below.
      for fieldIndex in [:fields.size] do
        let normalized := normalizer.whnf fieldTypes[fieldIndex]!
        let target? := all.find? fun candidate =>
          normalized.getAppFn.constName? == some candidate &&
            normalized.getAppArgs.size == first.numParams
        if target?.isNone && all.any (fieldTypes[fieldIndex]!.getUsedConstants.contains ·) then
          return .malformed (privateConstructor ownerType.name constructor.name)
        if target?.isSome then
          edges := edges.push (ownerType.name, target?.get!)
          let fieldId := fieldValues[fieldIndex]!.fvarId!
          for later in [fieldIndex + 1:fields.size] do
            if fieldTypes[later]!.containsFVar fieldId then
              return .malformed (privateConstructor ownerType.name constructor.name)
          changed := true
    anyChanged := anyChanged || (ownerType.ctors.length == 1 && changed)
  unless anyChanged do return .malformed root
  for source in all do
    let mut reached : Std.HashSet Name := { source }
    let mut progress := true
    while progress do
      progress := false
      for edge in edges do
        if reached.contains edge.1 && !reached.contains edge.2 then
          reached := reached.insert edge.2
          progress := true
    unless all.all reached.contains do return .malformed root
  let unique := fun name => match declarations.findD name #[] with
    | #[declaration] => some declaration
    | _ => none
  for name in support do
    let some declaration := unique name | return .malformed name
    unless declaration.kind == .induct do return .malformed name
  for memberIndex in [:ownerTypes.size] do
    let ownerType := ownerTypes[memberIndex]!
    let owner := ownerType.name
    let publicCarrierName := Naming.modelName owner
    let some publicCarrier := unique publicCarrierName
      | return .malformed publicCarrierName
    let some privateCarrier := unique (privateSelf owner)
      | return .malformed (privateSelf owner)
    let some privateRec := unique (privateRecursor owner)
      | return .malformed (privateRecursor owner)
    let some rollDecl := unique (roll owner) | return .malformed (roll owner)
    let some unrollDecl := unique (unroll owner) | return .malformed (unroll owner)
    let some sectionDecl := unique (unrollRoll owner)
      | return .malformed (unrollRoll owner)
    let some retractionDecl := unique (rollUnroll owner)
      | return .malformed (rollUnroll owner)
    unless privateCarrier.kind == .defn && privateCarrier.safety? == some "safe" &&
        privateRec.kind == .defn && privateRec.safety? == some "safe" &&
        rollDecl.kind == .defn && rollDecl.safety? == some "safe" &&
        unrollDecl.kind == .defn && unrollDecl.safety? == some "safe" &&
        sectionDecl.kind == .thm && retractionDecl.kind == .thm do
      return .malformed (privateSelf owner)
    unless privateCarrier.levelParams == publicCarrier.levelParams &&
        privateCarrier.type == publicCarrier.type do
      return .malformed (privateSelf owner)
    let some publicRecPair := family.correspondence.recursors.find? fun pair =>
        pair.owner == Name.str owner "rec"
      | return .malformed (privateRecursor owner)
    let some publicRec := unique publicRecPair.model
      | return .malformed publicRecPair.model
    unless privateRec.levelParams == publicRec.levelParams do
      return .malformed (privateRecursor owner)
    let ownerConstructors := constructors.filter (·.induct == owner)
    unless ownerConstructors.size == ownerType.ctors.length do
      return .malformed (privateSelf owner)
    for constructor in ownerConstructors do
      let privateName := privateConstructor owner constructor.name
      let some privateCtor := unique privateName | return .malformed privateName
      let some publicCtorPair := family.correspondence.constructors.find? fun pair =>
          pair.owner == constructor.name
        | return .malformed privateName
      let some publicCtor := unique publicCtorPair.model | return .malformed publicCtorPair.model
      unless privateCtor.kind == .defn && privateCtor.safety? == some "safe" &&
          privateCtor.levelParams == publicCtor.levelParams do
        return .malformed privateName
    let some sourceRec := recursors.find? fun recursor =>
        recursor.name == Name.str owner "rec"
      | return .malformed (privateRecursor owner)
    for ruleIndex in [0:sourceRec.rules.length] do
      let sourceRule := sourceRec.rules[ruleIndex]!
      let iotaName := privateIota owner sourceRule.ctor
      let ruleName := privateRule owner sourceRule.ctor
      let some iotaDecl := unique iotaName | return .malformed iotaName
      let some ruleDecl := unique ruleName | return .malformed ruleName
      let some publicIota := family.correspondence.iotas.find? fun iota =>
          iota.recursor == sourceRec.name && iota.ruleIndex == ruleIndex
        | return .malformed iotaName
      let some publicIotaDecl := unique publicIota.name | return .malformed publicIota.name
      unless iotaDecl.kind == .thm && ruleDecl.kind == .thm &&
          iotaDecl.levelParams == publicIotaDecl.levelParams &&
          ruleDecl.levelParams == iotaDecl.levelParams && ruleDecl.type == iotaDecl.type do
        return .malformed ruleName
    let (parameters, result) := openForalls
      ((`_check.mutualOneLayerCertificate).append owner) publicCarrier.type
    unless parameters.size == ownerType.numParams do return .malformed publicCarrierName
    let .sort carrierLevel := result | return .malformed publicCarrierName
    let levels := publicCarrier.levelParams.map Level.param
    let parameterValues := parameters.map (·.value)
    let publicCarrierType := mkAppN (.const publicCarrierName levels) parameterValues
    let privateCarrierType := mkAppN (.const (privateSelf owner) levels) parameterValues
    let publicValue : OpenBinder :=
      { name := `public, type := publicCarrierType, info := .default
        value := mkFVar (FVarId.mk ((`_check.mutualPublic).append owner)) }
    let privateValue : OpenBinder :=
      { name := `private, type := privateCarrierType, info := .default
        value := mkFVar (FVarId.mk ((`_check.mutualPrivate).append owner)) }
    let expectedRoll := closeForalls (parameters.push publicValue) privateCarrierType
    let expectedUnroll := closeForalls (parameters.push privateValue) publicCarrierType
    unless rollDecl.type == expectedRoll do return .malformed (roll owner)
    unless unrollDecl.type == expectedUnroll do return .malformed (unroll owner)
    let rollApp := mkAppN (.const (roll owner) levels) (parameterValues.push publicValue.value)
    let unrollRollApp := mkAppN (.const (unroll owner) levels)
      (parameterValues.push rollApp)
    let sectionBody := mkAppN (.const ``Eq [carrierLevel])
      #[publicCarrierType, unrollRollApp, publicValue.value]
    unless sectionDecl.type == closeForalls (parameters.push publicValue) sectionBody do
      return .malformed (unrollRoll owner)
    let unrollApp := mkAppN (.const (unroll owner) levels)
      (parameterValues.push privateValue.value)
    let rollUnrollApp := mkAppN (.const (roll owner) levels)
      (parameterValues.push unrollApp)
    let retractionBody := mkAppN (.const ``Eq [carrierLevel])
      #[privateCarrierType, rollUnrollApp, privateValue.value]
    unless retractionDecl.type == closeForalls (parameters.push privateValue) retractionBody do
      return .malformed (rollUnroll owner)
  return .valid

end InductiveModels.Check
