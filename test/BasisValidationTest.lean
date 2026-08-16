import InductiveModels.Driver

open Lean Meta InductiveModels

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def addInductiveRecord (declaration : Declaration) : MetaM EDecl := do
  let .inductDecl _ _ types _ := declaration
    | throwError "test declaration is not inductive"
  match (← getEnv).addDeclCore 0 0 declaration none true with
  | .error exception =>
    throwError "cannot mint test declaration: {← (exception.toMessageData {}).toString}"
  | .ok env =>
    setEnv env
    indEDecl (types.toArray.map (·.name))

def basisDeclarations : Array Declaration :=
  #[eqDecl, natDecl, punitDecl, psigmaPrimeDecl]

def basisNames : Array Name := #[`Eq, `Nat, `PUnit, `PSigma']

/-- One raw owner which consumes all four ordinary inductive basis interfaces.
The fifth member, `Quot`, is a kernel-special declaration rather than a type
former used by this fixture. -/
def consumerDeclaration : Declaration :=
  let nat : Expr := .const `Nat []
  let zero : Expr := .const `Nat.zero []
  let equality := mkAppN (.const `Eq [.succ .zero]) #[nat, zero, zero]
  let punit : Expr := .const `PUnit [.succ .zero]
  let fibre := .lam `n nat nat .default
  let pair := mkAppN (.const `PSigma' [.succ .zero, .succ .zero]) #[nat, fibre]
  let owner : Expr := .const `BasisConsumer []
  let constructorType := .forallE `equality equality
    (.forallE `number nat (.forallE `unit punit
      (.forallE `pair pair owner .default) .default) .default) .default
  .inductDecl [] 0
    [{ name := `BasisConsumer, type := .sort (.succ .zero),
       ctors := [{ name := `BasisConsumer.mk, type := constructorType }] }] false

/-- Change exported constructor metadata which `toDeclaration` deliberately
does not use. The replay remains kernel-valid, but the raw basis contract is
no longer canonical. -/
def corruptBasisRecord : EDecl → EDecl
  | .induct types (constructor :: constructors) recursors =>
    .induct types ({ constructor with numFields := constructor.numFields + 1 } :: constructors)
      recursors
  | declaration => declaration

def corruptBasisRecursor : EDecl → EDecl
  | .induct types constructors (recursor :: recursors) =>
    .induct types constructors
      ({ recursor with numMinors := recursor.numMinors + 1 } :: recursors)
  | declaration => declaration

def makeRawFixture (corrupt? used? : Bool) (target : Name) : IO Export := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<basis-validation-fixture>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (records, _) ← Core.CoreM.toIO (MetaM.run' do
    let mut records : Array EDecl := #[]
    for declaration in basisDeclarations do
      records := records.push (← addInductiveRecord declaration)
    if used? then records := records.push (← addInductiveRecord consumerDeclaration)
    return records) context { env }
  let selected := if used? then records else records.filter (·.names.contains target)
  return { metaLine := .null, decls := selected.map fun record =>
    if corrupt? && record.names.contains target then corruptBasisRecord record else record }

/-- An owner which names no basis constant in its own declaration but whose
model is written in all four of them — the Church route's shape. It can
therefore stand *in front of* every basis record, which
[`InductiveModels.consumerDeclaration`] cannot: that one has the basis types as
its own constructor fields and could not replay ahead of them. -/
def lateConsumerDeclaration : Declaration :=
  let owner : Expr := .const `LateConsumer []
  .inductDecl [] 0
    [{ name := `LateConsumer, type := .sort (.succ .zero),
       ctors := [{ name := `LateConsumer.zero, type := owner },
                 { name := `LateConsumer.succ,
                   type := .forallE `n owner owner .default }] }] false

/-- **The four basis records behind the owner whose model is written in them.**

Generation writes its own canonical basis declaration at the first point one is
needed, so the owner models here even though the input declares the basis
behind it — and the input's own record is then dropped where it stands. Which
of the two happens is the whole question this ordering exists to ask: a record
that is the canonical declaration is dropped silently, and one that is not
rejects the run rather than letting this tool's declaration silently take the
place of the input's. -/
def makeLateBasisFixture (corrupt? : Bool) (target : Name) : IO Export := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<basis-validation-late-fixture>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (records, _) ← Core.CoreM.toIO (MetaM.run' do
    let mut records : Array EDecl := #[← addInductiveRecord lateConsumerDeclaration]
    for declaration in basisDeclarations do
      records := records.push (← addInductiveRecord declaration)
    return records) context { env }
  return { metaLine := .null, decls := records.map fun record =>
    if corrupt? && record.names.contains target then corruptBasisRecord record else record }

/-- The exact diagnostic a dropped record which is not the canonical
declaration must carry. Spelled out here so a reworded rejection has to be
re-read rather than silently accepted. -/
def noncanonicalBasisRejection : String :=
  "generation already wrote the canonical basis declaration at this name, \
   and this input record is not that declaration"

/-- How often the output declares `name`. -/
def declarationCount (records : Array EDecl) (name : Name) : Nat :=
  records.foldl (init := 0) fun count record =>
    if record.names.contains name then count + 1 else count

/-- One declaration of the W fragment, which is what this tool writes under the
logical names it shares with the input. -/
def wCoreRecord (name : Name) : IO EDecl := do
  let .ok fragment := InductiveModels.parse wCoreText
    | throw <| IO.userError "the W core fragment does not parse"
  let some record := fragment.decls.find? (·.names.contains name)
    | throw <| IO.userError s!"the W core fragment has no {name}"
  return record

/-- **The canonical `Iff` and `propext` are the fragment's own.**

The W arm splices [`InductiveModels.wCoreText`] under the shared logical names, so
that fragment *is* the declaration this tool writes under `Iff` and `propext`.
`iffDecl` and `propextType` are this tool's own independent statement of the
same two, written without parsing the fragment: `canonicalSpliceInductives`
names `Iff` by `iffDecl`, and every rule keyed on
[`InductiveModels.canonicalBasisNames`] therefore reads `iffDecl`'s names. That
is sound only while the two agree. A Lean release that spelled either of them
differently, down to the binder Lean gives an anonymous arrow argument, has to
fail here rather than in a W target's decline.

The third check is the other half of the contract: a record which is not the
canonical declaration is not canonical, so it is never dropped against one. -/
def runCanonicalLogicalChecks : IO (Bool × Bool × Bool) := do
  let fragmentIff ← wCoreRecord `Iff
  let fragmentPropext ← wCoreRecord `propext
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<basis-validation-logical>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Core.CoreM.toIO (MetaM.run' do
    let canonicalIff ← isCanonicalInductiveRecord `Iff iffDecl fragmentIff
    let noncanonicalIff ←
      isCanonicalInductiveRecord `Iff iffDecl (corruptBasisRecord fragmentIff)
    let _ ← addInductiveRecord eqDecl
    let _ ← addInductiveRecord iffDecl
    let expected ← propextType `Eq
    let canonicalPropext ← match fragmentPropext with
      | .ax _ [] type _ => isDefEq type expected
      | _ => pure false
    return (canonicalIff, canonicalPropext, !noncanonicalIff)) context { env }
  return result

def runRaw (input : Export) : IO (Array EDecl × Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<basis-validation-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, _) ← Core.CoreM.toIO
    (MetaM.run' (runFilter input false {})) context { env }
  return result

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut state : TestState := {}
  let covered := ({} : Std.HashSet Name).insert `Eq |>.insert `Ordinary
  let generated := ({} : Std.HashSet Name).insert `Nat |>.insert `Generated
  state := state.check "covered malformed basis remains unsupported" <|
    declineIsUnsupported covered {} `Eq
  state := state.check "generated malformed basis remains unsupported" <|
    declineIsUnsupported {} generated `Nat
  state := state.check "covered ordinary decline is fulfilled" <|
    !declineIsUnsupported covered {} `Ordinary
  state := state.check "generated ordinary decline is fulfilled" <|
    !declineIsUnsupported {} generated `Generated
  state := state.check "unfulfilled ordinary decline remains unsupported" <|
    declineIsUnsupported {} {} `Unfulfilled
  for target in basisNames do
    let exact ← makeRawFixture false false target
    let (exactOutput, exactReport) ← runRaw exact
    state := state.check s!"exact unused {target} is exempt" <|
      exactReport.exempt.any (·.1 == target) &&
        !exactReport.declined.any (·.1 == target)
    state := state.check s!"validation alias for {target} does not escape" <|
      !({ metaLine := .null, decls := exactOutput } : Export).render.contains
        "_inductive_models_basis_validation"

    let malformed ← makeRawFixture true false target
    let (_, malformedReport) ← runRaw malformed
    state := state.check s!"malformed unused {target} is unsupported" <|
      malformedReport.declined.any (·.1 == target) &&
        !malformedReport.exempt.any (·.1 == target)

    let malformedUsed ← makeRawFixture true true target
    let (_, usedReport) ← runRaw malformedUsed
    state := state.check s!"malformed consumed {target} blocks generation" <|
      usedReport.declined.any (·.1 == target) &&
        !usedReport.exempt.any (·.1 == target) &&
        !usedReport.generated.any (·.1 == `BasisConsumer)

  let exactEq ← makeRawFixture false false `Eq
  let recursorCorrupt := { exactEq with decls := exactEq.decls.map corruptBasisRecursor }
  let (_, recursorReport) ← runRaw recursorCorrupt
  state := state.check "malformed unused Eq recursor metadata is unsupported" <|
    recursorReport.declined.any (·.1 == `Eq) &&
      !recursorReport.exempt.any (·.1 == `Eq)

  let exactUsed ← makeRawFixture false true `Eq
  let (_, exactUsedReport) ← runRaw exactUsed
  state := state.check "canonical four-inductive-basis consumer generates" <|
    basisNames.all fun target => exactUsedReport.exempt.any (·.1 == target)
  state := state.check "canonical basis is not declined" <|
    basisNames.all fun target => !exactUsedReport.declined.any (·.1 == target)
  state := state.check "canonical consumed basis permits generation" <|
    exactUsedReport.generated.any (·.1 == `BasisConsumer)

  -- **The basis behind its consumer**, which is the ordering the canonical
  -- declaration is written early for.
  let lateExact ← makeLateBasisFixture false `Eq
  let (lateOutput, lateReport) ← runRaw lateExact
  state := state.check "late canonical basis still models its consumer" <|
    lateReport.unreplayable.isNone && lateReport.generated.any (·.1 == `LateConsumer)
  state := state.check "late canonical basis is exempt, not declined" <|
    basisNames.all fun target =>
      lateReport.exempt.any (·.1 == target) && !lateReport.declined.any (·.1 == target)
  state := state.check "a dropped late basis record leaves exactly one declaration" <|
    basisNames.all fun target => declarationCount lateOutput target == 1

  for target in basisNames do
    let lateMalformed ← makeLateBasisFixture true target
    let (lateMalformedOutput, lateMalformedReport) ← runRaw lateMalformed
    state := state.check s!"a noncanonical late {target} rejects the run" <|
      lateMalformedReport.unreplayable.any fun why =>
        (why.splitOn noncanonicalBasisRejection).length == 2
    state := state.check s!"a rejected late {target} writes no output" <|
      lateMalformedOutput == lateMalformed.decls

  let (canonicalIff, canonicalPropext, refusesNoncanonicalIff) ← runCanonicalLogicalChecks
  state := state.check "the canonical Iff is the W fragment's own declaration" canonicalIff
  state := state.check "the canonical propext is the W fragment's own statement" canonicalPropext
  state := state.check "a noncanonical Iff record is not canonical" refusesNoncanonicalIff

  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  IO.println s!"basis validation: {state.passed} passed, {state.failed.size} failed"
  return if state.failed.isEmpty then 0 else 1
