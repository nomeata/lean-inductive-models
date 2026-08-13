import Modelgen.Driver

open Lean Meta Modelgen

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def addInductiveRecord (declaration : Declaration) : MetaM EDecl := do
  let .inductDecl _ _ types _ := declaration
    | throwError "test declaration is not inductive"
  match (← getEnv).addDeclCore 0 declaration none true with
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
        "_modelgen_basis_validation"

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

  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  IO.println s!"basis validation: {state.passed} passed, {state.failed.size} failed"
  return if state.failed.isEmpty then 0 else 1
