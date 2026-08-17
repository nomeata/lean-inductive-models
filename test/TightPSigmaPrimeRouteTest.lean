import InductiveModels.Driver
import InductiveModels.Check

namespace TightPSigmaPrimeRouteTest

open Lean Meta InductiveModels

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def readExport (path : String) : IO Export := do
  let .ok result := parse (← IO.FS.readFile path)
    | throw <| IO.userError s!"cannot parse {path}"
  return result

def runExport (input : Export) (generation : Cli.Config := {}) : IO (Export × Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<tight-ppsigma-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((declarations, report), _) ← Core.CoreM.toIO
    (MetaM.run' (runFilter input false generation)) context { env }
  return ({ input with decls := declarations }, report)

def withoutDeclaration (input : Export) (name : Name) : Export :=
  { input with decls := input.decls.filter (!·.names.contains name) }

def declarationValue? (input : Export) (name : Name) : Option Expr := do
  let .defn got _ _ value .. ← input.decls.find? (·.names.contains name) | none
  if got == name then some value else none

def declarationType? (input : Export) (name : Name) : Option Expr := do
  let declaration ← input.decls.find? (·.names.contains name)
  match declaration with
  | .ax got _ type _ | .quot got _ type _ => if got == name then some type else none
  | .defn got _ type .. | .thm got _ type .. | .opaq got _ type .. =>
      if got == name then some type else none
  | .induct types constructors recursors =>
      (types.find? (·.name == name)).map (·.type) <|>
      (constructors.find? (·.name == name)).map (·.type) <|>
      (recursors.find? (·.name == name)).map (·.type)

partial def containsConst (target : Name) : Expr → Bool
  | .const name _ => name == target
  | .proj _ _ value => containsConst target value
  | .app function argument => containsConst target function || containsConst target argument
  | .lam _ type body _ | .forallE _ type body _ =>
      containsConst target type || containsConst target body
  | .letE _ type value body _ =>
      containsConst target type || containsConst target value || containsConst target body
  | .mdata _ body => containsConst target body
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => false

partial def containsProjection (owner : Name) (fieldIndex : Nat) : Expr → Bool
  | .proj gotOwner gotField value =>
      (gotOwner == owner && gotField == fieldIndex) ||
        containsProjection owner fieldIndex value
  | .app function argument =>
      containsProjection owner fieldIndex function || containsProjection owner fieldIndex argument
  | .lam _ type body _ | .forallE _ type body _ =>
      containsProjection owner fieldIndex type || containsProjection owner fieldIndex body
  | .letE _ type value body _ =>
      containsProjection owner fieldIndex type || containsProjection owner fieldIndex value ||
        containsProjection owner fieldIndex body
  | .mdata _ body => containsProjection owner fieldIndex body
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => false

def ownerPasses (input : Export) (owner : Name) : Bool :=
  (Check.check input).all (·.familyOwner != owner)

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let raw ← readExport "test/fixtures/inductive-models/tight_psigma_prime.ndjson"
  let noBasis := withoutDeclaration raw `PSigma'
  let (generated, report) ← runExport noBasis
  let names := generated.decls.flatMap (·.names.toArray)
  let pi2Projection0 := Naming.projectionName `PI2 0
  let pi2Projection1 := Naming.projectionName `PI2 1
  let pi2Rule0 := Naming.projectionIotaName `PI2 0
  let pi2Rule1 := Naming.projectionIotaName `PI2 1
  let depProjection0 := Naming.projectionName `PIDep 0
  let depProjection1 := Naming.projectionName `PIDep 1
  let depRule0 := Naming.projectionIotaName `PIDep 0
  let depRule1 := Naming.projectionIotaName `PIDep 1
  let mut state : TestState := {}

  let tightSupport :=
    #[`PSigma', `PSigma'.mk, `PSigma'.rec, `PSigma'.fst, `PSigma'.snd,
      `PSigma'.fst_mk, `PSigma'.snd_mk, `PSigma'.rec', `PSigma'.rec'_mk,
      -- The binder-free pair travels with it wherever a rung is constant, and
      -- its bundle is one derived declaration where the tight pair's is six.
      `PProd', `PProd'.mk, `PProd'.rec, `PProd'.rec']
  state := state.check "missing tight pair is spliced with its complete support bundle" <|
    tightSupport.all names.contains &&
      report.spliced.any fun (_, spliced) => tightSupport.all spliced.contains
  state := state.check "both tight families generate" <|
    #[`PI2, `PIDep].all fun owner =>
      report.generated.any (·.1 == owner) && !report.declined.any (·.1 == owner)
  state := state.check "both complete interfaces pass the literal checker" <|
    ownerPasses generated `PI2 && ownerPasses generated `PIDep
  state := state.check "every source field gets a projection and iota theorem" <|
    #[pi2Projection0, pi2Projection1, pi2Rule0, pi2Rule1,
      depProjection0, depProjection1, depRule0, depRule1].all names.contains
  -- **The two owners are stored in different pairs, and that is the claim.**
  -- `PIDep`'s second field's type mentions its first, so its rung's family is a
  -- real function and the rung is a `PSigma'`. `PI2`'s two fields are
  -- independent, so its family would be constant and the rung is a `PProd'` —
  -- the same pair with no binder, at the same sort. Asserting `PSigma'` for
  -- both would pass on a run that had stopped distinguishing them, which is
  -- the whole thing this fixture exists to hold apart.
  state := state.check "the dependent carrier is stored in the tight pair" <|
    (declarationValue? generated (Naming.modelName `PIDep)).any (containsConst `PSigma')
  state := state.check "the independent carrier is stored in the binder-free pair" <|
    (declarationValue? generated (Naming.modelName `PI2)).any (containsConst `PProd') &&
      (declarationValue? generated (Naming.modelName `PI2)).all
        (!containsConst `PSigma' ·)
  state := state.check "selectors use each carrier's own primitive projections" <|
    (declarationValue? generated pi2Projection0).any (containsProjection `PProd' 0) &&
      (declarationValue? generated pi2Projection1).any (containsProjection `PProd' 1) &&
      (declarationValue? generated depProjection0).any (containsProjection `PSigma' 0) &&
      (declarationValue? generated depProjection1).any (containsProjection `PSigma' 1)
  state := state.check "nonrecursive dependent field rules are both literal" <|
    (declarationType? generated depRule0).any (!containsConst ``Eq.rec ·) &&
      (declarationType? generated depRule1).any (!containsConst ``Eq.rec ·)
  state := state.check "tight families retain structure eta" <|
    #[Naming.etaName `PI2, Naming.etaName `PIDep].all names.contains

  let (presentBasisOutput, presentBasisReport) ← runExport raw
  state := state.check "an exact input PSigma' is accepted and exempt" <|
    presentBasisReport.exempt.any (·.1 == `PSigma') &&
      presentBasisReport.generated.any (·.1 == `PI2) &&
      ownerPasses presentBasisOutput `PI2 && ownerPasses presentBasisOutput `PIDep

  let (noBasicOutput, noBasicReport) ← runExport noBasis { basic := false }
  state := state.check "PSigma' is a simple-model basis splice, not a --basic model" <|
    noBasicReport.generated.any (·.1 == `PI2) &&
      noBasicReport.generated.any (·.1 == `PIDep) &&
      noBasicOutput.decls.any (·.names.contains `PSigma') &&
      ownerPasses noBasicOutput `PI2 && ownerPasses noBasicOutput `PIDep

  IO.println s!"tight PSigma': {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1

end TightPSigmaPrimeRouteTest
