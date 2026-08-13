import Modelgen.Driver
import Modelgen.Order

/-!
# Exact export-syntax normalization controls

The format-only checker may reproduce the kernel's weak-head observations, but
only from syntax present in the export.  This test pins that boundary directly:
transparent definitions unfold, opaque definitions do not, cycles terminate,
and declaration types remain literal.  It also exercises the two regressions
which motivated the shared normalizer: `SvIx` is proposition-valued through a
transparent former alias and `Flat`'s generated projection iotas contain
β-normalized local binder types.
-/

open Lean Meta Modelgen

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def declarationType? (x : Export) (name : Name) : Option Expr :=
  x.decls.findSome? fun declaration => match declaration with
    | .ax got _ type _ | .quot got _ type _ => if got == name then some type else none
    | .defn got _ type .. | .thm got _ type .. | .opaq got _ type .. =>
      if got == name then some type else none
    | .induct types constructors recursors =>
      (types.find? (·.name == name)).map (·.type) <|>
      (constructors.find? (·.name == name)).map (·.type) <|>
      (recursors.find? (·.name == name)).map (·.type)

def readExport (path : String) : IO Export := do
  let .ok result := parse (← IO.FS.readFile path) (analyse := false)
    | throw <| IO.userError s!"cannot parse {path}"
  return result

def generatedExport (input : Export) : IO (Export × Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<export-syntax-normalization-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((declarations, report), _) ← Core.CoreM.toIO
    (MetaM.run' (runFilter input false {})) context { env }
  match Order.reorder { input with decls := declarations } with
  | .ok output => return (output, report)
  | .error failure =>
    throw <| IO.userError s!"cannot order generated export: {repr failure}"

def run (root : String) : IO UInt32 := do
  let literalType :=
    mkApp (.lam `ignored (.sort (.succ .zero)) (.sort .zero) .default) (.sort .zero)
  let synthetic : Export :=
    { metaLine := Json.null
      decls := #[
        .defn `Transparent [] (.sort (.succ .zero)) (.sort .zero) .abbrev "safe" [],
        .opaq `Opaque [] (.sort (.succ .zero)) (.sort .zero) false [],
        .defn `Self [] (.sort (.succ .zero)) (.const `Self []) (.regular 0) "safe" [],
        .defn `CycleA [] (.sort (.succ .zero)) (.const `CycleB []) (.regular 0) "safe" [],
        .defn `CycleB [] (.sort (.succ .zero)) (.const `CycleA []) (.regular 0) "safe" [],
        .defn `Literal [] literalType (.sort .zero) .abbrev "safe" []] }
  let normalizer := synthetic.exactNormalizationEnv
  let mut state : TestState := {}
  state := state.check "transparent exported definition unfolds"
    (normalizer.whnf (.const `Transparent []) == .sort .zero)
  state := state.check "opaque exported definition remains opaque"
    (normalizer.whnf (.const `Opaque []) == .const `Opaque [])
  state := state.check "self-recursive transparent definition terminates"
    (normalizer.whnf (.const `Self []) == .const `Self [])
  state := state.check "cyclic transparent definitions terminate"
    (normalizer.whnf (.const `CycleA []) == .const `CycleA [])
  state := state.check "beta-only face retains named public constants"
    (normalizer.beta
      (mkApp (.lam `ignored (.sort (.succ .zero)) (.const `Transparent []) .default)
        (.sort .zero)) == .const `Transparent [])
  state := state.check "beta-only face retains literal lets"
    (normalizer.beta
      (.letE `X (.sort (.succ .zero)) (.sort .zero) (.bvar 0) false) ==
        .letE `X (.sort (.succ .zero)) (.sort .zero) (.bvar 0) false)
  state := state.check "normalization does not rewrite declaration types"
    (declarationType? synthetic `Literal == some literalType)

  let prim ← readExport s!"{root}/test/fixtures/modelgen/prim_declines.ndjson"
  let some svIxDecl := prim.decls.findIdx? fun declaration =>
      declaration.names.contains `SvIx
    | throw <| IO.userError "prim_declines does not declare SvIx"
  let some svIxTable := Check.correspondenceAt? prim svIxDecl
    | throw <| IO.userError "SvIx has no correspondence"
  let svIxType := declarationType? prim `SvIx
  state := state.check "transparent Prop former has no illegal projections"
    svIxTable.projections.isEmpty
  state := state.check "SvIx public declaration type stays literal"
    (declarationType? prim `SvIx == svIxType)

  let flatInput ← readExport s!"{root}/test/fixtures/modelgen/nest_fam_arg.ndjson"
  let (flatOutput, flatReport) ← generatedExport flatInput
  let flatFamilyOwner := (`Flat._model._impl).mkNum 0
  let flatOwner := (`Flat._model._impl).mkNum 1
  let flatIotas := #[Naming.projectionIotaName flatOwner 0,
    Naming.projectionIotaName flatOwner 1]
  state := state.check "Flat exports both exact projection iotas"
    (flatIotas.all fun name => flatOutput.decls.any (·.names.contains name))
  state := state.check "Flat projection iotas check literally"
    ((Check.check flatOutput).all fun violation =>
      !(flatOwner.isPrefixOf violation.familyOwner))
  state := state.check "generated Flat owner checks through the source syntax overlay"
    (flatReport.generated.any (·.1 == flatFamilyOwner) && flatReport.stmtErrors.isEmpty)

  IO.println s!"export syntax normalization: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1

def main (args : List String) : IO UInt32 :=
  run (args.head?.getD ".")
