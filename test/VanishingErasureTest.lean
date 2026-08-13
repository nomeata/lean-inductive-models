import InductiveModels.Driver
import InductiveModels.Check
import InductiveModels.Order

/-!
# Focused test for βζ-dead owner mentions in internal erasures

Lean's nested specialisation can leave a field type such as
`(fun _ : T i => N) k`: the exported expression mentions `T`, but its reduct
does not.  The public constructor retains that exact expression.  Only an
internal erased skeleton or tuple spine may use its reduct and treat the field
as non-recursive.
-/

open Lean Meta InductiveModels

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (state : TestState) (label : String) (condition : Bool) : TestState :=
  if condition then { state with passed := state.passed + 1 }
  else { state with failed := state.failed.push label }

def readExport (path : String) : IO Export := do
  let .ok result := parse (← IO.FS.readFile path) (analyse := false)
    | throw <| IO.userError s!"cannot parse {path}"
  return result

def runExport (input : Export) : IO (Export × Report) := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<vanishing-erasure-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((declarations, report), _) ← Core.CoreM.toIO
    (MetaM.run' (runFilter input false {})) context { env }
  let output := { input with decls := declarations }
  let ordered ← match Order.reorder output with
    | .ok result => pure result
    | .error failure =>
      throw <| IO.userError s!"cannot order vanishing-erasure output: {repr failure}"
  return (ordered, report)

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

partial def hasVanishingDomain (owner : Name) : Expr → Bool
  | .forallE _ domain body _ =>
      (containsConst owner domain && erasureFieldDomain owner domain != domain) ||
        hasVanishingDomain owner body
  | _ => false

partial def hasHiddenBinderDomain (owner : Name) : Expr → Bool
  | .forallE _ domain body _ =>
      (containsConst owner domain && domain != headNorm domain &&
        (headNorm domain matches .forallE ..)) || hasHiddenBinderDomain owner body
  | _ => false

def inductiveMetadata? (input : Export) (owner : Name) : Option EIndType :=
  input.decls.findSome? fun declaration => match declaration with
    | .induct types _ _ => types.find? (·.name == owner)
    | _ => none

def constructorTypes (input : Export) (owner : Name) : Array Expr :=
  input.decls.foldl (init := #[]) fun result declaration =>
    match declaration with
    | .induct types constructors _ =>
      if types.any (·.name == owner) then
        result ++ (constructors.filter (owner.isPrefixOf ·.name)).map (·.type)
      else result
    | _ => result

def ownerPasses (input : Export) (owner : Name) : Bool :=
  (Check.check input).all (·.familyOwner != owner)

def generatedExactly (report : Report) (owner : Name) (count : Nat) : Bool :=
  report.generated.any fun entry => entry == (owner, count)

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let raw ← readExport "test/fixtures/lean-inductive-models/nest_fam_arg.ndjson"
  let (generated, report) ← runExport raw
  let auxName := fun (owner : Name) =>
    Name.str (Name.str (Name.str (Name.num (Name.str (Name.str owner "_model") "_impl") 0)
      "_model") "_impl") "aux"
  let skeletonName := fun (aux : Name) =>
    Name.str (Name.str (Name.str aux "_model") "_impl") "skel"
  let okAux := auxName `OK
  let keyAux := auxName `Key
  let okSkeleton := skeletonName okAux
  let keySkeleton := skeletonName keyAux
  let mut state : TestState := {}

  state := state.check "OK and Key auxiliary families model instead of declining" <|
    generatedExactly report okAux 10 && generatedExactly report keyAux 14 &&
      !report.declined.any fun (owner, _) => owner == okAux || owner == keyAux
  state := state.check "both erased skeletons model completely" <|
    generatedExactly report okSkeleton 14 && generatedExactly report keySkeleton 18
  state := state.check "public auxiliary constructors retain their literal redexes" <|
    #[okAux, keyAux].all fun owner =>
      (constructorTypes generated owner).any (hasVanishingDomain owner)
  state := state.check "internal skeleton constructors contain no erased owner" <|
    #[(okAux, okSkeleton), (keyAux, keySkeleton)].all fun (owner, skeleton) =>
      let types := constructorTypes generated skeleton
      !types.isEmpty && types.all fun type => !containsConst owner type
  state := state.check "literal model correspondence accepts auxiliaries and skeletons" <|
    #[okAux, keyAux, okSkeleton, keySkeleton].all (ownerPasses generated)
  state := state.check "all generated recursor statements stay literal" <|
    report.stmtChecked == 443 && report.stmtErrors.isEmpty
  state := state.check "a genuine indexed nested source is routed before Simple" <|
    (inductiveMetadata? raw `Ix).any (·.numNested > 0) &&
      generatedExactly report `Ix 15 &&
      !report.declined.any fun (owner, _) => owner == `Ix

  -- The same syntax at the ordinary non-indexed Type route.  `Dead.step` has
  -- one genuine recursive child followed by a field whose annotation mentions
  -- `Dead` but whose β-reduct is `N`; the tuple spine must count only the
  -- former.
  let nonindexedRaw ← readExport "test/fixtures/lean-inductive-models/nonindexed_vanishing.ndjson"
  let (nonindexedGenerated, nonindexedReport) ← runExport nonindexedRaw
  state := state.check "the raw non-indexed constructor retains a dead owner mention" <|
    (constructorTypes nonindexedRaw `Dead).any (hasVanishingDomain `Dead)
  state := state.check "the non-indexed tuple route models one real predecessor" <|
    generatedExactly nonindexedReport `Dead 6 &&
      !nonindexedReport.declined.any fun (owner, _) => owner == `Dead
  state := state.check "the non-indexed public interface checks literally" <|
    ownerPasses nonindexedGenerated `Dead && nonindexedReport.stmtChecked == 6 &&
      nonindexedReport.stmtErrors.isEmpty

  -- An indexed Type-family whose recursive field is infinitary only after β
  -- reduction. This is a simple (numNested = 0) kernel declaration, so arm C
  -- must expose the binder in its private skeleton while retaining the public
  -- constructor and recursor expressions literally.
  let hiddenRaw ← readExport "test/fixtures/lean-inductive-models/indexed_hidden_erasure.ndjson"
  let (hiddenGenerated, hiddenReport) ← runExport hiddenRaw
  let hiddenSkeleton := `Hidden._model._impl.skel
  state := state.check "the raw indexed constructor retains its hidden binder" <|
    (inductiveMetadata? hiddenRaw `Hidden).any (·.numNested == 0) &&
      (constructorTypes hiddenRaw `Hidden).any (hasHiddenBinderDomain `Hidden)
  state := state.check "the hidden-binder family and its skeleton both model" <|
    hiddenReport.generated.any (·.1 == `Hidden) &&
      hiddenReport.generated.any (·.1 == hiddenSkeleton) &&
      !hiddenReport.declined.any fun (owner, _) => owner == `Hidden || owner == hiddenSkeleton
  state := state.check "the public hidden-binder constructor stays literal" <|
    (constructorTypes hiddenGenerated `Hidden).any (hasHiddenBinderDomain `Hidden)
  state := state.check "the hidden-binder output passes exact model checking" <|
    ownerPasses hiddenGenerated `Hidden && ownerPasses hiddenGenerated hiddenSkeleton &&
      hiddenReport.stmtErrors.isEmpty

  -- Unit-level boundary controls.  These expressions need not elaborate: the
  -- erasure helper is intentionally raw syntax surgery over exported Exprs.
  let owner := `Boundary.Owner
  let ownerT := Expr.const owner []
  let natT := Expr.const ``Nat []
  let zero := Expr.const ``Nat.zero []
  let dead := Expr.app (Expr.lam `x ownerT natT .default) zero
  let hiddenBody := Expr.forallE `z natT ownerT .default
  let hidden := Expr.app (Expr.lam `x natT hiddenBody .default) zero
  let nestedBody := Expr.app (Expr.const ``List [.zero]) ownerT
  let nested := Expr.app (Expr.lam `x natT nestedBody .default) zero
  state := state.check "only a βζ-dead owner mention is normalized" <|
    erasureFieldDomain owner dead == natT && !erasureRecursive owner dead
  state := state.check "a βζ-revealed binder is exposed for the internal erasure" <|
    erasureFieldDomain owner hidden == headNorm hidden && erasureRecursive owner hidden &&
      (headNorm hidden matches .forallE ..)
  state := state.check "a surviving nested occurrence remains on the nested path" <|
    erasureFieldDomain owner nested == headNorm nested && erasureRecursive owner nested &&
      !(headNorm nested).getAppFn.isConstOf owner

  IO.println s!"vanishing erasure: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  unless state.failed.isEmpty do
    IO.eprintln s!"wanted auxiliaries: {okAux}, {keyAux}"
    IO.eprintln s!"generated: {report.generated}"
    IO.eprintln s!"declined: {report.declined}"
  return if state.failed.isEmpty then 0 else 1
