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
  let .ok result := parse (← IO.FS.readFile path)
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

/-- One generated definition or theorem's type, by name. -/
def declaredType? (input : Export) (name : Name) : Option Expr :=
  input.decls.findSome? fun declaration => match declaration with
    | .defn n _ type _ _ _ _ => if n == name then some type else none
    | .thm n _ type _ _ => if n == name then some type else none
    | .ax n _ type _ => if n == name then some type else none
    | _ => none

def ownerPasses (input : Export) (owner : Name) : Bool :=
  (Check.check input).all (·.familyOwner != owner)

def generatedExactly (report : Report) (owner : Name) (count : Nat) : Bool :=
  report.generated.any fun entry => entry == (owner, count)

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let raw ← readExport "test/fixtures/inductive-models/nest_fam_arg.ndjson"
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
  let nonindexedRaw ← readExport "test/fixtures/inductive-models/nonindexed_vanishing.ndjson"
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
  let hiddenRaw ← readExport "test/fixtures/inductive-models/indexed_hidden_erasure.ndjson"
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

  -- **The ζ spelling, at the four routes that read the field domain as
  -- written.**  Every owner in `dead_owner_mention` carries one data field
  -- whose `let` binding names the type being declared; before the site
  -- normalised its telescope once, `DeadLabel` declined
  -- `.shapeUnsupported .incomplete` on `labelFactored` and the other three
  -- aborted the run outright.  What is asserted here is the pair of facts the
  -- normalisation has to keep apart: the **public** constructor still spells
  -- the dead mention exactly as the source does, and the **private** carrier
  -- does not mention the source owner at all.
  let deadRaw ← readExport "test/fixtures/inductive-models/dead_owner_mention.ndjson"
  let (deadGenerated, deadReport) ← runExport deadRaw
  let deadOwners : Array Name := #[`DeadLabel, `DeadBranch, `DeadStruct, `DeadProp]
  state := state.check "every ζ-dead source constructor mentions its own owner" <|
    deadOwners.all fun owner =>
      (constructorTypes deadRaw owner).any (hasVanishingDomain owner)
  state := state.check "all four ζ-dead owners model rather than declining or aborting" <|
    deadOwners.all fun owner =>
      deadReport.generated.any (·.1 == owner) &&
        !deadReport.declined.any fun (declined, _) => declined == owner
  state := state.check "each public ζ-dead constructor keeps the source spelling" <|
    deadOwners.all fun owner =>
      let model := Naming.modelName owner
      (deadRaw.decls.foldl (init := #[]) fun result declaration =>
        match declaration with
        | .induct types constructors _ =>
          if types.any (·.name == owner) then result ++ constructors.map (·.name)
          else result
        | _ => result).any fun constructor =>
          (declaredType? deadGenerated (Naming.modelName constructor)).any
            (hasVanishingDomain model)
  state := state.check "no private carrier mentions the ζ-dead source owner" <|
    deadOwners.all fun owner =>
      let private_ := Name.str (Naming.modelName owner) "_impl"
      deadGenerated.decls.all fun declaration =>
        !(declaration.names.any fun n => private_.isPrefixOf n) ||
          match declaration with
          | .defn _ _ type value _ _ _ =>
            !containsConst owner type && !containsConst owner value
          | .thm _ _ type value _ => !containsConst owner type && !containsConst owner value
          | _ => true
  -- `DeadStruct` is the one whose *only* owner mention is ζ-dead, so after the
  -- reduction it is a plain nonrecursive one-constructor record and is asked
  -- for both of its fields back.  A route that reads its domain as written
  -- calls it recursive and emits no projection at all.
  state := state.check "the wholly ζ-dead owner is a nonrecursive record with both fields" <|
    #[`DeadStruct._model.proj_0, `DeadStruct._model.proj_0.iota,
      `DeadStruct._model.proj_1, `DeadStruct._model.proj_1.iota].all fun n =>
      (declaredType? deadGenerated n).isSome
  state := state.check "the ζ-dead output passes exact model checking" <|
    deadOwners.all (ownerPasses deadGenerated) && deadReport.stmtErrors.isEmpty &&
      deadReport.stmtChecked == 86

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

  -- **What the one normalisation reaches, and what it deliberately does not.**
  -- `shapeCtorTy` reduces a *field domain* whose owner mention βζ disappears
  -- and nothing else, so `labelFactored`'s `recAt` stops calling such a field
  -- an earlier recursive one.  A binder type *inside* a recursive field's own
  -- telescope is one level deeper and is left as written; the guard therefore
  -- stays a live conjunct rather than becoming an assertion, and these two
  -- constructor types are the two sides of that line.
  let family := fun (argument : Expr) => Expr.app (Expr.const `Boundary.Fam []) argument
  let deadThenChild :=
    Expr.forallE `k dead
      (Expr.forallE `f (Expr.forallE `z (family (.bvar 0)) ownerT .default) ownerT .default)
      .default
  let childBinderRedex :=
    Expr.forallE `c ownerT
      (Expr.forallE `f
        (Expr.forallE `z (Expr.app (Expr.lam `x ownerT natT .default) (.bvar 0)) ownerT .default)
        ownerT .default)
      .default
  state := state.check "a dead field domain stops being an earlier recursive field" <|
    !labelFactored owner 0 #[(`Boundary.lim, deadThenChild)] &&
      labelFactored owner 0 (shapeCtors owner 0 #[(`Boundary.lim, deadThenChild)])
  state := state.check "a dead mention inside a child's binder is still refused" <|
    shapeCtorTy owner 0 childBinderRedex == childBinderRedex &&
      !labelFactored owner 0 (shapeCtors owner 0 #[(`Boundary.lim, childBinderRedex)])
  state := state.check "normalization is the identity on a live occurrence and on parameters" <|
    shapeCtorTy owner 0 (Expr.forallE `f hidden ownerT .default)
        == Expr.forallE `f hidden ownerT .default &&
      shapeCtorTy owner 1 (Expr.forallE `p dead (Expr.forallE `k dead ownerT .default) .default)
        == Expr.forallE `p dead (Expr.forallE `k natT ownerT .default) .default

  IO.println s!"vanishing erasure: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  unless state.failed.isEmpty do
    IO.eprintln s!"wanted auxiliaries: {okAux}, {keyAux}"
    IO.eprintln s!"generated: {report.generated}"
    IO.eprintln s!"declined: {report.declined}"
  return if state.failed.isEmpty then 0 else 1
