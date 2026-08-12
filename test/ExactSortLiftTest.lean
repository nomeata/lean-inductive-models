import Modelgen.Simple

open Lean Meta Modelgen

partial def containsConst (target : Name) : Expr → Bool
  | .const name _ => name == target
  | .proj _ _ value => containsConst target value
  | .app fn argument => containsConst target fn || containsConst target argument
  | .lam _ type body _ | .forallE _ type body _ =>
      containsConst target type || containsConst target body
  | .letE _ type value body _ =>
      containsConst target type || containsConst target value || containsConst target body
  | .mdata _ body => containsConst target body
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => false

def checkDerivedDefeqs : MetaM (Bool × Bool × Bool) := do
  let u := Level.param `u
  let v := Level.param `v
  withLocalDeclD `p (.sort .zero) fun p =>
    withLocalDeclD `h p fun h => do
      let lifted := puliftT u p
      let up := puliftUp u p h
      let downIota ← isDefEq (puliftDown u p up) h
      let recIota ← withLocalDeclD `motive (.forallE `x lifted (.sort v) .default) fun motive =>
        withLocalDeclD `minor (.forallE `proof p (mkApp motive (puliftUp u p (.bvar 0))) .default)
          fun minor => isDefEq (puliftRec v u p motive minor up) (mkApp minor h)
      let eta ← withLocalDeclD `x lifted fun x =>
        isDefEq x (puliftUp u p (puliftDown u p x))
      return (downIota, recIota, eta)

def auditLift : MetaM (Except Decline (Array Name × Bool × Bool × Bool × Bool × Bool)) :=
  (do
    let (_, eqDecls) ← ensureEq {}
    let support ← ensureExactSortLift {}
    let second ← ensureExactSortLift {}
    let names := support.flatMap fun (declaration : Declaration) => declaration.getNames.toArray
    let expressions := #[puliftT (.param `u) trueP, puliftUp (.param `u) trueP trueI]
    let noLegacy := expressions.all (fun expression => !containsConst `PULiftP expression) &&
      names.all fun name => name != `PULiftP && name != `PULiftP.up && name != `PULiftP.rec
    let (downIota, recIota, eta) ← checkDerivedDefeqs
    return (eqDecls.flatMap (fun (declaration : Declaration) =>
        declaration.getNames.toArray) ++ names,
      checkPUnit (← getEnv) |>.isOk, second.isEmpty, noLegacy,
      downIota && recIota && eta, !primBasis.contains `PULiftP)).run

def main : IO UInt32 := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<exact-sort-lift-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 4096 }
  let (result, _) ← Core.CoreM.toIO (MetaM.run' auditLift) context { env }
  let .ok (names, punitExact, idempotent, noLegacy, defeqs, basisClean) := result
    | IO.eprintln "exact-sort lift support declined"; return 1
  let complete :=
    [`PSigma', `PSigma'.mk, `PSigma'.fst, `PSigma'.snd, `PSigma'.rec',
      `PSigma'.fst_mk, `PSigma'.snd_mk, `PSigma'.rec'_mk,
      `PUnit, `PUnit.unit].all names.contains
  let checks : Array (String × Bool) := #[
    ("complete tight-pair/PUnit support", complete),
    ("exact standard PUnit shape", punitExact),
    ("present support validates idempotently", idempotent),
    ("derived expressions contain no PULiftP", noLegacy),
    ("down, arbitrary rec iota, and full eta are definitional", defeqs),
    ("PULiftP is absent from the primitive basis", basisClean)]
  for (label, passed) in checks do
    unless passed do IO.eprintln s!"FAIL: {label}"
  let passed := (checks.filter (·.2)).size
  IO.println s!"exact-sort lift: {passed} passed, {checks.size - passed} failed"
  return if checks.all (·.2) then 0 else 1
