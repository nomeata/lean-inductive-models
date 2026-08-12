import Modelgen.Simple

open Lean Meta Modelgen

partial def containsProjection (owner : Name) (field : Nat) : Expr → Bool
  | .proj got index value =>
      (got == owner && index == field) || containsProjection owner field value
  | .app fn argument => containsProjection owner field fn || containsProjection owner field argument
  | .lam _ type body _ | .forallE _ type body _ =>
      containsProjection owner field type || containsProjection owner field body
  | .letE _ type value body _ =>
      containsProjection owner field type || containsProjection owner field value ||
        containsProjection owner field body
  | .mdata _ body => containsProjection owner field body
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => false

def auditPrimitive : MetaM (Except Decline (Array Name × Bool × Bool × Bool)) :=
  (do
    let (_, eqDecls) ← ensureEq {}
    let records ← ensurePSigmaPrime {}
    let second ← ensurePSigmaPrime {}
    let names := records.flatMap (·.getNames.toArray)
    let coreOk := checkPSigmaPrimeCore (← getEnv) |>.isOk
    let some (.defnInfo recursor) := (← getEnv).constants.find? `PSigma'.rec'
      | badShape "PSigma'.rec' is not a definition"
    let projections := containsProjection `PSigma' 0 recursor.value &&
      containsProjection `PSigma' 1 recursor.value
    return (eqDecls.flatMap (·.getNames.toArray) ++ names, coreOk,
      second.isEmpty, projections)).run

def main : IO UInt32 := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<psigma-prime-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 4096 }
  let (result, _) ← Core.CoreM.toIO (MetaM.run' auditPrimitive) context { env }
  let .ok (names, coreOk, idempotent, projections) := result
    | IO.eprintln s!"PSigma' support declined: {result}"; return 1
  let expected :=
    [`PSigma', `PSigma'.mk, `PSigma'.fst, `PSigma'.snd, `PSigma'.rec',
      `PSigma'.fst_mk, `PSigma'.snd_mk, `PSigma'.rec'_mk]
  let complete := expected.all names.contains
  let checks := #[
    ("exact support bundle", complete),
    ("tight primitive shape", coreOk),
    ("idempotent validation", idempotent),
    ("custom recursor uses both primitive projections", projections)]
  for (label, passed) in checks do
    unless passed do IO.eprintln s!"FAIL: {label}"
  IO.println s!"PSigma' primitive: {checks.count (·.2)} passed, {checks.count (!·.2)} failed"
  return if checks.all (·.2) then 0 else 1
