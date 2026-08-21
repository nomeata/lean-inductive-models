import InductiveModels.Simple

namespace ExactSortLiftTest

open Lean Meta InductiveModels

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
    let (_, eqDecls) ← ensureEq
    let support ← ensureExactSortLift
    let second ← ensureExactSortLift
    let names := support.flatMap fun (declaration : Declaration) => declaration.getNames.toArray
    let expressions := #[puliftT (.param `u) trueP, puliftUp (.param `u) trueP trueI]
    let noLegacy := expressions.all (fun expression => !containsConst `PULiftP expression) &&
      names.all fun name => name != `PULiftP && name != `PULiftP.up && name != `PULiftP.rec
    let (downIota, recIota, eta) ← checkDerivedDefeqs
    return (eqDecls.flatMap (fun (declaration : Declaration) =>
        declaration.getNames.toArray) ++ names,
      checkPUnit (← getEnv) |>.isOk, second.isEmpty, noLegacy,
      downIota && recIota && eta, !basis.contains `PULiftP)).run

/-- **Every level expression of depth ≤ 2 over `zero`, `u` and `v`.**

A family rather than a handful of specimens, because the claim below is
universally quantified over the carrier level and one specimen would say
nothing about the shapes it does not have.  The three constructors are applied
through the smart constructors, so what is enumerated is the set of levels the
front end can actually hand the site. -/
partial def levelFamily : Nat → Array Level
  | 0 => #[.zero, .param `u, .param `v]
  | n + 1 =>
    let previous := levelFamily n
    let succs := previous.map Level.succ
    let maxes := previous.flatMap fun a => previous.map fun b => mkLevelMax' a b
    let imaxes := previous.flatMap fun a => previous.map fun b => mkLevelIMax' a b
    previous ++ succs ++ maxes ++ imaxes

/-- **The tree arm's carrier plan delivers at every never-zero sort.**

The W core fixes its `A` and `B'` at `Type u`, so the arm needs the public
`Sort w` to be a successor level or to be reachable from a `Type` core by the
constrained lift, whose result sort is `max 1 w`.  `wCarrierPlan` takes the
second road exactly when `isLevelDefEq (max 1 w) w`.

That test succeeds for **every** never-zero `w`, and it is not a coincidence of
the specimens in the corpus: Lean's level normal form drops an explicit numeral
`k` from a `max` whenever a sibling argument has offset at least `k`, and a
normalized level is never-zero exactly when it has such a sibling — an `imax`
whose second argument is never-zero has already been rewritten to a `max` by
the smart constructor.  So `isNeverZero` and `max 1 w ≡ w` are the same
property, and this enumeration says so over the whole depth-2 grammar rather
than over the levels that happen to appear in a fixture.

The returned triple is (levels tested, never-zero levels, failures). -/
def auditCarrierPlans : MetaM (Nat × Nat × Array Level) := do
  let mut neverZero := 0
  let mut bad : Array Level := #[]
  let family := levelFamily 2
  for w in family do
    let normal := w.normalize
    unless normal.isNeverZero do
      -- The complement is asserted too: a level that may be zero must *not*
      -- take the lift, or the arm would claim an exact sort it cannot land at.
      if (← isLevelDefEq (mkLevelMax' (.succ .zero) w) w) then bad := bad.push w
      continue
    neverZero := neverZero + 1
    let plan ← (wCarrierPlan true w).run
    match plan with
    | .error _ => bad := bad.push w
    | .ok plan =>
      -- What the arm needs: the core level is a successor, so `uL` exists, and
      -- the plan's carrier lands at the declared sort.
      let usable := plan.coreLevel.normalize.dec.isSome
      let exact ←
        if plan.lifted then isLevelDefEq (mkLevelMax' plan.coreLevel w) w
        else pure (normal.dec.isSome)
      unless usable && exact do bad := bad.push w
  return (family.size, neverZero, bad)

def main : IO UInt32 := do
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<exact-sort-lift-test>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 4096 }
  let (result, _) ← Core.CoreM.toIO (MetaM.run' auditLift) context { env }
  let .ok (names, punitExact, idempotent, noLegacy, defeqs, basisClean) := result
    | IO.eprintln "exact-sort lift support declined"; return 1
  let ((tested, neverZero, badPlans), _) ←
    Core.CoreM.toIO (MetaM.run' auditCarrierPlans) context { env }
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
    ("PULiftP is absent from the primitive basis", basisClean),
    ("the tree arm's carrier plan delivers at every never-zero level", badPlans.isEmpty),
    ("the level family is populated on both sides", tested == 1200 && neverZero == 234)]
  for (label, passed) in checks do
    unless passed do IO.eprintln s!"FAIL: {label}"
  unless badPlans.isEmpty do
    IO.eprintln s!"carrier plan undelivered at: {(badPlans.toList.take 8).map toString}"
  IO.eprintln s!"levels tested: {tested}, never-zero: {neverZero}"
  let passed := (checks.filter (·.2)).size
  IO.println s!"exact-sort lift: {passed} passed, {checks.size - passed} failed"
  return if checks.all (·.2) then 0 else 1

end ExactSortLiftTest
