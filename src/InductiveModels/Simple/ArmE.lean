import InductiveModels.Simple.Site

/-!
# Arm E: the linearly recursive declaration with no base constructor
-/

open Lean Meta

namespace InductiveModels

def primArmE (site : PrimSite) (st : PrimOut) : GenM PrimOut := do
  -- The site, under the names this arm has always read it by.
  let lparams := site.lparams
  let np := site.np
  let exportCtors := site.exportCtors
  let selfN := site.selfN
  let ern := site.ern
  let recN := site.recN
  let ctorN := site.ctorN
  let nc := site.nc
  let declaredMemberTy := site.declaredMemberTy
  let w := site.w
  let rv := site.rv
  let large := site.large
  let v := site.v
  let eqi := site.eqi
  let installedRecTy := site.installedRecTy
  let publicSource := site.publicSource
  let publicRecTy := site.publicRecTy
  let emptySlots := site.emptySlots
  let mut out := st.out
  let mut spliced := st.spliced
  -- ════ arm E: an exact empty model for recursion without a base ════
  unless large do badShape s!"{ern} is not large-eliminating at a Type-valued carrier"
  for d in ← ensureNat do out := out.push d; spliced := spliced ++ d.getNames
  for d in ← ensureExactSortLift do out := out.push d; spliced := spliced ++ d.getNames

  -- The carrier is empty at exactly the inductive's universe.
  let selfVal ← site.withParams fun ps =>
    mkLambdaFVars ps (emptyAt w)
  let dSelf := Declaration.defnDecl
    { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfVal
      hints := ← hintsFor selfVal, safety := .safe }
  addChecked dSelf
  out := out.push dSelf

  -- A constructor cannot manufacture an element: its direct recursive
  -- field already inhabits the empty carrier, so return it.
  for j in [0:nc] do
    let (_, cty) := exportCtors[j]!
    let ty := publicSource cty
    let nfj ← site.withParams fun ps => do pure (numForalls (← instForall cty ps))
    let val ← site.withParams fun ps => do
      let rtele ← instForall ty ps
      forallBoundedTelescope rtele (some nfj) fun fs _ => do
        let some k := emptySlots[j]!
          | badShape s!"{exportCtors[j]!.1} has no recursive field in the empty route"
        mkLambdaFVars (ps ++ fs) fs[k]!
    let d := Declaration.defnDecl
      { name := ctorN j, levelParams := lparams, type := ty, value := val
        hints := ← hintsFor val, safety := .safe }
    addChecked d
    out := out.push d

  -- The major premise is an inhabitant of the empty carrier.  Eliminating
  -- it gives the recursor's motive at any result universe.
  let recVal ← forallBoundedTelescope installedRecTy (some (np + 1 + nc + 1)) fun bs _ => do
    let motive := bs[np]!
    let major := bs[bs.size - 1]!
    mkLambdaFVars bs (← emptyAtElim eqi v w (mkApp motive major) major)
  let dRec := Declaration.defnDecl
    { name := recN, levelParams := rv.levelParams, type := publicRecTy, value := recVal
      hints := ← hintsFor recVal, safety := .safe }
  addChecked dRec
  out := out.push dRec
  return { st with out, spliced }

end InductiveModels
