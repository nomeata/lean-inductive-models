import InductiveModels.Simple.Site

/-!
# Arm E: the declaration every one of whose constructors has a bare recursive field

Such a declaration is **empty** — no constructor can be applied, because
applying one would already require an inhabitant of the carrier — and the model
is the empty type at exactly the declared sort. Everything else follows from
that one fact: the constructors return their own recursive field, and the
recursor, its ι rules, and (at one constructor) the intrinsic projections and
their ι rules all eliminate the same uninhabited value.

The arm serves the never-zero and the **maybe-zero** routes alike, because
nothing in it is sort-specific. [`InductiveModels.emptyAt`] is the derived
exact-sort lift of Church `⊥`, `PSigma'.{0,w} (∀ p : Prop, p) (fun _ => PUnit.{w})`,
which is empty at every `w` and lands at `Sort (max 0 w) = Sort w` for a bare
`w` exactly as for a never-zero one; and [`InductiveModels.emptyAtElim`] is
`cfalseElim` after that lift's `down`, which serves at every result universe
including `Level.zero`.
-/

open Lean Meta

namespace InductiveModels

def primArmE (site : PrimSite) (st : PrimOut) : GenM PrimOut := do
  -- The site, under the names this arm has always read it by.
  let lparams := site.lparams
  let np := site.np
  let exportCtors := site.exportCtors
  let sourceCtors := site.sourceCtors
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
  -- ════ arm E: an exact empty model, at every route's sort ════
  --
  -- **Largeness is not a precondition of this arm**, and asking for it used to
  -- confine it to the never-zero route. `v` below is the recursor's result
  -- universe, which is `Level.zero` exactly when the kernel minted a small
  -- eliminator, and [`InductiveModels.emptyAtElim`] serves at every `v` —
  -- `cfalseElim` builds its `Nat.rec` family at `Sort (v+1)` and transports
  -- into `Sort v`, with `v = 0` no different from any other. `MZData`'s
  -- recursor is small (its data field is neither a proof nor a conclusion
  -- index, so the kernel's subsingleton rule declines it) and its model is
  -- exactly as complete for that.
  --
  -- On the never-zero route the recursor is large unconditionally, so the test
  -- below is an invariant of that route rather than a shape question; it is
  -- kept as one so a carrier that stopped being `Type`-valued cannot pass
  -- silently.
  unless large || site.route matches PrimRoute.bare do
    badShape s!"{ern} is not large-eliminating at a Type-valued carrier"
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
    let ty := publicSource sourceCtors[j]!.2
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
