import InductiveModels.Simple.Site

/-!
# Arm W: the tagged W construction
-/

open Lean Meta

namespace InductiveModels

def primArmW (site : PrimSite) (st : PrimOut) : GenM PrimOut := do
  -- The site, under the names this arm has always read it by.
  let tname := site.tname
  let lparams := site.lparams
  let np := site.np
  let exportCtors := site.exportCtors
  let reserved := site.reserved
  let us := site.us
  let selfN := site.selfN
  let ern := site.ern
  let recN := site.recN
  let ctorN := site.ctorN
  let nc := site.nc
  let taken := site.taken
  let declaredMemberTy := site.declaredMemberTy
  let rv := site.rv
  let large := site.large
  let v := site.v
  let recLs := site.recLs
  let installedRecTy := site.installedRecTy
  let publicSource := site.publicSource
  let publicRecTy := site.publicRecTy
  let wTagged := site.wTagged
  let wPlan := site.wPlan
  let wW := site.wW
  let wDN := site.wDN
  let wTelN := site.wTelN
  let wBN := site.wBN
  let wAN := site.wAN
  let wTgN := site.wTgN
  let wFN := site.wFN
  let wNatT := site.wNatT
  let uL := site.uL
  let wKL := site.wKL
  let wShapeOf := site.wShapeOf
  let wRecCount := site.wRecCount
  let wDAt := site.wDAt
  let wAAt := site.wAAt
  let wKTy := site.wKTy
  let wBAt := site.wBAt
  let wBFn := site.wBFn
  let wTgAt := site.wTgAt
  let wDecEq := site.wDecEq
  let wSup := site.wSup
  let wLowSelfAt := site.wLowSelfAt
  let wDataTy := site.wDataTy
  let wNrProjs := site.wNrProjs
  let wTelTy := site.wTelTy
  let wCtorParts := site.wCtorParts
  let wMkF := site.wMkF
  let mut out := st.out
  let mut spliced := st.spliced
  let mut requires := st.requires
  -- ════ arm W: branching and infinitary, out of the spliced W core ════
  --
  -- The tagged W construction and its untagged instantiation. Six
  -- definitions, the constructors, one `Nat.rec` cascade for `rec_0` and one
  -- `WT.Wrec_iota` per rule. Junk uninhabited in both directions and both
  -- towers ending at exactly the selected `Sort wW`, at either instantiation.
  --
  -- **The two differ in four declarations and nowhere else**:
  -- `Tel`'s and `B'`'s domain (the tag, or the whole label), `tg` (the first
  -- projection, or the identity) and `DecidableEq K`. `D` and `A` are
  -- literally the same term.
  unless large do badShape s!"{ern} is not large-eliminating at a Type-valued carrier"
  -- **The carrier level, asked here because this is the arm that must deliver
  -- it.** The dispatcher chose W on the shape question alone
  -- ([`InductiveModels.mkPrimSite`]'s `wShapeEligible`), which is the honest
  -- split: the tuple tower cannot express a branching or infinitary spine at
  -- *any* level, so there is nowhere to route this declaration on to. Either
  -- the public `Sort w` has a syntactic predecessor, and the core runs at it
  -- directly, or `max 1 w ≡ w` and the plan runs the core at `Type` inside the
  -- exact-sort `PSigma'`. Where neither holds `WT.W.{u,w}`'s `A` and `B'`
  -- cannot be written at all, and this arm says so rather than handing the
  -- shape to a construction that would decline it in W's name.
  unless site.w.normalize.dec.isSome || wPlan.lifted do
    badShape s!"{tname}'s carrier inhabits Sort {site.w}, which has no syntactic predecessor \
and is not definitionally `max 1` of itself, so the W core's `A` and `B'` — which the core \
fixes at `Type u` — have no level to be written at; the branching or infinitary \
recursion this declaration has is outside the tuple tower at every level, so there is no \
other construction for it"
  for n in [wDN, wTelN, wBN, wAN, wTgN, wFN] do taken n

  -- **The level question, before anything is spliced.** Both towers are
  -- written with codomain level `wW`, so every field and every recursive
  -- field's binder must satisfy `max ℓ wW ≡ wW`. Exposed `imax` components are
  -- measured after the same recursive boxing the towers will use; anything
  -- still too large fails here rather than 528 KB later.
  site.withParams fun ps => do
    for k in [0:nc] do
      let (cn, cty) := exportCtors[k]!
      let (nrs, rcs) ← wShapeOf k
      let tele ← instForall cty ps
      forallBoundedTelescope tele (some (numForalls tele)) fun fs _ => do
        if let some ℓ ← wTowerLevelOf wW (nrs.map (fs[·]!)) then
          badShape s!"{cn} has a non-recursive field at Sort {ℓ} and the carrier is \
Sort {wW}, so the data tower does not land at the W core's sort"
        for i in rcs do
          forallTelescope (← ityp fs[i]!) fun zs res => do
            -- Lean's recursive-argument test reduces transparent aliases.
            -- Ask the same definitional question here, but use it only for
            -- recognition: `wRecDom`, every public type restored below, and
            -- the iota statement all retain the export's literal syntax.
            -- `AliasW.lim : (N → As AliasW) → AliasW` is the witness: `As`
            -- is not a nested container, and its result is definitionally
            -- the owner at precisely these parameters.
            let self := mkAppN (.const tname us) ps
            unless ← isDefEq res self do
              badShape s!"{cn}'s recursive field {i} does not reduce to {tname} at its \
own parameters under its binders, so it is nested rather than infinitary"
            if let some ℓ ← wTowerLevelOf wW zs then
              badShape s!"{cn}'s recursive field {i} has a binder at Sort {ℓ} and the \
carrier is Sort {wW}, so the branch tower does not land at the W core's sort"

  for d in ← ensureNat do out := out.push d; spliced := spliced ++ d.getNames
  for d in ← ensurePSigmaPrime do out := out.push d; spliced := spliced ++ d.getNames
  for d in ← ensureExactSortLift do out := out.push d; spliced := spliced ++ d.getNames
  -- **The core itself.** `#[]` when it is
  -- already in, which is every W target after the first in a run.
  let core ← ensureWCore reserved
  for d in core do out := out.push d; spliced := spliced ++ d.getNames
  -- **The inductives the core brought with it, which this model may not
  -- leave unmodelled** — `Iso.requires`' rule, and the same one arm C's
  -- skeleton is under. Empty when the fragment was already spliced, and that
  -- is not a hole: [`InductiveModels.genPrim`] rolls the environment back on every
  -- withdrawal and on every decline, so a fragment that is *present* was put
  -- there by an earlier model whose own `requires` were met.
  let wRequires : Array Name := core.flatMap fun d =>
    match d with
    | .inductDecl _ _ types _ =>
      (types.map (·.name)).toArray.filter (!inductiveBasis.contains ·)
    | _ => #[]

  let unitMot : Expr := .lam `x wNatT (.sort wW) .default
  let junkTy : Expr → GenM Expr := fun _ => pure (emptyAt wW)

  -- ── `D` — tag ↦ that constructor's non-recursive fields ──
  let dTy ← site.withParams fun ps =>
    mkForallFVars ps (.forallE `t wNatT (.sort wW) .default)
  let dVal ← site.withParams fun ps => withLocalDeclD `t wNatT fun t => do
    mkLambdaFVars (ps.push t)
      (← natCascade (.succ wW) nc (fun _ => pure unitMot) (wDataTy ps) junkTy 0 t)
  let dD := Declaration.defnDecl
    { name := wDN, levelParams := lparams, type := dTy, value := dVal
      hints := ← hintsFor dVal, safety := .safe }
  addChecked dD
  out := out.push dD

  -- ── `A` — the label, tag paired with that constructor's data ──
  -- **Emitted before `Tel` at the untagged instantiation**, because there
  -- `Tel` and `B'` are indexed by the label rather than by the tag and would
  -- name a constant absent from the environment. At the tagged one it
  -- keeps its old place, so nothing about that emission moves.
  let aTyD ← site.withParams fun ps => mkForallFVars ps (.sort wW)
  let aVal ← site.withParams fun ps =>
    mkLambdaFVars ps (psigmaT (.succ .zero) wW wNatT (wDAt ps))
  let dA := Declaration.defnDecl
    { name := wAN, levelParams := lparams, type := aTyD, value := aVal
      hints := ← hintsFor aVal, safety := .safe }
  unless wTagged do
    addChecked dA
    out := out.push dA

  -- ── `Tel` — the branch type's telescope, at a key and a branch index ──
  -- Two cascades: a branch index past a constructor's recursive-field count
  -- must be as
  -- empty as a tag past the constructor count, or `W` acquires children no
  -- constructor produces and the model is strictly bigger than the target.
  --
  -- **Untagged, the outer cascade's motive takes the data as an argument.**
  -- This is the whole untagged delta and the one thing the tag scheme has no
  -- analogue of: the cascade is still on the tag — a `Nat`, so
  -- still `Nat.rec` — but each arm receives that constructor's own `D t` and
  -- projects the fields its children's binders mention out of it.
  let telKey : Name := if wTagged then `t else `a
  let telTyD ← site.withParams fun ps => mkForallFVars ps
    (.forallE telKey (wKTy ps) (.forallE `j wNatT (.sort wW) .default) .default)
  let telVal ← site.withParams fun ps =>
    withLocalDeclD telKey (wKTy ps) fun a => withLocalDeclD `j wNatT fun j => do
      if wTagged then
        let arm : Nat → GenM Expr := fun k => do
          natCascade (.succ wW) (← wRecCount k) (fun _ => pure unitMot)
            (wTelTy ps k #[]) junkTy 0 j
        mkLambdaFVars (ps ++ #[a, j])
          (← natCascade (.succ wW) nc (fun _ => pure unitMot) arm junkTy 0 a)
      else
        let dAt : Expr → Expr := fun t => mkAppN (.const wDN us) (ps ++ #[t])
        -- `fun t => D p⃗ (succ^kk t) → Nat → Sort wW`, which lands in `Sort wW+1`
        -- exactly as the tagged motive does.
        let motAt : Nat → GenM Expr := fun kk =>
          withLocalDeclD `t wNatT fun t => mkLambdaFVars #[t]
            (.forallE `d (dAt (natSuccs kk t))
              (.forallE `j wNatT (.sort wW) .default) .default)
        let armAt : Nat → GenM Expr := fun k =>
          withLocalDeclD `d (dAt (natNumeral k)) fun d =>
            withLocalDeclD `jj wNatT fun jj => do
              mkLambdaFVars #[d, jj]
                (← natCascade (.succ wW) (← wRecCount k) (fun _ => pure unitMot)
                  (wTelTy ps k (← wNrProjs ps k d)) junkTy 0 jj)
        -- **The junk tag's arm is a constant and need not be empty**:
        -- `A = Σ' t, D t` and `D`'s own junk arm
        -- is already `PEmpty`, so `Tel` is never asked at a tag no
        -- constructor has. It is written empty anyway; the requirement that
        -- is load-bearing is the *branch index* one above, and that one is
        -- `junkTy`.
        let junkAt : Expr → GenM Expr := fun t =>
          withLocalDeclD `d (dAt (natSuccs nc t)) fun d =>
            withLocalDeclD `jj wNatT fun jj => mkLambdaFVars #[d, jj] (emptyAt wW)
        let a1 := psigmaFst (.succ .zero) wW wNatT (wDAt ps) a
        let a2 := psigmaSnd (.succ .zero) wW wNatT (wDAt ps) a
        mkLambdaFVars (ps ++ #[a, j])
          (mkApp (mkApp (← natCascade (.succ wW) nc motAt armAt junkAt 0 a1) a2) j)
  let dTel := Declaration.defnDecl
    { name := wTelN, levelParams := lparams, type := telTyD, value := telVal
      hints := ← hintsFor telVal, safety := .safe }
  addChecked dTel
  out := out.push dTel

  -- ── `B'` and `tg` ──
  let bTyD ← site.withParams fun ps =>
    mkForallFVars ps (.forallE telKey (wKTy ps) (.sort wW) .default)
  let bVal ← site.withParams fun ps => withLocalDeclD telKey (wKTy ps) fun t => do
    mkLambdaFVars (ps.push t) (← wBAt ps t)
  let dB := Declaration.defnDecl
    { name := wBN, levelParams := lparams, type := bTyD, value := bVal
      hints := ← hintsFor bVal, safety := .safe }
  addChecked dB
  out := out.push dB

  if wTagged then
    addChecked dA
    out := out.push dA

  -- `PSigma'.fst` at the tag scheme and the identity at the label scheme. The
  -- latter is the former at `tg := id`, and this line is where that reading
  -- is cashed.
  let tgTyD ← site.withParams fun ps =>
    mkForallFVars ps (.forallE `a (wAAt ps) (wKTy ps) .default)
  let tgVal ← site.withParams fun ps => withLocalDeclD `a (wAAt ps) fun a => do
    mkLambdaFVars (ps.push a)
      (if wTagged then psigmaFst (.succ .zero) wW wNatT (wDAt ps) a else a)
  let dTg := Declaration.defnDecl
    { name := wTgN, levelParams := lparams, type := tgTyD, value := tgVal
      hints := ← hintsFor tgVal, safety := .safe }
  addChecked dTg
  out := out.push dTg

  -- ── the carrier ──
  let selfVal ← site.withParams fun ps => mkLambdaFVars ps
    (wPlan.carrier (wLowSelfAt ps))
  let dSelf := Declaration.defnDecl
    { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfVal
      hints := ← hintsFor selfVal, safety := .safe }
  addChecked dSelf
  out := out.push dSelf

  -- ── the constructors ──
  for j in [0:nc] do
    let ty := publicSource exportCtors[j]!.2
    let val ← site.withParams fun ps => do
      let rtele ← instForall ty ps
      forallBoundedTelescope rtele (some (numForalls rtele)) fun fs _ => do
        let (a, disp) ← wCtorParts ps j fs
        mkLambdaFVars (ps ++ fs) (wPlan.wrap (wLowSelfAt ps) (wSup ps a disp))
    let d := Declaration.defnDecl
      { name := ctorN j, levelParams := lparams, type := ty, value := val
        hints := ← hintsFor val, safety := .safe }
    addChecked d
    out := out.push d

  -- ── `F`, the core's minor, as its own declaration ──
  -- **Hoisted rather than inlined**, because it is named once by `rec_0` and
  -- once by *every* ι rule while being itself `nc` arms deep, each arm
  -- carrying its own eta lemma: inlined, the emitted output is quadratic in
  -- the constructor count for nothing, and the kernel checks the same
  -- cascade `nc + 1` times. Hoisted, the ι rule's left side and its proof
  -- name the same constant.
  let fTy ← forallBoundedTelescope installedRecTy (some (np + 1 + nc)) fun pre _ => do
    let ps := pre.extract 0 np
    let motive := pre[np]!
    let selfTy := wLowSelfAt ps
    let coreMotive ← wPlan.motive (wLowSelfAt ps) motive
    withLocalDeclD `a (wAAt ps) fun a => do
      let bt ← wBAt ps (mkApp (wTgAt ps) a)
      withLocalDeclD `f (.forallE `b bt selfTy .default) fun f => do
        let ihT ← withLocalDeclD `b bt fun b =>
          mkForallFVars #[b] (mkApp coreMotive (mkApp f b))
        withLocalDeclD `ih ihT fun ih =>
          mkForallFVars (pre ++ #[a, f, ih]) (mkApp coreMotive (wSup ps a f))
  let fVal ← forallBoundedTelescope installedRecTy (some (np + 1 + nc)) fun pre _ => do
    mkLambdaFVars pre
      (← wMkF (pre.extract 0 np) pre[np]! (pre.extract (np + 1) (np + 1 + nc)))
  let dF := Declaration.defnDecl
    { name := wFN, levelParams := rv.levelParams, type := fTy, value := fVal
      hints := ← hintsFor fVal, safety := .safe }
  addChecked dF
  out := out.push dF

  -- ── the recursor ──
  let recVal ← forallBoundedTelescope installedRecTy
      (some (np + 1 + nc + 1)) fun bs _ => do
    let ps := bs.extract 0 np
    let major := bs[bs.size - 1]!
    let coreMotive ← wPlan.motive (wLowSelfAt ps) bs[np]!
    mkLambdaFVars bs (mkAppN (.const wCoreRec [uL, v, wKL])
      #[wKTy ps, wAAt ps, wBFn ps, wDecEq ps, wTgAt ps, coreMotive,
        mkAppN (.const wFN recLs) (bs.extract 0 (np + 1 + nc)),
        wPlan.unwrap (wLowSelfAt ps) major])
  let dRec := Declaration.defnDecl
    { name := recN, levelParams := rv.levelParams, type := publicRecTy, value := recVal
      hints := ← hintsFor recVal, safety := .safe }
  addChecked dRec
  out := out.push dRec
  requires := wRequires
  return { st with out, spliced, requires }

end InductiveModels
