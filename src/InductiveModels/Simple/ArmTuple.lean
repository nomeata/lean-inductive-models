import InductiveModels.Simple.Site

/-!
# The Type route: the `Nat`-tagged tuple tower
-/

open Lean Meta

namespace InductiveModels

def primArmTuple (site : PrimSite) (st : PrimOut) : GenM PrimOut := do
  -- The site, under the names this arm has always read it by.
  let tname := site.tname
  let lparams := site.lparams
  let np := site.np
  let exportCtors := site.exportCtors
  let selfN := site.selfN
  let ern := site.ern
  let recN := site.recN
  let ctorN := site.ctorN
  let nc := site.nc
  let declaredMemberTy := site.declaredMemberTy
  let ni := site.ni
  let w := site.w
  let isRec := site.isRec
  let rv := site.rv
  let large := site.large
  let v := site.v
  let eqi := site.eqi
  let installedRecTy := site.installedRecTy
  let publicSource := site.publicSource
  let publicRecTy := site.publicRecTy
  let wTagged := site.wTagged
  let mut out := st.out
  let mut spliced := st.spliced
  -- ════ the Type route ════
  unless large do badShape s!"{ern} is not large-eliminating at a Type-valued carrier"
  for d in ← ensureNat do out := out.push d; spliced := spliced ++ d.getNames
  for d in ← ensurePSigmaPrime do out := out.push d; spliced := spliced ++ d.getNames
  for d in ← ensureExactSortLift do out := out.push d; spliced := spliced ++ d.getNames

  -- Storage decisions — pure level arithmetic, and a decline here costs no
  -- further splice. A chain of one field is that field bare (no `PSigma'`,
  -- so no pair); longer tight chains carry exactly `max ℓ⃗`. A pad at `1`
  -- deliberately raises this to `max 1 ℓ⃗`, and `w` itself covers a raised
  -- carrier — at *any* `w` now, since the derived lift exists at every level.
  -- What no pad absorbs is an `imax` in a field's level: those fields are
  -- recursively boxed ([`InductiveModels.boxTyOf`]) and the plan is retried on the
  -- boxed levels, whose exposed Π codomains are never-zero `max`es.
  let plans : Array CPlan ← site.withParams fun ps =>
    exportCtors.mapM fun (cn, cty) => do
      let tele ← instForall cty ps
      let nf := numForalls tele
      forallBoundedTelescope tele (some nf) fun fs _ => do
        let tys ← fs.mapM ityp
        let ℓs ← tys.mapM ilevel
        -- The three storage questions, asked with whichever level equality
        -- the caller passes.
        let plan : (Level → Level → GenM Bool) → Array Level →
            GenM (Option (Option Level)) := fun eq ms => do
          let raw := if nf == 1 then ms[0]! else (ms.foldl mkLevelMax' .zero).normalize
          if nf > 0 then
            if ← eq raw w then return some none
          let withOne := (ms.foldl mkLevelMax' (.succ .zero)).normalize
          if ← eq withOne w then return some (some (Level.succ .zero))
          if ← eq (mkLevelMax' withOne w) w then return some (some w)
          return none
        -- bare first, then the same questions again on the boxed levels
        let attempt : (Level → Level → GenM Bool) → GenM (Option CPlan) := fun eq => do
          if let some pad? ← plan eq ℓs then
            return some { boxed := Array.replicate nf false, pad? }
          let boxed := ℓs.map fun ℓ => levelHasIMax ℓ.normalize
          if boxed.any id then
            let ms ← (Array.range nf).mapM fun k => do
              if boxed[k]! then ilevel (← boxTyOf tys[k]!) else pure ℓs[k]!
            if let some pad? ← plan eq ms then
              return some { boxed, pad? }
          return none
        -- **The elaborator gets first refusal, and that ordering is the
        -- whole design.** `LevelAlgebra.isLevelDefEqComplete` is complete
        -- where `isLevelDefEq` is not, but a level equality only the
        -- *complete* procedure can see is one **Lean's kernel cannot see
        -- either** — the kernel's `lean::is_equivalent` is a different
        -- function with the same `max`-does-not-absorb-`imax` gap. So a
        -- plan reached only by the complete procedure is not justified by
        -- the stock kernel equality used by the optional exact generated gate.
        --
        -- Asking completely *first* is therefore actively worse, and was
        -- measured so: `Trans` in `init-prelude` has a bare chain the
        -- complete procedure equates to `w` and the stock kernel does not,
        -- so it took the unboxed plan and the exact generated gate rejected it
        -- — where the elaborator's own refusal had sent it to the boxing
        -- retry, which the stock kernel accepts. Coverage went 125 → 124. Second
        -- refusal costs nothing and cannot lose a plan that already works:
        -- every accepted declaration keeps the route chosen by the first
        -- procedure, and the complete procedure is consulted only where
        -- the alternative is a decline.
        if let some p ← attempt (fun a b => isLevelDefEq a b) then return p
        if let some p ← attempt (fun a b => LevelAlgebra.isLevelDefEqComplete a b) then
          return p
        let raw := if nf == 1 then ℓs[0]! else (ℓs.foldl mkLevelMax' .zero).normalize
        badShape s!"{cn}'s fields reach Sort {raw} and the carrier is Sort {w}: no \
          pad or recursive box closes the gap"

  -- A pad at a level `dsingOk` cannot build is discharged by transport
  -- along the lift's eta ([`InductiveModels.unitAtUniq`]) — a recursor call and
  -- proof irrelevance. The `False`-Π pad this replaces needed `funext`
  -- here, and with it `Quot.sound` and a wait on the input's quotient; the
  -- construction now splices neither.
  let natT : Expr := .const `Nat []
  let fibreAt := fun (ps : Array Expr) => do
    let pads ← padsAt plans
    let cs ← pctorsAt exportCtors plans pads ps
    withLocalDeclD `n natT fun n =>
      return (cs, ← mkLambdaFVars #[n] (← fibreTower w cs 0 n))

  -- Which constructors carry the recursion, and where. Empty for a
  -- non-recursive declaration, in which case everything below degenerates
  -- to the single tag tower the previous tranche had.
  let slots : Array (Option Nat) ← site.withParams fun ps =>
    exportCtors.mapM fun (cn, cty) => do
      let tele ← instForall cty ps
      recSlotOf tname np ni cn (numForalls tele) tele wTagged
        w.normalize.dec.isSome (labelFactored tname np exportCtors)
  let baseJ := (Array.range nc).filter fun j => slots[j]!.isNone
  let stepJ := (Array.range nc).filter fun j => slots[j]!.isSome
  -- **Arm E has already taken every recursive declaration without a base
  -- constructor**, and now takes the whole of that shape class rather than its
  -- linear corner: reaching the tuple tower at all means `recSlotOf` accepted
  -- every constructor, so each has exactly one recursive field and that
  -- occurrence is bare — which is precisely arm E's guard once `baseJ` is
  -- empty. This is therefore an assertion about the route classification and
  -- not a shape the tower declines; the tower below would in fact build the
  -- zero-base spine, and it must not, because the exact model of an empty
  -- carrier is the empty carrier and not a tower over it.
  if isRec && baseJ.isEmpty then
    badShape s!"internal: {tname}'s empty recursive shape missed the empty route"
  -- export constructor index ↦ its tag *within its own tower*
  let tagOf : Array Nat := (Array.range nc).map fun j =>
    let tower := if slots[j]!.isNone then baseJ else stepJ
    (tower.findIdx? (· == j)).getD 0

  -- The tag tower of a set of constructors, at a parameter scope. `sub` is
  -- the shorter spine's fibre `V n`, which a step constructor's chain
  -- stores in place of its recursive field; base constructors never look
  -- at it.
  let towerAt : Array Expr → Array Nat → Expr → GenM (Array PCtor × Expr) :=
    fun ps js sub => do
    let pads ← padsAt plans
    let cs : Array PCtor ← js.mapM fun j => do
      let (_, cty) := exportCtors[j]!
      let tele0 ← instForall cty ps
      let nf := numForalls tele0
      let tele ← spineSwap tname sub nf tele0
      let pl : CPlan := plans[j]!
      let (chain, _) ← chainTy pads[j]! pl.boxed nf tele
      pure { tele, nf, pad? := pads[j]!, boxed := pl.boxed, chain }
    let fib ← withLocalDeclD `tag natT fun tg =>
      do mkLambdaFVars #[tg] (← fibreTower w cs 0 tg)
    return (cs, fib)

  -- `V : Nat → Sort w`, the spine tower: base chains at spine 0, step
  -- chains at every successor, with the predecessor's fibre plugged in.
  let spineAt := fun (ps : Array Expr) => do
    let (_, bfib) ← towerAt ps baseJ (.sort w)
    let zc := psigmaT (.succ .zero) w natT bfib
    let sc ← withLocalDeclD `n natT fun n =>
      withLocalDeclD `R (.sort w) fun R => do
        let (_, sfib) ← towerAt ps stepJ R
        mkLambdaFVars #[n, R] (psigmaT (.succ .zero) w natT sfib)
    withLocalDeclD `n natT fun n =>
      mkLambdaFVars #[n]
        (natRec (.succ w) (.lam `x natT (.sort w) .default) zc sc n)

  -- ── the carrier ──
  -- Non-recursive: one tag tower under a `Nat`. Linearly recursive: the
  -- spine tower, `Σ'(n : Nat), V n`.
  let carrierAt := fun (ps : Array Expr) => do
    if isRec then pure (psigmaT (.succ .zero) w natT (← spineAt ps))
    else do pure (psigmaT (.succ .zero) w natT (← fibreAt ps).2
  )
  let selfVal ← site.withParams fun ps => do mkLambdaFVars ps (← carrierAt ps)
  let dSelf := Declaration.defnDecl
    { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfVal
      hints := ← hintsFor selfVal, safety := .safe }
  addChecked dSelf
  out := out.push dSelf

  -- ── the constructors ──
  for j in [0:nc] do
    let (_, cty) := exportCtors[j]!
    let ty := publicSource cty
    let val ← site.withParams fun ps => do
      if !isRec then
        let (cs, fib) ← fibreAt ps
        let c := cs[j]!
        forallBoundedTelescope c.tele (some c.nf) fun fs _ => do
          let tup ← chainTuple c.pad? c.boxed c.nf c.tele fs
          mkLambdaFVars (ps ++ fs)
            (psigmaMk (.succ .zero) w natT fib (natNumeral j) tup)
      else do
        -- The binders come from the **restored** telescope: the recursive
        -- field's type there is `T._model.self p⃗`, i.e. the spine pair, and
        -- what goes into the chain is its second component.
        let spine ← spineAt ps
        let rtele ← instForall ty ps
        let nf := numForalls rtele
        forallBoundedTelescope rtele (some nf) fun fs _ => do
          let mkOuter := fun (n tup : Expr) =>
            psigmaMk (.succ .zero) w natT spine n tup
          match slots[j]! with
          | none =>
            let (bcs, bfib) ← towerAt ps baseJ (.sort w)
            let c := bcs[tagOf[j]!]!
            let tup ← chainTuple c.pad? c.boxed c.nf c.tele fs
            mkLambdaFVars (ps ++ fs) (mkOuter (natNumeral 0)
              (psigmaMk (.succ .zero) w natT bfib (natNumeral (tagOf[j]!)) tup))
          | some k =>
            let r := fs[k]!
            let rn := psigmaFst (.succ .zero) w natT spine r
            let rv2 := psigmaSnd (.succ .zero) w natT spine r
            let (scs, sfib) ← towerAt ps stepJ (mkApp spine rn).headBeta
            let c := scs[tagOf[j]!]!
            let tup ← chainTuple c.pad? c.boxed c.nf c.tele (fs.set! k rv2)
            mkLambdaFVars (ps ++ fs) (mkOuter (.app (.const `Nat.succ []) rn)
              (psigmaMk (.succ .zero) w natT sfib (natNumeral (tagOf[j]!)) tup))
    let d := Declaration.defnDecl
      { name := ctorN j, levelParams := lparams, type := ty, value := val
        hints := ← hintsFor val, safety := .safe }
    addChecked d
    out := out.push d

  -- ── the recursor ──
  let recVal ← forallBoundedTelescope installedRecTy
      (some (np + 1 + nc + 1)) fun bs _ => do
    let ps := bs.extract 0 np
    let motive := bs[np]!
    let minors := bs.extract (np + 1) (np + 1 + nc)
    let major := bs[bs.size - 1]!
    if !isRec then
      let (cs, fib) ← fibreAt ps
      -- One call at every constructor count, including zero: at zero
      -- constructors `fib` is [`InductiveModels.emptyAt`] `w` at every tag and
      -- [`InductiveModels.stepTower`] is its eliminator, which is exactly the
      -- term the special case beside this one used to build. `headBeta` is
      -- what keeps that term the same term: the tower returns a `Nat.rec`
      -- application wherever there is a constructor to case on, so the
      -- reduction only ever fires on the constructorless tower's own lambda.
      let minor ←
        withLocalDeclD `n natT fun n => do
          withLocalDeclD `f (mkApp fib n).headBeta fun f => do
            mkLambdaFVars #[n, f]
              (mkApp (← stepTower v w eqi fib (fun z => mkApp motive z)
                (fun j vs => mkAppN minors[j]! vs) cs 0 n) f).headBeta
      mkLambdaFVars bs (psigmaRec v (.succ .zero) w natT fib motive minor major)
    else do
      -- `PSigma'.rec'` on the outer pair, `Nat.rec` on the spine, the tag
      -- towers inside each level, `PSigma'.rec'` down each chain.
      let spine ← spineAt ps
      let mkOuter := fun (n tup : Expr) => psigmaMk (.succ .zero) w natT spine n tup
      -- the Nat.rec motive: `fun n => (x : V n) → motive ⟨n, x⟩`
      let nmot ← withLocalDeclD `n natT fun n =>
        withLocalDeclD `x (mkApp spine n).headBeta fun x => do
          mkLambdaFVars #[n] (← mkForallFVars #[x] (mkApp motive (mkOuter n x)))
      -- spine 0: the base tower
      let zc ← do
        let (bcs, bfib) ← towerAt ps baseJ (.sort w)
        withLocalDeclD `x (psigmaT (.succ .zero) w natT bfib) fun x => do
          let tgt := fun (tup : Expr) => mkApp motive (mkOuter (natNumeral 0) tup)
          let minorOf := fun (b : Nat) (vs : Array Expr) => mkAppN minors[baseJ[b]!]! vs
          let inner ← withLocalDeclD `tag natT fun tg =>
            withLocalDeclD `f (mkApp bfib tg).headBeta fun f => do
              mkLambdaFVars #[tg, f]
                (mkApp (← stepTower v w eqi bfib tgt minorOf bcs 0 tg) f)
          let mot ← withLocalDeclD `z (psigmaT (.succ .zero) w natT bfib) fun z =>
            mkLambdaFVars #[z] (mkApp motive (mkOuter (natNumeral 0) z))
          mkLambdaFVars #[x]
            (psigmaRec v (.succ .zero) w natT bfib mot inner x)
      -- spine n+1: the step tower, with the induction hypothesis in hand
      let sc ← withLocalDeclD `n natT fun n =>
        withLocalDeclD `ih (mkApp nmot n).headBeta fun ih => do
          let sub := (mkApp spine n).headBeta
          let (scs, sfib) ← towerAt ps stepJ sub
          let nsucc := Expr.app (.const `Nat.succ []) n
          withLocalDeclD `x (psigmaT (.succ .zero) w natT sfib) fun x => do
            let tgt := fun (tup : Expr) => mkApp motive (mkOuter nsucc tup)
            let minorOf := fun (b : Nat) (vs : Array Expr) =>
              let j := stepJ[b]!
              let k := (slots[j]!).getD 0
              let sv := vs[k]!
              mkAppN minors[j]! ((vs.set! k (mkOuter n sv)).push (mkApp ih sv))
            let inner ← withLocalDeclD `tag natT fun tg =>
              withLocalDeclD `f (mkApp sfib tg).headBeta fun f => do
                mkLambdaFVars #[tg, f]
                  (mkApp (← stepTower v w eqi sfib tgt minorOf scs 0 tg) f)
            let mot ← withLocalDeclD `z (psigmaT (.succ .zero) w natT sfib) fun z =>
              mkLambdaFVars #[z] (mkApp motive (mkOuter nsucc z))
            mkLambdaFVars #[n, ih, x]
              (psigmaRec v (.succ .zero) w natT sfib mot inner x)
      let minor ← withLocalDeclD `n natT fun n =>
        withLocalDeclD `x (mkApp spine n).headBeta fun x => do
          mkLambdaFVars #[n, x]
            (mkApp (natRec (mkLevelIMax' w v).normalize nmot zc sc n) x)
      mkLambdaFVars bs (psigmaRec v (.succ .zero) w natT spine motive minor major)
  let dRec := Declaration.defnDecl
    { name := recN, levelParams := rv.levelParams, type := publicRecTy, value := recVal
      hints := ← hintsFor recVal, safety := .safe }
  addChecked dRec
  out := out.push dRec
  return { st with out, spliced }

end InductiveModels
