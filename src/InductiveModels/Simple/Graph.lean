import InductiveModels.Simple.GraphKit

/-!
# The graph arm's construction: the recursion by its graph

`graphArm` and the context it reads. The Church-conjunction, telescope and
`funext` kit it shares with the carve and recovery arms is one module below it.
-/

open Lean Meta

namespace InductiveModels

/-- Everything [`InductiveModels.graphArm`] needs about the declaration it is
modelling, settled before a single declaration is emitted so that a decline
costs no splice. -/
structure GraphCtx where
  tname : Name
  np : Nat
  ni : Nat
  nf : Nat
  /-- The declaration's own levels, and the recursor's (`v` in front). -/
  us : List Level
  recLs : List Level
  lparams : List Name
  recLevels : List Name
  /-- The motive universe. -/
  v : Level
  selfN : Name
  ctorN0 : Name
  recN : Name
  indN : Name
  grN : Name
  grMkN : Name
  grInvTN : Name
  grInvN : Name
  grUniqN : Name
  grExN : Name
  recGrN : Name
  /-- The declaration's own type, and the model constructor's — **restored**,
  so a recursive field's type is `T._model.self p⃗ e⃗`. -/
  memberTy : Expr
  ctorTy : Expr
  /-- Per field: is it data (rather than a proof), and if so which index
  position it *is*; and, for a recursive field, its binder count. -/
  isData : Array Bool
  idxPos : Array Nat
  /-- Index positions not supplied by a constructor data field.  The graph
  inversion packs exactly this dependent subsequence and transports its step
  value from the constructor indices to the caller indices. -/
  nonPiv : Array Nat
  recNb : Array (Option Nat)
  eqi : EqInfo
  /-- The `funext` the `Graph.unique` congruence transports along, `none` when
  no recursive field has a binder and none is reached. -/
  fx? : Option Name
  deriving Inhabited

/-- **The graph arm**, emitting `graph`, `graph_mk`, `graph_inv_ty`,
`graph_inv`, `graph_unique`, `graph_exists`, `rec_0` and `rec_graph`. The
carrier, the constructor and the `Prop`-motive recursor `ind` are the Church
route's own and are emitted by the caller; the ι theorem is the caller's too,
because its *statement* is shared with every other arm and only its proof is
this one's. -/
def graphArm (c : GraphCtx) (recTy : Expr) : GenM (Array Declaration) := do
  let np := c.np
  let ni := c.ni
  let nf := c.nf
  let nnp := c.nonPiv.size
  -- the recursive slots, in field order
  let rs := (Array.range nf).filter fun i => c.recNb[i]!.isSome
  let nr := rs.size

  -- **One scope for the whole arm**: the parameters, the motive and the step,
  -- read off the recursor's own type rather than rebuilt. `rest` is what is
  -- left of that type — `∀ ι⃗ (t : Self ι⃗), motive ι⃗ t` — and the two
  -- declarations that need the full telescope continue it rather than
  -- reopening.
  forallBoundedTelescope recTy (some (np + 2)) fun bs rest => do
    let mut out : Array Declaration := #[]
    let ps := bs.extract 0 np
    let motive := bs[np]!
    let step := bs[np + 1]!
    let pre := ps ++ #[motive, step]

    let selfAt := fun (is : Array Expr) => mkAppN (.const c.selfN c.us) (ps ++ is)
    let ctorAt := fun (fs : Array Expr) => mkAppN (.const c.ctorN0 c.us) (ps ++ fs)
    let motAt := fun (is : Array Expr) (t : Expr) => mkAppN motive (is.push t)
    let grAt := fun (is : Array Expr) (t val : Expr) =>
      mkAppN (.const c.grN c.recLs) (pre ++ is ++ #[t, val])
    let grInvAt := fun (is : Array Expr) (t val : Expr) =>
      mkAppN (.const c.grInvTN c.recLs) (pre ++ is ++ #[t, val])
    let idxTele ← instForall c.memberTy ps
    let ctorTele ← instForall c.ctorTy ps

    -- The dependent tuple of non-pivot indices at a caller's pivot values.
    -- Pivot types cannot mention non-pivots (the classifier checks that before
    -- entering this arm), so leaving the pivots free while closing exactly the
    -- complementary subsequence is sound even when the two are interleaved.
    let pkAt := fun (is : Array Expr) => do
      if nnp == 0 then return (none : Option (Expr × Level))
      forallBoundedTelescope idxTele (some ni) fun opened _ => do
        let (pk, ℓ) ← packTyAt opened c.nonPiv 0
        pure (some (pk.replaceFVars opened is, ℓ))

    let packedAt := fun (pk : Expr) (is : Array Expr) =>
      packChain nnp pk (c.nonPiv.map (is[·]!)) 0

    let indexEqAt := fun (is ctorIs : Array Expr) => do
      let some (pk, ℓ) ← pkAt is
        | badShape "the graph index equality was requested without a non-pivot"
      let lhs ← packedAt pk ctorIs
      let rhs ← packedAt pk is
      pure (pk, ℓ, lhs, rhs, c.eqi.mk' ℓ pk lhs rhs)

    -- Move a step value from the constructor's fibre to the arbitrary fibre
    -- at which GraphInv is queried.  The motive transports a function over the
    -- proof-valued carrier: after the indices move, proof irrelevance identifies
    -- its argument with the transported constructor proof, so applying it to
    -- the caller's `t` needs no second equality.
    let transportStep := fun (is : Array Expr) (t : Expr) (ctorIs : Array Expr)
        (value heq : Expr) => do
      if nnp == 0 then return value
      let (pk, ℓ, lhs, rhs, _) ← indexEqAt is ctorIs
      let motiveE ← withLocalDeclD `y pk fun y => do
        withLocalDeclD `hy (c.eqi.mk' ℓ pk lhs y) fun hy => do
          let ys ← unpackChain nnp pk y
          let mut full := is
          for k in [0:nnp] do full := full.set! c.nonPiv[k]! ys[k]!
          withLocalDeclD `s (selfAt full) fun s => do
            let body ← mkForallFVars #[s] (motAt full s)
            mkLambdaFVars #[y, hy] body
      let base ← withLocalDeclD `s (selfAt ctorIs) fun s =>
        mkLambdaFVars #[s] value
      pure (mkApp (c.eqi.recAt c.v ℓ pk lhs motiveE base rhs heq) t)

    -- A recursive field's own binders, and the index vector it lands at. The
    -- telescope is opened **bounded**: `forallTelescope` would whnf through
    -- `T._model.self` and open the Church encoding's own Π as well.
    let recAt := fun (f : Expr) (nb : Nat) (k : Array Expr → Array Expr → GenM Expr) => do
      forallBoundedTelescope (← ityp f) (some nb) fun zs res => do
        let some args ← ownerAppArgs? c.selfN np ni res
          | badShape s!"a recursive field of {c.tname} does not land at {c.selfN}"
        k zs (args.extract np args.size)

    -- The constructor's field telescope. `is?` supplies the data fields.
    let fields := fun (is? : Option (Array Expr))
        (k : Array Expr → Array Expr → Expr → GenM Expr) =>
      ctorFieldsAux is?.isSome c.isData c.idxPos (is?.getD #[]) nf 0 ctorTele #[] #[] k

    -- The index vector a walked telescope ends at.
    let idxOfRes := fun (res : Expr) => do
      let some args ← ownerAppArgs? c.selfN np ni res
        | badShape s!"{c.ctorN0}'s result is not {c.selfN} at {np} parameters and {ni} indices"
      pure (args.extract np args.size)

    -- `g_i : ∀ z⃗_i, motive e⃗_i (f_i z⃗_i)`, the value functions.
    let gTysAt := fun (fs : Array Expr) => rs.mapM fun i => do
      let t ← recAt fs[i]! c.recNb[i]!.get! fun zs ris =>
        mkForallFVars zs (motAt ris (mkAppN fs[i]! zs))
      pure (Name.mkSimple s!"g{i}", t)
    -- `hg_i : ∀ z⃗_i, Graph e⃗_i (f_i z⃗_i) (g_i z⃗_i)`.
    let hTysAt := fun (fs gs : Array Expr) => (Array.range nr).mapM fun j => do
      let i := rs[j]!
      let t ← recAt fs[i]! c.recNb[i]!.get! fun zs ris =>
        mkForallFVars zs (grAt ris (mkAppN fs[i]! zs) (mkAppN gs[j]! zs))
      pure (Name.mkSimple s!"hg{i}", t)

    -- ── `Q`, and the graph's one closure rule at it ──
    let qTy ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `s (selfAt is) fun s =>
        withLocalDeclD `m (motAt is s) fun m =>
          mkForallFVars (is ++ #[s, m]) (.sort .zero)
    let qStepTy := fun (Q : Expr) =>
      fields none fun fs bnd res => do
        let e ← idxOfRes res
        withLocalsD (← gTysAt fs) 0 #[] fun gs => do
          let qTys ← (Array.range nr).mapM fun j => do
            let i := rs[j]!
            let t ← recAt fs[i]! c.recNb[i]!.get! fun zs ris =>
              mkForallFVars zs (mkAppN Q (ris ++ #[mkAppN fs[i]! zs, mkAppN gs[j]! zs]))
            pure (Name.mkSimple s!"q{i}", t)
          withLocalsD qTys 0 #[] fun qs =>
            mkForallFVars (bnd ++ gs ++ qs)
              (mkAppN Q (e ++ #[ctorAt fs, mkAppN step (fs ++ gs)]))

    -- ── `Graph` ──
    let grTy ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `val (motAt is t) fun val =>
          mkForallFVars (pre ++ is ++ #[t, val]) (.sort .zero)
    let grVal ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `val (motAt is t) fun val =>
          withLocalDeclD `Q qTy fun Q => do
            let body ← mkForallFVars #[Q]
              (.forallE `q (← qStepTy Q) (mkAppN Q (is ++ #[t, val])) .default)
            mkLambdaFVars (pre ++ is ++ #[t, val]) body
    let dGr := Declaration.defnDecl
      { name := c.grN, levelParams := c.recLevels, type := grTy, value := grVal
        hints := ← hintsFor grVal, safety := .safe }
    addChecked dGr
    out := out.push dGr

    -- ── `Graph.mk` ──
    let grMkTy ← fields none fun fs bnd res => do
      let e ← idxOfRes res
      withLocalsD (← gTysAt fs) 0 #[] fun gs => do
        withLocalsD (← hTysAt fs gs) 0 #[] fun hs =>
          mkForallFVars (pre ++ bnd ++ gs ++ hs)
            (grAt e (ctorAt fs) (mkAppN step (fs ++ gs)))
    let grMkVal ← fields none fun fs bnd _ => do
      withLocalsD (← gTysAt fs) 0 #[] fun gs => do
        withLocalsD (← hTysAt fs gs) 0 #[] fun hs =>
          withLocalDeclD `Q qTy fun Q => do
            withLocalDeclD `q (← qStepTy Q) fun q => do
              let qargs ← (Array.range nr).mapM fun j => do
                let i := rs[j]!
                recAt fs[i]! c.recNb[i]!.get! fun zs _ =>
                  mkLambdaFVars zs (mkAppN (mkAppN hs[j]! zs) #[Q, q])
              mkLambdaFVars (pre ++ bnd ++ gs ++ hs)
                (← mkLambdaFVars #[Q, q] (mkAppN q (fs ++ gs ++ qargs)))
    let dGrMk := Declaration.thmDecl
      { name := c.grMkN, levelParams := c.recLevels, type := grMkTy, value := grMkVal }
    addChecked dGrMk
    out := out.push dGrMk

    -- ── `GraphInv` ──
    -- The `k` argument's type, shared by the definition and by the two places
    -- that build or consume an inhabitant of it.
    let invArmTyAt := fun (is : Array Expr) (t val : Expr) (fs ctorIs : Array Expr)
        (D : Expr) => do
      withLocalsD (← gTysAt fs) 0 #[] fun gs => do
        withLocalsD (← hTysAt fs gs) 0 #[] fun hs => do
          if nnp == 0 then
            let eq := c.eqi.mk' c.v (motAt is t) val (mkAppN step (fs ++ gs))
            mkForallFVars (gs ++ hs) (.forallE `he eq D .default)
          else
            let (_, _, _, _, idxEq) ← indexEqAt is ctorIs
            withLocalDeclD `hidx idxEq fun hidx => do
              let rhs ← transportStep is t ctorIs (mkAppN step (fs ++ gs)) hidx
              let eq := c.eqi.mk' c.v (motAt is t) val rhs
              mkForallFVars (gs ++ hs ++ #[hidx]) (.forallE `he eq D .default)
    let grInvVal ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `val (motAt is t) fun val => do
          let body ← fields (some is) fun fs bnd res => do
            let e ← idxOfRes res
            withLocalDeclD `D (.sort .zero) fun D => do
              mkForallFVars (bnd ++ #[D])
                (.forallE `k (← invArmTyAt is t val fs e D) D .default)
          mkLambdaFVars (pre ++ is ++ #[t, val]) body
    let dGrInvT := Declaration.defnDecl
      { name := c.grInvTN, levelParams := c.recLevels, type := grTy, value := grInvVal
        hints := ← hintsFor grInvVal, safety := .safe }
    addChecked dGrInvT
    out := out.push dGrInvT

    -- ── `Graph.inv` ──
    -- Fold at `Graph ∧ GraphInv`: the graph alone is not closed enough to
    -- rebuild the sub-values' graph facts. The `rfl` at the end is where
    -- proof irrelevance does the work — the fold's own fields and the
    -- inversion's quantified ones are two proofs of one proposition, so
    -- `step f⃗ g⃗` and `step f'⃗ g⃗` are the same term.
    let grInvThmTy ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `val (motAt is t) fun val =>
          mkForallFVars (pre ++ is ++ #[t, val])
            (.forallE `g (grAt is t val) (grInvAt is t val) .default)
    let grInvThmVal ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `val (motAt is t) fun val =>
          withLocalDeclD `g (grAt is t val) fun g => do
            let qArg ← forallBoundedTelescope idxTele (some ni) fun is' _ =>
              withLocalDeclD `s (selfAt is') fun s =>
                withLocalDeclD `w (motAt is' s) fun w =>
                  mkLambdaFVars (is' ++ #[s, w]) (andCOf (grAt is' s w) (grInvAt is' s w))
            let qStepArg ← fields none fun fs bnd res => do
              let e ← idxOfRes res
              withLocalsD (← gTysAt fs) 0 #[] fun gs => do
                let ihTys ← (Array.range nr).mapM fun j => do
                  let i := rs[j]!
                  let t' ← recAt fs[i]! c.recNb[i]!.get! fun zs ris =>
                    mkForallFVars zs
                      (andCOf (grAt ris (mkAppN fs[i]! zs) (mkAppN gs[j]! zs))
                        (grInvAt ris (mkAppN fs[i]! zs) (mkAppN gs[j]! zs)))
                  pure (Name.mkSimple s!"ih{i}", t')
                withLocalsD ihTys 0 #[] fun ihs => do
                  -- the left projection of each `AndC`, pointwise
                  let hgs ← (Array.range nr).mapM fun j => do
                    let i := rs[j]!
                    recAt fs[i]! c.recNb[i]!.get! fun zs ris => do
                      let gt := grAt ris (mkAppN fs[i]! zs) (mkAppN gs[j]! zs)
                      let it := grInvAt ris (mkAppN fs[i]! zs) (mkAppN gs[j]! zs)
                      let proj ← withLocalDeclD `a gt fun a =>
                        withLocalDeclD `b it fun b => mkLambdaFVars #[a, b] a
                      mkLambdaFVars zs (mkAppN (mkAppN ihs[j]! zs) #[gt, proj])
                  let major := ctorAt fs
                  let val' := mkAppN step (fs ++ gs)
                  let aTerm := mkAppN (.const c.grMkN c.recLs) (pre ++ bnd ++ gs ++ hgs)
                  let bTerm ← fields (some e) fun fs' bnd' res' => do
                    withLocalDeclD `D (.sort .zero) fun D => do
                      let e' ← idxOfRes res'
                      withLocalDeclD `k (← invArmTyAt e major val' fs' e' D) fun k' => do
                        let args ← if nnp == 0 then
                            pure (gs ++ hgs ++ #[c.eqi.refl' c.v (motAt e major) val'])
                          else do
                            let (pk, ℓ, lhs, _, _) ← indexEqAt e e'
                            pure (gs ++ hgs ++ #[c.eqi.refl' ℓ pk lhs,
                              c.eqi.refl' c.v (motAt e major) val'])
                        mkLambdaFVars (bnd' ++ #[D, k']) (mkAppN k' args)
                  let aT := grAt e major val'
                  let bT := grInvAt e major val'
                  let pair ← withLocalDeclD `D (.sort .zero) fun D =>
                    withLocalDeclD `k (.forallE `a aT (.forallE `b bT D .default) .default)
                      fun k' => mkLambdaFVars #[D, k'] (mkAppN k' #[aTerm, bTerm])
                  mkLambdaFVars (bnd ++ gs ++ ihs) pair
            let fin ← withLocalDeclD `a (grAt is t val) fun a =>
              withLocalDeclD `b (grInvAt is t val) fun b => mkLambdaFVars #[a, b] b
            mkLambdaFVars (pre ++ is ++ #[t, val, g])
              (mkAppN g #[qArg, qStepArg, grInvAt is t val, fin])
    let dGrInv := Declaration.thmDecl
      { name := c.grInvN, levelParams := c.recLevels, type := grInvThmTy
        value := grInvThmVal }
    addChecked dGrInv
    out := out.push dGrInv

    -- ── `Graph.unique` ──
    -- Single-valuedness, by the free `Prop`-motive recursor. This is the one
    -- place `funext` enters, and only for a recursive field with binders.
    let uniqTy ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `a (motAt is t) fun a =>
          withLocalDeclD `b (motAt is t) fun b =>
            mkForallFVars (pre ++ is ++ #[t, a, b])
              (.forallE `ga (grAt is t a)
                (.forallE `gb (grAt is t b) (c.eqi.mk' c.v (motAt is t) a b) .default)
                .default)
    let indMotUniq ← forallBoundedTelescope idxTele (some ni) fun is' _ =>
      withLocalDeclD `t' (selfAt is') fun t' => do
        let inner ← withLocalDeclD `a' (motAt is' t') fun a' =>
          withLocalDeclD `b' (motAt is' t') fun b' =>
            mkForallFVars #[a', b']
              (.forallE `ga' (grAt is' t' a')
                (.forallE `gb' (grAt is' t' b') (c.eqi.mk' c.v (motAt is' t') a' b')
                  .default) .default)
        mkLambdaFVars (is' ++ #[t']) inner
    let uniqVal ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `a (motAt is t) fun a =>
          withLocalDeclD `b (motAt is t) fun b =>
            withLocalDeclD `ga (grAt is t a) fun ga =>
              withLocalDeclD `gb (grAt is t b) fun gb => do
                let minor ← fields none fun fs bnd res => do
                  let e ← idxOfRes res
                  let major := ctorAt fs
                  let α := motAt e major
                  let ihTys ← rs.mapM fun i => do
                    let t' ← recAt fs[i]! c.recNb[i]!.get! fun zs ris =>
                      mkForallFVars zs
                        (mkAppN indMotUniq (ris ++ #[mkAppN fs[i]! zs])).headBeta
                    pure (Name.mkSimple s!"ih{i}", t')
                  withLocalsD ihTys 0 #[] fun ihs =>
                    withLocalDeclD `x (motAt e major) fun x =>
                      withLocalDeclD `y (motAt e major) fun y =>
                        withLocalDeclD `gx (grAt e major x) fun gx =>
                          withLocalDeclD `gy (grAt e major y) fun gy => do
                            let goal := c.eqi.mk' c.v α x y
                            -- the fields inversion quantifies are the **proof**
                            -- ones; the data fields are the indices and are
                            -- already fixed by the point `GraphInv` is at.
                            let pf := (Array.range nf).filterMap fun i =>
                              if c.isData[i]! then none else some fs[i]!
                            let withIdxEq := fun (k : Array Expr → GenM Expr) => do
                              if nnp == 0 then k #[]
                              else
                                let (_, _, _, _, eqTy) ← indexEqAt e e
                                withLocalDeclD `hidx eqTy fun hidx => k #[hidx]
                            let contA ←
                              withLocalsD (← gTysAt fs) 0 #[] fun gA => do
                                withLocalsD (← hTysAt fs gA) 0 #[] fun hA =>
                                  withIdxEq fun hidxA =>
                                    withLocalDeclD `ea
                                      (c.eqi.mk' c.v α x (mkAppN step (fs ++ gA))) fun eA => do
                                      let contB ←
                                        withLocalsD (← gTysAt fs) 0 #[] fun gB => do
                                          withLocalsD (← hTysAt fs gB) 0 #[] fun hB =>
                                            withIdxEq fun hidxB =>
                                              withLocalDeclD `eb
                                                (c.eqi.mk' c.v α y (mkAppN step (fs ++ gB)))
                                                fun eB => do
                                                let pfs ← (Array.range nr).mapM fun j => do
                                                  let i := rs[j]!
                                                  recAt fs[i]! c.recNb[i]!.get! fun zs _ => do
                                                    let pt := mkAppN (mkAppN ihs[j]! zs)
                                                      #[mkAppN gA[j]! zs, mkAppN gB[j]! zs,
                                                        mkAppN hA[j]! zs, mkAppN hB[j]! zs]
                                                    funextUp c.fx? zs zs.size gA[j]! gB[j]! pt
                                                let cong ← congrChain c.eqi c.v α
                                                  (fun gv => mkAppN step (fs ++ gv)) gA gB pfs
                                                let sb ← symmOf c.eqi c.v α y
                                                  (mkAppN step (fs ++ gB)) eB
                                                let t2 ← transOf c.eqi c.v α
                                                  (mkAppN step (fs ++ gA))
                                                  (mkAppN step (fs ++ gB)) y cong sb
                                                let whole ← transOf c.eqi c.v α x
                                                  (mkAppN step (fs ++ gA)) y eA t2
                                                mkLambdaFVars
                                                  (gB ++ hB ++ hidxB ++ #[eB]) whole
                                      let invB := mkAppN (.const c.grInvN c.recLs)
                                        (pre ++ e ++ #[major, y, gy])
                                      mkLambdaFVars (gA ++ hA ++ hidxA ++ #[eA])
                                        (mkAppN invB (pf ++ #[goal, contB]))
                            let invA := mkAppN (.const c.grInvN c.recLs)
                              (pre ++ e ++ #[major, x, gx])
                            mkLambdaFVars (bnd ++ ihs ++ #[x, y, gx, gy])
                              (mkAppN invA (pf ++ #[goal, contA]))
                mkLambdaFVars (pre ++ is ++ #[t, a, b, ga, gb])
                  (mkAppN (mkAppN (.const c.indN c.us) (ps ++ #[indMotUniq, minor] ++ is ++ #[t]))
                    #[a, b, ga, gb])
    let dGrUniq := Declaration.thmDecl
      { name := c.grUniqN, levelParams := c.recLevels, type := uniqTy, value := uniqVal }
    addChecked dGrUniq
    out := out.push dGrUniq

    -- ── `Graph.exists` ──
    -- Totality, again by the `Prop`-motive recursor. `Classical.choice` picks
    -- the sub-values here, and single-valuedness above is what makes the
    -- choice harmless. The `Nonempty` is of the **`PSigma'` of value and graph
    -- proof**, never of `motive ι⃗ t`: that is the whole difference from the
    -- route described above refutes.
    let neAt := fun (is : Array Expr) (t : Expr) => do
      let α := motAt is t
      let β ← withLocalDeclD `val α fun val => mkLambdaFVars #[val] (grAt is t val)
      let σ := psigmaT c.v .zero α β
      let ℓσ := c.v.normalize
      pure (mkAppN (.const `Nonempty [ℓσ]) #[σ], σ, α, β, ℓσ)
    let grExTy ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t => do
        let (ne, _, _, _, _) ← neAt is t
        mkForallFVars (pre ++ is ++ #[t]) ne
    let indMotEx ← forallBoundedTelescope idxTele (some ni) fun is' _ =>
      withLocalDeclD `t' (selfAt is') fun t' => do
        let (ne, _, _, _, _) ← neAt is' t'
        mkLambdaFVars (is' ++ #[t']) ne
    let grExVal ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t => do
        let minor ← fields none fun fs bnd res => do
          let e ← idxOfRes res
          let ihTys ← rs.mapM fun i => do
            let t' ← recAt fs[i]! c.recNb[i]!.get! fun zs ris => do
              let (ne, _, _, _, _) ← neAt ris (mkAppN fs[i]! zs)
              mkForallFVars zs ne
            pure (Name.mkSimple s!"ih{i}", t')
          withLocalsD ihTys 0 #[] fun ihs => do
            let pick := fun (j : Nat) (snd : Bool) => do
              let i := rs[j]!
              recAt fs[i]! c.recNb[i]!.get! fun zs ris => do
                let (_, σ, α, β, ℓσ) ← neAt ris (mkAppN fs[i]! zs)
                let ch := mkAppN (.const `Classical.choice [ℓσ]) #[σ, mkAppN ihs[j]! zs]
                mkLambdaFVars zs
                  (if snd then psigmaSnd c.v .zero α β ch else psigmaFst c.v .zero α β ch)
            let ghat ← (Array.range nr).mapM fun j => pick j false
            let hhat ← (Array.range nr).mapM fun j => pick j true
            let (_, σ0, α0, β0, ℓσ0) ← neAt e (ctorAt fs)
            let value := mkAppN step (fs ++ ghat)
            let proof := mkAppN (.const c.grMkN c.recLs) (pre ++ fs ++ ghat ++ hhat)
            mkLambdaFVars (bnd ++ ihs)
              (mkAppN (.const `Nonempty.intro [ℓσ0])
                #[σ0, psigmaMk c.v .zero α0 β0 value proof])
        mkLambdaFVars (pre ++ is ++ #[t])
          (mkAppN (.const c.indN c.us) (ps ++ #[indMotEx, minor] ++ is ++ #[t]))
    let dGrEx := Declaration.thmDecl
      { name := c.grExN, levelParams := c.recLevels, type := grExTy, value := grExVal }
    addChecked dGrEx
    out := out.push dGrEx

    -- ── the recursor, and the graph fact about it ──
    let recVal ← forallBoundedTelescope rest (some (ni + 1)) fun bs2 _ => do
      let is := bs2.extract 0 ni
      let t := bs2[ni]!
      let (_, σ, α, β, ℓσ) ← neAt is t
      let ch := mkAppN (.const `Classical.choice [ℓσ])
        #[σ, mkAppN (.const c.grExN c.recLs) (pre ++ is ++ #[t])]
      mkLambdaFVars (pre ++ bs2) (psigmaFst c.v .zero α β ch)
    let dRec := Declaration.defnDecl
      { name := c.recN, levelParams := c.recLevels, type := recTy, value := recVal
        hints := ← hintsFor recVal, safety := .safe }
    addChecked dRec
    out := out.push dRec

    let rgTy ← forallBoundedTelescope rest (some (ni + 1)) fun bs2 _ => do
      let is := bs2.extract 0 ni
      let t := bs2[ni]!
      mkForallFVars (pre ++ bs2)
        (grAt is t (mkAppN (.const c.recN c.recLs) (pre ++ bs2)))
    let rgVal ← forallBoundedTelescope rest (some (ni + 1)) fun bs2 _ => do
      let is := bs2.extract 0 ni
      let t := bs2[ni]!
      let (_, σ, α, β, ℓσ) ← neAt is t
      let ch := mkAppN (.const `Classical.choice [ℓσ])
        #[σ, mkAppN (.const c.grExN c.recLs) (pre ++ is ++ #[t])]
      mkLambdaFVars (pre ++ bs2) (psigmaSnd c.v .zero α β ch)
    let dRg := Declaration.thmDecl
      { name := c.recGrN, levelParams := c.recLevels, type := rgTy, value := rgVal }
    addChecked dRg
    out := out.push dRg

    return out

end InductiveModels
