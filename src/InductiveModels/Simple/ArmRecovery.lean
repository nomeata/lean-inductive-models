import InductiveModels.Simple.Site
import InductiveModels.Simple.RecoveryKit
import InductiveModels.Simple.GraphKit

/-!
# The recovery arm: the indexed subsingleton, by one packed index equation
-/

open Lean Meta

namespace InductiveModels

def primArmRecovery (site : PrimSite) (st : PrimOut) : GenM PrimOut := do
  -- The site, under the names this arm has always read it by.
  let tname := site.tname
  let lparams := site.lparams
  let np := site.np
  let memberTy := site.memberTy
  let exportCtors := site.exportCtors
  let sourceCtors := site.sourceCtors
  let selfN := site.selfN
  let recN := site.recN
  let ctorN := site.ctorN
  let nc := site.nc
  let declaredMemberTy := site.declaredMemberTy
  let ni := site.ni
  let w := site.w
  let rv := site.rv
  let v := site.v
  let route := site.route
  let gIsData := site.gIsData
  let gIdxPos := site.gIdxPos
  let gPivotTransports := site.gPivotTransports
  let gNonPiv := site.gNonPiv
  let eqi := site.eqi
  let installedRecTy := site.installedRecTy
  let publicSource := site.publicSource
  let publicRecTy := site.publicRecTy
  let mut out := st.out
  let mut spliced := st.spliced
  -- ════ the recovery arm: the indexed subsingleton, by one packed index equation ════
  --
  -- Shape: one constructor, every field a `Prop` or a
  -- variable that literally *is* one of the output's indices. The kernel
  -- then grants a `Sort w` motive, and the model has to deliver it — the
  -- Church fold cannot, since it only eliminates into `Prop`.
  --
  -- **Ordinarily the index vector splits in two** (the analysis above): the *pivot*
  -- positions, each literally one of the constructor's data fields, and the
  -- rest. The model **substitutes** at the pivots — that is the only way a
  -- data field can come back at all, since a `Prop`'s proof yields nothing
  -- but proofs — and equates at the rest. So the carrier quantifies the
  -- constructor's `Prop` fields *at the pivots already supplied*, and
  -- Church-conjoins them with **one** `Eq` at the **non-pivot subsequence**
  -- packed into a `PSigma'` ([`InductiveModels.packTyAt`]) — the Henry-Ford
  -- equation, stated once because a later index's type may mention an
  -- earlier one:
  --
  --     T' p⃗ ι⃗ := ∀ r : Prop,
  --                 (∀ h⃗[d⃗ := ι⃗_piv],
  --                    Eq Pk (pack ι⃗_ctor|np) (pack ι⃗|np) → r) → r
  --
  -- If a pivot's declared type moves with an earlier index, direct
  -- substitution is ill-typed.  The zipper variant instead packs each full
  -- prefix before a moving pivot, binds an equality from the constructor
  -- prefix to the caller prefix, transports the pivot back, and continues.
  -- Proof fields are bound at that recovered telescope; one last equation
  -- packs the complete index vector.  The recursor transports a function
  -- over all these premises and applies the extracted premises at the caller
  -- endpoint.  Hence every equation is `refl` at a constructor and the iota
  -- theorem remains definitionally `refl`, including with multiple pivots,
  -- a later proof field, or a later endpoint depending on a pivot.
  --
  -- At **no** pivots this is exactly what the arm was before — the
  -- subsequence is the whole telescope and `h⃗` is every field — which is
  -- what makes the generalisation additive rather than a rewrite. At **no
  -- non-pivots** (`Fall` in `test/fixtures/inductive-models/prim_idx.lean`) there is
  -- nothing left to
  -- equate: the carrier is a bare Church conjunction, the recursor is the
  -- minor applied to the recovered fields, and no `Eq.rec` is built.
  --
  -- Recursor: read the data fields off the recursor's own index arguments,
  -- extract the proof fields by small elimination (their target is a `Prop`,
  -- so no large eliminator for ∃/∧ is consumed), extract the equation the
  -- same way, and discharge the non-pivot indices with a single `Eq.rec`
  -- whose motive rebuilds a carrier proof at each packed point. Every
  -- mismatch between the rebuilt proof and the caller's is closed by proof
  -- irrelevance — and so is every mismatch between a proof field as the
  -- carrier binds it and as the extraction recovers it, which is what lets
  -- the equation mention proof fields (`Inf.below`'s `Inf.mk a`). `pack
  -- (unpack y) ≡ y` by structure eta is what makes the motive typecheck at
  -- all. ι is `Eq.refl`: at the constructor the stored equation *is*
  -- `Eq.refl`, the pivots are the constructor's own fields, and `Eq.rec`'s
  -- own ι rule fires.
  let lift? : Option Level := if route matches PrimRoute.bare then some w else none
  if lift?.isSome then
    for d in ← ensureExactSortLift do out := out.push d; spliced := spliced ++ d.getNames
  for d in ← ensurePSigmaPrime do out := out.push d; spliced := spliced ++ d.getNames
  let (cn0, cty0) := exportCtors[0]!
  let nonPiv := gNonPiv
  let zipRoute := !gPivotTransports.isEmpty
  let packSel := if zipRoute then Array.range ni else nonPiv
  let npack := packSel.size

  -- The index vector a walked result type ends at, at either head: the
  -- export's `T p⃗ ι⃗` or the model's own `T._model.self p⃗ ι⃗`.
  let idxOfRes := fun (hd : Name) (res : Expr) => do
    let some args ← ownerAppArgs? hd np ni res
      | badShape s!"{cn0} does not end in {hd} at {np} parameters and {ni} indices"
    pure (args.extract np args.size)

  -- The constructor's field telescope with the **data fields substituted**
  -- from an index vector — [`InductiveModels.ctorFieldsAux`], the same walk the graph arm's
  -- `GraphInv` is stated by. `fs` is every field (substituted or bound),
  -- `bnd` only the bound ones, and `res` the conclusion at them.
  let fieldsAt := fun (ps is : Array Expr)
      (k : Array Expr → Array Expr → Expr → GenM Expr) => do
    let tele ← instForall cty0 ps
    ctorFieldsAux true gIsData gIdxPos is (numForalls tele) 0 tele #[] #[] k

  -- **`Pk`, the packed non-pivot type, at a given index vector.** Its
  -- component types may mention the *pivots*, which [`InductiveModels.packTyAt`]
  -- deliberately leaves free, so it is built once at an opened telescope and
  -- then instantiated. `none` when every index is a pivot.
  let pkAt := fun (ps : Array Expr) (vs : Array Expr) => do
    if npack == 0 then return (none : Option (Expr × Level))
    forallBoundedTelescope (← instForall memberTy ps) (some ni) fun is _ => do
      let (pkT, ℓ) ← packTyAt is packSel 0
      pure (some (pkT.replaceFVars is vs, ℓ))

  -- `∀ h⃗, Eq Pk (pack ι⃗_ctor|np) (pack ι⃗|np) → …`, the encoding's one
  -- minor, as a binder-introducing continuation so that the equation is
  -- built at the *bound* proof fields rather than at a stand-in.
  let underMinor := fun (ps is : Array Expr) (pk? : Option (Expr × Level))
      (mk : Array Expr → Expr → GenM Expr)
      (k : Array Expr → Option Expr → GenM Expr) =>
    if zipRoute then
      let (pk, ℓpk) := pk?.get!
      recoveryZipMinor eqi memberTy cty0 ni gIsData gIdxPos gPivotTransports
        ps is pk ℓpk (idxOfRes tname) mk fun fs h => k fs (some h)
    else
      fieldsAt ps is fun fs bnd res => do
        match pk? with
        | none => mk bnd (← k fs none)
        | some (pk, ℓpk) => do
          let idx ← idxOfRes tname res
          let lhs ← packChain npack pk (packSel.map (idx[·]!)) 0
          let rhs ← packChain npack pk (packSel.map (is[·]!)) 0
          withLocalDeclD `heq (eqi.mk' ℓpk pk lhs rhs) fun h => do
            mk (bnd.push h) (← k fs (some h))
  let allTy : Array Expr → Expr → GenM Expr := fun xs e => mkForallFVars xs e
  let lamF : Array Expr → Expr → GenM Expr := fun xs e => mkLambdaFVars xs e
  let minorTyAt := fun (ps is : Array Expr) (pk? : Option (Expr × Level)) (r : Expr) =>
    underMinor ps is pk? allTy (fun _ _ => pure r)
  let encodedAt := fun (ps is : Array Expr) => do
    let pk? ← pkAt ps is
    withLocalDeclD `r (.sort .zero) fun r => do
      mkForallFVars #[r] (.forallE `k (← minorTyAt ps is pk? r) r .default)

  -- ── the carrier ──
  let selfVal ← site.withParams fun ps => do
    forallBoundedTelescope (← instForall memberTy ps) (some ni) fun is _ => do
      let encoded ← encodedAt ps is
      mkLambdaFVars (ps ++ is)
        (match lift? with | none => encoded | some ℓ => puliftT ℓ encoded)
  let dSelf := Declaration.defnDecl
    { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfVal
      hints := ← hintsFor selfVal, safety := .safe }
  addChecked dSelf
  out := out.push dSelf

  -- ── the constructor ──
  -- Its own index vector is `ι⃗_ctor` at its own fields, so the pivots the
  -- carrier substitutes come back as exactly those fields and the stored
  -- equation is `Eq.refl`.
  let ty := publicSource sourceCtors[0]!.2
  let cval ← site.withParams fun ps => do
    let rtele ← instForall ty ps
    let nf := numForalls rtele
    forallBoundedTelescope rtele (some nf) fun fs res => do
      let idx ← idxOfRes selfN res
      let pk? ← pkAt ps idx
      let args ← match pk? with
        | none => pure (((Array.range nf).filter (!gIsData[·]!)).map (fs[·]!))
        | some (pk, ℓpk) =>
          if zipRoute then
            recoveryZipCtorArgs eqi memberTy ni gIsData gIdxPos gPivotTransports ps idx fs pk ℓpk
          else do
            let bnd := ((Array.range nf).filter (!gIsData[·]!)).map (fs[·]!)
            pure (bnd.push (eqi.refl' ℓpk pk
              (← packChain npack pk (packSel.map (idx[·]!)) 0)))
      let encoded ← encodedAt ps idx
      let proof ← withLocalDeclD `r (.sort .zero) fun r => do
        withLocalDeclD `k (← minorTyAt ps idx pk? r) fun kk =>
          mkLambdaFVars #[r, kk] (mkAppN kk args)
      mkLambdaFVars (ps ++ fs)
        (match lift? with | none => proof | some ℓ => puliftUp ℓ encoded proof)
  let dCtor := Declaration.defnDecl
    { name := ctorN 0, levelParams := lparams, type := ty, value := cval
      hints := ← hintsFor cval, safety := .safe }
  addChecked dCtor
  out := out.push dCtor

  -- ── the recursor ──
  let recVal ← forallBoundedTelescope installedRecTy
      (some (np + 1 + nc + ni + 1)) fun bs _ => do
    let ps := bs.extract 0 np
    let motive := bs[np]!
    let minor := bs[np + 1]!
    let idxs := bs.extract (np + 1 + nc) (np + 1 + nc + ni)
    let t := bs[bs.size - 1]!
    let pk? ← pkAt ps idxs
    let encoded ← encodedAt ps idxs
    let base := match lift? with | none => t | some ℓ => puliftDown ℓ encoded t
    let tele ← instForall cty0 ps
    let nf := numForalls tele
    if zipRoute then
      let (pk, ℓpk) := pk?.get!
      let body ← recoveryZipModelRec eqi lift? memberTy cty0 ni gIsData gIdxPos
        gPivotTransports ps idxs base pk motive minor ℓpk (idxOfRes tname)
        (fun full r => minorTyAt ps full (some (pk, ℓpk)) r)
        (fun full => encodedAt ps full)
      return ← mkLambdaFVars bs body
    -- **Recover the fields.** Ordinarily a data field is the recursor's own
    -- index argument at that field's pivot position.  When its declared type
    -- depends on a non-pivot, the packed equation canonically transports it
    -- below before it reaches the minor. A proof field is extracted sequentially: a
    -- later field's type is instantiated at the earlier recoveries, and the
    -- projector is written at the carrier's own minor telescope so that a
    -- field whose type mentions a *data* field is asked for at the index and
    -- not at a stand-in.
    let mut es : Array Expr := #[]
    let mut curT := tele
    for i in [0:nf] do
      let .forallE _ ft rest _ := curT | badShape "telescope shorter than its field count"
      let v ←
        if gIsData[i]! then pure idxs[gIdxPos[i]!]!
        else do
          let proj ← underMinor ps idxs pk? lamF fun fs _ => pure fs[i]!
          pure (mkAppN base #[ft, proj])
      es := es.push v
      curT := rest.instantiate1 v
    -- the proof fields alone, in telescope order: what the carrier's minor
    -- binds and what the rebuilt carrier proof below is applied to.
    let esBnd := ((Array.range nf).filter (!gIsData[·]!)).map (es[·]!)
    -- the constructor's index vector at the recovered fields
    let idxE ← idxOfRes tname (← instForall (← instForall cty0 ps) es)
    match pk? with
    | none =>
      -- Every index is a pivot: `ι⃗_ctor` at the recovered fields **is**
      -- `ι⃗`, and `T._model.ctor_0 es` is `t` by proof irrelevance.
      mkLambdaFVars bs (mkAppN minor es)
    | some (pk, ℓpk) => do
      let pkc ← packChain npack pk (packSel.map (idxE[·]!)) 0
      let pki ← packChain npack pk (packSel.map (idxs[·]!)) 0
      let eqTy := eqi.mk' ℓpk pk pkc pki
      let heq := mkAppN base #[eqTy, ← underMinor ps idxs pk? lamF
        fun _ h? => pure h?.get!]
      -- one `Eq.rec` at the packed point: the motive rebuilds a carrier
      -- proof at each `y`, and `pack (unpack y) ≡ y` makes it typecheck.
      -- Only the **non-pivot** slots move with `y`; the pivots are the
      -- recursor's own index arguments throughout, which is why no transport
      -- is needed on the fields.
      let fam := fun (y : Expr) (h : Expr) => do
        let ys ← unpackChain npack pk y
        let mut full := idxs
        for k in [0:npack] do full := full.set! packSel[k]! ys[k]!
        let rebuilt ← withLocalDeclD `r (.sort .zero) fun r => do
          withLocalDeclD `k (← minorTyAt ps full pk? r) fun kk =>
            mkLambdaFVars #[r, kk] (mkAppN kk (esBnd.push h))
        let lifted ← match lift? with
          | none => pure rebuilt
          | some ℓ => pure (puliftUp ℓ (← encodedAt ps full) rebuilt)
        pure (mkAppN motive (full.push lifted))
      let motiveE ← withLocalDeclD `y pk fun y => do
        withLocalDeclD `hy (eqi.mk' ℓpk pk pkc y) fun hy => do
          mkLambdaFVars #[y, hy] (← fam y hy)
      mkLambdaFVars bs (eqi.recAt v ℓpk pk pkc motiveE (mkAppN minor es) pki heq)
  let dRec := Declaration.defnDecl
    { name := recN, levelParams := rv.levelParams, type := publicRecTy, value := recVal
      hints := ← hintsFor recVal, safety := .safe }
  addChecked dRec
  out := out.push dRec
  return { st with out, spliced }

end InductiveModels
