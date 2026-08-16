import InductiveModels.Simple.Site
import InductiveModels.Simple.Graph

/-!
# The Church routes, and arm G's graph recursion beside them
-/

open Lean Meta

namespace InductiveModels

def primArmChurch (site : PrimSite) (st : PrimOut) : GenM PrimOut := do
  -- The site, under the names this arm has always read it by.
  let tname := site.tname
  let lparams := site.lparams
  let np := site.np
  let memberTy := site.memberTy
  let exportCtors := site.exportCtors
  let sourceCtors := site.sourceCtors
  let reserved := site.reserved
  let us := site.us
  let impl := site.impl
  let selfN := site.selfN
  let ern := site.ern
  let recN := site.recN
  let ctorN := site.ctorN
  let indN := site.indN
  let nc := site.nc
  let declaredMemberTy := site.declaredMemberTy
  let ni := site.ni
  let w := site.w
  let isRec := site.isRec
  let rv := site.rv
  let large := site.large
  let v := site.v
  let recLs := site.recLs
  let route := site.route
  let gIsData := site.gIsData
  let gIdxPos := site.gIdxPos
  let gRecNb := site.gRecNb
  let gNf := site.gNf
  let gNonPiv := site.gNonPiv
  let armG := site.armG
  let eqi := site.eqi
  let installedRecTy := site.installedRecTy
  let publicSource := site.publicSource
  let publicRecTy := site.publicRecTy
  let mut out := st.out
  let mut spliced := st.spliced
  -- ════ the Church routes: `Prop`, and the maybe-zero sort under a lift ════
  --
  -- One construction serves both. At `Sort 0` the carrier is the
  -- impredicative Church encoding itself; at a **maybe-zero** sort it is
  -- that same encoding under the derived lift, which puts it at exactly `Sort w`
  -- for any `w`. The constructors are the folds, `up` of the folds under a
  -- lift. The recursor is the fold at the right `C`, plus — under a lift —
  -- one transport along [`InductiveModels.puliftEta`], because the lifted `p` is not
  -- itself a proposition and proof irrelevance no longer closes the
  -- "which element" question by itself.
  --
  -- Why this is a model and not a collapse: at a maybe-zero sort the
  -- contract never forces two provably distinct elements. Zero constructors
  -- and the subsingleton shape large-eliminate and are subsingletons
  -- anyway; everything else there small-eliminates, so the motive lands in
  -- `Prop` and cannot discriminate. The lift of a proposition is exactly
  -- the right size.
  let lift? : Option Level := if route matches PrimRoute.bare then some w else none

  -- The index telescope at a parameter scope, and the Church motive's type
  -- `C : ∀ ι⃗, Prop` over it. At `ni = 0` this is just `Prop` and everything
  -- below degenerates to the original non-indexed construction.
  let idxTeleAt := fun (ps : Array Expr) => instForall memberTy ps
  let motiveTyAt := fun (ps : Array Expr) => do
    forallBoundedTelescope (← idxTeleAt ps) (some ni) fun is _ =>
      mkForallFVars is (.sort .zero)

  let churchAt := fun (ps : Array Expr)
      (k : Expr → Array Expr → Array Expr → GenM Expr) => do
    -- `C`, the `k_j` binders, and their types, in one scope. Each `k_j` is
    -- constructor `j`'s telescope with `T p⃗` replaced by `C` — at its
    -- recursive fields as well as at its result.
    withLocalDeclD `C (← motiveTyAt ps) fun C => do
      let kTys ← exportCtors.mapM fun (_, cty) => do
        let tele ← instForall cty ps
        return (← churchSwapAt tname np ni C (numForalls tele) tele).1
      churchBinders kTys 0 #[] (fun ks => k C ks kTys)

  if lift?.isSome then
    for d in ← ensureExactSortLift do out := out.push d; spliced := spliced ++ d.getNames

  -- **Arm G's prelude, asked for before anything is emitted.** The graph
  -- route pairs a value with its graph proof (`PSigma'`) and extracts it with
  -- `Classical.choice`, whose own domain is `Nonempty`; and `Graph.unique`
  -- transports along a `funext` — but only when a recursive field has a
  -- binder, because [`InductiveModels.funextUp`] is the only caller and it is the
  -- identity at none. That is the whole of why the axiom cost is per shape.
  let mut gFx? : Option Name := none
  if armG then
    for d in ← ensurePSigmaPrime do out := out.push d; spliced := spliced ++ d.getNames
    for d in ← ensureNonempty do out := out.push d; spliced := spliced ++ d.getNames
    for d in ← ensureChoice do out := out.push d; spliced := spliced ++ d.getNames
    if (Array.range gNf).any (fun i => (gRecNb[i]!.getD 0) > 0) then
      let (fxN, fxDecls) ← ensureFunext impl eqi reserved
      for d in fxDecls do out := out.push d; spliced := spliced ++ d.getNames
      gFx? := some fxN

  -- The bare Church proposition at a parameter *and index* scope — what
  -- sits under the lift, and the carrier itself when there is none.
  let churchPropAt := fun (ps : Array Expr) (is : Array Expr) =>
    churchAt ps fun C ks _ => mkForallFVars (#[C] ++ ks) (mkAppN C is)

  -- ── the carrier ──
  let selfVal ← site.withParams fun ps => do
    forallBoundedTelescope (← idxTeleAt ps) (some ni) fun is _ => do
      let pr ← churchPropAt ps is
      mkLambdaFVars (ps ++ is)
        (match lift? with | none => pr | some ℓ => puliftT ℓ pr)
  let dSelf := Declaration.defnDecl
    { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfVal
      hints := ← hintsFor selfVal, safety := .safe }
  addChecked dSelf
  out := out.push dSelf

  -- ── the constructors ──
  -- The binders come from the **restored** telescope. At `Prop`, a recursive
  -- field's `T._model.self p⃗ e⃗` δ-unfolds to the encoding; under a lift it
  -- is first mapped through `down`. In either case the fold
  -- `fun z⃗ => f z⃗ C k⃗` then typechecks. Classification is positional and
  -- read off the export's telescope.
  for j in [0:nc] do
    let (_, cty) := exportCtors[j]!
    let ty := publicSource sourceCtors[j]!.2
    let nfj ← site.withParams fun ps => do pure (numForalls (← instForall cty ps))
    let flds ← site.withParams fun ps => do classifyCtor tname nfj (← instForall cty ps)
    let val ← site.withParams fun ps => do
      let rtele ← instForall ty ps
      forallBoundedTelescope rtele (some nfj) fun fs res => do
        let fold ← churchAt ps fun C ks _ => do
          let args ← (Array.range nfj).mapM fun i => do
            match flds[i]!.rec? with
            | none => pure fs[i]!
            | some nb =>
              -- exactly the field's OWN binders: `forallTelescope` would
              -- whnf through `T._model.self` and open the encoding's Π too.
              forallBoundedTelescope (← ityp fs[i]!) (some nb) fun zs res => do
                let child := mkAppN fs[i]! zs
                let base ← match lift? with
                  | none => pure child
                  | some ℓ => do
                    let some args ← ownerAppArgs? selfN np ni res
                      | badShape s!"a recursive field of {ctorN j} does not end in {selfN} \
                          at {np} parameters and {ni} indices"
                    let is := args.extract np args.size
                    pure (puliftDown ℓ (← churchPropAt ps is) child)
                mkLambdaFVars zs (mkAppN base (#[C] ++ ks))
          mkLambdaFVars (#[C] ++ ks) (mkAppN ks[j]! args)
        match lift? with
        | none => mkLambdaFVars (ps ++ fs) fold
        | some ℓ =>
          let some args ← ownerAppArgs? selfN np ni res
            | badShape s!"{ctorN j}'s result is not {selfN} at {np} parameters and {ni} indices"
          let is := args.extract np args.size
          mkLambdaFVars (ps ++ fs) (puliftUp ℓ (← churchPropAt ps is) fold)
    let d := Declaration.defnDecl
      { name := ctorN j, levelParams := lparams, type := ty, value := val
        hints := ← hintsFor val, safety := .safe }
    addChecked d
    out := out.push d

  -- ── the recursor ──
  if large && nc == 0 then
    for d in ← ensureNat do out := out.push d; spliced := spliced ++ d.getNames
    for d in ← ensureExactSortLift do out := out.push d; spliced := spliced ++ d.getNames
  -- **One fold, two consumers.** Arm G's `ind` — the free `Prop`-motive
  -- recursor the graph route folds at — *is* the strong-induction fold
  -- below at `v := 0`, so the arm forces the small-elimination branches and
  -- takes the result as `ind` instead of as `rec_0`. Building it a second
  -- time by hand would be a second thing to keep in step.
  let installedIndTy :=
    if armG then installedRecTy.instantiateLevelParams [rv.levelParams[0]!] [.zero]
    else installedRecTy
  let publicIndTy :=
    if armG then publicRecTy.instantiateLevelParams [rv.levelParams[0]!] [.zero]
    else publicRecTy
  let large := large && !armG
  let recVal ← forallBoundedTelescope installedIndTy
      (some (np + 1 + nc + ni + 1)) fun bs _ => do
    let ps := bs.extract 0 np
    let motive := bs[np]!
    let minors := bs.extract (np + 1) (np + 1 + nc)
    let idxs := bs.extract (np + 1 + nc) (np + 1 + nc + ni)
    let t := bs[bs.size - 1]!
    -- Under a lift the fold runs on `down t`. Its result lands at
    -- `motive ι⃗ (up (down t))`, which *is* `motive ι⃗ t`: structure eta on
    -- tight-pair/unit eta gives `t ≡ up (down t)`. So there is no transport, and the
    -- two routes differ in exactly the `down` here and the `up` in the
    -- constructors above.
    let body : Expr ←
      match lift? with
      | none => pure t
      | some ℓ => do pure (puliftDown ℓ (← churchPropAt ps idxs) t)
    let goalAt := mkAppN motive (idxs.push t)
    -- `Self ι⃗`, the carrier at an index vector.
    let selfAt := fun (is : Array Expr) => mkAppN (.const selfN us) (ps ++ is)
    if !large && ni == 0 && !isRec then
      -- The plain fold, at `C := goalAt`: every minor's motive is closed by
      -- definitional proof irrelevance — under a lift too, because the two
      -- `up`s differ only in a proof of the encoding's own proposition.
      mkLambdaFVars bs (mkAppN body (#[goalAt] ++ minors))
    else if !large then
      -- ── strong induction ──
      -- The plain fold cannot serve an indexed or recursive declaration: a
      -- minor premise wants `motive ι⃗_j (c_j f⃗)` and the fold only offers
      -- `C ι⃗_j`, which proof irrelevance no longer identifies with it once
      -- the index moves. So fold at the Church **pair**
      --
      --     Pair ι⃗ := ∀ D : Prop, (Self ι⃗ → (∀ h : Self ι⃗, motive ι⃗ h) → D) → D
      --
      -- of a rebuilt carrier element and a proof about *every* element at
      -- that index — the `∀ h` is what proof irrelevance collapses, and the
      -- element component is what a recursive minor premise needs an
      -- argument for. Every ι rule is still `Eq.refl`, and for a reason
      -- that has nothing to do with whether the fold reduces: the motive is
      -- `Prop`-valued, so both sides of every ι equation are proofs of one
      -- proposition.
      let pairTy ← forallBoundedTelescope (← idxTeleAt ps) (some ni) fun is _ => do
        let sf := selfAt is
        let inner ← withLocalDeclD `D (.sort .zero) fun D => do
          let armTy ← withLocalDeclD `e sf fun e => do
            let qTy ← withLocalDeclD `h sf fun h =>
              mkForallFVars #[h] (mkAppN motive (is.push h))
            withLocalDeclD `q qTy fun q => mkForallFVars #[e, q] D
          mkForallFVars #[D] (.forallE `k armTy D .default)
        mkLambdaFVars is inner
      -- one `Pair`-valued premise per constructor
      let pairAt := fun (is : Array Expr) => do
        let sf := selfAt is
        withLocalDeclD `D (.sort .zero) fun D => do
          let armTy ← withLocalDeclD `e sf fun e => do
            let qTy ← withLocalDeclD `h sf fun h =>
              mkForallFVars #[h] (mkAppN motive (is.push h))
            withLocalDeclD `q qTy fun q => mkForallFVars #[e, q] D
          mkForallFVars #[D] (.forallE `k armTy D .default)
      let pairBaseAt := fun (is : Array Expr) => match lift? with
        | none => pure (selfAt is)
        | some _ => churchPropAt ps is
      let cs ← (Array.range nc).mapM fun j => do
        let (_, cty) := exportCtors[j]!
        let tele ← instForall cty ps
        pairArm tname np ni us selfAt pairAt pairBaseAt lift?
          motive (ctorN j) minors[j]! ps
          (numForalls tele) tele #[] #[]
      let cont ← withLocalDeclD `e (selfAt idxs) fun e => do
        let qTy ← withLocalDeclD `h (selfAt idxs) fun h =>
          mkForallFVars #[h] (mkAppN motive (idxs.push h))
        withLocalDeclD `q qTy fun q => mkLambdaFVars #[e, q] (mkApp q t)
      mkLambdaFVars bs (mkAppN (mkAppN body (#[pairTy] ++ cs)) #[goalAt, cont])
    else if nc == 0 then
      -- Church `⊥` at every index: instantiate the encoding at the constant
      -- family. At `ni = 0` this is the encoding itself.
      let cf ← withLocalDeclD `p (.sort .zero) fun pv => do
        let fam ← forallBoundedTelescope (← idxTeleAt ps) (some ni) fun is _ =>
          mkLambdaFVars is pv
        mkLambdaFVars #[pv] (mkApp body fam)
      mkLambdaFVars bs (← cfalseElim eqi v goalAt cf)
    else do
      -- Large elimination: one constructor, every field a proposition
      -- (the subsingleton rule, which minted this recursor, says so) —
      -- extract each by instantiating the encoding at the field's type.
      unless nc == 1 do
        badShape s!"{ern} is large-eliminating with {nc} constructors"
      let (_, cty) := exportCtors[0]!
      let tele ← instForall cty ps
      let nf := numForalls tele
      let mut es : Array Expr := #[]
      let mut curT := tele
      for _ in [0:nf] do
        let .forallE _ ft rest _ := curT | badShape "telescope shorter than its field count"
        unless (← ilevel ft).normalize.isZero do
          badShape s!"{ern} is large-eliminating and a field is not a proposition"
        let i := es.size
        let proj ← forallBoundedTelescope tele (some nf) fun fs _ =>
          mkLambdaFVars fs fs[i]!
        es := es.push (mkAppN body #[ft, proj])
        curT := rest.instantiate1 es[i]!
      mkLambdaFVars bs (mkAppN minors[0]! es)
  if armG then
    -- ════ arm G: the recursive subsingleton, by the graph ════
    -- The carrier and the constructor above are already the graph route's
    -- own — `CAcc` and `CAcc.intro` cost no primitive whatsoever — and so is
    -- the `Prop`-motive recursor just built. What is emitted here is the
    -- large eliminator the kernel granted the *declaration* and an emitted
    -- `def` does not inherit.
    let dInd := Declaration.thmDecl
      { name := indN, levelParams := lparams, type := publicIndTy, value := recVal }
    addChecked dInd
    out := out.push dInd
    let ctx : GraphCtx :=
      { tname, np, ni, nf := gNf, us, recLs, lparams, recLevels := rv.levelParams, v
        selfN, ctorN0 := ctorN 0, recN, indN
        grN := Name.str impl "graph", grMkN := Name.str impl "graph_mk"
        grInvTN := Name.str impl "graph_inv_ty", grInvN := Name.str impl "graph_inv"
        grUniqN := Name.str impl "graph_unique", grExN := Name.str impl "graph_exists"
        recGrN := Name.str impl "rec_graph"
        memberTy, ctorTy := publicSource sourceCtors[0]!.2
        isData := gIsData, idxPos := gIdxPos, nonPiv := gNonPiv
        recNb := gRecNb, eqi, fx? := gFx? }
    for d in ← graphArm ctx publicRecTy do out := out.push d
  else
    let dRec := Declaration.defnDecl
      { name := recN, levelParams := rv.levelParams, type := publicRecTy, value := recVal
        hints := ← hintsFor recVal, safety := .safe }
    addChecked dRec
    out := out.push dRec
  return { st with out, spliced }

end InductiveModels
