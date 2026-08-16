import InductiveModels.Simple.Site
import InductiveModels.Simple.Tight

/-!
# Arm S: the indexed singleton whose data the index vector does not carry

    T p⃗ ι⃗ := Σ'(t : Store p⃗), pack ι⃗_ctor(proj⃗ t) = pack ι⃗

`Store` is [`InductiveModels.tightTowerTy`] over the constructor's fields — the
same exact-sort storage the unindexed direct routes use, and a *definition*
rather than a spliced inductive — and the equation is arm F's Henry-Ford
equation, stated once at the whole index telescope packed into a `PSigma'`
because a later index's type may mention an earlier one.

**Why the pair is at exactly the carrier's sort.** The tower lands at
`max ℓ⃗`, which the route guard has already equated with `w`
([`InductiveModels.planIndexedStoreRoute`]), and the equation is a `Prop`, so
the pair is at `max w 0` — literally `w` after normalization, with no lift and
no pad.

**Why every rule reduces.** `proj⃗` and the tower are `PSigma'` projections and
a `PSigma'.mk`, so `proj⃗ (mk f⃗) ≡ f⃗` by ι and `mk (proj⃗ t) ≡ t` by structure
eta; the stored equation at the constructor is `Eq.refl`, so the recursor's one
`Eq.rec` fires by its own ι rule and the recursor ι theorem is `Eq.refl`; and
the second component is a proof, so the rebuilt pair and the caller's are one
term by proof irrelevance. `pack (unpack y) ≡ y` is what lets the transport's
motive be stated about a packed variable and still apply to the declaration's
own index telescope.

**Why the intrinsic projections are overridden.** The model recursor here has
the recursor the kernel minted, which for this shape is `Prop`-valued: the
constructor has a data field that is not a conclusion index, so the kernel's
subsingleton rule grants no large eliminator. A projection built through that
recursor cannot be stated. The selector is the storage's own projection
instead, which selects definitionally, and each rule is `Eq.refl` at the
constructor's own field binder.
-/

open Lean Meta

namespace InductiveModels

def primArmS (site : PrimSite) (st : PrimOut) : GenM PrimOut := do
  -- The site, under the names this arm has always read it by.
  let tname := site.tname
  let lparams := site.lparams
  let np := site.np
  let memberTy := site.memberTy
  let exportCtors := site.exportCtors
  let us := site.us
  let selfN := site.selfN
  let recN := site.recN
  let ctorN := site.ctorN
  let nc := site.nc
  let declaredMemberTy := site.declaredMemberTy
  let ni := site.ni
  let w := site.w
  let rv := site.rv
  let v := site.v
  let eqi := site.eqi
  let installedRecTy := site.installedRecTy
  let publicSource := site.publicSource
  let publicRecTy := site.publicRecTy
  let mut out := st.out
  let mut spliced := st.spliced
  let mut projectionOverrides := st.projectionOverrides
  for d in ← ensurePSigmaPrime do out := out.push d; spliced := spliced ++ d.getNames

  let (cn0, cty0) := exportCtors[0]!
  let nf := numForalls cty0 - np
  let modelCtorTy := publicSource cty0

  -- **The storage, its projections and its introduction**, at a parameter
  -- scope. One tower serves every field count: at one field it *is* that
  -- field's type and its sole projection is the value itself, which is the
  -- unindexed `.identity` route's carrier written by the same function.
  let storeAt : Array Expr → GenM Expr := fun ps => do
    let tele ← instForall cty0 ps
    forallBoundedTelescope tele (some nf) fun fields _ => tightTowerTy fields 0
  let projsAt : Array Expr → Expr → GenM (Array Expr) := fun ps value => do
    let tele ← instForall cty0 ps
    forallBoundedTelescope tele (some nf) fun fields _ => tightTowerProjs fields 0 value
  let towerOf : Array Expr → Array Expr → GenM Expr := fun _ fs =>
    tightTowerMk fs 0

  -- **`Pk`, the whole index telescope packed.** Closed over the parameters
  -- alone: [`InductiveModels.packTyOf`] abstracts every selected index, and
  -- here the selection is all of them, so the packed *type* is the same type at
  -- every index vector and only the packed *values* move.
  let pkAt : Array Expr → GenM (Expr × Level) := fun ps => do
    forallBoundedTelescope (← instForall memberTy ps) (some ni) fun is _ =>
      packTyOf is 0

  -- The constructor's own index vector at a given field vector, read off its
  -- result type rather than reconstructed.
  let idxOfVals : Array Expr → Array Expr → GenM (Array Expr) := fun ps vs => do
    let res ← instForall (← instForall cty0 ps) vs
    let some args ← ownerAppArgs? tname np ni res
      | badShape s!"{cn0} does not end in {tname} at {np} parameters and {ni} indices"
    pure (args.extract np args.size)

  -- **The carrier's fibre**, as a function of the packed caller index. Every
  -- one of the four declarations below needs it, and at a different packed
  -- point, which is why it is a builder and not a term.
  let fibreAt : Array Expr → Expr → Expr → Level → Expr → GenM Expr :=
    fun ps store pk ℓpk packedIs =>
      withLocalDeclD `t store fun t => do
        let vs ← projsAt ps t
        let packedC ← packChain ni pk (← idxOfVals ps vs) 0
        mkLambdaFVars #[t] (eqi.mk' ℓpk pk packedC packedIs)

  -- ── the carrier ──
  let selfVal ← site.withParams fun ps => do
    let store ← storeAt ps
    let (pk, ℓpk) ← pkAt ps
    forallBoundedTelescope (← instForall memberTy ps) (some ni) fun is _ => do
      let packedIs ← packChain ni pk is 0
      let fibre ← fibreAt ps store pk ℓpk packedIs
      mkLambdaFVars (ps ++ is) (psigmaT w .zero store fibre)
  let dSelf := Declaration.defnDecl
    { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfVal
      hints := ← hintsFor selfVal, safety := .safe }
  addChecked dSelf
  out := out.push dSelf

  -- ── the constructor ──
  -- Its own index vector is `ι⃗_ctor` at its own fields, and the storage's
  -- projections reduce to those fields, so the stored equation is `Eq.refl`.
  let cval ← site.withParams fun ps => do
    let store ← storeAt ps
    let (pk, ℓpk) ← pkAt ps
    let rtele ← instForall modelCtorTy ps
    forallBoundedTelescope rtele (some nf) fun fs _ => do
      let packedC ← packChain ni pk (← idxOfVals ps fs) 0
      let fibre ← fibreAt ps store pk ℓpk packedC
      mkLambdaFVars (ps ++ fs)
        (psigmaMk w .zero store fibre (← towerOf ps fs) (eqi.refl' ℓpk pk packedC))
  let dCtor := Declaration.defnDecl
    { name := ctorN 0, levelParams := lparams, type := modelCtorTy, value := cval
      hints := ← hintsFor cval, safety := .safe }
  addChecked dCtor
  out := out.push dCtor

  -- ── the recursor ──
  -- Take the pair apart, recover the fields from the storage, apply the minor
  -- at them, and move the result from the constructor's index vector to the
  -- caller's along the stored equation. The motive rebuilds a carrier element
  -- at each packed point; at the equation's own endpoint that element and the
  -- caller's major are one term by structure eta and proof irrelevance.
  let recVal ← forallBoundedTelescope installedRecTy
      (some (np + 1 + nc + ni + 1)) fun bs _ => do
    let ps := bs.extract 0 np
    let motive := bs[np]!
    let minor := bs[np + 1]!
    let idxs := bs.extract (np + 1 + nc) (np + 1 + nc + ni)
    let major := bs[bs.size - 1]!
    let store ← storeAt ps
    let (pk, ℓpk) ← pkAt ps
    let packedIs ← packChain ni pk idxs 0
    let fibre ← fibreAt ps store pk ℓpk packedIs
    let stored := psigmaFst w .zero store fibre major
    let heq := psigmaSnd w .zero store fibre major
    let fs ← projsAt ps stored
    let packedC ← packChain ni pk (← idxOfVals ps fs) 0
    let motiveE ← withLocalDeclD `y pk fun y => do
      withLocalDeclD `hy (eqi.mk' ℓpk pk packedC y) fun hy => do
        let ys ← unpackChain ni pk y
        let fibreY ← fibreAt ps store pk ℓpk y
        mkLambdaFVars #[y, hy]
          (mkAppN motive (ys.push (psigmaMk w .zero store fibreY stored hy)))
    mkLambdaFVars bs
      (eqi.recAt v ℓpk pk packedC motiveE (mkAppN minor fs) packedIs heq)
  let dRec := Declaration.defnDecl
    { name := recN, levelParams := rv.levelParams, type := publicRecTy, value := recVal
      hints := ← hintsFor recVal, safety := .safe }
  addChecked dRec
  out := out.push dRec

  -- ── the intrinsic projections ──
  let overrides ← site.withParams fun ps => do
    let store ← storeAt ps
    let (pk, ℓpk) ← pkAt ps
    forallBoundedTelescope (← instForall memberTy ps) (some ni) fun is _ => do
      let packedIs ← packChain ni pk is 0
      let fibre ← fibreAt ps store pk ℓpk packedIs
      withLocalDeclD `self (mkAppN (.const selfN us) (ps ++ is)) fun self => do
        let projections ← projsAt ps (psigmaFst w .zero store fibre self)
        (Array.range nf).mapM fun fieldIndex => do
          let selector ← mkLambdaFVars (ps ++ is ++ #[self]) projections[fieldIndex]!
          let proof ← do
            let tele ← instForall cty0 ps
            forallBoundedTelescope tele (some nf) fun constructorFields _ => do
              let selected := constructorFields[fieldIndex]!
              let fieldType ← inferType selected
              let fieldLevel ← ilevel fieldType
              mkLambdaFVars (ps ++ constructorFields)
                (eqi.refl' fieldLevel fieldType selected)
          return (tname, fieldIndex, selector, proof)
  projectionOverrides := projectionOverrides ++ overrides
  return { st with out, spliced, projectionOverrides }

end InductiveModels
