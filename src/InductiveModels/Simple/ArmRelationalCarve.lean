import InductiveModels.Simple.Site
import InductiveModels.Simple.Erasure

/-!
# Relational Carve for indexed sometimes-`Prop` families

The erased skeleton has only small elimination when its sort may instantiate to
`Prop`.  Instead of computing a predicate-valued `good` with that recursor,
splice goodness as an inductive relation and recurse on its proof.
-/

open Lean Meta

namespace InductiveModels

private partial def withRelLocalsD (tys : Array (Name × Expr)) (i : Nat)
    (acc : Array Expr) (k : Array Expr → GenM Expr) : GenM Expr := do
  if i == tys.size then k acc
  else
    withLocalDeclD tys[i]!.1 tys[i]!.2 fun x =>
      withRelLocalsD tys (i + 1) (acc.push x) k

def primArmRelationalCarve (site : PrimSite) (st : PrimOut) : GenM PrimOut := do
  let tname := site.tname
  let lparams := site.lparams
  let np := site.np
  let memberTy := site.memberTy
  let exportCtors := site.exportCtors
  let sourceCtors := site.sourceCtors
  let us := site.us
  let selfN := site.selfN
  let recN := site.recN
  let ctorN := site.ctorN
  let skelN := site.skelN
  let goodN := site.goodN
  let skelCtorN := site.skelCtorN
  let goodCtorN := fun (j : Nat) => Name.str goodN s!"c_{j}"
  let nc := site.nc
  let taken := site.taken
  let declaredMemberTy := site.declaredMemberTy
  let ni := site.ni
  let w := site.w
  let rv := site.rv
  let publicSource := site.publicSource
  let publicRecTy := site.publicRecTy
  let installedRecTy := site.installedRecTy
  let eqi := site.eqi
  let mut out := st.out
  let mut spliced := st.spliced
  let mut requires := st.requires
  let mut projectionOverrides := st.projectionOverrides

  if site.large then
    badShape s!"internal: relational Carve received the large-elimination family {tname}"
  for n in [skelN, goodN] do taken n
  for j in [0:nc] do
    taken (skelCtorN j)
    taken (goodCtorN j)
  for d in ← ensurePSigmaPrime do out := out.push d; spliced := spliced ++ d.getNames

  let skelSelf := fun (ps : Array Expr) => mkAppN (.const skelN us) ps
  let goodAt := fun (ps : Array Expr) (s : Expr) (is : Array Expr) =>
    mkAppN (.const goodN us) (ps ++ #[s] ++ is)
  let βOf := fun (ps is : Array Expr) =>
    withLocalDeclD `s (skelSelf ps) fun s =>
      mkLambdaFVars #[s] (goodAt ps s is)

  -- Constructor indices and recursive slots, re-expressed at `fields`.
  let shapeAt := fun (ps fields : Array Expr) (j : Nat) => do
    let (cn, cty) := exportCtors[j]!
    let tele ← instForall cty ps
    let nf := numForalls tele
    forallBoundedTelescope tele (some nf) fun fs res => do
      let some args ← ownerAppArgs? tname np ni res
        | badShape s!"{cn} does not end in {tname} at {np} parameters and {ni} indices"
      let idx := (args.extract np args.size).map fun e => e.replaceFVars fs fields
      let mut slots : Array (Nat × Expr) := #[]
      for i in [0:nf] do
        let ft ← ityp fs[i]!
        if erasureRecursive tname ft then
          slots := slots.push (i, ft.replaceFVars fs fields)
      pure (idx, slots)

  let proofTypesAt := fun (ps gs : Array Expr) (slots : Array (Nat × Expr)) =>
    slots.mapM fun (k, dom) =>
      withRecSlot tname np ni dom fun zs chi =>
        mkForallFVars zs (goodAt ps (mkAppN gs[k]! zs) chi)

  -- The index-erased carrier.  Unlike functional Carve, this skeleton needs
  -- only the small recursor the kernel naturally gives a maybe-zero sort.
  let skelDecl : Declaration :=
    .inductDecl lparams np
      [{ name := skelN, type := eraseSelfTy np w memberTy,
         ctors := (List.range nc).map fun j =>
           { name := skelCtorN j,
             type := eraseCtorTy tname skelN us np exportCtors[j]!.2 } }] false
  addChecked skelDecl
  out := out.push skelDecl
  spliced := spliced.push skelN
  requires := requires.push skelN

  -- `Good s i⃗` mirrors the original constructors.  Original recursive fields
  -- become skeleton fields plus recursive `Good` proofs; all proof fields are
  -- appended after the erased constructor telescope so the generated recursor
  -- presents the erased fields, the proofs, and then their induction hypotheses.
  let goodTy ← site.withParams fun ps => do
    withLocalDeclD `s (skelSelf ps) fun s => do
      let tele ← instForall memberTy ps
      forallBoundedTelescope tele (some ni) fun is _ =>
        mkForallFVars (ps ++ #[s] ++ is) (.sort .zero)
  let goodCtors ← site.withParams fun ps =>
    (Array.range nc).mapM fun j => do
      let tele ← instForall exportCtors[j]!.2 ps
      let nf := numForalls tele
      let swapped ← spineSwap tname (skelSelf ps) nf tele
      forallBoundedTelescope swapped (some nf) fun gs _ => do
        let (idx, slots) ← shapeAt ps gs j
        let proofTypes ← proofTypesAt ps gs slots
        withRelLocalsD (proofTypes.mapIdx fun i ty => (Name.mkSimple s!"good_{i}", ty)) 0 #[]
          fun proofs => do
            let s := mkAppN (.const (skelCtorN j) us) (ps ++ gs)
            mkForallFVars (ps ++ gs ++ proofs) (goodAt ps s idx)
  let goodDecl : Declaration :=
    .inductDecl lparams np
      [{ name := goodN, type := goodTy,
         ctors := (List.range nc).map fun j =>
           { name := goodCtorN j, type := goodCtors[j]! } }] false
  addChecked goodDecl
  out := out.push goodDecl
  spliced := spliced.push goodN
  requires := requires.push goodN

  let goodRecN := Name.str goodN "rec"
  let some (.recInfo goodRV) := (← getEnv).find? goodRecN
    | badShape s!"the kernel minted no recursor for the spliced {goodN}"
  unless goodRV.numParams == np && goodRV.numIndices == ni + 1 &&
      goodRV.numMotives == 1 && goodRV.numMinors == nc do
    badShape s!"{goodRecN} has an unexpected recursor shape"
  let goodRecLevels :=
    if goodRV.levelParams.length == lparams.length + 1 then Level.zero :: us else us
  let goodRec := fun (ps : Array Expr) (motive : Expr) (minors : Array Expr)
      (s : Expr) (is : Array Expr) (g : Expr) =>
    mkAppN (.const goodRecN goodRecLevels) (ps ++ #[motive] ++ minors ++ #[s] ++ is ++ #[g])

  -- The carved family has exactly the source sort: `max w 0 = w`, including
  -- the `w = 0` instantiation.
  let selfVal ← site.withParams fun ps => do
    let tele ← instForall memberTy ps
    forallBoundedTelescope tele (some ni) fun is _ => do
      mkLambdaFVars (ps ++ is) (psigmaT w .zero (skelSelf ps) (← βOf ps is))
  let selfDecl := Declaration.defnDecl
    { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfVal
      hints := ← hintsFor selfVal, safety := .safe }
  addChecked selfDecl
  out := out.push selfDecl

  -- Constructors pair the erased constructor with the corresponding evidence.
  for j in [0:nc] do
    let ty := publicSource sourceCtors[j]!.2
    let val ← site.withParams fun ps => do
      let tele ← instForall ty ps
      let nf := numForalls tele
      forallBoundedTelescope tele (some nf) fun fs _ => do
        let (idx, slots) ← shapeAt ps fs j
        let mut gs := fs
        let mut proofs : Array Expr := #[]
        for (k, dom) in slots do
          let (sk, proof) ← withRecSlot tname np ni dom fun zs chi => do
            let child := mkAppN fs[k]! zs
            let β ← βOf ps chi
            pure (← mkLambdaFVars zs (psigmaFst w .zero (skelSelf ps) β child),
              ← mkLambdaFVars zs (psigmaSnd w .zero (skelSelf ps) β child))
          gs := gs.set! k sk
          proofs := proofs.push proof
        let s := mkAppN (.const (skelCtorN j) us) (ps ++ gs)
        let g := mkAppN (.const (goodCtorN j) us) (ps ++ gs ++ proofs)
        mkLambdaFVars (ps ++ fs)
          (psigmaMk w .zero (skelSelf ps) (← βOf ps idx) s g)
    let decl := Declaration.defnDecl
      { name := ctorN j, levelParams := lparams, type := ty, value := val
        hints := ← hintsFor val, safety := .safe }
    addChecked decl
    out := out.push decl

  -- Recurse on the `Good` proof. Its small eliminator has exactly the strength
  -- of a sometimes-`Prop` source recursor, and its recursive proof fields
  -- provide the source induction hypotheses.
  let recVal ← forallBoundedTelescope installedRecTy
      (some (np + 1 + nc + ni + 1)) fun bs _ => do
    let ps := bs.extract 0 np
    let motive := bs[np]!
    let sourceMinors := bs.extract (np + 1) (np + 1 + nc)
    let idxs := bs.extract (np + 1 + nc) (np + 1 + nc + ni)
    let t := bs[bs.size - 1]!
    let goodMotive ← withLocalDeclD `s (skelSelf ps) fun s => do
      let tele ← instForall memberTy ps
      forallBoundedTelescope tele (some ni) fun is _ =>
        withLocalDeclD `g (goodAt ps s is) fun g => do
          let pair := psigmaMk w .zero (skelSelf ps) (← βOf ps is) s g
          mkLambdaFVars (#[s] ++ is ++ #[g]) (mkAppN motive (is.push pair))
    let goodMinors ← (Array.range nc).mapM fun j => do
      let tele ← instForall exportCtors[j]!.2 ps
      let nf := numForalls tele
      let swapped ← spineSwap tname (skelSelf ps) nf tele
      forallBoundedTelescope swapped (some nf) fun gs _ => do
        let (_, slots) ← shapeAt ps gs j
        let proofTypes ← proofTypesAt ps gs slots
        withRelLocalsD (proofTypes.mapIdx fun i ty => (Name.mkSimple s!"good_{i}", ty)) 0 #[]
          fun proofs => do
            let ihTypes ← slots.mapIdxM fun r (k, dom) =>
              withRecSlot tname np ni dom fun zs chi =>
                mkForallFVars zs (mkAppN goodMotive
                  (#[mkAppN gs[k]! zs] ++ chi ++ #[mkAppN proofs[r]! zs]))
            withRelLocalsD (ihTypes.mapIdx fun i ty => (Name.mkSimple s!"ih_{i}", ty)) 0 #[]
              fun ihs => do
                let mut fields := gs
                for r in [0:slots.size] do
                  let (k, dom) := slots[r]!
                  let child ← withRecSlot tname np ni dom fun zs chi => do
                    let β ← βOf ps chi
                    mkLambdaFVars zs (psigmaMk w .zero (skelSelf ps) β
                      (mkAppN gs[k]! zs) (mkAppN proofs[r]! zs))
                  fields := fields.set! k child
                mkLambdaFVars (gs ++ proofs ++ ihs)
                  (mkAppN sourceMinors[j]! (fields ++ ihs))
    let β ← βOf ps idxs
    let s := psigmaFst w .zero (skelSelf ps) β t
    let g := psigmaSnd w .zero (skelSelf ps) β t
    mkLambdaFVars bs (goodRec ps goodMotive goodMinors s idxs g)
  let recDecl := Declaration.defnDecl
    { name := recN, levelParams := rv.levelParams, type := publicRecTy, value := recVal
      hints := ← hintsFor recVal, safety := .safe }
  addChecked recDecl
  out := out.push recDecl

  -- A one-constructor model reads every intrinsic field from its erased
  -- skeleton.  A recursive field additionally needs its `Good` proof; obtain
  -- that proof by small elimination on the parent's `Good` evidence, then pair
  -- it with the already-projected skeleton child.  Thus even recursive
  -- projections never ask the source recursor to eliminate into `Sort u`.
  if nc == 1 then
    let (nonrecursive, recursive) ← site.wShapeOf 0
    for fieldIndex in nonrecursive ++ recursive do
      let selector ← site.withParams fun ps => do
        let tele ← instForall memberTy ps
        forallBoundedTelescope tele (some ni) fun is _ => do
          let β ← βOf ps is
          withLocalDeclD `self (mkAppN (.const selfN us) (ps ++ is)) fun self => do
            let s := psigmaFst w .zero (skelSelf ps) β self
            let g := psigmaSnd w .zero (skelSelf ps) β self
            if nonrecursive.contains fieldIndex then
              mkLambdaFVars (ps ++ is ++ #[self]) (.proj skelN fieldIndex s)
            else
              let ctele ← instForall exportCtors[0]!.2 ps
              let nf := numForalls ctele
              let fields := (Array.range nf).map fun k => .proj skelN k s
              let (_, slots) ← shapeAt ps fields 0
              let some selectedSlot := slots.findIdx? fun slot => slot.1 == fieldIndex
                | badShape s!"{exportCtors[0]!.1}'s recursive field {fieldIndex} vanished from relational Carve"

              let projectionMotive ← withLocalDeclD `s (skelSelf ps) fun sm => do
                let indexTele ← instForall memberTy ps
                forallBoundedTelescope indexTele (some ni) fun js _ =>
                  withLocalDeclD `g (goodAt ps sm js) fun gm => do
                    let projected := (Array.range nf).map fun k => .proj skelN k sm
                    let (_, motiveSlots) ← shapeAt ps projected 0
                    let proofTypes ← proofTypesAt ps projected motiveSlots
                    mkLambdaFVars (#[sm] ++ js ++ #[gm]) proofTypes[selectedSlot]!

              let projectionMinors ← (Array.range nc).mapM fun j => do
                let sourceTele ← instForall exportCtors[j]!.2 ps
                let sourceNf := numForalls sourceTele
                let swapped ← spineSwap tname (skelSelf ps) sourceNf sourceTele
                forallBoundedTelescope swapped (some sourceNf) fun gs _ => do
                  let (_, minorSlots) ← shapeAt ps gs j
                  let proofTypes ← proofTypesAt ps gs minorSlots
                  withRelLocalsD
                      (proofTypes.mapIdx fun i ty => (Name.mkSimple s!"good_{i}", ty))
                      0 #[] fun proofs => do
                    let ihTypes ← minorSlots.mapIdxM fun r (k, dom) =>
                      withRecSlot tname np ni dom fun zs chi =>
                        mkForallFVars zs (mkAppN projectionMotive
                          (#[mkAppN gs[k]! zs] ++ chi ++ #[mkAppN proofs[r]! zs]))
                    withRelLocalsD
                        (ihTypes.mapIdx fun i ty => (Name.mkSimple s!"ih_{i}", ty))
                        0 #[] fun ihs =>
                      mkLambdaFVars (gs ++ proofs ++ ihs) proofs[selectedSlot]!

              let childGood := goodRec ps projectionMotive projectionMinors s is g
              let (_, childDom) := slots[selectedSlot]!
              let child ← withRecSlot tname np ni childDom fun zs chi => do
                let childβ ← βOf ps chi
                mkLambdaFVars zs (psigmaMk w .zero (skelSelf ps) childβ
                  (mkAppN fields[fieldIndex]! zs) (mkAppN childGood zs))
              mkLambdaFVars (ps ++ is ++ #[self]) child
      let proof ← site.withParams fun ps => do
        let tele ← instForall (publicSource sourceCtors[0]!.2) ps
        let nf := numForalls tele
        forallBoundedTelescope tele (some nf) fun fs _ => do
          let selected := fs[fieldIndex]!
          let ty ← inferType selected
          mkLambdaFVars (ps ++ fs) (eqi.refl' (← ilevel ty) ty selected)
      projectionOverrides := projectionOverrides.push (tname, fieldIndex, selector, proof)

  return { st with out, spliced, requires, projectionOverrides }

end InductiveModels
