import InductiveModels.Simple.Site
import InductiveModels.Simple.Erasure
import InductiveModels.Simple.GraphKit

/-!
# Arm C: an indexed family carved out of its own index erasure
-/

open Lean Meta

namespace InductiveModels

def primArmC (site : PrimSite) (st : PrimOut) : GenM PrimOut := do
  -- The site, under the names this arm has always read it by.
  let tname := site.tname
  let lparams := site.lparams
  let np := site.np
  let memberTy := site.memberTy
  let exportCtors := site.exportCtors
  let reserved := site.reserved
  let us := site.us
  let selfN := site.selfN
  let ern := site.ern
  let recN := site.recN
  let ctorN := site.ctorN
  let skelN := site.skelN
  let goodN := site.goodN
  let skelCtorN := site.skelCtorN
  let nc := site.nc
  let taken := site.taken
  let declaredMemberTy := site.declaredMemberTy
  let ni := site.ni
  let w := site.w
  let rv := site.rv
  let large := site.large
  let v := site.v
  let eqi := site.eqi
  let installedRecTy := site.installedRecTy
  let publicSource := site.publicSource
  let publicRecTy := site.publicRecTy
  let andCMk := site.andCMk
  let andCFst := site.andCFst
  let andCSnd := site.andCSnd
  let mut out := st.out
  let mut spliced := st.spliced
  -- ════ arm C: an indexed family, carved out of its spliced erasure ════
  --
  -- A skeleton-plus-`good` construction standing on a **real inductive**
  -- rather than on a W-type. The requirement to use the real type picks the
  -- shape: the thing the carve needs underneath it is a non-indexed
  -- inductive with the same constructor telescopes, and that is a
  -- declaration we can *splice* — so we splice it, the kernel mints its
  -- recursor, and everything below is written against the genuine article
  -- with its definitional ι. The splice-and-model pass then models it like
  -- any other spliced inductive, and `Iso.requires` withdraws the whole
  -- model if it cannot.
  --
  --     skel p⃗           := T with its indices erased  (spliced inductive)
  --     good p⃗ s y       := skel.rec … — `Eq Pk e⃗_j y`, conjoined with
  --                         **each** child's own goodness at its own index
  --     T._model.self p⃗ ι⃗ := Σ'(s : skel p⃗), good p⃗ s (pack ι⃗)
  --
  -- **Any number of recursive fields per constructor.** The erasure replaces
  -- each recursive field's whole domain, so a branching constructor erases as
  -- readily as a linear one; `good`'s clause for it is a right-nested chain
  -- with one conjunct per child, the constructor's carve proof supplies one
  -- component per child, and the recursor takes one induction hypothesis per
  -- child. All three read `ctorIdxAt`'s slot array, in telescope order.
  -- The skeleton that comes out **branches**, and arm W is what models it —
  -- which is why this could not be relaxed before arm W landed.
  --
  -- What this buys over carving out of W: **no per-constructor currying
  -- glue** (a
  -- spliced skeleton keeps the field telescope, so the minor `skel.rec`
  -- wants is the minor `T.rec` wants — no `B a ≅ Fin k` iso, no eta lemma,
  -- no `funext`), **ι by `Eq.refl`** (the shared block below proves every
  -- rule that way, unchanged), and **no axioms at all**.
  --
  -- Three reductions carry the ι rules and each is load-bearing:
  -- definitional proof irrelevance (`⟨s, h⟩ ≡ ⟨s, h'⟩`, so the carved
  -- component never obstructs), the skeleton's own ι, and `PSigma'`'s
  -- structure eta (`⟨t.1, t.2⟩ ≡ t`, and `unpack (pack ι⃗) ≡ ι⃗`).
  unless large do
    badShape s!"{ern} is not large-eliminating at a Type-valued carrier"
  for n in [skelN, goodN] do taken n
  for j in [0:nc] do taken (skelCtorN j)
  for d in ← ensurePSigmaPrime reserved do out := out.push d; spliced := spliced ++ d.getNames

  let skelSelf := fun (ps : Array Expr) => mkAppN (.const skelN us) ps
  -- The index telescope packed into one `PSigma'` ([`InductiveModels.packTyOf`]),
  -- at a parameter scope. Closed over the telescope, so it depends on `ps`
  -- alone.
  let pkAt := fun (ps : Array Expr) => do
    forallBoundedTelescope (← instForall memberTy ps) (some ni) fun is _ => packTyOf is 0
  -- `fun s => good p⃗ s y` — the carve's predicate as `PSigma'`'s `β`.
  let βOf := fun (ps : Array Expr) (y : Expr) =>
    withLocalDeclD `s (skelSelf ps) fun s =>
      mkLambdaFVars #[s] (mkAppN (.const goodN us) (ps ++ #[s, y]))

  -- ── the skeleton, spliced ──
  -- Each constructor keeps its field telescope; only the recursive fields'
  -- types and the codomain lose their indices. [`InductiveModels.spineSwap`] does
  -- the first and is the tuple tower's own swap, which is the same swap
  -- because `erasureBare` has already said the recursive occurrence reduces
  -- to `∀ z⃗, T p⃗ e⃗` rather than remaining nested.
  let skelDecl : Declaration :=
    .inductDecl lparams np
      [{ name := skelN, type := eraseSelfTy np w memberTy,
         ctors := (List.range nc).map fun j =>
           { name := skelCtorN j,
             type := eraseCtorTy tname skelN us np exportCtors[j]!.2 } }] false
  addChecked skelDecl
  out := out.push skelDecl
  spliced := spliced.push skelN

  let skelRecN := Name.str skelN "rec"
  let some (.recInfo srv) := (← getEnv).find? skelRecN
    | badShape s!"the kernel minted no recursor for the spliced {skelN}"
  unless srv.levelParams.length == lparams.length + 1 do
    badShape s!"{skelRecN} is not large-eliminating, so the carve cannot state \
      a recursor at an arbitrary motive"
  let skelRec := fun (m : Level) (ps : Array Expr) (mot : Expr)
      (minors : Array Expr) (t : Expr) =>
    mkAppN (.const skelRecN (m :: us)) (ps ++ #[mot] ++ minors ++ #[t])

  -- Constructor `j`'s **index expressions** and **every** recursive slot's
  -- position with its own **domain**, read off the export's own telescope
  -- and re-expressed at whatever field vector the caller has opened — the
  -- erased one when building `good`, the restored one when building the
  -- constructor. The substitution is sound because an index expression can
  -- only mention parameters and *non-recursive* fields: there is no way to
  -- compute an index out of a recursive field before the type exists.
  --
  -- **The domain rather than the child's indices**, because an infinitary
  -- field's indices are not expressions at this scope at all: they mention
  -- the field's own binders, and those exist only once someone has opened
  -- them. So each consumer opens the slot itself with
  -- [`InductiveModels.withRecSlot`] and gets `z⃗` and `e⃗(z⃗)` together, inside a
  -- scope where it can abstract them again. At zero binders every consumer
  -- builds exactly the term it built when this returned `e⃗` directly.
  --
  -- **The array is in telescope order and every consumer depends on that.**
  -- The skeleton recursor's minor binds its induction hypotheses in the order
  -- of the recursive fields, `good`'s conjunction is built in that order, and
  -- the constructor's carve proof supplies its components in that order — so
  -- the three agree only because all three read this one array.
  --
  -- Where a constructor's recursive fields sit at *different* indices, a
  -- dropped or permuted slot is a type error in the model constructor. Where
  -- they are interchangeable it is **not**: the constructor is well typed and
  -- the kernel accepts it, and what catches the permutation is `rec_0`, whose
  -- index transport is written against the skeleton term the model
  -- constructor is supposed to reduce to.
  -- `test/fixtures/inductive-models/prim_carve.lean`'s `Sm3` is
  -- that occupant and its header records the four mutations — including the
  -- association error that two recursive fields cannot see at all.
  let ctorIdxAt := fun (ps gs : Array Expr) (j : Nat) => do
    let (cn, cty) := exportCtors[j]!
    let tele ← instForall cty ps
    let nf := numForalls tele
    forallBoundedTelescope tele (some nf) fun fs res => do
      let some args ← ownerAppArgs? tname np ni res
        | badShape s!"{cn} does not end in {tname} at {np} parameters and {ni} indices"
      let idx := (args.extract np args.size).map (·.replaceFVars fs gs)
      let mut slots : Array (Nat × Expr) := #[]
      for i in [0:nf] do
        -- `mentionsAny` on the type **as written**, which is the test
        -- [`InductiveModels.eraseCtorTy`] and [`InductiveModels.spineSwap`] replace an
        -- occurrence on; the reading through `headNorm` happens in
        -- [`InductiveModels.withRecSlot`], where the consumer opens the slot.
        let ft0 ← ityp fs[i]!
        if erasureRecursive tname ft0 then
          slots := slots.push (i, ft0.replaceFVars fs gs)
      pure (idx, slots)

  -- ── the carve's conjunction, at an arbitrary number of slots ──
  -- `good p⃗ (c f⃗) y` is `y = ι⃗_c` conjoined with **one clause per recursive
  -- field**, right-nested: `A ∧ (B₀ ∧ (B₁ ∧ B₂))`. Right-nested rather than
  -- left because then the *first* projection is always the index equation and
  -- the second is always "the rest", which is the shape the recursor's minor
  -- destructs and the shape it rebuilds under the index transport — it moves
  -- the whole tail as one proof and never has to re-associate.
  --
  -- With no recursive field there is no tail at all and `good` is the bare
  -- equation, which is the arm's original zero-slot branch unchanged.
  let chainTyOf : Array Expr → Option Expr := fun bs =>
    bs.foldr (fun b acc => some (match acc with | none => b | some t => andCOf b t)) none
  -- The tail of `bs` from `i`, as a type. `bs[i:]` right-nested.
  let tailTyOf : Array Expr → Nat → Option Expr := fun bs i =>
    chainTyOf (bs.extract i bs.size)
  -- The proof of `chainTyOf bs` from one proof per conjunct.
  let chainMkOf : Array Expr → Array Expr → GenM (Option Expr) := fun bs prs => do
    let mut acc : Option Expr := none
    for i' in [0:bs.size] do
      let i := bs.size - 1 - i'
      acc := some (← match acc with
        | none => pure prs[i]!
        | some t => andCMk bs[i]! (tailTyOf bs (i + 1)).get! prs[i]! t)
    pure acc
  -- The conjuncts of `chainTyOf bs`, extracted from one proof of it.
  let chainSplit : Array Expr → Expr → GenM (Array Expr) := fun bs p => do
    let mut out : Array Expr := #[]
    let mut cur := p
    for i in [0:bs.size] do
      if i + 1 == bs.size then out := out.push cur
      else
        let rest := (tailTyOf bs (i + 1)).get!
        out := out.push (← andCFst bs[i]! rest cur)
        cur ← andCSnd bs[i]! rest cur
    pure out

  -- ── `good`, by the skeleton's own recursor ──
  -- The motive is `fun _ => Pk → Prop`, which is a `Prop`, so this uses only
  -- the skeleton's **small** elimination. The large one is spent once, on
  -- the recursor below.
  let goodTy ← site.withParams fun ps => do
    let (pk, _) ← pkAt ps
    withLocalDeclD `s (skelSelf ps) fun s => withLocalDeclD `y pk fun y =>
      mkForallFVars (ps ++ #[s, y]) (.sort .zero)
  let goodVal ← site.withParams fun ps => do
    let (pk, ℓpk) ← pkAt ps
    let predTy := Expr.forallE `y pk (.sort .zero) .default
    let mot ← withLocalDeclD `s (skelSelf ps) fun s => mkLambdaFVars #[s] predTy
    let minors ← (Array.range nc).mapM fun j => do
      let tele ← instForall exportCtors[j]!.2 ps
      let nf := numForalls tele
      let swapped ← spineSwap tname (skelSelf ps) nf tele
      forallBoundedTelescope swapped (some nf) fun gs _ => do
        let (idx, slots) ← ctorIdxAt ps gs j
        let pkc ← packChain ni pk idx 0
        -- One induction hypothesis per recursive field, in telescope order —
        -- which is the order the kernel's own minor binds them in. At an
        -- infinitary field the kernel binds it **under the field's own
        -- binders**: for `g : ∀ z⃗, S p⃗` the hypothesis is
        -- `∀ z⃗, motive (g z⃗)`, and at the constant motive `fun _ => Pk →
        -- Prop` that is `∀ z⃗, Pk → Prop` — which is [`InductiveModels.swapOcc`] at
        -- `predTy`, the same rewrite that built the erased telescope.
        let ihTys ← slots.mapM fun (_, dom) => do pure (`ih, ← swapOcc predTy dom)
        withLocalsD ihTys 0 #[] fun ihs => do
          -- and the clause it carries is `∀ z⃗, good p⃗ (g z⃗) (pack e⃗(z⃗))`,
          -- which `∀` into `Prop` keeps a `Prop`, so the Church conjunction
          -- takes it unchanged.
          let bs ← slots.mapIdxM fun i (_, dom) =>
            withRecSlot tname np ni dom fun zs chi => do
              mkForallFVars zs (mkApp (mkAppN ihs[i]! zs) (← packChain ni pk chi 0))
          let body ← withLocalDeclD `y pk fun y => do
            let eq := eqi.mk' ℓpk pk pkc y
            mkLambdaFVars #[y] (match chainTyOf bs with
              | none => eq
              | some t => andCOf eq t)
          mkLambdaFVars (gs ++ ihs) body
    -- **The motive's universe is `imax ℓpk 1`, not `0`.** `Pk → Prop` is a
    -- *predicate type*, and its codomain is the type `Prop`, which lives in
    -- `Sort 1` — so the fold is a `Sort 1`-valued elimination and not a
    -- propositional one. Asked of the expression rather than assumed: the
    -- first attempt passed `0` and the kernel said `skel α → Type`.
    let mGood ← ilevel predTy
    withLocalDeclD `s (skelSelf ps) fun s => withLocalDeclD `y pk fun y =>
      mkLambdaFVars (ps ++ #[s, y]) (mkApp (skelRec mGood ps mot minors s) y)
  let dGood := Declaration.defnDecl
    { name := goodN, levelParams := lparams, type := goodTy, value := goodVal
      hints := ← hintsFor goodVal, safety := .safe }
  addChecked dGood
  out := out.push dGood

  -- ── the carrier ──
  let selfVal ← site.withParams fun ps => do
    let (pk, _) ← pkAt ps
    forallBoundedTelescope (← instForall memberTy ps) (some ni) fun is _ => do
      let β ← βOf ps (← packChain ni pk is 0)
      mkLambdaFVars (ps ++ is) (psigmaT w .zero (skelSelf ps) β)
  let dSelf := Declaration.defnDecl
    { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfVal
      hints := ← hintsFor selfVal, safety := .safe }
  addChecked dSelf
  out := out.push dSelf

  -- ── the constructors ──
  for j in [0:nc] do
    let ty := publicSource exportCtors[j]!.2
    let val ← site.withParams fun ps => do
      let (pk, ℓpk) ← pkAt ps
      let rtele ← instForall ty ps
      let nf := numForalls rtele
      forallBoundedTelescope rtele (some nf) fun fs _ => do
        let (idx, slots) ← ctorIdxAt ps fs j
        let pkc ← packChain ni pk idx 0
        -- Each recursive field arrives as a carve pair `⟨s, h⟩`; the skeleton
        -- constructor takes the first component and the carve proof's tail is
        -- the second, one per slot and in the same order. At an infinitary
        -- field it arrives as a **function into** carve pairs, so all three
        -- go under the field's own binders: the skeleton's field is
        -- `fun z⃗ => (f z⃗).1`, the clause is `∀ z⃗, good p⃗ ((f z⃗).1) (pack
        -- e⃗(z⃗))`, and its proof is `fun z⃗ => (f z⃗).2`.
        let mut gs := fs
        let mut bs : Array Expr := #[]
        let mut prs : Array Expr := #[]
        for (k, dom) in slots do
          let (sk, b, pr) ← withRecSlot tname np ni dom fun zs chi => do
            let pkchi ← packChain ni pk chi 0
            let βchi ← βOf ps pkchi
            let fk := mkAppN fs[k]! zs
            let s1 := psigmaFst w .zero (skelSelf ps) βchi fk
            pure (← mkLambdaFVars zs s1,
                  ← mkForallFVars zs (mkAppN (.const goodN us) (ps ++ #[s1, pkchi])),
                  ← mkLambdaFVars zs (psigmaSnd w .zero (skelSelf ps) βchi fk))
          gs := gs.set! k sk
          bs := bs.push b
          prs := prs.push pr
        let refl := eqi.refl' ℓpk pk pkc
        let proof ← match ← chainMkOf bs prs with
          | none => pure refl
          | some tail =>
            andCMk (eqi.mk' ℓpk pk pkc pkc) (chainTyOf bs).get! refl tail
        let β ← βOf ps pkc
        mkLambdaFVars (ps ++ fs)
          (psigmaMk w .zero (skelSelf ps) β
            (mkAppN (.const (skelCtorN j) us) (ps ++ gs)) proof)
    let d := Declaration.defnDecl
      { name := ctorN j, levelParams := lparams, type := ty, value := val
        hints := ← hintsFor val, safety := .safe }
    addChecked d
    out := out.push d

  -- ── the recursor ──
  -- One `skel.rec` at the motive `fun s => ∀ y h, C (unpack y) ⟨s, h⟩`, and
  -- one `Eq.rec` per constructor to move the conclusion from the
  -- constructor's own index to the caller's. The index equation is the
  -- first component of the `good` proof the major already carries, so
  -- nothing per-constructor is *proved* here — it is extracted.
  let recVal ← forallBoundedTelescope installedRecTy
      (some (np + 1 + nc + ni + 1)) fun bs _ => do
    let ps := bs.extract 0 np
    let motive := bs[np]!
    let minors := bs.extract (np + 1) (np + 1 + nc)
    let idxs := bs.extract (np + 1 + nc) (np + 1 + nc + ni)
    let t := bs[bs.size - 1]!
    let (pk, ℓpk) ← pkAt ps
    -- `∀ (y : Pk) (h : good p⃗ s y), motive (unpack y) ⟨s, h⟩` at a given
    -- skeleton element — the skeleton recursor's motive, and the type of the
    -- induction hypothesis at a recursive field.
    let atSkel := fun (s : Expr) => withLocalDeclD `y pk fun y => do
      let βy ← βOf ps y
      withLocalDeclD `h (mkAppN (.const goodN us) (ps ++ #[s, y])) fun h => do
        let ys ← unpackChain ni pk y
        mkForallFVars #[y, h]
          (mkAppN motive (ys.push (psigmaMk w .zero (skelSelf ps) βy s h)))
    let (sMotive, m) ← withLocalDeclD `s (skelSelf ps) fun s => do
      let inner ← atSkel s
      pure (← mkLambdaFVars #[s] inner, ← ilevel inner)
    let sMinors ← (Array.range nc).mapM fun j => do
      let tele ← instForall exportCtors[j]!.2 ps
      let nf := numForalls tele
      let swapped ← spineSwap tname (skelSelf ps) nf tele
      forallBoundedTelescope swapped (some nf) fun gs _ => do
        let (idx, slots) ← ctorIdxAt ps gs j
        let pkc ← packChain ni pk idx 0
        let head := mkAppN (.const (skelCtorN j) us) (ps ++ gs)
        -- `B⃗` are the tail conjuncts of `good p⃗ head y` — one per recursive
        -- field, in telescope order, and empty when there is none. They are
        -- the very clauses `good`'s own minor built, so they go under the
        -- field's binders in exactly the same way.
        let bTys ← slots.mapM fun (k, dom) =>
          withRecSlot tname np ni dom fun zs chi => do
            mkForallFVars zs (mkAppN (.const goodN us)
              (ps ++ #[mkAppN gs[k]! zs, ← packChain ni pk chi 0]))
        let body := fun (ihs : Array Expr) => withLocalDeclD `y pk fun y => do
          let aTy := eqi.mk' ℓpk pk pkc y
          withLocalDeclD `h (mkAppN (.const goodN us) (ps ++ #[head, y])) fun h => do
            -- The index equation, and the whole tail as **one** proof. The
            -- tail is split into its per-slot components only where the
            -- minor's own arguments need them; the transport moves it intact.
            let (he, tail?) ← match chainTyOf bTys with
              | none => pure (h, none)
              | some bTy => do
                pure (← andCFst aTy bTy h, some (← andCSnd aTy bTy h))
            let hcs ← match tail? with
              | none => pure #[]
              | some tail => chainSplit bTys tail
            -- the motive of the index transport: rebuild the carve proof at
            -- each point, which proof irrelevance then identifies with `h`.
            let motiveE ← withLocalDeclD `y2 pk fun y2 => do
              withLocalDeclD `hh (eqi.mk' ℓpk pk pkc y2) fun hh => do
                let β2 ← βOf ps y2
                let reb ← match chainTyOf bTys, tail? with
                  | some bTy, some tail =>
                    andCMk (eqi.mk' ℓpk pk pkc y2) bTy hh tail
                  | _, _ => pure hh
                let ys ← unpackChain ni pk y2
                mkLambdaFVars #[y2, hh]
                  (mkAppN motive (ys.push (psigmaMk w .zero (skelSelf ps) β2 head reb)))
            -- the minor premise, at the carrier's own fields: every recursive
            -- slot repaired into a carve pair, and one induction hypothesis
            -- per slot appended in the same order.
            --
            -- At an infinitary slot the carrier's field is a *function* into
            -- carve pairs and the minor's hypothesis is `∀ z⃗, C ι⃗(z⃗) (f
            -- z⃗)`, so both go under the field's binders: the argument is
            -- `fun z⃗ => ⟨g z⃗, hc z⃗⟩` and the hypothesis is `fun z⃗ => ih z⃗
            -- (pack e⃗(z⃗)) (hc z⃗)`, whose conclusion is at `unpack (pack
            -- e⃗(z⃗))` and so at `e⃗(z⃗)` by structure eta.
            let mut args := gs
            let mut extra : Array Expr := #[]
            for i in [0:slots.size] do
              let (k, dom) := slots[i]!
              let (a, e) ← withRecSlot tname np ni dom fun zs chi => do
                let pkchi ← packChain ni pk chi 0
                let βchi ← βOf ps pkchi
                let hc := mkAppN hcs[i]! zs
                pure (← mkLambdaFVars zs
                        (psigmaMk w .zero (skelSelf ps) βchi (mkAppN gs[k]! zs) hc),
                      ← mkLambdaFVars zs (mkAppN ihs[i]! (zs ++ #[pkchi, hc])))
              args := args.set! k a
              extra := extra.push e
            let base := mkAppN minors[j]! (args ++ extra)
            mkLambdaFVars #[y, h] (eqi.recAt v ℓpk pk pkc motiveE base y he)
        -- The skeleton recursor's minor binds the fields, then one induction
        -- hypothesis per recursive field in telescope order — and at an
        -- infinitary field under that field's own binders, at the skeleton
        -- element it names there.
        let ihTys ← slots.mapM fun (k, dom) => do
          pure (`ih, ← withRecSlot tname np ni dom fun zs _ => do
            mkForallFVars zs (← atSkel (mkAppN gs[k]! zs)))
        withLocalsD ihTys 0 #[] fun ihs => do
          mkLambdaFVars (gs ++ ihs) (← body ihs)
    let pki ← packChain ni pk idxs 0
    let βi ← βOf ps pki
    let t1 := psigmaFst w .zero (skelSelf ps) βi t
    let t2 := psigmaSnd w .zero (skelSelf ps) βi t
    mkLambdaFVars bs (mkAppN (skelRec m ps sMotive sMinors t1) #[pki, t2])
  let dRec := Declaration.defnDecl
    { name := recN, levelParams := rv.levelParams, type := publicRecTy, value := recVal
      hints := ← hintsFor recVal, safety := .safe }
  addChecked dRec
  out := out.push dRec
  return { st with out, spliced }

end InductiveModels
