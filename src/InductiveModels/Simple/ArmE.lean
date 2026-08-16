import InductiveModels.Simple.Site

/-!
# Arm E: the declaration every one of whose constructors has a bare recursive field

Such a declaration is **empty** — no constructor can be applied, because
applying one would already require an inhabitant of the carrier — and the model
is an empty type at exactly the declared sort. The recursor and its ι rules
follow from that one fact alone: both eliminate the same uninhabited value.

**But empty does not have to mean empty-handed.** The carrier is a right-nested
`PSigma'` tower over the constructor's non-recursive fields, ending at
[`InductiveModels.emptyAt`] `w`. A pair is inhabited only when both components
are, so the tower is uninhabited *because of its tail* — at every arity, every
field level and every constructor count — while the fields in front of it are
genuinely stored and the tower's own projections select them by π. The tail is
a constant and mentions nothing recursive, so the carrier is still a plain
definition; that is the difference from storing the recursive field itself,
which is what made storage impossible here before.

So the constructor is the tower `⟨f⃗, drop t⟩`, where `t` is its own bare
recursive field and `drop` is the `snd` chain that takes any inhabitant back to
the emptiness it ends in: the constructor manufactures nothing it was not
handed. The intrinsic projections of the stored fields are the tower's own
`PSigma'` projections and reduce on that constructor, so their ι rules are
`Eq.refl`; the recursor, its ι rules and the projections of the *recursive*
fields still eliminate, now through `drop`.

Where the shape does not admit storage — two or more constructors, or a field
whose level the tower cannot reach — `eStored` is empty, `drop` is the identity
and every line below is the bare empty carrier it always was. That decision, and
why both of its answers are total, is stated at
[`InductiveModels.mkPrimSite`].

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

/-- **Arm E's intrinsic projections for the fields it stores.**

The common driver's projection-ι contract is literal — `T._model.proj_j` at the
modeled constructor *is* the constructor's own field binder, with no transport —
and for a field whose type names an earlier field that is a statable
proposition only if the earlier field's selector **reduces** on the modeled
constructor. An elimination never does: it is total at every codomain and
reduces to no field, because no field is there.

**The tower puts the fields there.** `T._model.mk p⃗ f⃗` δβ-reduces to
`⟨f⃗, drop t⟩`, so the tower's own `PSigma'.fst` after `q` `snd`s is `f_q` by π
alone, `unbox (box v) ≡ v` closes a boxed component, and the rule is `Eq.refl`
at the constructor's own binder and its own declared type. The driver states it
at the intrinsic codomain — field `j`'s type with each earlier field replaced by
*its* modeled projection at this major — and because every earlier projection in
that codomain is one of these selectors, the two statements are the same one.

**The recursive fields keep the elimination and that is a decision.** Lean's
positivity and nesting rules leave no spelling of a constructor field type that
reads a recursive occurrence's *value*
(`test/fixtures/inductive-models/nested_value_dependency.lean` writes out every
attempt and the kernel refuses each), so the stored fields are exactly the
fields a codomain can name; nothing is stated about a recursive field that the
emptiness does not prove. Those projections stay on the driver's
`emptyCarriers` path, which now descends through `drop` first.

**Empty exactly when nothing is stored**, which is the storage decision at
[`InductiveModels.mkPrimSite`] and not a second gate. -/
private def eStoredFieldOverrides (site : PrimSite) :
    GenM (Array (Name × Nat × Expr × Expr)) := do
  if site.eStored.isEmpty then return #[]
  let us := site.us
  let w := site.w
  let eqi := site.eqi
  let mut overrides : Array (Name × Nat × Expr × Expr) := #[]
  for q in [0:site.eStored.size] do
    let selector ← site.withParams fun ps => do
      site.withStored ps fun xs => do
        withLocalDeclD `self (mkAppN (.const site.selfN us) ps) fun self => do
          let projections ← eTowerProjsOf w xs self
          mkLambdaFVars (ps.push self) projections[q]!
    let proof ← site.withParams fun ps => do
      let tele ← instForall (site.publicSource site.sourceCtors[0]!.2) ps
      forallBoundedTelescope tele (some (numForalls tele)) fun fields _ => do
        let selected := fields[site.eStored[q]!]!
        let fieldType ← ityp selected
        mkLambdaFVars (ps ++ fields)
          (eqi.refl' (← ilevel fieldType) fieldType selected)
    overrides := overrides.push (site.tname, site.eStored[q]!, selector, proof)
  return overrides

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

  -- The carrier is empty at exactly the inductive's universe, and stores the
  -- one constructor's non-recursive fields in front of that emptiness where
  -- the shape admits it.
  let selfVal ← site.withParams fun ps =>
    return ← mkLambdaFVars ps (← site.eCarrier ps)
  let dSelf := Declaration.defnDecl
    { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfVal
      hints := ← hintsFor selfVal, safety := .safe }
  addChecked dSelf
  out := out.push dSelf

  -- **A constructor manufactures nothing.**  Its direct recursive field
  -- already inhabits the carrier, so the emptiness the carrier ends in is
  -- already in hand: `drop` it and put the constructor's own stored fields in
  -- front.  With nothing stored `drop` is the identity and this is the field
  -- returned bare, which is what the arm always did.
  for j in [0:nc] do
    let (_, cty) := exportCtors[j]!
    let ty := publicSource sourceCtors[j]!.2
    let nfj ← site.withParams fun ps => do pure (numForalls (← instForall cty ps))
    let val ← site.withParams fun ps => do
      let rtele ← instForall ty ps
      forallBoundedTelescope rtele (some nfj) fun fs _ => do
        let some k := emptySlots[j]!
          | badShape s!"{exportCtors[j]!.1} has no recursive field in the empty route"
        let tail ← site.eDrop ps fs[k]!
        let value ←
          if site.eStored.isEmpty then pure tail
          else site.withStored ps fun xs =>
            eTowerMkOf w xs (site.eStored.map (fs[·]!)) tail
        mkLambdaFVars (ps ++ fs) value
    let d := Declaration.defnDecl
      { name := ctorN j, levelParams := lparams, type := ty, value := val
        hints := ← hintsFor val, safety := .safe }
    addChecked d
    out := out.push d

  -- The major premise is an inhabitant of the empty carrier.  Dropping it to
  -- the emptiness that carrier ends in and eliminating that gives the
  -- recursor's motive at any result universe — **a large eliminator at every
  -- `v`, which storage does not touch**: the descent is `PSigma'` projections
  -- and [`InductiveModels.emptyAtElim`] is `cfalseElim` after the lift's
  -- `down`, neither of which is sensitive to the result universe.
  let recVal ← forallBoundedTelescope installedRecTy (some (np + 1 + nc + 1)) fun bs _ => do
    let motive := bs[np]!
    let major := bs[bs.size - 1]!
    let params := bs.extract 0 np
    mkLambdaFVars bs
      (← emptyAtElim eqi v w (mkApp motive major) (← site.eDrop params major))
  let dRec := Declaration.defnDecl
    { name := recN, levelParams := rv.levelParams, type := publicRecTy, value := recVal
      hints := ← hintsFor recVal, safety := .safe }
  addChecked dRec
  out := out.push dRec
  let projectionOverrides := st.projectionOverrides ++ (← eStoredFieldOverrides site)
  return { st with out, spliced, projectionOverrides }

end InductiveModels
