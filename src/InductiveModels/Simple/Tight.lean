import InductiveModels.Simple.Plan

open Lean Meta

namespace InductiveModels

/-! ## Tight dependent-pair storage

A maybe-`Prop` family with two or more data fields cannot use the Church route:
at a positive universe instantiation that route remembers only inhabitation,
so intrinsic projections could not satisfy their constructor rules.  A
right-nested `PSigma'` retains the fields at the exact maximum of their
universes.  Its named, projection-derived `rec'` is deliberately used rather
than the kernel's small recursor, so the storage interface itself has no
elimination-universe restriction.

### What the tower ends in, and the level gap the end closes

With **no pad** the tower ends at its last field, so it lands at
`Sort (max ℓ⃗)` and models only a carrier whose own sort the fields' levels
already reach.  A field at `Sort u` under a carrier at `Sort (max u v)` is the
shape that misses: the kernel admitted the declaration by `is_geq(max u v, u)`,
but conversion on levels is normal-form equality and `u` is not `max u v`.

With a **pad** the tower ends at [`InductiveModels.unitAt`] `w` instead — the
derived exact-sort lift of `⊤`, `PSigma'.{0,w} ⊤ (fun _ => PUnit.{w})`, which
is at `Sort (max 0 w) = Sort w` for a **bare, maybe-zero** `w` exactly as for a
never-zero one.  The tower then lands at `Sort (max ℓ⃗ w)`, and `max ℓᵢ w ≡ w`
is precisely the kernel's own `is_geq` on the input re-asked as a conversion.
This is the never-zero tuple tower's pad ([`InductiveModels.padsAt`]) at the
one sort it had never been taken to, and it costs nothing beyond the tail: the
lift's inhabitant is *definitionally* canonical (tight-pair and `PUnit`
structure eta, proof irrelevance on `⊤`), so `mk (proj⃗ t) ≡ t` still holds,
the recursor still discards the pad by ι alone, and every rule is `Eq.refl`.

A padded tower exists at every field count, including one, where an unpadded
tower is the bare field type. -/

/-- **Which stored fields a later field's type mentions**, read off the
constructor's `Π`-nest before anything is built.

`tele` is the field telescope with the owner's parameters already substituted,
so inside its `j`th domain the preceding fields are exactly the loose bound
variables and field `i` is `bvar (j - 1 - i)`. `looseBVarRange` bounds how far a
domain reaches — a header field on `Expr` rather than a traversal — so a field
type that mentions nothing costs one comparison, and `hasLooseBVar` decides the
rest exactly, with the same bound as its own early-out.

**Answered from de Bruijn indices and not from free variables** because the
answer is a property of the telescope and not of any one entry into it: the
carrier, the constructor, the recursor and the projections each open the same
`Π`-nest into a fresh set of `fvar`s, and re-deriving the mask at each would be
four traversals of the field types for one fact about their shape.

A `tele` with fewer than `nf` leading binders is a caller fault rather than a
shape this can answer; it reports every field as depended upon, which is the
unconditional abstraction this mask exists to skip, so a fault costs
instructions and never a different term. -/
def tightFieldDepMask (tele : Expr) (nf : Nat) : Array Bool := Id.run do
  let allDependent := (Array.range nf).map fun _ => true
  let mut fieldTypes : Array Expr := #[]
  let mut current := tele
  for _ in [0:nf] do
    let .forallE _ domain body _ := current | return allDependent
    fieldTypes := fieldTypes.push domain
    current := body
  let mut dep := (Array.range nf).map fun _ => false
  for j in [0:nf] do
    let fieldType := fieldTypes[j]!
    for k in [0:min fieldType.looseBVarRange j] do
      if fieldType.hasLooseBVar k then dep := dep.set! (j - 1 - k) true
  return dep

/-- **One owner's storage tower**: the fields it stores, which of them a later
field's type mentions, and where it ends.  `fields` and `dep` are index-aligned;
`fields` are the free variables of whichever telescope the tower is being built
in, and `dep` is [`InductiveModels.tightFieldDepMask`] of that telescope. -/
structure TightTower where
  /-- The constructor's stored fields, as free variables. -/
  fields : Array Expr
  /-- `dep[i]` — does any **later** field's type mention field `i`? -/
  dep : Array Bool
  /-- The tail: `none` where the tower ends at its last field, `some w` where it
  ends at the pad [`InductiveModels.unitAt`] `w`. -/
  pad? : Option Level := none

/-- The tower over an opened field telescope.  `tele` must be the very `Π`-nest
`fields` was opened from, so that the mask's indices are the fields' own. -/
def tightTowerOf (tele : Expr) (fields : Array Expr) (pad? : Option Level) : TightTower :=
  { fields, dep := tightFieldDepMask tele fields.size, pad? }

/-- Has the tower reached its tail?  A padded tower runs past its last field
and ends at the pad; an unpadded one ends *at* its last field. -/
def tightTowerDone (tower : TightTower) (i : Nat) : Bool :=
  if tower.pad?.isSome then i == tower.fields.size else i + 1 == tower.fields.size

/-- The type the tower ends in: the pad, or the last field's own type. -/
def tightTowerTail (tower : TightTower) (i : Nat) : GenM Expr :=
  match tower.pad? with
  | some w => pure (unitAt w)
  | none => ityp tower.fields[i]!

/-- **The rung's family, where the tail does not mention the field.**

`mkLambdaFVars #[f] rest` abstracts `f` out of `rest` — a full traversal of
everything above this rung — and then binds it at `f`'s own name, binder info
and (head-beta-reduced) type.  Where no later field's type mentions `f` there is
nothing in `rest` to abstract, so the binding is written directly and the
traversal is skipped.  The term is the one `mkLambdaFVars` would have returned,
to the byte: `Lean.MetavarContext.mkBinding` binds a `cdecl` at
`mkLambda' userName binderInfo type.headBeta`, and `abstractRange` over a
variable that does not occur is the identity. -/
def tightConstantFamily (field α body : Expr) (binderInfo : BinderInfo) : GenM Expr :=
  return .lam (← field.fvarId!.getUserName) α.headBeta body binderInfo

partial def tightTowerTy (tower : TightTower) (i : Nat) : GenM Expr := do
  if tightTowerDone tower i then return ← tightTowerTail tower i
  let field := tower.fields[i]!
  let α ← ityp field
  let u ← ilevel α
  let rest ← tightTowerTy tower (i + 1)
  let v ← ilevel rest
  let β ← if tower.dep[i]! then mkLambdaFVars #[field] rest
    else tightConstantFamily field α rest (← field.fvarId!.getBinderInfo)
  return mkAppN (.const `PSigma' [u, v]) #[α, β]

def tightTowerAt (tower : TightTower) (i : Nat) (pre : Array Expr) :
    GenM (Level × Level × Expr × Expr) := do
  let field := tower.fields[i]!
  let substitute := fun (expression : Expr) =>
    expression.replaceFVars (tower.fields.extract 0 pre.size) pre
  let α := substitute (← ityp field)
  let u ← ilevel α
  let rest ← tightTowerTy tower (i + 1)
  -- The tail does not mention this field, so the binder it would be abstracted
  -- under holds nothing: substituting `pre` for the fields *before* it is the
  -- whole of the substitution, and the family is constant.
  unless tower.dep[i]! do
    let rest := substitute rest
    let v ← ilevel rest
    return (u, v, α, ← tightConstantFamily field α rest .default)
  let (v, β) ← withLocalDeclD (← field.fvarId!.getUserName) α fun value => do
    let rest := rest.replaceFVars
      (tower.fields.extract 0 (pre.size + 1)) (pre.push value)
    let v ← ilevel rest
    return (v, ← mkLambdaFVars #[value] rest)
  return (u, v, α, β)

partial def tightTowerMk (tower : TightTower) (i : Nat) : GenM Expr := do
  if tightTowerDone tower i then
    return match tower.pad? with
      | some w => unitAtCanon w
      | none => tower.fields[i]!
  let pre := tower.fields.extract 0 i
  let (u, v, α, β) ← tightTowerAt tower i pre
  return mkAppN (.const `PSigma'.mk [u, v])
    #[α, β, tower.fields[i]!, ← tightTowerMk tower (i + 1)]

/-- **The tower read out**, one primitive projection pair per rung.

**It builds no types.** A primitive `.proj` carries the structure's name and a
field index and nothing else — not the rung's `α`, not its `β`, not either
level — so walking the tower to its `i`th field needs only the shape the
recursion already has. This used to call [`InductiveModels.tightTowerAt`] at
every rung and discard all four of its results, a vestige of the day the
projections were `PSigma'.fst`/`.snd` *applications* and did need `α` and `β`
spelled out. It was measured at 81% of this function's cost.

Nor was it a well-formedness assertion standing in for one: every rung it
rebuilt is rebuilt for real, at the same fields and the same `pad?`, by
[`InductiveModels.tightTowerTy`] for the carrier and by
[`InductiveModels.tightTowerAt`] under [`InductiveModels.tightTowerMk`] for the
constructor, both of which run **before** the projections on both routes that
reach here. Any shape this could have rejected is rejected there first, with
the same message. -/
partial def tightTowerProjs (tower : TightTower) (i : Nat) (value : Expr)
    (pre : Array Expr := #[]) : Array Expr :=
  if tightTowerDone tower i then
    (if tower.pad?.isSome then pre else pre.push value)
  else
    let first := .proj `PSigma' 0 value
    tightTowerProjs tower (i + 1) (.proj `PSigma' 1 value) (pre.push first)

partial def tightTowerPrepend (tower : TightTower) (pre : Array Expr) (i : Nat)
    (tail : Expr) : GenM Expr := do
  if i == pre.size then return tail
  let (u, v, α, β) ← tightTowerAt tower i (pre.extract 0 i)
  return mkAppN (.const `PSigma'.mk [u, v])
    #[α, β, pre[i]!, ← tightTowerPrepend tower pre (i + 1) tail]

/-- **The tower taken apart**, one `PSigma'.rec'` per stored field.

At a padded tower the last call arrives with every field already bound and the
pad in hand; the minor premise is applied to the fields alone and the pad is
dropped.  That is well typed and not a coincidence: the branch owes
`motive ⟨f⃗, t⟩` for the bound pad `t`, the minor delivers
`motive ⟨f⃗, canon⟩`, and `t ≡ canon` is a conversion the kernel performs —
tight-pair and `PUnit` structure eta expand `t` against the literal pair
`canon` is, and proof irrelevance closes its `⊤` component.  No transport
rides along and the recursor's ι rule stays `Eq.refl`. -/
partial def tightTowerRec (s : Level) (tower : TightTower) (motive minor value : Expr)
    (i : Nat := 0) (pre : Array Expr := #[]) : GenM Expr := do
  if tightTowerDone tower i then
    return mkAppN minor (if tower.pad?.isSome then pre else pre.push value)
  let (u, v, α, β) ← tightTowerAt tower i pre
  let tailType := mkAppN (.const `PSigma' [u, v]) #[α, β]
  let targetMotive ← withLocalDeclD `tail tailType fun tail => do
    let full ← tightTowerPrepend tower pre 0 tail
    mkLambdaFVars #[tail] (mkApp motive full)
  let branch ← withLocalDeclD `fst α fun fst =>
    withLocalDeclD `snd (mkApp β fst).headBeta fun snd => do
      mkLambdaFVars #[fst, snd]
        (← tightTowerRec s tower motive minor snd (i + 1) (pre.push fst))
  return mkAppN (.const `PSigma'.rec' [u, v, s])
    #[α, β, targetMotive, branch, value]

/-- Emit an exact-sort model for a non-recursive, unindexed, one-constructor
family, storing its fields in the tower.  `pad?` is that tower's tail: `none`
where the fields' own levels already reach the carrier's sort, `some w` where
the pad is what takes them there. -/
def directTightModel (eqi : EqInfo) (tname : Name) (lparams : List Name) (np : Nat)
    (memberTy constructorType modelConstructorType declaredMemberTy : Expr)
    (selfN constructorN recursorN : Name) (recursorLevelParams : List Name)
    (recursorProofType recursorPublicType : Expr) (v : Level) (pad? : Option Level) :
    GenM (Array Declaration × Array (Name × Nat × Expr × Expr)) := do
  let us := lparams.map Level.param
  let nf := numForalls constructorType - np
  let withParams := fun {α : Type} (k : Array Expr → GenM α) =>
    forallBoundedTelescope memberTy (some np) fun ps _ => k ps
  let selfAt := fun (ps : Array Expr) => mkAppN (.const selfN us) ps
  let mut declarations : Array Declaration := #[]

  let selfValue ← withParams fun ps => do
    let tele ← instForall constructorType ps
    forallBoundedTelescope tele (some nf) fun fields _ => do
      mkLambdaFVars ps (← tightTowerTy (tightTowerOf tele fields pad?) 0)
  let selfDecl := Declaration.defnDecl
    { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfValue
      hints := ← hintsFor selfValue, safety := .safe }
  addChecked selfDecl
  declarations := declarations.push selfDecl

  let constructorValue ← withParams fun ps => do
    let tele ← instForall modelConstructorType ps
    forallBoundedTelescope tele (some nf) fun fields _ => do
      mkLambdaFVars (ps ++ fields) (← tightTowerMk (tightTowerOf tele fields pad?) 0)
  let constructorDecl := Declaration.defnDecl
    { name := constructorN, levelParams := lparams, type := modelConstructorType,
      value := constructorValue, hints := ← hintsFor constructorValue, safety := .safe }
  addChecked constructorDecl
  declarations := declarations.push constructorDecl

  let recursorValue ← forallBoundedTelescope recursorProofType
      (some (np + 3)) fun binders _ => do
    let motive := binders[np]!
    let minor := binders[np + 1]!
    let self := binders[binders.size - 1]!
    let ps := binders.extract 0 np
    let tele ← instForall constructorType ps
    forallBoundedTelescope tele (some nf) fun fields _ => do
      mkLambdaFVars binders
        (← tightTowerRec v (tightTowerOf tele fields pad?) motive minor self)
  let recursorDecl := Declaration.defnDecl
    { name := recursorN, levelParams := recursorLevelParams, type := recursorPublicType,
      value := recursorValue, hints := ← hintsFor recursorValue, safety := .safe }
  addChecked recursorDecl
  declarations := declarations.push recursorDecl

  let overrides ← withParams fun ps => do
    let tele ← instForall constructorType ps
    forallBoundedTelescope tele (some nf) fun fields _ => do
      withLocalDeclD `self (selfAt ps) fun self => do
        let projections := tightTowerProjs (tightTowerOf tele fields pad?) 0 self
        (Array.range nf).mapM fun fieldIndex => do
          let selector ← mkLambdaFVars (ps.push self) projections[fieldIndex]!
          let proof ← do
            let proofTele ← instForall constructorType ps
            forallBoundedTelescope proofTele (some nf) fun constructorFields _ => do
              let selected := constructorFields[fieldIndex]!
              let fieldType ← inferType selected
              let fieldLevel ← ilevel fieldType
              mkLambdaFVars (ps ++ constructorFields)
                (eqi.refl' fieldLevel fieldType selected)
          return (tname, fieldIndex, selector, proof)
  return (declarations, overrides)

/-- Emit an exact-sort model for a non-recursive **indexed** one-constructor
family: the same storage as [`InductiveModels.directTightModel`], in the same
tower, with the conclusion's index telescope discharged by one packed equation.

    T p⃗ ι⃗ := Σ'(t : Store p⃗), pack ι⃗_ctor(proj⃗ t) = pack ι⃗

`Store` is [`InductiveModels.tightTowerTy`] over the constructor's fields — at
one field and no pad that *is* the field's type, so this is `.identity`'s
carrier and the `tight` tower written by one function — and a **definition**
rather than a spliced inductive. The equation is stated once at the whole index
telescope packed into a `PSigma'`, because a later index's type may mention an
earlier one; it is the same Henry-Ford equation arm F discharges its non-pivot
indices with, which is why the two are the storage half and the substitution
half of one axis rather than two ideas.

**Why the pair is at exactly the carrier's sort.** The tower lands at
`max ℓ⃗` unpadded and at `max ℓ⃗ w` padded, and the route guard has already
equated whichever one it plans with `w`
([`InductiveModels.planDirectIndexedRoute`]); the equation is a `Prop`, so the
pair is at `max w 0` — literally `w` after normalization. The pad is inside
the storage and never around it, which is why an index costs the plan nothing.

**Why every rule reduces.** `proj⃗` and the tower are `PSigma'` projections and
a `PSigma'.mk`, so `proj⃗ (mk f⃗) ≡ f⃗` by ι and `mk (proj⃗ t) ≡ t` by structure
eta; the stored equation at the constructor is `Eq.refl`, so the recursor's one
`Eq.rec` fires by its own ι rule and the recursor ι theorem is `Eq.refl`; and
the second component is a proof, so the rebuilt pair and the caller's are one
term by proof irrelevance. `pack (unpack y) ≡ y` is what lets the transport's
motive be stated about a packed variable and still apply to the declaration's
own index telescope.

**Why the intrinsic projections are the storage's own**, as on every direct
route. The model recursor here has the recursor the kernel minted, which for
this shape is `Prop`-valued: the constructor has a data field that is not a
conclusion index, so the kernel's subsingleton rule grants no large eliminator,
and a projection built through that recursor could not be stated. The selector
is the tower's projection instead, which selects definitionally, and each rule
is `Eq.refl` at the constructor's own field binder. -/
def directIndexedModel (eqi : EqInfo) (tname : Name) (lparams : List Name) (np ni : Nat)
    (constructorName : Name)
    (memberTy constructorType modelConstructorType declaredMemberTy : Expr)
    (selfN constructorN recursorN : Name) (recursorLevelParams : List Name)
    (recursorProofType recursorPublicType : Expr) (w v : Level) (pad? : Option Level) :
    GenM (Array Declaration × Array (Name × Nat × Expr × Expr)) := do
  let us := lparams.map Level.param
  let nf := numForalls constructorType - np
  let withParams := fun {α : Type} (k : Array Expr → GenM α) =>
    forallBoundedTelescope memberTy (some np) fun ps _ => k ps
  let mut declarations : Array Declaration := #[]

  -- **The storage, its projections and its introduction**, at a parameter
  -- scope. One tower serves every field count: at one field it *is* that
  -- field's type and its sole projection is the value itself, which is the
  -- unindexed `.identity` route's carrier written by the same function.
  let storeAt : Array Expr → GenM Expr := fun ps => do
    let tele ← instForall constructorType ps
    forallBoundedTelescope tele (some nf) fun fields _ =>
      tightTowerTy (tightTowerOf tele fields pad?) 0
  let projsAt : Array Expr → Expr → GenM (Array Expr) := fun ps value => do
    let tele ← instForall constructorType ps
    forallBoundedTelescope tele (some nf) fun fields _ =>
      pure (tightTowerProjs (tightTowerOf tele fields pad?) 0 value)
  -- Takes the `Π`-nest its fields were opened from rather than the parameters,
  -- because the tower's dependency mask is read off that nest.
  let towerOf : Expr → Array Expr → GenM Expr := fun tele fs =>
    tightTowerMk (tightTowerOf tele fs pad?) 0

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
    let res ← instForall (← instForall constructorType ps) vs
    let some args ← ownerAppArgs? tname np ni res
      | badShape s!"{constructorName} does not end in {tname} at {np} parameters and \
{ni} indices"
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
  let selfValue ← withParams fun ps => do
    let store ← storeAt ps
    let (pk, ℓpk) ← pkAt ps
    forallBoundedTelescope (← instForall memberTy ps) (some ni) fun is _ => do
      let packedIs ← packChain ni pk is 0
      let fibre ← fibreAt ps store pk ℓpk packedIs
      mkLambdaFVars (ps ++ is) (psigmaT w .zero store fibre)
  let selfDecl := Declaration.defnDecl
    { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfValue
      hints := ← hintsFor selfValue, safety := .safe }
  addChecked selfDecl
  declarations := declarations.push selfDecl

  -- ── the constructor ──
  -- Its own index vector is `ι⃗_ctor` at its own fields, and the storage's
  -- projections reduce to those fields, so the stored equation is `Eq.refl`.
  let constructorValue ← withParams fun ps => do
    let store ← storeAt ps
    let (pk, ℓpk) ← pkAt ps
    let tele ← instForall modelConstructorType ps
    forallBoundedTelescope tele (some nf) fun fields _ => do
      let packedC ← packChain ni pk (← idxOfVals ps fields) 0
      let fibre ← fibreAt ps store pk ℓpk packedC
      mkLambdaFVars (ps ++ fields)
        (psigmaMk w .zero store fibre (← towerOf tele fields) (eqi.refl' ℓpk pk packedC))
  let constructorDecl := Declaration.defnDecl
    { name := constructorN, levelParams := lparams, type := modelConstructorType,
      value := constructorValue, hints := ← hintsFor constructorValue, safety := .safe }
  addChecked constructorDecl
  declarations := declarations.push constructorDecl

  -- ── the recursor ──
  -- Take the pair apart, recover the fields from the storage, apply the minor
  -- at them, and move the result from the constructor's index vector to the
  -- caller's along the stored equation. The motive rebuilds a carrier element
  -- at each packed point; at the equation's own endpoint that element and the
  -- caller's major are one term by structure eta and proof irrelevance. The
  -- telescope is the unindexed route's `np + 3` — parameters, motive, the one
  -- minor, the major — with the caller's `ni` indices in front of the major.
  let recursorValue ← forallBoundedTelescope recursorProofType
      (some (np + 3 + ni)) fun binders _ => do
    let ps := binders.extract 0 np
    let motive := binders[np]!
    let minor := binders[np + 1]!
    let idxs := binders.extract (np + 2) (np + 2 + ni)
    let self := binders[binders.size - 1]!
    let store ← storeAt ps
    let (pk, ℓpk) ← pkAt ps
    let packedIs ← packChain ni pk idxs 0
    let fibre ← fibreAt ps store pk ℓpk packedIs
    let stored := psigmaFst w .zero store fibre self
    let heq := psigmaSnd w .zero store fibre self
    let fields ← projsAt ps stored
    let packedC ← packChain ni pk (← idxOfVals ps fields) 0
    let motiveE ← withLocalDeclD `y pk fun y => do
      withLocalDeclD `hy (eqi.mk' ℓpk pk packedC y) fun hy => do
        let ys ← unpackChain ni pk y
        let fibreY ← fibreAt ps store pk ℓpk y
        mkLambdaFVars #[y, hy]
          (mkAppN motive (ys.push (psigmaMk w .zero store fibreY stored hy)))
    mkLambdaFVars binders
      (eqi.recAt v ℓpk pk packedC motiveE (mkAppN minor fields) packedIs heq)
  let recursorDecl := Declaration.defnDecl
    { name := recursorN, levelParams := recursorLevelParams, type := recursorPublicType,
      value := recursorValue, hints := ← hintsFor recursorValue, safety := .safe }
  addChecked recursorDecl
  declarations := declarations.push recursorDecl

  -- ── the intrinsic projections ──
  let overrides ← withParams fun ps => do
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
            let proofTele ← instForall constructorType ps
            forallBoundedTelescope proofTele (some nf) fun constructorFields _ => do
              let selected := constructorFields[fieldIndex]!
              let fieldType ← inferType selected
              let fieldLevel ← ilevel fieldType
              mkLambdaFVars (ps ++ constructorFields)
                (eqi.refl' fieldLevel fieldType selected)
          return (tname, fieldIndex, selector, proof)
  return (declarations, overrides)

/-- **Where must the tower end so that it lands on the carrier's sort?** — the
one level question both unindexed and indexed direct storage asks, asked once.

The answer is a *pad*, and there are exactly two of them because there are
exactly two shapes of answer:

* **`none`** — the fields' own levels already reach the carrier's,
  `max ℓ⃗ ≡ w`, and the tower ends at its last field. Every model this route
  built before a pad existed is this answer, unchanged.
* **`some w`** — they do not, but `max ℓ⃗ w ≡ w` does, and the tower ends at
  [`InductiveModels.unitAt`] `w`. That equation is Lean's own `is_geq(w, ℓᵢ)`
  on the input re-asked as a *conversion*, and the pad exists at a maybe-zero
  `w` for the same reason arm E's `emptyAt` does: the derived exact-sort lift
  is `PSigma'.{0,w}` of a proposition, so `max 0 w` is `w` for a bare `w`
  exactly as for a never-zero one.

**Stock `isLevelDefEq`, deliberately**, exactly as
[`InductiveModels.wTowerLevel`] and for the same reason.
[`InductiveModels.LevelAlgebra.isLevelDefEqComplete`] is strictly stronger and
the extra strength is *useless* here rather than merely unused: the tower is a
term whose type the kernel must accept against `Sort w`, and the kernel decides
that by normal-form equality (`level.cpp:518-520`). Admitting a plan the
elaborator refuses would not widen coverage, it would turn a decline into a
kernel rejection at `addChecked`. So no widening is reachable from this
question and none is counted.

**What is left is `outOfScope` and no longer `incomplete`.** With the pad in
place, `max ℓ⃗ w ≢ w` says a field's level retains an `imax` that a `max`-shaped
`w` does not absorb, and at a **maybe-zero** carrier that is closed on both
sides at once. Conversion will not equate them, which is the documented
`max`-does-not-absorb-`imax` gap and a property of Lean's conversion rather
than of our normaliser. And the recursive box that removes an `imax` elsewhere
([`InductiveModels.boxTyOf`]) cannot be used, because every boxed level carries
a `max 1 ·` floor and no `max 1 ·` is ever a maybe-zero `w` — at `w := 0` the
carrier is `Prop` and a boxed field is not a proof. There is no third pad to
build: any pad that raised the tower above `Sort 0` would miss `Prop`, and any
that did not would not absorb the `imax`. That is a stated boundary and not an
unfinished arm. -/
def planTightTower (tname constructorName : Name) (fieldLevels : Array Level) (w : Level)
    (what : String) : GenM (Option Level) := do
  let raw :=
    if fieldLevels.size == 1 then fieldLevels[0]!
    else (fieldLevels.foldl mkLevelMax' .zero).normalize
  if ← isLevelDefEq raw w then return none
  let padded := (mkLevelMax' raw w).normalize
  if ← isLevelDefEq padded w then return some w
  declineWith (.shapeUnsupported tname .outOfScope
    s!"{constructorName}'s {what} reaches Sort {raw} and pads to Sort {padded} while the \
carrier inhabits Sort {w}, so neither the bare tower nor the exact-sort pad lands on the \
declared sort; the level retains an imax a max-shaped carrier does not absorb, and at a \
maybe-zero sort no box closes it either, since every boxed level carries a max 1 floor \
and no max 1 is Prop")

/-- Decide whether the exact-sort unindexed storage route applies, and settle
its tower's pad before any support is installed. Kept outside
[`InductiveModels.primIso`] so the route dispatcher does not elaborate this
telescope walk as another large inline branch.

`none` is *the route does not apply*; `some pad?` is *it does, with this tail*.
The two are not the same answer and the caller may not collapse them: a route
that does not apply leaves the owner to the next one, and a route that applies
with a pad is the model.

**Any field count, including one.** The guard used to be `>= 2`, with the
one-field shapes belonging to [`InductiveModels.directFieldModel`]'s two exact
answers. Those two still run first and are still byte for byte what they were;
what changed is that a one-field owner they *both* refuse now reaches this
tower with a pad instead of a decline, because a one-field padded tower —
`Σ'(f : F), unitAt w` — is a tower like any other and the storage, its
projection and its rule are the ones this file already writes. -/
def planDirectTightRoute (tname : Name) (eligible : Bool) (np : Nat)
    (memberTy : Expr) (exportCtors : Array (Name × Expr)) (w : Level) :
    GenM (Option (Option Level)) := do
  unless eligible do return none
  let (constructorName, constructorType) := exportCtors[0]!
  unless numForalls constructorType - np >= 1 do return none
  forallBoundedTelescope memberTy (some np) fun ps _ => do
    let tele ← instForall constructorType ps
    let nf := numForalls tele
    forallBoundedTelescope tele (some nf) fun fields _ => do
      let fieldLevels ← fields.mapM fun field => do ilevel (← ityp field)
      return some (← planTightTower tname constructorName fieldLevels w "tight field tower")

/-- **Can an indexed one-constructor owner's fields be stored at the carrier's
exact sort?** — the question that decides the direct routes' *indexed* case,
and the one piece of it that must be settled before anything is spliced.

**Why this is a case of the direct routes and not an arm beside them.** The
storage is [`InductiveModels.tightTowerTy`], the very tower
[`InductiveModels.planDirectTightRoute`] admits, asked of the very same fields;
what the index telescope adds is a `Prop`-valued equation saying which fibre
that storage sits in, and a `Prop` changes no level. So the question the two
guards ask is one question — *does the tower land on `Sort w`?* — and the
answer settles both. Keeping the indexed case as a separate construction would
have been two copies of that question, free to drift apart, and would have hid
that the direct guard's `ni == 0` was a narrowness rather than a boundary.

The tower's level is the max of the field levels at any field count, plus the
pad's own `w` where a pad is planned. Wrapping it in the index equation adds
nothing to that level (`max ℓ 0` is `ℓ`), so the whole carrier lands at exactly
`Sort w` precisely when the tower does.

**A tower that misses the carrier's sort is the same answer
[`InductiveModels.planTightTower`] gives everywhere else**, and for the same
reason: the case is reached only after arm F has been ruled out, which means
the constructor has a data field the conclusion's index vector does not carry,
so the model must store it and the Church encoding underneath — which remembers
only inhabitation — cannot. The pad is what takes that storage to the declared
sort, and where even the pad misses, the boundary is stated rather than
recorded as an unfinished arm. Settled before anything is spliced, so the owner
passes through unchanged.

Zero fields is a different answer: every non-proof field is then vacuously one
of the conclusion's indices, so the kernel minted the large eliminator and arm
F fired. Reaching this with no fields is a route-classification fault. -/
def planDirectIndexedRoute (tname : Name) (eligible : Bool) (np : Nat) (memberTy : Expr)
    (exportCtors : Array (Name × Expr)) (w : Level) : GenM (Option (Option Level)) := do
  unless eligible do return none
  let (constructorName, constructorType) := exportCtors[0]!
  let nf := numForalls constructorType - np
  unless nf >= 1 do
    badShape s!"internal: {constructorName} has no fields, so every non-proof field of \
{tname} is vacuously one of the conclusion's indices and arm F, not the direct routes' \
indexed case, is the one that models it"
  forallBoundedTelescope memberTy (some np) fun ps _ => do
    let tele ← instForall constructorType ps
    forallBoundedTelescope tele (some nf) fun fields _ => do
      let fieldLevels ← fields.mapM fun field => do ilevel (← ityp field)
      return some (← planTightTower tname constructorName fieldLevels w "field tower")

/-- Install tight-pair support and emit the complete exact-sort model branch.
The caller only merges the returned declarations, splice witnesses, and
projection overrides into its route state. -/
def emitDirectTightModel (eqi : EqInfo) (tname : Name) (lparams : List Name) (np : Nat)
    (memberTy constructorType modelConstructorType declaredMemberTy : Expr)
    (selfN constructorN recursorN : Name) (recursorLevelParams : List Name)
    (recursorProofType recursorPublicType : Expr) (v : Level) (pad? : Option Level) :
    GenM (Array Declaration × Array Name × Array (Name × Nat × Expr × Expr)) := do
  let support ← if pad?.isSome then ensureExactSortLift else ensurePSigmaPrime
  let (declarations, overrides) ← directTightModel eqi tname lparams np memberTy
    constructorType modelConstructorType declaredMemberTy selfN constructorN recursorN
    recursorLevelParams recursorProofType recursorPublicType v pad?
  let spliced := support.flatMap fun declaration => declaration.getNames.toArray
  return (support ++ declarations, spliced, overrides)

/-- Install tight-pair support and emit the indexed exact-sort model branch.
The same support as the unindexed tower — the storage is that tower — plus the
`PSigma'` the index equation's own pair is built from, which is the same
record. A padded tower additionally ends at the derived exact-sort lift, whose
`PUnit` is the one further constant either branch splices. -/
def emitDirectIndexedModel (eqi : EqInfo) (tname : Name) (lparams : List Name)
    (np ni : Nat) (constructorName : Name)
    (memberTy constructorType modelConstructorType declaredMemberTy : Expr)
    (selfN constructorN recursorN : Name) (recursorLevelParams : List Name)
    (recursorProofType recursorPublicType : Expr) (w v : Level) (pad? : Option Level) :
    GenM (Array Declaration × Array Name × Array (Name × Nat × Expr × Expr)) := do
  let support ← if pad?.isSome then ensureExactSortLift else ensurePSigmaPrime
  let (declarations, overrides) ← directIndexedModel eqi tname lparams np ni constructorName
    memberTy constructorType modelConstructorType declaredMemberTy selfN constructorN
    recursorN recursorLevelParams recursorProofType recursorPublicType w v pad?
  let spliced := support.flatMap fun declaration => declaration.getNames.toArray
  return (support ++ declarations, spliced, overrides)

/-- Emit the field-preserving implementation of a tight one-field model.
Kept outside [`InductiveModels.primIso`] so the already-large route dispatcher does
not pay to elaborate both the identity and proposition-lift implementations. -/
def directFieldModel (route : DirectFieldRoute) (eqi : EqInfo) (tname : Name)
    (lparams : List Name) (np : Nat) (memberTy constructorType modelConstructorType : Expr)
    (declaredMemberTy : Expr)
    (selfN constructorN recursorN : Name) (recursorLevelParams : List Name)
    (recursorProofType recursorPublicType : Expr) (w v : Level) :
    GenM (Array Declaration × (Name × Nat × Expr × Expr)) := do
  let us := lparams.map Level.param
  let withParams := fun {α : Type} (k : Array Expr → GenM α) =>
    forallBoundedTelescope memberTy (some np) fun ps _ => k ps
  let fieldTypeAt := fun (ps : Array Expr) => do
    let tele ← instForall constructorType ps
    let .forallE _ fieldType _ _ := tele
      | badShape s!"{constructorN} is not a one-field constructor"
    pure fieldType
  let selfAt := fun (ps : Array Expr) => mkAppN (.const selfN us) ps
  let mut declarations : Array Declaration := #[]

  let selfValue ← withParams fun ps => do
    let fieldType ← fieldTypeAt ps
    mkLambdaFVars ps <| match route with
      | .identity => fieldType
      | .propLift => puliftT w fieldType
  let selfDecl := Declaration.defnDecl
    { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfValue
      hints := ← hintsFor selfValue, safety := .safe }
  addChecked selfDecl
  declarations := declarations.push selfDecl

  let constructorValue ← withParams fun ps => do
    let tele ← instForall modelConstructorType ps
    forallBoundedTelescope tele (some 1) fun fields _ => do
      let field := fields[0]!
      let value ← match route with
        | .identity => pure field
        | .propLift => do pure (puliftUp w (← inferType field) field)
      mkLambdaFVars (ps ++ fields) value
  let constructorDecl := Declaration.defnDecl
    { name := constructorN, levelParams := lparams, type := modelConstructorType,
      value := constructorValue, hints := ← hintsFor constructorValue, safety := .safe }
  addChecked constructorDecl
  declarations := declarations.push constructorDecl

  let recursorValue ← forallBoundedTelescope recursorProofType
      (some (np + 3)) fun binders _ => do
    let ps := binders.extract 0 np
    let motive := binders[np]!
    let minor := binders[np + 1]!
    let self := binders[binders.size - 1]!
    let value ← match route with
      | .identity => pure (mkApp minor self)
      | .propLift => do pure (puliftRec v w (← fieldTypeAt ps) motive minor self)
    mkLambdaFVars binders value
  let recursorDecl := Declaration.defnDecl
    { name := recursorN, levelParams := recursorLevelParams, type := recursorPublicType,
      value := recursorValue, hints := ← hintsFor recursorValue, safety := .safe }
  addChecked recursorDecl
  declarations := declarations.push recursorDecl

  let selector ← withParams fun ps => withLocalDeclD `self (selfAt ps) fun self => do
    let value ← match route with
      | .identity => pure self
      | .propLift => do pure (puliftDown w (← fieldTypeAt ps) self)
    mkLambdaFVars (ps.push self) value
  let proof ← withParams fun ps => do
    let tele ← instForall modelConstructorType ps
    forallBoundedTelescope tele (some 1) fun fields _ => do
      let field := fields[0]!
      let fieldType ← inferType field
      let fieldLevel ← ilevel fieldType
      mkLambdaFVars (ps ++ fields) (eqi.refl' fieldLevel fieldType field)
  return (declarations, (tname, 0, selector, proof))

/-- Emit any field-preserving direct route, including its exact support
splice. Keeping this case split outside [`InductiveModels.primIso`] leaves the main
dispatcher with one compact direct-model branch. -/
def emitDirectModel (route : DirectRoute) (eqi : EqInfo) (tname : Name)
    (lparams : List Name) (np ni : Nat) (constructorName : Name)
    (memberTy constructorType modelConstructorType declaredMemberTy : Expr)
    (selfN constructorN recursorN : Name) (recursorLevelParams : List Name)
    (recursorProofType recursorPublicType : Expr) (w v : Level) :
    GenM (Array Declaration × Array Name × Array (Name × Nat × Expr × Expr)) := do
  match route with
  | .field fieldRoute =>
    let support ← if fieldRoute matches .propLift then ensureExactSortLift else pure #[]
    let (declarations, override) ← directFieldModel fieldRoute eqi tname lparams np
      memberTy constructorType modelConstructorType declaredMemberTy selfN constructorN
      recursorN recursorLevelParams recursorProofType recursorPublicType w v
    let spliced := support.flatMap fun declaration => declaration.getNames.toArray
    return (support ++ declarations, spliced, #[override])
  | .tight pad? =>
    emitDirectTightModel eqi tname lparams np memberTy constructorType modelConstructorType
      declaredMemberTy selfN constructorN recursorN recursorLevelParams
      recursorProofType recursorPublicType v pad?
  | .indexed pad? =>
    emitDirectIndexedModel eqi tname lparams np ni constructorName memberTy constructorType
      modelConstructorType declaredMemberTy selfN constructorN recursorN recursorLevelParams
      recursorProofType recursorPublicType w v pad?

end InductiveModels
