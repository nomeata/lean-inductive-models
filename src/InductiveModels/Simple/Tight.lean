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
elimination-universe restriction. -/

partial def tightTowerTy (fields : Array Expr) (i : Nat) : GenM Expr := do
  if i + 1 == fields.size then return ← ityp fields[i]!
  let α ← ityp fields[i]!
  let u ← ilevel α
  let rest ← tightTowerTy fields (i + 1)
  let v ← ilevel rest
  let β ← mkLambdaFVars #[fields[i]!] rest
  return mkAppN (.const `PSigma' [u, v]) #[α, β]

def tightTowerAt (fields : Array Expr) (i : Nat) (pre : Array Expr) : GenM
    (Level × Level × Expr × Expr) := do
  let substitute := fun (expression : Expr) =>
    expression.replaceFVars (fields.extract 0 pre.size) pre
  let α := substitute (← ityp fields[i]!)
  let u ← ilevel α
  let rest ← tightTowerTy fields (i + 1)
  let (v, β) ← withLocalDeclD (← fields[i]!.fvarId!.getUserName) α fun value => do
    let rest := rest.replaceFVars
      (fields.extract 0 (pre.size + 1)) (pre.push value)
    let v ← ilevel rest
    return (v, ← mkLambdaFVars #[value] rest)
  return (u, v, α, β)

partial def tightTowerMk (fields : Array Expr) (i : Nat) : GenM Expr := do
  if i + 1 == fields.size then return fields[i]!
  let pre := fields.extract 0 i
  let (u, v, α, β) ← tightTowerAt fields i pre
  return mkAppN (.const `PSigma'.mk [u, v])
    #[α, β, fields[i]!, ← tightTowerMk fields (i + 1)]

partial def tightTowerProjs (fields : Array Expr) (i : Nat) (value : Expr)
    (pre : Array Expr := #[]) : GenM (Array Expr) := do
  if i + 1 == fields.size then return pre.push value
  let (_, _, _, _) ← tightTowerAt fields i pre
  let first := .proj `PSigma' 0 value
  tightTowerProjs fields (i + 1) (.proj `PSigma' 1 value) (pre.push first)

partial def tightTowerPrepend (fields pre : Array Expr) (i : Nat) (tail : Expr) :
    GenM Expr := do
  if i == pre.size then return tail
  let (u, v, α, β) ← tightTowerAt fields i (pre.extract 0 i)
  return mkAppN (.const `PSigma'.mk [u, v])
    #[α, β, pre[i]!, ← tightTowerPrepend fields pre (i + 1) tail]

partial def tightTowerRec (s : Level) (fields : Array Expr) (motive minor value : Expr)
    (i : Nat := 0) (pre : Array Expr := #[]) : GenM Expr := do
  if i + 1 == fields.size then return mkAppN minor (pre.push value)
  let (u, v, α, β) ← tightTowerAt fields i pre
  let tailType := mkAppN (.const `PSigma' [u, v]) #[α, β]
  let targetMotive ← withLocalDeclD `tail tailType fun tail => do
    let full ← tightTowerPrepend fields pre 0 tail
    mkLambdaFVars #[tail] (mkApp motive full)
  let branch ← withLocalDeclD `fst α fun fst =>
    withLocalDeclD `snd (mkApp β fst).headBeta fun snd => do
      mkLambdaFVars #[fst, snd]
        (← tightTowerRec s fields motive minor snd (i + 1) (pre.push fst))
  return mkAppN (.const `PSigma'.rec' [u, v, s])
    #[α, β, targetMotive, branch, value]

/-- Emit an exact-sort model for a non-recursive, unindexed,
one-constructor family with at least two fields. -/
def directTightModel (eqi : EqInfo) (tname : Name) (lparams : List Name) (np : Nat)
    (memberTy constructorType modelConstructorType declaredMemberTy : Expr)
    (selfN constructorN recursorN : Name) (recursorLevelParams : List Name)
    (recursorProofType recursorPublicType : Expr) (v : Level) :
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
      mkLambdaFVars ps (← tightTowerTy fields 0)
  let selfDecl := Declaration.defnDecl
    { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfValue
      hints := ← hintsFor selfValue, safety := .safe }
  addChecked selfDecl
  declarations := declarations.push selfDecl

  let constructorValue ← withParams fun ps => do
    let tele ← instForall modelConstructorType ps
    forallBoundedTelescope tele (some nf) fun fields _ => do
      mkLambdaFVars (ps ++ fields) (← tightTowerMk fields 0)
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
      mkLambdaFVars binders (← tightTowerRec v fields motive minor self)
  let recursorDecl := Declaration.defnDecl
    { name := recursorN, levelParams := recursorLevelParams, type := recursorPublicType,
      value := recursorValue, hints := ← hintsFor recursorValue, safety := .safe }
  addChecked recursorDecl
  declarations := declarations.push recursorDecl

  let overrides ← withParams fun ps => do
    let tele ← instForall constructorType ps
    forallBoundedTelescope tele (some nf) fun fields _ => do
      withLocalDeclD `self (selfAt ps) fun self => do
        let projections ← tightTowerProjs fields 0 self
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
one field that *is* the field's type, so this is `.identity`'s carrier and the
`tight` tower written by one function — and a **definition** rather than a
spliced inductive. The equation is stated once at the whole index telescope
packed into a `PSigma'`, because a later index's type may mention an earlier
one; it is the same Henry-Ford equation arm F discharges its non-pivot indices
with, which is why the two are the storage half and the substitution half of
one axis rather than two ideas.

**Why the pair is at exactly the carrier's sort.** The tower lands at
`max ℓ⃗`, which the route guard has already equated with `w`
([`InductiveModels.planDirectIndexedRoute`]), and the equation is a `Prop`, so
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
    (recursorProofType recursorPublicType : Expr) (w v : Level) :
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
    forallBoundedTelescope tele (some nf) fun fields _ => tightTowerTy fields 0
  let projsAt : Array Expr → Expr → GenM (Array Expr) := fun ps value => do
    let tele ← instForall constructorType ps
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
        (psigmaMk w .zero store fibre (← towerOf ps fields) (eqi.refl' ℓpk pk packedC))
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

/-- Decide whether the exact-sort multi-field route applies, and check its
right-nested tight-pair carrier level before any support is installed. Kept
outside [`InductiveModels.primIso`] so the route dispatcher does not elaborate this
telescope walk as another large inline branch.

A tower that does not land on the carrier's sort is the multi-field half of the
gap the one-field route's own comment describes: the arm has no pad, the owner
reaches no other arm, and the answer is therefore a decline naming the arm
rather than an internal tool error that stops the stream. -/
def planDirectTightRoute (tname : Name) (bare nonrecursiveOneConstructor : Bool) (np ni : Nat)
    (memberTy : Expr) (exportCtors : Array (Name × Expr)) (w : Level) : GenM Bool := do
  unless bare && nonrecursiveOneConstructor && ni == 0 do return false
  let (constructorName, constructorType) := exportCtors[0]!
  unless numForalls constructorType - np >= 2 do return false
  forallBoundedTelescope memberTy (some np) fun ps _ => do
    let tele ← instForall constructorType ps
    let nf := numForalls tele
    forallBoundedTelescope tele (some nf) fun fields _ => do
      let fieldLevels ← fields.mapM fun field => do ilevel (← ityp field)
      let towerLevel := fieldLevels.foldl mkLevelMax' .zero |>.normalize
      unless ← isLevelDefEq towerLevel w do
        declineWith (.shapeUnsupported tname .incomplete
          s!"{constructorName}'s tight field tower inhabits Sort {towerLevel} while the \
carrier inhabits Sort {w}, so the right-nested tight pair does not land on the declared \
sort, and the field-preserving arm at a maybe-zero sort has no pad for the level gap the \
never-zero tuple tower pads")
      return true

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

The tower's level is the max of the field levels at any field count: at one
field the tower *is* that field's type, at two or more the right-nested
`PSigma'` over them. Wrapping it in the index equation adds nothing to that
level (`max ℓ 0` is `ℓ`), so the whole carrier lands at exactly `Sort w`
precisely when the tower does.

**A tower that misses the carrier's sort is `incomplete` and not
`outOfScope`, exactly as [`InductiveModels.planDirectTightRoute`]'s is.** The
case is reached only after arm F has been ruled out, which means the
constructor has a data field the conclusion's index vector does not carry; the
model must therefore store it, and the Church encoding underneath — which
remembers only inhabitation — cannot, so the intrinsic projection every
one-constructor owner is asked for would state an equation the kernel refuses.
Nothing about the shape is out of bounds; the route is short the pad the
never-zero tuple tower has, and the message names both levels. Settled before
anything is spliced, so the owner passes through unchanged.

Zero fields is a different answer: every non-proof field is then vacuously one
of the conclusion's indices, so the kernel minted the large eliminator and arm
F fired. Reaching this with no fields is a route-classification fault. -/
def planDirectIndexedRoute (tname : Name) (eligible : Bool) (np : Nat) (memberTy : Expr)
    (exportCtors : Array (Name × Expr)) (w : Level) : GenM Bool := do
  unless eligible do return false
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
      let towerLevel :=
        if nf == 1 then fieldLevels[0]! else (fieldLevels.foldl mkLevelMax' .zero).normalize
      unless ← isLevelDefEq towerLevel w do
        declineWith (.shapeUnsupported tname .incomplete
          s!"{constructorName}'s field tower inhabits Sort {towerLevel} while the carrier \
inhabits Sort {w}, so the direct routes' indexed case cannot hold the data field the \
conclusion's index vector does not carry, and the maybe-zero route has no pad for the \
level gap the never-zero tuple tower pads")
      return true

/-- Install tight-pair support and emit the complete exact-sort model branch.
The caller only merges the returned declarations, splice witnesses, and
projection overrides into its route state. -/
def emitDirectTightModel (eqi : EqInfo) (tname : Name) (lparams : List Name) (np : Nat)
    (memberTy constructorType modelConstructorType declaredMemberTy : Expr)
    (selfN constructorN recursorN : Name) (recursorLevelParams : List Name)
    (recursorProofType recursorPublicType : Expr) (v : Level) :
    GenM (Array Declaration × Array Name × Array (Name × Nat × Expr × Expr)) := do
  let support ← ensurePSigmaPrime
  let (declarations, overrides) ← directTightModel eqi tname lparams np memberTy
    constructorType modelConstructorType declaredMemberTy selfN constructorN recursorN
    recursorLevelParams recursorProofType recursorPublicType v
  let spliced := support.flatMap fun declaration => declaration.getNames.toArray
  return (support ++ declarations, spliced, overrides)

/-- Install tight-pair support and emit the indexed exact-sort model branch.
The same support as the unindexed tower — the storage is that tower — plus the
`PSigma'` the index equation's own pair is built from, which is the same
record. -/
def emitDirectIndexedModel (eqi : EqInfo) (tname : Name) (lparams : List Name)
    (np ni : Nat) (constructorName : Name)
    (memberTy constructorType modelConstructorType declaredMemberTy : Expr)
    (selfN constructorN recursorN : Name) (recursorLevelParams : List Name)
    (recursorProofType recursorPublicType : Expr) (w v : Level) :
    GenM (Array Declaration × Array Name × Array (Name × Nat × Expr × Expr)) := do
  let support ← ensurePSigmaPrime
  let (declarations, overrides) ← directIndexedModel eqi tname lparams np ni constructorName
    memberTy constructorType modelConstructorType declaredMemberTy selfN constructorN
    recursorN recursorLevelParams recursorProofType recursorPublicType w v
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
  | .tight =>
    emitDirectTightModel eqi tname lparams np memberTy constructorType modelConstructorType
      declaredMemberTy selfN constructorN recursorN recursorLevelParams
      recursorProofType recursorPublicType v
  | .indexed =>
    emitDirectIndexedModel eqi tname lparams np ni constructorName memberTy constructorType
      modelConstructorType declaredMemberTy selfN constructorN recursorN recursorLevelParams
      recursorProofType recursorPublicType w v

end InductiveModels
