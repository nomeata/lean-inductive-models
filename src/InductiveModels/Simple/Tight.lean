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
exact sort?** — the question that decides the stored-index route, and the one
piece of it that must be settled before anything is spliced.

The storage is [`InductiveModels.tightTowerTy`] at any field count: at one
field the tower *is* that field's type, at two or more the right-nested
`PSigma'` over them, and its level is the max of the field levels either way.
Wrapping it in a `Prop`-valued index equation adds nothing to that level
(`max ℓ 0` is `ℓ`), so the whole carrier lands at exactly `Sort w` precisely
when the tower does.

**A tower that misses the carrier's sort is `incomplete` and not
`outOfScope`, exactly as [`InductiveModels.planDirectTightRoute`]'s is.** The
route is reached only after arm F has been ruled out, which means the
constructor has a data field the conclusion's index vector does not carry; the
model must therefore store it, and the Church encoding underneath — which
remembers only inhabitation — cannot, so the intrinsic projection every
one-constructor owner is asked for would state an equation the kernel refuses.
Nothing about the shape is out of bounds; the arm is short the pad the
never-zero tuple tower has, and the message names both levels. Settled before
anything is spliced, so the owner passes through unchanged.

Zero fields is a different answer: every non-proof field is then vacuously one
of the conclusion's indices, so the kernel minted the large eliminator and arm
F fired. Reaching this with no fields is a route-classification fault. -/
def planIndexedStoreRoute (tname : Name) (eligible : Bool) (np : Nat) (memberTy : Expr)
    (exportCtors : Array (Name × Expr)) (w : Level) : GenM Bool := do
  unless eligible do return false
  let (constructorName, constructorType) := exportCtors[0]!
  let nf := numForalls constructorType - np
  unless nf >= 1 do
    badShape s!"internal: {constructorName} has no fields, so every non-proof field of \
{tname} is vacuously one of the conclusion's indices and arm F, not the stored-index \
route, is the one that models it"
  forallBoundedTelescope memberTy (some np) fun ps _ => do
    let tele ← instForall constructorType ps
    forallBoundedTelescope tele (some nf) fun fields _ => do
      let fieldLevels ← fields.mapM fun field => do ilevel (← ityp field)
      let towerLevel :=
        if nf == 1 then fieldLevels[0]! else (fieldLevels.foldl mkLevelMax' .zero).normalize
      unless ← isLevelDefEq towerLevel w do
        declineWith (.shapeUnsupported tname .incomplete
          s!"{constructorName}'s field tower inhabits Sort {towerLevel} while the carrier \
inhabits Sort {w}, so the stored-index arm cannot hold the data field the conclusion's \
index vector does not carry, and the maybe-zero route has no pad for the level gap the \
never-zero tuple tower pads")
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
    (lparams : List Name) (np : Nat)
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

end InductiveModels
