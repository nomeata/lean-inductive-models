import InductiveModels.Simple.Plan

open Lean Meta

namespace InductiveModels

/-! ## Tight dependent-pair storage

A maybe-`Prop` family with two or more data fields cannot use the Church route:
at a positive universe instantiation that route remembers only inhabitation,
so intrinsic projections could not satisfy their constructor rules.  A
right-nested `PSigma'` retains the fields at the exact maximum of their
universes.  The storage is taken apart by **primitive `.proj`** and never by
the kernel's own recursor, so the storage interface itself has no
elimination-universe restriction: a projection carries no motive, so there is
no elimination universe for a subsingleton rule to restrict.  This is why the
pair's derived `rec'` existed here at all — it is `fun … minor self => minor
self.1 self.2`, a projection read wearing an eliminator's type — and why the
tower no longer needs even that ([`InductiveModels.tightTowerRec`]).

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

`skip` drops that many leading binders first, so the same function answers for
a raw constructor type whose owner parameters have not been instantiated: a
parameter is a *deeper* loose variable than any field, and the `min … j` below
is what keeps the walk to the field binders alone.

A `tele` with fewer than `skip + nf` leading binders is a caller fault rather
than a shape this can answer; it reports every field as depended upon, which is
the unconditional abstraction this mask exists to skip, so a fault costs
instructions and never a different term. -/
def tightFieldDepMask (tele : Expr) (nf : Nat) (skip : Nat := 0) : Array Bool := Id.run do
  let allDependent := (Array.range nf).map fun _ => true
  let mut fieldTypes : Array Expr := #[]
  let mut current := tele
  for _ in [0:skip] do
    let .forallE _ _ body _ := current | return allDependent
    current := body
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
field's type mentions, where it ends, and the **split** those two facts settle.

The tower is a right-nested `PSigma'` **spine** carrying exactly the fields some
later field's type mentions, ending in a balanced binary `PProd'` **block** over
everything else. A block leaf can never mention another block leaf — a
mentioned field is by definition on the spine — so the block needs no binders
at all; it may mention spine variables freely, because it is built at the
bottom of the spine where every spine binder is open. Field order is not
touched: the split is a storage layout, and the public interface indexes a
projection by the *source's* field position, which
[`InductiveModels.tightTowerProjs`] answers from the split rather than from the
storage's own order.

**Balanced rather than right-nested**, because a right-nested block costs
`O(n²)` to write down — every rung of the tail is written again inside the rung
above it — and depth `n` to project the last leaf, where a balanced one costs
`O(n log n)` and `log n`. That trade is the opposite of the dependent tower's,
and for a stated reason: a balanced *`PSigma'`* would force `fun p => …` motives
and turn every field reference into a projection path into a pair, and neither
applies to a pair with no family over leaves that reference nothing inside it.

`fields` and `dep` are index-aligned; `fields` are the free variables of
whichever telescope the tower is being built in, and `dep` is
[`InductiveModels.tightFieldDepMask`] of that telescope. -/
structure TightTower where
  /-- The constructor's stored fields, as free variables. -/
  fields : Array Expr
  /-- `dep[i]` — does any **later** field's type mention field `i`? -/
  dep : Array Bool
  /-- The tail: `none` where the block ends at its last field, `some w` where it
  ends at the pad [`InductiveModels.unitAt`] `w`. -/
  pad? : Option Level := none
  /-- **May this tower carry its independent fields in a block?**

  True everywhere but at one owner: `PProd'` itself.  Its own two fields are
  independent, so the ordinary route would carry them in a `PProd'` — that is,
  it would model the binder-free pair *by* the binder-free pair, and the
  inductive this tool splices would be left standing on itself.  So `PProd'`'s
  model is hard-coded to the plain tight tower, `PSigma' α (fun _ => β)`, which
  is the construction every carrier had before this flag existed: the whole
  telescope stays on the spine and a field nothing mentions gets a constant
  family rather than a block leaf.  Nothing else about it is special-cased: it
  is spliced, modelled, checked, ordered and emitted like any other inductive a
  construction introduces. -/
  pairs : Bool := true
  /-- The field indices the spine carries, in field order. -/
  spine : Array Nat := #[]
  /-- The block's leaves, in field order: a field index, or `none` for the pad.
  Never empty at a tower with a field, because the *last* field is mentioned by
  nothing after it and is therefore always a leaf. -/
  leaves : Array (Option Nat) := #[]

/-- The tower over an opened field telescope.  `tele` must be the very `Π`-nest
`fields` was opened from, so that the mask's indices are the fields' own. -/
def tightTowerOf (tele : Expr) (fields : Array Expr) (pad? : Option Level)
    (pairs : Bool := true) : TightTower :=
  let n := fields.size
  let dep := tightFieldDepMask tele n
  let padLeaf : Array (Option Nat) := if pad?.isSome then #[none] else #[]
  let (spine, leaves) :=
    if pairs then
      ((Array.range n).filter (fun i => dep[i]!),
        ((Array.range n).filter (fun i => !dep[i]!)).map some ++ padLeaf)
    else if pad?.isSome then
      (Array.range n, padLeaf)
    else
      (Array.range (n - 1), #[some (n - 1)])
  { fields, dep, pad?, pairs, spine, leaves }

/-- **The rung's family, where the tail does not mention the field.**

`mkLambdaFVars #[f] rest` abstracts `f` out of `rest` — a full traversal of
everything above this rung — and then binds it at `f`'s own name, binder info
and (head-beta-reduced) type.  Where no later field's type mentions `f` there is
nothing in `rest` to abstract, so the binding is written directly and the
traversal is skipped.  The term is the one `mkLambdaFVars` would have returned,
to the byte: `Lean.MetavarContext.mkBinding` binds a `cdecl` at
`mkLambda' userName binderInfo type.headBeta`, and `abstractRange` over a
variable that does not occur is the identity.

Reached only at a tower denied the block, since everywhere else such a field is
a leaf and has no rung at all. -/
def tightConstantFamily (field α body : Expr) (binderInfo : BinderInfo) : GenM Expr :=
  return .lam (← field.fvarId!.getUserName) α.headBeta body binderInfo

/-- The block's leaves as types and levels, in leaf order. -/
def tightBlockLeaves (tower : TightTower) : GenM (Array (Expr × Level)) :=
  tower.leaves.mapM fun leaf => do
    let ty ← match leaf, tower.pad? with
      | some i, _ => ityp tower.fields[i]!
      | none, some w => pure (unitAt w)
      | none, none => badShape "a tight tower's pad leaf has no pad"
    return (ty, ← ilevel ty)

/-- The block's type: the balanced `PProd'` tree over its leaves. -/
def tightBlockTy (tower : TightTower) : GenM Expr := do
  let leaves ← tightBlockLeaves tower
  if leaves.isEmpty then badShape "a tight tower with no fields needs a pad"
  return (blockTy leaves 0 leaves.size).1

/-- The tower's type from spine position `k` down. -/
partial def tightTowerTy (tower : TightTower) (k : Nat) : GenM Expr := do
  if k == tower.spine.size then return ← tightBlockTy tower
  let i := tower.spine[k]!
  let field := tower.fields[i]!
  let α ← ityp field
  let u ← ilevel α
  let rest ← tightTowerTy tower (k + 1)
  let v ← ilevel rest
  let β ← if tower.dep[i]! then mkLambdaFVars #[field] rest
    else tightConstantFamily field α rest (← field.fvarId!.getBinderInfo)
  return mkAppN (.const `PSigma' [u, v]) #[α, β]

/-- An expression built at the tower's own field variables, at a substituted
spine prefix: `pre` holds the values of the first `pre.size` **spine** fields. -/
def tightSpineSubst (tower : TightTower) (pre : Array Expr) (expression : Expr) : Expr :=
  expression.replaceFVars
    ((tower.spine.extract 0 pre.size).map (fun i => tower.fields[i]!)) pre

/-- **One spine rung, at a substituted prefix**: its two levels, its first
component's type, and its second component — always a *family*, because a field
the tail does not mention is a block leaf and never a rung, except at a tower
denied the block, where the family is constant. -/
def tightTowerAt (tower : TightTower) (k : Nat) (pre : Array Expr) :
    GenM (Level × Level × Expr × Expr) := do
  let i := tower.spine[k]!
  let field := tower.fields[i]!
  let α := tightSpineSubst tower pre (← ityp field)
  let u ← ilevel α
  let rest ← tightTowerTy tower (k + 1)
  -- The tail does not mention this field, so the binder it is abstracted under
  -- holds nothing: substituting `pre` for the spine fields before it is the
  -- whole of the substitution.
  unless tower.dep[i]! do
    let rest := tightSpineSubst tower pre rest
    let v ← ilevel rest
    return (u, v, α, ← tightConstantFamily field α rest .default)
  let (v, β) ← withLocalDeclD (← field.fvarId!.getUserName) α fun value => do
    let rest := tightSpineSubst tower (pre.push value) rest
    let v ← ilevel rest
    return (v, ← mkLambdaFVars #[value] rest)
  return (u, v, α, β)

/-- The block's value: the balanced tree of `PProd'.mk` over the leaf fields,
at the node types the block's own type carries. -/
partial def tightBlockMk (tower : TightTower) (block : Expr) (lo hi : Nat) : GenM Expr := do
  if hi ≤ lo + 1 then
    match tower.leaves[lo]!, tower.pad? with
    | some i, _ => return tower.fields[i]!
    | none, some w => return unitAtCanon w
    | none, none => badShape "a tight tower's pad leaf has no pad"
  let (u, v, α, β) ← blockNode block
  let mid := blockSplit lo hi
  return mkAppN (.const `PProd'.mk [u, v])
    #[α, β, ← tightBlockMk tower α lo mid, ← tightBlockMk tower β mid hi]

partial def tightTowerMk (tower : TightTower) (k : Nat) : GenM Expr := do
  if k == tower.spine.size then
    return ← tightBlockMk tower (← tightBlockTy tower) 0 tower.leaves.size
  let pre := (tower.spine.extract 0 k).map (fun i => tower.fields[i]!)
  let (u, v, α, snd) ← tightTowerAt tower k pre
  return mkAppN (.const `PSigma'.mk [u, v])
    #[α, snd, tower.fields[tower.spine[k]!]!, ← tightTowerMk tower (k + 1)]

/-- The block read out, one primitive projection pair per node. -/
partial def tightBlockProjs (tower : TightTower) (out : Array Expr) (value : Expr)
    (lo hi : Nat) : Array Expr :=
  if hi ≤ lo + 1 then
    match tower.leaves[lo]! with
    | some i => out.set! i value
    | none => out
  else
    let mid := blockSplit lo hi
    tightBlockProjs tower
      (tightBlockProjs tower out (.proj `PProd' 0 value) lo mid)
      (.proj `PProd' 1 value) mid hi

/-- **The tower read out**, at each field's *source* index.

**It builds no types.** A primitive `.proj` carries the structure's name and a
field index and nothing else — not the rung's `α`, not its second component,
not either level — so walking the tower to a field needs only the split the
tower already carries. This used to call [`InductiveModels.tightTowerAt`] at
every rung and discard all four of its results, a vestige of the day the
projections were `PSigma'.fst`/`.snd` *applications* and did need `α` and `β`
spelled out. It was measured at 81% of this function's cost.

Nor was it a well-formedness assertion standing in for one: every rung it
rebuilt is rebuilt for real, at the same fields and the same `pad?`, by
[`InductiveModels.tightTowerTy`] for the carrier and by
[`InductiveModels.tightTowerAt`] under [`InductiveModels.tightTowerMk`] for the
constructor, both of which run **before** the projections on both routes that
reach here. Any shape this could have rejected is rejected there first, with
the same message.

**A block field's path is `log n` long and a spine field's is its spine
position**, where a right-nested tower gave every field a path as long as its
own index; the array below is still indexed by the source field position, which
is the whole of the bookkeeping the split costs a consumer. -/
def tightTowerProjs (tower : TightTower) (value : Expr) : Array Expr := Id.run do
  let mut out := Array.replicate tower.fields.size value
  let mut current := value
  for k in [0:tower.spine.size] do
    out := out.set! tower.spine[k]! (.proj `PSigma' 0 current)
    current := .proj `PSigma' 1 current
  return tightBlockProjs tower out current 0 tower.leaves.size

/-- **The tower taken apart**, with no eliminator anywhere in it: every field —
spine rung and block leaf alike — is *read* at the primitive projection path
that reaches it ([`InductiveModels.tightTowerProjs`]), and the minor premise is
applied to those paths at the fields' source positions. The recursor's whole
body is that one application.

### Why nothing is eliminated

The block used to be eliminated by one `PProd'.rec'` per node and **the spine by
one `PSigma'.rec'` per rung**, each carrying a motive `fun tail => motive
(prepend pre tail)` — and `prepend` writes down every spine rung above it. A
spine of `m` rungs therefore wrote itself `m` times, and a block of `n` leaves
under it wrote the spine `n - 1` times more, with the kernel checking every
copy. `da1e3f4` removed the block's `n - 1` copies; this removes the spine's
`m`, which is the same defect one level up and the larger half of it on a record
with a dependent head.

Reading costs one conversion instead, at the end: the minor's type says
`motive (ctor f⃗)`, `ctor` unfolds to [`InductiveModels.tightTowerMk`], and this
owes `motive value` — so the kernel must see `towerMk (projs value) ≡ value`,
which is structure eta at each of the `m` `PSigma'` rungs and each of the
`n - 1` `PProd'` nodes. Both are genuine single-constructor, index-free
inductives ([`InductiveModels.psigmaPrimeDecl`],
[`InductiveModels.pprodPrimeDecl`]), so both have primitive projections and that
conversion.

**`PSigma'.rec'` was never a kernel recursor and this asks the kernel for
nothing new.** Its own body is `fun … minor self => minor self.1 self.2` over
primitive projections ([`InductiveModels.ensurePSigmaPrime`]), so it is well
typed *only* because `mk self.1 self.2 ≡ self` — the very eta this now spends
directly. Emitting the rung's `rec'` bought nothing but the motive: `rec'`
δ-unfolds to exactly the application below, so the kernel did this conversion
either way and paid for `m` motives on top. The tight route already reads the
spine this way where it matters most — [`InductiveModels.tightTowerProjs`] is
what the projection overrides are built from, and each of those is checked to
**select** its field by `isDefEq` before it may be emitted, so the paths applied
below are the same paths that contract already certifies reduce to their fields.
They are now the same *call*: the recursor's body and this route's projection
overrides are one function's output, where they used to be two constructions —
a recursion over bound `fst` variables and a walk over paths — that had to
agree and were only checked to.

### Why the spine's dependency does not obstruct this

Rung `k`'s type mentions the fields before it, so unlike the block's the paths
are not independent — but they do not have to be. The minor binds
`∀ (f₀ : T₀) (f₁ : T₁ f₀) …`, and the kernel's own typing rule for `.proj` on a
dependent structure instantiates the later field's type at the *earlier
projections of the same value*: `.proj 1 s` is typed at `β (.proj 0 s)`. So
supplying `p₀ = .proj 0 s`, `p₁ = .proj 0 (.proj 1 s)`, … threads the dependency
exactly as the telescope demands, and it does so definitionally rather than by
transport. This is why the paths may be handed to a telescope that was opened at
fresh variables: they are not the variables, but the kernel substitutes them
into the binder types itself.

**The pad is still dropped**, and for the reason it always was: the tower stores
`canon` at that leaf and the projection reaches an element of the same
singleton, so the conversion closes there by tight-pair and `PUnit` structure eta
plus proof irrelevance. No transport rides along and the recursor's ι rule stays
`Eq.refl`.

**What still says field `k` is source field `k`.** The old check was the ι rule,
`Eq.refl` at the minor applied in source order. This is the same check on the
same fields, and it now covers the spine as well as the block: if the fill and
the tower's own layout disagreed by a permutation, the conversion would ask the
kernel to equate two *distinct* projection paths applied to the **variable**
`value`. Neither is a redex, so the kernel refuses them unless they are the same
path. On the spine the paths are `.proj 0 (.proj 1)ᵏ`, distinct for distinct
`k`; in the block they are distinct by [`InductiveModels.blockSplit`], a
function of the leaf count alone. A permutation is additionally ill-typed on the
spine — swapping two rungs offers rung `k`'s path where a type mentioning it is
expected — but the path argument alone already decides it, and it is the one
that does not depend on the fields' types being distinguishable.

`tightTowerTy`, `tightTowerMk` and `tightTowerProjs` walk one spine and split
one leaf range, so the three cannot disagree about the layout they are
each asked about. -/
def tightTowerRec (tower : TightTower) (minor value : Expr) : GenM Expr := do
  if tower.leaves.isEmpty then badShape "a tight tower with no fields needs a pad"
  return mkAppN minor (tightTowerProjs tower value)

/-- Emit an exact-sort model for a non-recursive, unindexed, one-constructor
family, storing its fields in the tower.  `pad?` is that tower's tail: `none`
where the fields' own levels already reach the carrier's sort, `some w` where
the pad is what takes them there. -/
def directTightModel (eqi : EqInfo) (tname : Name) (lparams : List Name) (np : Nat)
    (memberTy constructorType modelConstructorType declaredMemberTy : Expr)
    (selfN constructorN recursorN : Name) (recursorLevelParams : List Name)
    (recursorProofType recursorPublicType : Expr) (pad? : Option Level)
    (pairs : Bool) :
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
      mkLambdaFVars ps (← tightTowerTy (tightTowerOf tele fields pad? pairs) 0)
  let selfDecl := Declaration.defnDecl
    { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfValue
      hints := ← hintsFor selfValue, safety := .safe }
  addChecked selfDecl
  declarations := declarations.push selfDecl

  let constructorValue ← withParams fun ps => do
    let tele ← instForall modelConstructorType ps
    forallBoundedTelescope tele (some nf) fun fields _ => do
      mkLambdaFVars (ps ++ fields) (← tightTowerMk (tightTowerOf tele fields pad? pairs) 0)
  let constructorDecl := Declaration.defnDecl
    { name := constructorN, levelParams := lparams, type := modelConstructorType,
      value := constructorValue, hints := ← hintsFor constructorValue, safety := .safe }
  addChecked constructorDecl
  declarations := declarations.push constructorDecl

  let recursorValue ← forallBoundedTelescope recursorProofType
      (some (np + 3)) fun binders _ => do
    -- The motive is bound and not read: the body is the minor at the tower's
    -- projection paths, and what ties it to `motive self` is the kernel's
    -- structure-eta conversion rather than an eliminator stated at a motive.
    let minor := binders[np + 1]!
    let self := binders[binders.size - 1]!
    let ps := binders.extract 0 np
    let tele ← instForall constructorType ps
    forallBoundedTelescope tele (some nf) fun fields _ => do
      mkLambdaFVars binders
        (← tightTowerRec (tightTowerOf tele fields pad? pairs) minor self)
  let recursorDecl := Declaration.defnDecl
    { name := recursorN, levelParams := recursorLevelParams, type := recursorPublicType,
      value := recursorValue, hints := ← hintsFor recursorValue, safety := .safe }
  addChecked recursorDecl
  declarations := declarations.push recursorDecl

  let overrides ← withParams fun ps => do
    let tele ← instForall constructorType ps
    forallBoundedTelescope tele (some nf) fun fields _ => do
      withLocalDeclD `self (selfAt ps) fun self => do
        let projections := tightTowerProjs (tightTowerOf tele fields pad? pairs) self
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
earlier one; it is the same Henry-Ford equation the recovery arm discharges its non-pivot
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
    (recursorProofType recursorPublicType : Expr) (w v : Level) (pad? : Option Level)
    (pairs : Bool) :
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
      tightTowerTy (tightTowerOf tele fields pad? pairs) 0
  let projsAt : Array Expr → Expr → GenM (Array Expr) := fun ps value => do
    let tele ← instForall constructorType ps
    forallBoundedTelescope tele (some nf) fun fields _ =>
      pure (tightTowerProjs (tightTowerOf tele fields pad? pairs) value)
  -- Takes the `Π`-nest its fields were opened from rather than the parameters,
  -- because the tower's dependency mask is read off that nest.
  let towerOf : Expr → Array Expr → GenM Expr := fun tele fs =>
    tightTowerMk (tightTowerOf tele fs pad? pairs) 0

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

/-- The level an unpadded tower reaches: the fields' own max, and at one field
that field's level unwrapped, since a one-field unpadded tower **is** that
field's type. -/
def tightTowerRawLevel (fieldLevels : Array Level) : Level :=
  if fieldLevels.size == 1 then fieldLevels[0]!
  else (fieldLevels.foldl mkLevelMax' .zero).normalize

/-- **Does the tower land on `Sort w`, and with which tail?** — the level
question alone, with no verdict attached. `none` is *neither the bare tower nor
the pad reaches the sort*; whether that is a decline or a fall-through to
another arm is the caller's to say. -/
def tightTowerPad? (fieldLevels : Array Level) (w : Level) :
    GenM (Option (Option Level)) := do
  let raw := tightTowerRawLevel fieldLevels
  if ← isLevelDefEq raw w then return some none
  if ← isLevelDefEq (mkLevelMax' raw w).normalize w then return some (some w)
  return none

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
  `w` for the same reason the empty arm's `emptyAt` does: the derived exact-sort lift
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
  if let some pad? ← tightTowerPad? fieldLevels w then return pad?
  let raw := tightTowerRawLevel fieldLevels
  let padded := (mkLevelMax' raw w).normalize
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
projection and its rule are the ones this file already writes.

**`fallback` is whether a *later* arm stores what this tower cannot**, and it
is the whole of what the never-zero sort adds. A tower that misses `Sort w` is
the end of the line at a maybe-zero carrier — [`InductiveModels.planTightTower`]
writes out why no third construction exists there — but at a **never-zero** one
it is not: the tuple tower's plan retries the same fields **recursively boxed**
([`InductiveModels.boxTyOf`]), and boxing removes exactly the `imax` a
`max`-shaped carrier does not absorb. Every boxed level carries a `max 1 ·`
floor, which is why the retry is unavailable at a maybe-zero `w` and available
at a never-zero one. So where `fallback` holds this answers *the route does not
apply* and the owner goes on to the arm that does; where it does not, the
missed sort is the stated boundary it has always been. Neither side is a
special case of a shape: the question asked is the same one, and only who owes
the verdict changes. -/
def planDirectTightRoute (tname : Name) (eligible : Bool) (np : Nat)
    (memberTy : Expr) (exportCtors : Array (Name × Expr)) (w : Level)
    (fallback : Bool) : GenM (Option (Option Level)) := do
  unless eligible do return none
  let (constructorName, constructorType) := exportCtors[0]!
  unless numForalls constructorType - np >= 1 do return none
  forallBoundedTelescope memberTy (some np) fun ps _ => do
    let tele ← instForall constructorType ps
    let nf := numForalls tele
    forallBoundedTelescope tele (some nf) fun fields _ => do
      let fieldLevels ← fields.mapM fun field => do ilevel (← ityp field)
      if fallback then return (← tightTowerPad? fieldLevels w)
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
reason: the case is reached only after the recovery arm has been ruled out, which means
the constructor has a data field the conclusion's index vector does not carry,
so the model must store it and the Church encoding underneath — which remembers
only inhabitation — cannot. The pad is what takes that storage to the declared
sort, and where even the pad misses, the boundary is stated rather than
recorded as an unfinished arm. Settled before anything is spliced, so the owner
passes through unchanged.

Zero fields is a different answer, and which answer depends on the sort. At a
**maybe-zero** carrier every non-proof field is then vacuously one of the
conclusion's indices, so the kernel minted the large eliminator and the recovery arm
fired; reaching this there with no fields is a route-classification fault. At a
**never-zero** one the recovery arm is not in the chain at all, so a zero-field indexed
family is an ordinary shape with nothing to store, and it belongs to the arm
behind this route rather than to this one.

`fallback` is [`InductiveModels.planDirectTightRoute`]'s, for the same reason
and with the same meaning: at a never-zero sort the carve arm stands behind this route
and takes both the zero-field owner and the owner whose fields carry an `imax`
the tower cannot reach, so neither is a decline here. -/
def planDirectIndexedRoute (tname : Name) (eligible : Bool) (np : Nat) (memberTy : Expr)
    (exportCtors : Array (Name × Expr)) (w : Level) (fallback : Bool) :
    GenM (Option (Option Level)) := do
  unless eligible do return none
  let (constructorName, constructorType) := exportCtors[0]!
  let nf := numForalls constructorType - np
  if nf == 0 then
    if fallback then return none
    badShape s!"internal: {constructorName} has no fields, so every non-proof field of \
{tname} is vacuously one of the conclusion's indices and the recovery arm, not the direct routes' \
indexed case, is the one that models it"
  forallBoundedTelescope memberTy (some np) fun ps _ => do
    let tele ← instForall constructorType ps
    forallBoundedTelescope tele (some nf) fun fields _ => do
      let fieldLevels ← fields.mapM fun field => do ilevel (← ityp field)
      if fallback then return (← tightTowerPad? fieldLevels w)
      return some (← planTightTower tname constructorName fieldLevels w "field tower")

/-- **The binder-free pair's support, where a tower will use it** — three
answers in one, because they must agree or the island references a constant it
never installed:

* `pairs` — may this owner's tower use the pair at all?  Everywhere but at
  `PProd'` itself; see [`InductiveModels.TightTower.pairs`].
* the support to install — `PProd'`, the whole of it now that the pair is
  projected rather than eliminated, spliced if the input has
  none and validated if it has one, and only where the block holds **two or
  more** leaves, which is exactly when [`InductiveModels.blockTy`] writes a
  node rather than returning its one leaf bare.  A fully dependent telescope
  pays nothing, and so does a telescope with a single unmentioned field and no
  pad.  The count is the tower's own: the fields no later field's type
  mentions, plus the pad's leaf where there is a pad — which is why `pad?` is
  a parameter and the answer is not read off the dependency mask alone.
* `requires` — `PProd'` where **this** island is the one that spliced it, and
  empty where an earlier island already did.  That is
  [`InductiveModels.Iso.requires`]' rule at the tree arm's shape exactly: the model
  that introduces an inductive is the one that may not leave it unmodelled, and
  a later island reusing persistent support has nothing to model.

The need is asked of the source constructor type **and** the model's, and
answered yes if either says so.  The two are one telescope up to renaming, and
each of the four constructions opens one or the other; a field that fell into
the block in only one of them would otherwise reach for `PProd'` in an island
that never installed it. -/
def tightBinderFreeSupport (tname : Name) (constructorType modelConstructorType : Expr)
    (np nf : Nat) (pad? : Option Level) :
    GenM (Bool × Array Declaration × Array Name) := do
  let pairs := tname != `PProd'
  let padLeaves := if pad?.isSome then 1 else 0
  let node := fun (ty : Expr) =>
    ((tightFieldDepMask ty nf np).filter (!·)).size + padLeaves >= 2
  unless pairs && (node constructorType || node modelConstructorType) do
    return (pairs, #[], #[])
  let support ← ensurePProdPrime
  let spliced := support.any fun declaration => declaration.getNames.contains `PProd'
  return (true, support, if spliced then #[`PProd'] else #[])

/-- Install tight-pair support and emit the complete exact-sort model branch.
The caller only merges the returned declarations, splice witnesses, model
requirements, and projection overrides into its route state. -/
def emitDirectTightModel (eqi : EqInfo) (tname : Name) (lparams : List Name) (np : Nat)
    (memberTy constructorType modelConstructorType declaredMemberTy : Expr)
    (selfN constructorN recursorN : Name) (recursorLevelParams : List Name)
    (recursorProofType recursorPublicType : Expr) (pad? : Option Level) :
    GenM (Array Declaration × Array Name × Array Name ×
      Array (Name × Nat × Expr × Expr)) := do
  let (pairs, pairSupport, requires) ← tightBinderFreeSupport tname constructorType
    modelConstructorType np (numForalls constructorType - np) pad?
  let support ← if pad?.isSome then ensureExactSortLift else ensurePSigmaPrime
  let support := support ++ pairSupport
  let (declarations, overrides) ← directTightModel eqi tname lparams np memberTy
    constructorType modelConstructorType declaredMemberTy selfN constructorN recursorN
    recursorLevelParams recursorProofType recursorPublicType pad? pairs
  let spliced := support.flatMap fun declaration => declaration.getNames.toArray
  return (support ++ declarations, spliced, requires, overrides)

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
    GenM (Array Declaration × Array Name × Array Name ×
      Array (Name × Nat × Expr × Expr)) := do
  let (pairs, pairSupport, requires) ← tightBinderFreeSupport tname constructorType
    modelConstructorType np (numForalls constructorType - np) pad?
  let support ← if pad?.isSome then ensureExactSortLift else ensurePSigmaPrime
  let support := support ++ pairSupport
  let (declarations, overrides) ← directIndexedModel eqi tname lparams np ni constructorName
    memberTy constructorType modelConstructorType declaredMemberTy selfN constructorN
    recursorN recursorLevelParams recursorProofType recursorPublicType w v pad? pairs
  let spliced := support.flatMap fun declaration => declaration.getNames.toArray
  return (support ++ declarations, spliced, requires, overrides)

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
    GenM (Array Declaration × Array Name × Array Name ×
      Array (Name × Nat × Expr × Expr)) := do
  match route with
  | .field fieldRoute =>
    let support ← if fieldRoute matches .propLift then ensureExactSortLift else pure #[]
    let (declarations, override) ← directFieldModel fieldRoute eqi tname lparams np
      memberTy constructorType modelConstructorType declaredMemberTy selfN constructorN
      recursorN recursorLevelParams recursorProofType recursorPublicType w v
    let spliced := support.flatMap fun declaration => declaration.getNames.toArray
    return (support ++ declarations, spliced, #[], #[override])
  | .tight pad? =>
    emitDirectTightModel eqi tname lparams np memberTy constructorType modelConstructorType
      declaredMemberTy selfN constructorN recursorN recursorLevelParams
      recursorProofType recursorPublicType pad?
  | .indexed pad? =>
    emitDirectIndexedModel eqi tname lparams np ni constructorName memberTy constructorType
      modelConstructorType declaredMemberTy selfN constructorN recursorN recursorLevelParams
      recursorProofType recursorPublicType w v pad?

end InductiveModels
