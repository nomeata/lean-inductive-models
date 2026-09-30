import InductiveModels.Simple.Box

open Lean Meta

namespace InductiveModels

/-! ## One constructor's chain

A constructor's field telescope becomes a **spine** and a **block**, both at
exactly `Sort w`. The spine is a right-nested `PSigma'` carrying exactly the
fields some *later* field mentions; the block is everything else, in a balanced
binary tree of `PProd'` beneath the spine. The builders below recurse on the
(progressively instantiated) telescope expression, so nothing is stored across
scopes. `pad?` closes the chain when the field levels do not already reach `w`
— and always for a nullary constructor — and is the block's last leaf.
`boxed` says, per field, whether the field is stored boxed
([`InductiveModels.boxTyOf`]); a later field's type always depends on the
*unboxed* value, so the recursions instantiate with `unbox` of the bound
variable and the real value stays what the minor is applied to.

### Why the split is the telescope's own property

Field `i` is on the spine exactly when the rest of the telescope has a loose
occurrence of it. That question is asked *before* the instantiation, so there
is no mask to build: this walk descends by `rest.instantiate1`, and
`instantiate1` is what renumbers the loose variables, so at every field `rest`'s
own `bvar 0` is this field and `rest.hasLooseBVar 0` is exactly "does what is
left mention it" — one header comparison on `Expr`, with no per-telescope
precomputation and nothing carried between fields.

The question is asked of the remaining telescope entire, which includes the
constructor's trailing result type. That is conservative in the one direction
that costs only instructions: an index the field appears in keeps the field on
the spine where the block would have held it.

**A block field can never mention another block field.** A mentioned field is
by definition on the spine, so the block's leaves are pairwise independent —
which is what lets them be reassociated at all. They may mention spine
variables freely, because the block is built at the bottom of the spine and
every spine binder is open there. The block therefore needs no binders of its
own, and `PProd'` — the tight pair with the second component's binder removed,
at the same `Sort (max u v)` ([`InductiveModels.pprodPrimeDecl`]) — is the pair
it is built at.

**And the tree is balanced rather than right-nested.** Right-nesting costs
`O(n²)` in the construction — every rung of the tail is written again inside
the rung above it — and depth `n` to reach the last leaf. Balancing makes both
`O(n log n)` and `log n`. The reason balancing is right *here* and was measured
wrong for the dependent tower is that the two carriers are not the same
construction: a balanced `PSigma'` forces `fun p => …` motives and turns a
field reference into a deep projection path into a pair, and neither applies to
a pair with no family whose leaves reference nothing inside it.

### A boxed field nothing later names is a slot

The recursor hands the minor the unboxed value and owes `motive` at the value it
read, so a boxed field's round trip `box (unbox p) ≡ p` is a conversion the
kernel must decide — by taking `p` apart at every Π of the field type, counted
as a tree. Where a later field names the field, that conversion is forced: the
later field's type is stated at the unboxed value, and the tuple holding it is
typed at the stored one. Where nothing does, the field is a **slot**
([`InductiveModels.ChainSlot`]): the destructor goes through the box's
`boxFix` instead, and the constructor's ι rule is proved by the box's `rt`
([`InductiveModels.chainFinish`]). The split is `rest.hasLooseBVar 0`, the same
question the block/spine split asks.

`pairs` is false at one owner only, the pair itself, which may not be modelled
by a tower built out of it; there the whole telescope stays on the spine and a
field nothing mentions gets a constant family rather than a block leaf. The
never-zero tuple tower does not in fact reach `PProd'`, whose own
`Sort (max u v)` is maybe-zero and takes the direct route, so the flag is a
guard and not a branch this arm exercises. -/

/-- **The block's shape is its leaf count and nothing else**, so every one of
the three walks below splits the same range the same way and none of them has
to record the shape or read it back. `lo` and `hi` bound the leaves this
subtree holds; a single leaf is that leaf's own type, with no pair around it. -/
def blockSplit (lo hi : Nat) : Nat := (lo + hi) / 2

/-- The balanced `PProd'` tree over the block's leaves and their levels. -/
partial def blockTy (leaves : Array (Expr × Level)) (lo hi : Nat) : Expr × Level :=
  if hi ≤ lo + 1 then leaves[lo]!
  else
    let mid := blockSplit lo hi
    let (α, ℓa) := blockTy leaves lo mid
    let (β, ℓb) := blockTy leaves mid hi
    (pprodT ℓa ℓb α β, (mkLevelMax' ℓa ℓb).normalize)

/-- **The block node a chain type already spells out**: its two levels and its
two subtrees, read back off the pair [`InductiveModels.blockTy`] built. Asked
only where the leaf range has more than one leaf, which is what tells a node
apart from a leaf whose own type happens to be a `PProd'`. -/
def blockNode (block : Expr) : GenM (Level × Level × Expr × Expr) := do
  match block with
  | .app (.app (.const `PProd' [ℓa, ℓb]) α) β => return (ℓa, ℓb, α, β)
  | _ => badShape "the chain's block node is not the binder-free pair it was built at"

/-- **The spine rung a chain type already spells out**: its two levels, its
stored component's type and its tail family, read back off the pair
[`InductiveModels.chainTy`] built rather than rebuilt from the telescope.

`chain` is the type of the value being taken apart or put together, so it is
already in every caller's hand — `stepTower` binds its scrutinee at it and
[`InductiveModels.PCtor`] carries it beside the telescope it was built from.
Rebuilding it was the tower's quadratic: at rung `i` both the tuple and the
destructor called `chainTy` again on the *whole* tail, and each rebuild ends in
a `mkLambdaFVars` that traverses everything above the rung, so a chain of `n`
fields paid `O(n²)` rung constructions over terms that grow with the fields'
own size.

Reading the rung off the type is also the stronger statement. The rebuilt rung
had to *agree* with the scrutinee's type for the recursor to be well typed, and
nothing but the kernel gate said it did; the components below are that type's
own, so the constructor and the destructor cannot disagree with the carrier
about the shape of a rung.

A spine rung is always the tight pair: a field the tail does not mention is a
block leaf and never a rung at all, so the binder-free pair appears below the
spine and nowhere in it. -/
def chainRung (chain : Expr) : GenM (Level × Level × Expr × Expr) := do
  match chain with
  | .app (.app (.const `PSigma' [ℓt, ℓi]) st) β => return (ℓt, ℓi, st, β)
  | _ => badShape "the chain's spine rung is not the tight pair its carrier was built at"

/-- The chain's type and level. `nf` is the field count; the telescope's
trailing result type is never entered.

`block` is the leaves collected so far, in the fields' own order; the tree over
them closes the chain once the telescope is exhausted. A chain whose last field
is on the spine with no block leaf under it and no pad is that field's type
bare, which is what a chain of one field has always been. -/
partial def chainTy (pairs : Bool) (pad? : Option Pad) (boxed : Array Bool) (nf : Nat)
    (tele : Expr) (i : Nat := 0) (block : Array (Expr × Level) := #[]) :
    GenM (Expr × Level) := do
  if nf == 0 then
    let leaves := match pad? with
      | some p => block.push (p.ty, p.lv)
      | none => block
    if leaves.isEmpty then badShape "a chain with no fields needs a pad"
    return blockTy leaves 0 leaves.size
  let .forallE x t rest _ := tele | badShape "field telescope shorter than the field count"
  let bx := boxed[i]?.getD false
  let st ← if bx then boxTyOf t else pure t
  let ℓt ← ilevel st
  if nf == 1 && pad?.isNone && block.isEmpty then
    return (st, ℓt)
  unless rest.hasLooseBVar 0 do
    -- **The block, where the pair is allowed.** Nothing left in the telescope
    -- names this field, so it needs no binder and the instantiation below is a
    -- lowering. Where the pair is denied, the field stays on the spine and its
    -- rung carries a constant family: `mkLambdaFVars #[xv] inner` would
    -- traverse everything above the rung to abstract a variable that does not
    -- occur in it, and the direct `.lam` is the term it would have returned to
    -- the byte — `Lean.MetavarContext.mkBinding` binds a `cdecl` at
    -- `mkLambda' userName binderInfo type.headBeta`, and `abstractRange` over
    -- a variable that does not occur is the identity.
    if pairs then
      return ← chainTy pairs pad? boxed (nf - 1) (rest.lowerLooseBVars 1 1) (i + 1)
        (block.push (st, ℓt))
    let (inner, ℓi) ← chainTy pairs pad? boxed (nf - 1) rest (i + 1) block
    return (psigmaT ℓt ℓi st (.lam x st.headBeta inner .default),
      (mkLevelMax' ℓt ℓi).normalize)
  withLocalDeclD x st fun xv => do
    let rv ← if bx then unboxValOf t xv else pure xv
    let (inner, ℓi) ← chainTy pairs pad? boxed (nf - 1) (rest.instantiate1 rv) (i + 1) block
    return (psigmaT ℓt ℓi st (← mkLambdaFVars #[xv] inner),
      (mkLevelMax' ℓt ℓi).normalize)

/-- The block's tuple: the balanced tree of `PProd'.mk` over the stored leaf
values, at the node types the block's own type carries. -/
partial def blockTuple (block : Expr) (leaves : Array Expr) (lo hi : Nat) : GenM Expr := do
  if hi ≤ lo + 1 then return leaves[lo]!
  let (ℓa, ℓb, α, β) ← blockNode block
  let mid := blockSplit lo hi
  return pprodMk ℓa ℓb α β (← blockTuple α leaves lo mid) (← blockTuple β leaves mid hi)

/-- The tuple `⟨v₁, ⟨v₂, …⟩⟩` at the given field values — each boxed where its
plan says so — closed by the block over the values no later field mentions and
by the pad's canonical element when there is one. `chain` is
[`InductiveModels.chainTy`] of `tele`, i.e. the tuple's own type.

**The tail's own chain type is the rung's second component applied to the
stored value**, and never a rebuild from the telescope. The two differ in one
place: at a *boxed* rung the family abstracts the stored value and the tail
mentions `unbox` of it, so applying it at `box v` leaves `unbox (box v)` where
a rebuild would leave `v`. That is the type the carrier actually declares the
tail at, which is what the tuple must be built against — and the rebuild was
`O(n²)`, since it walked the whole tail at every rung. -/
partial def chainTuple (pairs : Bool) (pad? : Option Pad) (boxed : Array Bool) (nf : Nat)
    (tele : Expr) (chain : Expr) (vals : Array Expr) (i : Nat := 0)
    (block : Array Expr := #[]) : GenM Expr := do
  if nf == 0 then
    let leaves := match pad? with
      | some p => block.push p.canon
      | none => block
    if leaves.isEmpty then badShape "a chain with no fields needs a pad"
    return ← blockTuple chain leaves 0 leaves.size
  let .forallE _ t rest _ := tele | badShape "field telescope shorter than the field count"
  let bx := boxed[i]?.getD false
  let sv ← if bx then boxValOf t vals[i]! else pure vals[i]!
  if nf == 1 && pad?.isNone && block.isEmpty then
    return sv
  let tailTele := rest.instantiate1 vals[i]!
  if pairs && !rest.hasLooseBVar 0 then
    return ← chainTuple pairs pad? boxed (nf - 1) tailTele chain vals (i + 1) (block.push sv)
  let (ℓt, ℓi, st, β) ← chainRung chain
  let snd ← chainTuple pairs pad? boxed (nf - 1) tailTele (mkApp β sv).headBeta vals
    (i + 1) block
  return psigmaMk ℓt ℓi st β sv snd

/-- One block leaf: the pad, or a field at its source index together with
whether it is stored boxed and the type the box was taken of. -/
abbrev BlockLeaf := Option (Nat × Bool × Expr)

/-- **The block read out**, each leaf at the primitive projection path that
reaches it: `.proj PProd' 0` into the left subtree, `.proj PProd' 1` into the
right, `log n` deep, with a one-leaf block reached by no projection at all.

**It builds no types.** A primitive `.proj` carries the structure's name and a
field index and nothing else, so the walk needs only the split
[`InductiveModels.blockSplit`] already decides — not a node's `α`, not its `β`,
not either level. The array is leaf-indexed; the caller moves each leaf to its
**source** field position.

This is [`InductiveModels.tightBlockProjs`] over the same tree, and the two
routes read the block the same way for the same reason. -/
partial def blockPaths (out : Array Expr) (value : Expr) (lo hi : Nat) : Array Expr :=
  if hi ≤ lo + 1 then out.set! lo value
  else
    let mid := blockSplit lo hi
    blockPaths (blockPaths out (.proj `PProd' 0 value) lo mid)
      (.proj `PProd' 1 value) mid hi

/-- **The block taken apart by projection**, from the chain's innermost spine
value.

`vals` is the destructor's field vector, at **source** indices; the leaves it
still owes are exactly the block's, so this fills them and returns it. The pad
leaf fills nothing: the minor's telescope is the source constructor's and has no
binder for it.

### Why this is a projection and not a `PProd'.rec'`

The block used to be eliminated by one `PProd'.rec'` per node, each carrying a
motive `fun s => target (rebuild s)` — and `rebuild` names the whole chain value
the target is stated about, spine `PSigma'.mk`s included. A block of `n` leaves
under a spine of `m` rungs therefore wrote the spine down `n - 1` times, and the
kernel type-checked each copy. That is what the split was costing on a record
whose fields are mostly dependent and whose *tail* is a run of independent proof
fields: a long spine and a wide block are the same declaration.

Reading the block instead costs one conversion, once, at the end: the minor's
own type says `motive (ctor f⃗)`, `ctor` unfolds to the chain's tuple, and the
destructor owes `motive ⟨j̄, scrut⟩` — so the kernel must see
`blockTuple (paths scrut) ≡ scrut`, which is `PProd'` structure eta at each of
the `n - 1` nodes. Not a *proof* of eta — the eliminator that used to carry one
spent this same conversion in its own body to have it — but the kernel's
structure-eta conversion, which expands a neutral `scrut` against a literal
`PProd'.mk` and compares componentwise. `PProd'` is a genuine
single-constructor, index-free inductive
([`InductiveModels.pprodPrimeDecl`]), so it has both primitive projections and
that conversion, and neither is anything a derived declaration would have
supplied. `PProd'.rec'` is gone with its last consumer: the pair is now built
and projected and never eliminated, so its bundle is the inductive alone
([`InductiveModels.ensurePProdPrime`]).

### What still says leaf `k` is source field `k`

The recursor's ι rule was the old check: it is `Eq.refl` at the minor applied in
source order, so a mis-filled slot was a kernel rejection. **The conversion above
is the same check, and on the same fields.** Suppose the fill below and
[`InductiveModels.chainTy`]'s split disagreed by a permutation `π` of the block's
leaves. Then `blockTuple` puts the path to leaf `π ℓ` where the carrier stores
leaf `ℓ`, and the conversion asks the kernel for
`.proj⃗ (path ℓ) scrut ≡ .proj⃗ (path (π ℓ)) scrut` — two *distinct* projection
paths applied to a **variable**. Neither is a redex, so neither reduces, and the
kernel refuses them unless the paths are the same path. Distinct leaves have
distinct paths by construction, so `π` is the identity or the recursor does not
typecheck. A silent permutation among same-typed fields is not available here
either.

The three walks that have to agree agree because they are one walk: `chainTy`,
`chainTuple` and this function all descend the telescope by
`rest.hasLooseBVar 0` and split the leaf range by
[`InductiveModels.blockSplit`], which is a function of the leaf count alone. -/
def blockFill (leaves : Array BlockLeaf) (paths vals : Array Expr) : Array Expr := Id.run do
  let mut vals := vals
  for l in [0:leaves.size] do
    if let some (idx, false, _) := leaves[l]! then
      vals := vals.set! idx paths[l]!
  return vals

/-- **The fields a constructor's chain reads through a slot**: boxed, and
named by nothing after them — not by a later field's type and not by the
result type. `tele` is the constructor's type with its `np` parameters still
bound or already instantiated; either way index `0` under a field's binder is
that field. This is the chain walkers' own question
(`rest.hasLooseBVar 0`), asked once for the whole telescope. -/
def chainSlotFields (tele : Expr) (np : Nat) (boxed : Array Bool) : Array Nat := Id.run do
  let mut cur := tele
  for _ in [0:np] do
    if let .forallE _ _ b _ := cur then cur := b
  let mut out := #[]
  for i in [0:boxed.size] do
    if let .forallE _ _ rest _ := cur then
      if boxed[i]! && !rest.hasLooseBVar 0 then out := out.push i
      cur := rest
  return out

/-- A spine rung the destructor descended through: its pair and the value it
holds, which is what rebuilds the chain above a slot. -/
structure ChainRung where
  ℓt : Level
  ℓi : Level
  st : Expr
  β : Expr
  value : Expr
  deriving Inhabited

/-- Where a boxed field that nothing later names is stored in the chain. -/
inductive SlotAt
  | leaf (l : Nat)
  | rung (r : Nat)
  | whole
  deriving Inhabited

/-- **A boxed field no later field names**, which the destructor hands to the
minor through the box's generic `boxFix` ([`InductiveModels.boxFixName`])
rather than by asking the kernel for its round trip. -/
structure ChainSlot where
  src : Nat
  ty : Expr
  at' : SlotAt
  path : Expr
  deriving Inhabited

/-- The ι rule of a constructor with such slots, as the destructor is asked to
prove it: the constructor's own field values at source indices, the rule's two
sides and their type. -/
structure ChainIota where
  fields : Array Expr
  lhs : Expr
  rhs : Expr
  α : Expr

/-- **The destructor's value once the fields are read**, and the one place a
boxed field's round trip is paid for.

Each slot `i` is a boxed field nothing later names. The minor is applied to the
unboxed value `b`, and its type then says `motive (ctor … b …)`, where the
constructor stores `box b`; the destructor owes `motive` of the value it read,
which stores `p`. The kernel would close that by converting `box (unbox p)` to
`p` — a round trip — so instead each slot goes through `boxFix`, which applies
the minor at `unbox p` and transports along `sec p`. The slots nest, the first
outermost: slot `i`'s motive rebuilds the chain with `box` of the earlier slots'
values, the variable at slot `i`, and the read values after it.

Given `iota?`, the same term is built at the constructor's own values and the
ι rule proved from it instead: one `boxFix_iota` per slot, chained by
transitivity, which is `rt` of each slot's box and never its conversion. -/
partial def chainFinish (v : Level) (eqi : EqInfo) (vals : Array Expr)
    (slots : Array ChainSlot) (rebuild : Array (Option Expr) → GenM Expr)
    (target : Expr → GenM Expr) (minorAt : Array Expr → GenM Expr)
    (iota? : Option ChainIota) : GenM Expr := do
  if slots.isEmpty then
    match iota? with
    | some io => return eqi.refl' v io.α io.lhs
    | none => return ← minorAt vals
  let fixN ← boxFixName
  let k := slots.size
  let parts := fun (i : Nat) => do
    let s := slots[i]!
    let n ← boxNode s.ty
    return (s, n, n.bty, n.box, n.unbox, ← boxSecOfNode n)
  -- The term at a prefix of slot values: `none` at the full prefix.
  let rec fixAll (pre : Array Expr) : GenM (Expr × Option (Expr × Expr)) := do
    let i := pre.size
    if i == k then
      let vs := (Array.range k).foldl (fun vs m => vs.set! slots[m]!.src pre[m]!) vals
      return (← minorAt vs, none)
    let (s, n, bt, bx, ubx, sec) ← parts i
    let boxedPre ← (Array.range i).mapM fun m => do
      boxValOf slots[m]!.ty pre[m]!
    let motive ← withLocalDeclD `z bt fun z => do
      let ov := (Array.range k).map fun m =>
        if m < i then some boxedPre[m]! else if m == i then some z else none
      mkLambdaFVars #[z] (← target (← rebuild ov))
    let minor ← withLocalDeclD `b s.ty fun bv => do
      mkLambdaFVars #[bv] (← fixAll (pre.push bv)).1
    let term := mkAppN (.const fixN [n.uT, n.uB, v])
      #[s.ty, bt, bx, ubx, sec, motive, minor, s.path]
    return (term, some (motive, minor))
  let some io := iota? | return (← fixAll #[]).1
  -- `lhs = X₁ = … = X_k ≡ rhs`, where `Xᵢ` is the term at the first `i` field
  -- values and each step is one slot's `boxFix_iota`.
  let trans := fun (a b c h1 h2 : Expr) =>
    transportAlong eqi .zero v io.α b c h2 h1 fun z => pure (eqi.mk' v io.α a z)
  let iotaN ← boxFixIotaName
  let values := slots.map fun s => io.fields[s.src]!
  let mut acc := eqi.refl' v io.α io.rhs
  for i' in [0:k] do
    let i := k - 1 - i'
    let (s, n, bt, bx, ubx, sec) ← parts i
    let (xi, some (motive, minor)) ← fixAll (values.extract 0 i)
      | badShape "a slot's boxFix term has no motive"
    let a := if i == 0 then io.lhs else xi
    let next := (← fixAll (values.extract 0 (i + 1))).1
    let inst := mkAppN (.const iotaN [n.uT, n.uB, v])
      #[s.ty, bt, bx, ubx, sec, ← boxRtOfNode n, motive, minor, values[i]!]
    acc ← trans a next io.rhs inst acc
  return acc

/-- The recursor's destructor for one chain: from `scrut : chain`, an
element of `target (wrap scrut)` — `wrap` embeds a suffix value into the
full tuple (the identity at the top) and `target` is `fun tup => M ⟨j̄,
tup⟩`. The minor is applied to the collected fields, each unboxed where the
plan boxed it.

`chain` is `scrut`'s type, [`InductiveModels.chainTy`] of `tele`, and it is
what every rung is read off ([`InductiveModels.chainRung`]): the walk down the
spine builds no type at all, because each rung's family already carries the
next rung's. The block underneath it is read by
[`InductiveModels.blockPaths`], and the fields land in `vals` at their
**source** index rather than in the order the storage binds them — which is the
whole of the bookkeeping the split costs, since the minor's telescope is the
source constructor's.

### Nothing here is eliminated: the spine is read like the block

The block stopped being eliminated at `da1e3f4`; the spine had the identical
defect one level up. Each rung emitted a `PSigma'.rec'` whose motive is
`fun s => target (wrap s)`, and `wrap` writes down every rung above it, so an
`m`-rung spine wrote itself `m` times and the kernel checked every copy — on top
of `m` calls to `target`, which spells out the whole model application. A record
with a dependent head is exactly the shape that pays it.

Now the descent is two primitive projections per rung: the stored value is
`.proj PSigma' 0 scrut` and the tail is `.proj PSigma' 1 scrut`. No motive, no
`wrap` application, no `target` call at any rung — `target` survives only for
the non-canonical pad below, which is the one place there is a term to state a
transport about.

**This asks the kernel for nothing `PSigma'.rec'` did not already ask it.**
`rec'` is not a kernel recursor: its body is `minor self.1 self.2` over
primitive projections ([`InductiveModels.ensurePSigmaPrime`]), well typed only
because `mk self.1 self.2 ≡ self`. Emitting it per rung bought the motive and
nothing else, since it δ-unfolds to the very application built here. What is
owed at the end is `chainTuple (paths scrut) ≡ scrut`: `PSigma'` structure eta
at each of the `m` rungs and `PProd'` structure eta at each of the block's
`n - 1` nodes, both genuine single-constructor, index-free inductives.

**The rungs are dependent and that is fine.** Unlike the block's, a rung's type
mentions the rungs before it — but the kernel's typing rule for `.proj` on a
dependent structure instantiates the second component's family at the *first
projection of the same value*, so `.proj 1 scrut` is typed at `β (.proj 0
scrut)`. Descending by projection therefore threads each rung's dependency at
the earlier rungs' own paths, definitionally, which is exactly the substitution
`rest.instantiate1` performs on the telescope below. Selection stays
definitional: these are the same paths [`InductiveModels.tightTowerProjs`] hands
the projection overrides, and those are gated on kernel conversion against the field's
intrinsic codomain before an owner may emit them.

### What still says rung `k` and leaf `k` are source field `k`

The recursor's ι rule was the old check: it is `Eq.refl` at the minor applied in
source order, so a mis-filled slot was a kernel rejection. **The conversion is
the same check, and on the same fields.** Suppose the fill and
[`InductiveModels.chainTy`]'s split disagreed by a permutation `π`. Then
`chainTuple` puts the path to field `π k` where the carrier stores field `k`,
and the conversion asks the kernel for
`.proj⃗ (path k) scrut ≡ .proj⃗ (path (π k)) scrut` — two *distinct* projection
paths applied to a **variable**. Neither is a redex, so neither reduces, and the
kernel refuses them unless the paths are the same path. Spine paths are
`.proj 0 (.proj 1)ᵏ`, distinct for distinct `k`; block paths are distinct by
[`InductiveModels.blockSplit`]. So `π` is the identity or the recursor does not
typecheck, and a silent permutation among same-typed fields is not available.
On the spine a permutation is additionally ill-typed — a rung whose type
mentions an earlier field cannot be offered that field's own path — but the path
argument alone decides it, and it is the one that does not need the fields'
types to be distinguishable.

The three walks that have to agree agree because they are one walk: `chainTy`,
`chainTuple` and this function all descend the telescope by
`rest.hasLooseBVar 0` and split the leaf range by
[`InductiveModels.blockSplit`], which is a function of the leaf count alone. -/
partial def chainDestruct (v : Level) (eqi : EqInfo) (pairs : Bool)
    (pad? : Option Pad) (boxed : Array Bool) (nf : Nat)
    (tele : Expr) (chain : Expr) (scrut : Expr)
    (wrap : Expr → Expr) (target : Expr → GenM Expr)
    (minorAt : Array Expr → Expr) (iota? : Option ChainIota := none)
    (noSlots : Bool := false)
    (vals : Array Expr := #[]) (i : Nat := 0)
    (leaves : Array BlockLeaf := #[]) (rungs : Array ChainRung := #[])
    (slots : Array ChainSlot := #[]) : GenM Expr := do
  -- The chain above the current point, rebuilt at the given rung values.
  let above := fun (rv : Array Expr) (z : Expr) =>
    wrap ((Array.range rungs.size).foldr (fun r acc =>
      let g := rungs[r]!
      psigmaMk g.ℓt g.ℓi g.st g.β rv[r]! acc) z)
  let rungVals := fun (ov : Array (Option Expr)) => Id.run do
    let mut rv := rungs.map (·.value)
    for m in [0:slots.size] do
      if let (.rung r, some e) := (slots[m]!.at', ov[m]!) then rv := rv.set! r e
    return rv
  if nf == 0 then
    let leaves := if pad?.isSome then leaves.push none else leaves
    if leaves.isEmpty then badShape "a chain with no fields needs a pad"
    let n := leaves.size
    let paths := blockPaths (Array.replicate n scrut) scrut 0 n
    let mut vals := blockFill leaves paths vals
    -- Every slot a leaf holds reads its value off the block; a selector reads
    -- it unboxed instead.
    let mut slots := slots
    for l in [0:n] do
      if let some (idx, true, t) := leaves[l]! then
        if noSlots then vals := vals.set! idx (← unboxValOf t paths[l]!)
        else slots := slots.push { src := idx, ty := t, at' := .leaf l, path := paths[l]! }
    -- **The pad, and the one place a chain can still transport.** A canonical
    -- pad costs nothing — the path that reaches it is defeq to the pad's
    -- canonical element, so the applied minor already has the target type and
    -- the conversion above closes at that leaf like any other. A
    -- [`InductiveModels.unitAt`] pad is discharged by transporting the applied
    -- minor along [`InductiveModels.unitAtUniq`], and on a constructor
    -- application that proof is a closed self-equality which K-like reduction on
    -- `Eq.rec` erases — ι stays `Eq.refl` on both. The block is rebuilt here and
    -- only here, because only here is there a term to state the transport about.
    let padFixed := match pad? with
      | some p => if p.canonical then paths else paths.set! (n - 1) p.canon
      | none => paths
    let rebuild := fun (ov : Array (Option Expr)) => do
      let mut ps' := padFixed
      for m in [0:slots.size] do
        if let (.leaf l, some e) := (slots[m]!.at', ov[m]!) then ps' := ps'.set! l e
      return above (rungVals ov) (← blockTuple chain ps' 0 n)
    let body ← chainFinish v eqi vals slots rebuild target (pure ∘ minorAt) iota?
    let some p := pad? | return body
    if p.canonical then return body
    if iota?.isSome then
      badShape "a chain with a non-canonical pad has no propositional ι rule"
    return ← transportAlong eqi v p.lv p.ty p.canon paths[n - 1]!
      (unitAtUniq eqi p.lv paths[n - 1]!) body
      (fun z => do target (above (rungVals #[]) (← blockTuple chain (paths.set! (n - 1) z) 0 n)))
  let .forallE _ t rest _ := tele | badShape "field telescope shorter than the field count"
  let bx := boxed[i]?.getD false
  if nf == 1 && pad?.isNone && leaves.isEmpty then
    if bx && !noSlots && !rest.hasLooseBVar 0 then
      let slots := slots.push { src := i, ty := t, at' := .whole, path := scrut }
      let rebuild := fun (ov : Array (Option Expr)) =>
        pure (above (rungVals ov) (ov[slots.size - 1]!.getD scrut))
      return ← chainFinish v eqi (vals.push default) slots rebuild target (pure ∘ minorAt) iota?
    let rv ← if bx then unboxValOf t scrut else pure scrut
    return ← chainFinish v eqi (vals.push rv) slots
      (fun ov => pure (above (rungVals ov) scrut)) target (pure ∘ minorAt) iota?
  if pairs && !rest.hasLooseBVar 0 then
    -- A block leaf: nothing is bound here, and the placeholder `vals` grows by
    -- one so that a field's slot is its source index throughout.
    return ← chainDestruct v eqi pairs pad? boxed (nf - 1) (rest.lowerLooseBVars 1 1) chain
      scrut wrap target minorAt iota? noSlots (vals.push scrut) (i + 1)
      (leaves.push (some (i, bx, t))) rungs slots
  let (ℓt, ℓi, st, β) ← chainRung chain
  -- **A spine rung is read, not eliminated.** The rung's binder name goes
  -- unused: the value is the projection path into `scrut`, and the recursion
  -- descends into the tail's own path rather than under a lambda.
  let xv := Expr.proj `PSigma' 0 scrut
  let slot := bx && !noSlots && !rest.hasLooseBVar 0
  let rv ← if slot then pure default else if bx then unboxValOf t xv else pure xv
  let slots := if slot then
      slots.push { src := i, ty := t, at' := .rung rungs.size, path := xv }
    else slots
  -- The tail's chain type, which the rung's family already carries: the
  -- descent happens at the very value the family abstracts, so this is what
  -- rebuilding the tail would have returned. It is the tail path's own type.
  let tailChain := (mkApp β xv).headBeta
  let tailTele := if slot then rest.lowerLooseBVars 1 1 else rest.instantiate1 rv
  chainDestruct v eqi pairs pad? boxed (nf - 1) tailTele tailChain
    (.proj `PSigma' 1 scrut) wrap target minorAt iota? noSlots (vals.push rv) (i + 1) leaves
    (rungs.push { ℓt, ℓi, st, β, value := xv }) slots

end InductiveModels
