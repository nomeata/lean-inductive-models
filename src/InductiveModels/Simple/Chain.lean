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

/-- **The block taken apart**, one `PProd'.rec'` per node of the balanced tree.

`rebuild` carries this subtree's value back to the whole chain value the target
is stated about — the spine's `PSigma'.mk`s above and this subtree's `PProd'.mk`
ancestors — and `cont` is what the traversal owes once every leaf under this
subtree is bound: the leaves to its right, and finally the minor.

The right subtree's `rebuild` names the left subtree **rebuilt from its own
leaves**, because by the time it runs the left subtree's value has been taken
apart. That is where a right-nested block pays `O(n²)` and a balanced one pays
`O(n log n)`: the term a node has to write down is the size of its left sibling,
and the sum of those over a balanced tree is `n log n`. -/
partial def blockDestruct (v : Level) (eqi : EqInfo) (pad? : Option Pad)
    (leaves : Array BlockLeaf) (block value : Expr) (lo hi : Nat)
    (rebuild : Expr → Expr) (target : Expr → GenM Expr)
    (vals : Array Expr) (cont : Array Expr → Expr → GenM Expr) : GenM Expr := do
  if hi ≤ lo + 1 then
    match leaves[lo]! with
    | some (idx, bx, t) =>
      let rv ← if bx then unboxValOf t value else pure value
      return ← cont (vals.set! idx rv) value
    | none =>
      -- **The pad, and the one place a chain can still transport.** A canonical
      -- pad costs nothing — `value` is defeq to the pad's canonical element, so
      -- the applied minor already has the target type. A
      -- [`InductiveModels.unitAt`] pad is discharged by transporting the applied
      -- minor along [`InductiveModels.unitAtUniq`], and on a constructor
      -- application that proof is a closed self-equality which K-like reduction
      -- on `Eq.rec` erases — ι stays `Eq.refl` on both.
      let some p := pad? | badShape "internal: a block pad leaf with no pad"
      if p.canonical then return ← cont vals value
      return ← transportAlong eqi v p.lv p.ty p.canon value
        (unitAtUniq eqi p.lv value) (← cont vals p.canon)
        (fun z => target (rebuild z))
  let (ℓa, ℓb, α, β) ← blockNode block
  let mid := blockSplit lo hi
  let motive ← withLocalDeclD `s block fun s => do
    mkLambdaFVars #[s] (← target (rebuild s))
  let m ← withLocalDeclD `fst α fun a => withLocalDeclD `snd β fun b => do
    let body ← blockDestruct v eqi pad? leaves α a lo mid
      (fun z => rebuild (pprodMk ℓa ℓb α β z b)) target vals
      (fun vals' left =>
        blockDestruct v eqi pad? leaves β b mid hi
          (fun z => rebuild (pprodMk ℓa ℓb α β left z)) target vals'
          (fun vals'' right => cont vals'' (pprodMk ℓa ℓb α β left right)))
    mkLambdaFVars #[a, b] body
  return pprodRec v ℓa ℓb α β motive m value

/-- The recursor's destructor for one chain: from `scrut : chain`, an
element of `target (wrap scrut)` — `wrap` embeds a suffix value into the
full tuple (the identity at the top) and `target` is `fun tup => M ⟨j̄,
tup⟩`. The minor is applied to the collected fields, each unboxed where the
plan boxed it.

`chain` is `scrut`'s type, [`InductiveModels.chainTy`] of `tele`, and it is
what every rung is read off ([`InductiveModels.chainRung`]): the walk down the
spine builds no type at all, because each rung's family already carries the
next rung's. The block underneath it is bound by
[`InductiveModels.blockDestruct`], and the fields land in `vals` at their
**source** index rather than in the order the storage binds them — which is the
whole of the bookkeeping the split costs, since the minor's telescope is the
source constructor's. -/
partial def chainDestruct (v : Level) (eqi : EqInfo) (pairs : Bool)
    (pad? : Option Pad) (boxed : Array Bool) (nf : Nat) (tele : Expr) (chain : Expr)
    (scrut : Expr)
    (wrap : Expr → Expr) (target : Expr → GenM Expr)
    (minorAt : Array Expr → Expr) (vals : Array Expr := #[]) (i : Nat := 0)
    (leaves : Array BlockLeaf := #[]) : GenM Expr := do
  if nf == 0 then
    let leaves := if pad?.isSome then leaves.push none else leaves
    if leaves.isEmpty then badShape "a chain with no fields needs a pad"
    return ← blockDestruct v eqi pad? leaves chain scrut 0 leaves.size wrap target vals
      (fun vals _ => pure (minorAt vals))
  let .forallE x t rest _ := tele | badShape "field telescope shorter than the field count"
  let bx := boxed[i]?.getD false
  if nf == 1 && pad?.isNone && leaves.isEmpty then
    let rv ← if bx then unboxValOf t scrut else pure scrut
    return minorAt (vals.push rv)
  if pairs && !rest.hasLooseBVar 0 then
    -- A block leaf: nothing is bound here, and the placeholder `vals` grows by
    -- one so that a field's slot is its source index throughout.
    return ← chainDestruct v eqi pairs pad? boxed (nf - 1) (rest.lowerLooseBVars 1 1) chain
      scrut wrap target minorAt (vals.push scrut) (i + 1) (leaves.push (some (i, bx, t)))
  let (ℓt, ℓi, st, β) ← chainRung chain
  let motive ← withLocalDeclD `s chain fun s => do
    mkLambdaFVars #[s] (← target (wrap s))
  let m ← withLocalDeclD x st fun xv => do
    let rv ← if bx then unboxValOf t xv else pure xv
    -- The tail's chain type, which the rung's family already carries: the
    -- recursion descends at the very variable the family abstracts, so this is
    -- what rebuilding the tail would have returned. It is `s`'s type.
    let tailChain := (mkApp β xv).headBeta
    withLocalDeclD `s tailChain fun s => do
      let wrap' := fun (z : Expr) => wrap (psigmaMk ℓt ℓi st β xv z)
      mkLambdaFVars #[xv, s] (← chainDestruct v eqi pairs pad? boxed (nf - 1)
        (rest.instantiate1 rv) tailChain s wrap' target minorAt (vals.push rv) (i + 1) leaves)
  return psigmaRec v ℓt ℓi st β motive m scrut

end InductiveModels
