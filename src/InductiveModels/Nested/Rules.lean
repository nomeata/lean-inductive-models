import InductiveModels.Nested.Gen

/-!
# The nested construction's ι rules

`Rule` is one ι rule of one generated recursor under construction, and `Move`
is where a packed position stands in the transport fold that proves it.
-/

open Lean Meta

namespace InductiveModels
/-! ## The ι rules -/

/-- Where one packed position of a rule stands in the transport fold. -/
inductive Move where
  /-- At `unpackᵢ (packᵢ f)`, where the reduced left-hand side leaves it. -/
  | source
  /-- At `f`, having been transported along `unpackPackᵢ f`. -/
  | target
  /-- At the motive's own variable, along the motive's own equation — the
  position this step of the fold is abstracting. -/
  | abstract (x hx : Expr)
  deriving Inhabited

/-- **One ι rule of `T._model.rec_k`, under construction.**

The theorem's binder telescope is the recursor's own — `p⃗ M⃗ S⃗` — with the
constructor's **export-side** fields on the end, so a rule of `rec_1` binds
`List Tree`'s fields and not the mimic's. -/
structure Rule where
  g : Gen
  k : Nat
  v : Level
  ps : Array Expr
  motives : Array Expr
  minors : Array Expr
  /-- This constructor's minor, in the block-wide order. -/
  minorIx : Nat
  /-- The export-side constructor as it is applied: `T._model.ctor_j` at the
  root, or the real container's constructor at a mimic. -/
  head : Name
  headLevels : List Level
  headPrefix : Array Expr
  /-- The export-side fields the theorem binds, and their types. -/
  fields : Array Expr
  extTys : Array Expr
  /-- The block constructor's name and its field types. -/
  bcn : Name
  blkTys : Array Expr
  /-- Which block member each field sits at, if any. -/
  mem : Array (Option Nat)
  /-- **Which fields the block holds at a mimic, and how deep under a binder.**
  Wider than `mem`, which sees only a field at a member *directly*: `HTree`'s
  `(N → List HTree)` is at mimic 1 under one binder and `mem` calls it nothing.
  These are the positions the fold moves, and the ones a binder makes cost a
  `funext`. -/
  packed : Array (Option (Nat × Nat))
  /-- Which member each field's **induction hypothesis** is at. Wider than
  `mem`: a field of type `∀ x⃗, B₀ …` has one and sits at no member. -/
  ihAt : Array (Option Nat)
  /-- The type the minor declares for each field's induction hypothesis. Read
  off the minor rather than rebuilt, so the binder names the model writes are
  the recursor's own and the statement compares equal to the export's rule. -/
  ihTys : Array (Option Expr)
  /-- The fields at a **mimic**, in order — the positions the fold moves. -/
  moving : Array Nat

namespace Rule

def n (r : Rule) : Nat := r.fields.size

/-- The export-side constructor applied to `vals`. -/
def build (r : Rule) (vals : Array Expr) : Expr :=
  mkAppN (.const r.head r.headLevels) (r.headPrefix ++ vals)

/-- `T._model.rec_m p⃗ M⃗ S⃗ idx⃗ x`. The indices are read off `x`'s own type — at
the export's side that is `Rₘ._model.self p⃗ idx⃗` — and never rebuilt. -/
def recCall (r : Rule) (m : Nat) (x : Expr) : GenM Expr := do
  let idxs := r.g.idxOf m (← ftyp x)
  return mkAppN (.const (r.g.recName m) (r.g.recLs r.v))
    (r.ps ++ r.motives ++ r.minors ++ idxs ++ #[x])

/-- `Mₘ` applied to the indices `x`'s type carries, ready for `x` itself. -/
def motiveOf (r : Rule) (m : Nat) (x : Expr) : GenM Expr := do
  return mkAppN r.motives[m]! (r.g.idxOf m (← ftyp x))

/-- `p⃗ M''⃗ S''⃗` — everything a block recursor takes before its major. -/
def blkPrefix (r : Rule) : GenM (Array Expr) := do
  let bm ← r.g.blockMotives r.ps r.motives
  let bmin ← r.g.blockMinors r.ps r.motives r.minors r.v
  return r.ps ++ bm ++ bmin

/-- **A field's induction hypothesis, as the export's rule writes it.** At a
field sitting on a member it is `T._model.rec_m` at that field; at an
infinitary one — `FTree.branch : (N → FTree) → FTree` — it is
`fun x⃗ => T._model.rec_m … (f x⃗)`, and the binders come from the minor's own
declared hypothesis type so the names are the recursor's. -/
def ihFor (r : Rule) (x : Nat) : GenM (Option Expr) := do
  let some m := r.ihAt[x]! | return none
  let f := r.fields[x]!
  if (r.mem[x]!).isSome then return some (← r.recCall m f)
  let some ty := r.ihTys[x]! | badShape "an induction hypothesis with no declared type"
  forallTelescope ty fun xs _ =>
    return some (← mkLambdaFVars xs (← r.recCall m (mkAppN f xs)))

/-- `congrPack_o p⃗ ι⃗ l₀ l h`. -/
def congrPack (r : Rule) (o : Nat) (idxs : Array Expr) (l0 l h : Expr) : Expr :=
  mkAppN (.const (r.g.congrPackName o) r.g.us) (r.ps ++ idxs ++ #[l0, l, h])

/-- **The index vector a field at member `m` carries**, read off the field's
own *export-side* type — `Vec T._model.self ι⃗` — because the block's copy of
that type is at the block's own binders and would not name them. -/
def fieldIdx (r : Rule) (m x : Nat) : Array Expr := r.g.idxOf m r.extTys[x]!

/-- **A packed position's three terms**, under its binder telescope if it has
one: the round trip `fun x⃗ => unpackₒ (packₒ (f x⃗))`, the block recursor's
hypothesis at the packed field, and the retraction — closed with `funext` when
there is a binder and the bare retraction when there is not. -/
def packedAt (r : Rule) (x m nb : Nat) (blk : Array Expr) :
    GenM (Expr × Expr × Expr) := do
  let g := r.g
  let o := g.mimicOf m
  let at' := fun (res v : Expr) => do
    let idxs := g.idxOf m res
    let pk := g.call (g.packName o) r.ps idxs v
    return (g.call (g.unpackName o) r.ps idxs pk,
            mkAppN (g.blockRecAt m r.v) (blk ++ idxs ++ #[pk]),
            g.call (g.retractName o) r.ps idxs v)
  if nb == 0 then at' r.extTys[x]! r.fields[x]!
  else forallBoundedTelescope r.extTys[x]! (some nb) fun xs res => do
    let fx := r.fields[x]!.beta xs
    let (y, w, h) ← at' res fx
    return ((← mkLambdaFVars xs y).eta, ← mkLambdaFVars xs w, ← g.funextFor xs y fx h)

/-- `fun x⃗ => packₒ (val x⃗)` — a value at the *block's* side of a packed
position, which is where `T._model.ctor_j` holds it. -/
def packAt (r : Rule) (x m nb : Nat) (val : Expr) : GenM Expr :=
  Gen.underBinders nb r.extTys[x]! val fun _ res v =>
    return r.g.call (r.g.packName (r.g.mimicOf m)) r.ps (r.g.idxOf m res) v

/-- The hypothesis type a packed position's `Eq.rec` abstracts: `Mₘ ι⃗ xv` with
no binder, `∀ x⃗, Mₘ ι⃗ (xv x⃗)` with one. -/
def ihTypeAt (r : Rule) (x m nb : Nat) (xv : Expr) : GenM Expr := do
  if nb == 0 then return mkAppN r.motives[m]! ((r.g.idxOf m r.extTys[x]!).push xv)
  forallBoundedTelescope r.extTys[x]! (some nb) fun xs res =>
    mkForallFVars xs (mkAppN r.motives[m]! ((r.g.idxOf m res).push (xv.beta xs)))

/-- **The two sides at one stage of the fold** — the type they live at, the
left, and the right.

The left is the *reduced* left: the recursor unfolded, the block's ι rule fired
and the minor β-reduced, which at the root is a chain of transports over `pack`
and at a mimic is one transport of the whole constructor application. The right
is the rule, with each moved position's induction hypothesis at
`T._model.rec_m`. -/
def sides (r : Rule) (mv : Array Move) : GenM (Expr × Expr × Expr) := do
  let g := r.g
  let blk ← if r.moving.isEmpty then pure #[] else r.blkPrefix
  let mut srcVals : Array Expr := #[]
  let mut srcIhs : Array Expr := #[]
  let mut vals : Array Expr := #[]
  let mut ihs : Array Expr := #[]
  for x in [0:r.n] do
    let f := r.fields[x]!
    match r.packed[x]! with
    -- **A packed position, with or without a binder.** At `nb = 0` everything
    -- below writes no lambda for it.
    | some (m, nb) =>
      let (y, w, h) ← r.packedAt x m nb blk
      srcVals := srcVals.push y; srcIhs := srcIhs.push w
      match mv[x]! with
      | .source =>
        vals := vals.push y; ihs := ihs.push w
      -- Already moved: the value is the field and the hypothesis is
      -- `T._model.rec_m` at it, which δ-unfolds to exactly the transport the
      -- step below produced.
      | .target =>
        vals := vals.push f
        let some ih ← r.ihFor x | badShape "a packed position with no hypothesis"
        ihs := ihs.push ih
      -- Being moved: the value is the motive's own variable and the transport
      -- is along its equation. At `x := y` and `hx := Eq.refl` this ι-reduces
      -- back to `w`, which is what makes the previous stage this step's base.
      | .abstract xv hv =>
        let α := r.extTys[x]!
        if nb == 0 then
          let mot ← mkLambdaFVars #[xv, hv] (← r.ihTypeAt x m nb xv)
          ihs := ihs.push (g.eqi.recAt r.v (← ilevel α) α y mot w xv hv)
        else
          -- **Pointwise, because the other side is.** See
          -- [`InductiveModels.Gen.congrFunFor`].
          ihs := ihs.push (← forallBoundedTelescope α (some nb) fun xs res => do
            let ures ← ilevel res
            let yx := y.beta xs
            let idxs := g.idxOf m res
            let mot ← withLocalDeclD `z res fun z =>
              withLocalDeclD `hz (g.eqi.mk' ures res yx z) fun hz => do
                mkLambdaFVars #[z, hz] (mkAppN r.motives[m]! (idxs.push z))
            mkLambdaFVars xs (g.eqi.recAt r.v ures res yx mot (w.beta xs) (xv.beta xs)
              (← g.congrFunFor α y xv hv xs)))
        vals := vals.push xv
      -- `h` is unused here; the folds below take it from `packedAt` again.
      let _ := h
    | none =>
      match r.mem[x]! with
      | none =>
        srcVals := srcVals.push f
        vals := vals.push f
        -- **Infinitary at a *real* member, and so it does not move.** `pack`
        -- passes a field of type `∀ x⃗, Bₘ …` through untouched — the block
        -- types it at `Bₘ` where the export types it at the carrier, which is
        -- that by δ — so both sides hold it at `f` and the hypothesis is the
        -- same on both.
        if let some ih ← r.ihFor x then
          srcIhs := srcIhs.push ih; ihs := ihs.push ih
      -- A field at a **real** member does not move either.
      | some m =>
        let ih ← r.recCall m f
        srcVals := srcVals.push f; srcIhs := srcIhs.push ih
        vals := vals.push f; ihs := ihs.push ih
  let apply := fun (vs is : Array Expr) => mkAppN r.minors[r.minorIx]! (vs ++ is)
  let base := apply srcVals srcIhs
  let rhs := apply vals ihs
  let major := r.build vals
  let ty := mkApp (← r.motiveOf r.k major) major
  let lhs ←
    if g.isReal r.k then do
      -- A real member's minor lands at `M_k (T._model.ctor_j f⃗)`, which unfolds
      -- to `M_k (B_k.c (pack (unpack f⃗)))`, and the block hands it
      -- `M_k (B_k.c f⃗)`.
      let mut blLhs : Array Expr := #[]
      let mut blRhs : Array Expr := #[]
      let mut proofs : Array (Option Expr) := #[]
      for x in [0:r.n] do
        match r.packed[x]! with
        | some (m, nb) =>
          let o := g.mimicOf m
          let bl ← r.packAt x m nb srcVals[x]!
          let br ← r.packAt x m nb vals[x]!
          blLhs := blLhs.push bl
          blRhs := blRhs.push br
          -- **The congruence of `pack` at this position.** With no binder that
          -- is `congrPack_o`, a declaration; under one it abstracts the whole
          -- function and `congrOne` builds it inline.
          let cg := fun (l0 l h : Expr) => do
            if nb == 0 then
              return r.congrPack o (r.fieldIdx m x) l0 l h
            else
              g.congrOne r.extTys[x]! (← ityp bl) (r.packAt x m nb) l0 l h
          let pf : Option Expr ←
            match mv[x]! with
            | .source => pure none
            | .target => do
              let (_, _, h) ← r.packedAt x m nb blk
              pure (some (← cg srcVals[x]! vals[x]! h))
            | .abstract xv hv => do pure (some (← cg srcVals[x]! xv hv))
          proofs := proofs.push pf
        | none =>
          blLhs := blLhs.push vals[x]!
          blRhs := blRhs.push vals[x]!
          proofs := proofs.push none
      let rebuild := fun (a : Array Expr) => g.blockCtorAt r.k r.bcn r.ps a
      let m0 := mkAppN r.motives[r.k]! (g.idxOf r.k (← ftyp (rebuild blRhs)))
      g.foldValue r.v m0 r.blkTys blLhs blRhs proofs rebuild base
    else do
      -- A mimic's rule transports the **whole** constructor application: `recₖ`
      -- runs at `packᵢ (c f⃗)` and comes back along `unpackPackᵢ (c f⃗)`, whose
      -- reduct is the congruence of `c` over the packed positions.
      let a0 := r.build srcVals
      let b0 := r.build vals
      -- The occurrence **at the indices the constructor's own result carries**,
      -- read off `a0`'s type; the mimic's index telescope is the container's.
      let occ ← ftyp a0
      let ridx := g.idxOf r.k occ
      let mut proofs : Array (Option Expr) := #[]
      for x in [0:r.n] do
        match r.packed[x]! with
        | some (m, nb) =>
          proofs := proofs.push <| ←
            match mv[x]! with
            | .source => pure none
            | .target => do
              let (_, _, h) ← r.packedAt x m nb blk
              pure (some h)
            | .abstract _ hv => pure (some hv)
        | none => proofs := proofs.push none
      let uocc ← ilevel occ
      let p ← g.foldCongr occ r.extTys srcVals vals proofs r.build
      let mot ← withLocalDeclD `x occ fun xv =>
        withLocalDeclD `hx (g.eqi.mk' uocc occ a0 xv) fun hv =>
          mkLambdaFVars #[xv, hv] (mkAppN r.motives[r.k]! (ridx.push xv))
      pure (g.eqi.recAt r.v uocc occ a0 mot base b0 p)
  return (ty, lhs, rhs)

/-- **The equation**: `Eq (recₖ p⃗ M⃗ S⃗ (c f⃗)) (Sⱼ f⃗ ih⃗)`, at the recursor's own
motive universe. Free of the fold: each induction hypothesis is the model's
**constant** `T._model.rec_m` rather than its unfolding, because that is what
the export's own rule says and what the keying will read. -/
def statement (r : Rule) : GenM Expr := do
  let all := r.fields
  let mut ihs : Array Expr := #[]
  for x in [0:r.n] do
    if let some ih ← r.ihFor x then ihs := ihs.push ih
  let major := r.build all
  let ty := mkApp (← r.motiveOf r.k major) major
  return r.g.eqi.mk' r.v ty (← r.recCall r.k major) (mkAppN r.minors[r.minorIx]! (all ++ ihs))

/-- The proof: `Eq.refl` with nothing to move, and otherwise one `Eq.rec` on
`unpackPackᵢ f` per packed position, from a base where every one of them is
still at the source and both sides are the same term. -/
def value (r : Rule) : GenM Expr := do
  let g := r.g
  let mut mv := Array.replicate r.n Move.source
  let (ty0, _, rhs0) ← r.sides mv
  let mut acc := g.eqi.refl' r.v ty0 rhs0
  let blk ← if r.moving.isEmpty then pure #[] else r.blkPrefix
  for x in r.moving do
    let some (m, nb) := r.packed[x]! | badShape "a moving position with no member"
    let f := r.fields[x]!
    let (y, _, h) ← r.packedAt x m nb blk
    -- **The occurrence, or the function into it.** `extTys` is the export's own
    -- field type, which is `occₒ ι⃗` with no binder and `∀ x⃗, occₒ ι⃗` with one,
    -- and either way it is what this step abstracts.
    let occ := r.extTys[x]!
    let uocc ← ilevel occ
    -- The motive is the whole equation with this position abstracted; at
    -- `x := unpackᵢ (packᵢ f)` and `hx := Eq.refl` every transport it
    -- introduced ι-reduces away and what is left is the accumulator's own type.
    let mot ← withLocalDeclD `x occ fun xv =>
      withLocalDeclD `hx (g.eqi.mk' uocc occ y xv) fun hv => do
        let (ty2, l2, r2) ← r.sides (mv.set! x (.abstract xv hv))
        mkLambdaFVars #[xv, hv] (g.eqi.mk' r.v ty2 l2 r2)
    acc := g.eqi.recAt .zero uocc occ y mot acc f h
    mv := mv.set! x Move.target
  return acc

end Rule

end InductiveModels
