import Modelgen.Model
import Modelgen.LevelAlgebra
import Modelgen.Naming

/-!
# The model of a **plain mutual block**, generated

This is the second construction in this package. Given
`mutual inductive A … ; inductive B … end` with **no
nesting**, this emits ordinary Lean declarations: one *tag* enumeration carrying
each member's index telescope, one *single* inductive indexed by it, one carrier
per member, the block's constructors, one recursor per member and every one of
those recursors' ι rules as theorems. Every declaration goes through
`Environment.addDeclCore` with checking on.

The target shape can also be written by hand at a three-member block; doing so
answers the load-bearing question — *are the ι rules definitional?* — before
any generator is involved.

## Why this is not [`Modelgen.iso`] at zero mimics

`Modelgen.iso` models a **nested** declaration by specialising it into a mutual
block of `r + m` members and then proving the export's recursors over *that*.
Set `m = 0` and the specialised block is the declaration itself, renamed: the
model is the identity, and a consumer that could not take a mutual block still
cannot. The two constructions answer different questions — one removes
*nesting* and keeps mutuality, this one removes **mutuality** — and they are
related only through the interface they present, which is deliberately the
same one minus the rows that are about mimics.

## The encoding

For a block `R₀ … R_{r−1}` sharing a parameter telescope `p⃗` and a resultant
sort `Sort u`, where member `k` carries its own index telescope `ι⃗ₖ`:

```text
inductive T._model._impl.tag p⃗ : Sort W
inductive T._model._impl.aux p⃗ : tag p⃗ → Sort u
def R_k._model                 : ∀p⃗ ι⃗ₖ, Sort u := fun p⃗ ι⃗ₖ => aux p⃗ (tag.k p⃗ ι⃗ₖ)
def R_k.ctor._model            : <its own type> := fun p⃗ f⃗ => aux.k.c p⃗ f⃗
def R_k.rec._model             : <R_k.rec's> := fun p⃗ M⃗ S⃗ ι⃗ₖ t =>
                                   aux.rec p⃗ (tag.rec p⃗ (fun t => aux p⃗ t → Sort v) M⃗)
                                            S⃗ (tag.k p⃗ ι⃗ₖ) t
theorem R_k.rec._model.iota_j  : <R_k.rec's rule j> := Eq.refl _
```

Four things make it work, and each is load-bearing:

* **The tag is an *index* of `aux`, not a parameter.** It varies from
  constructor to constructor, which is what a parameter may not do.
* **Each member's indices live inside its tag constructor, so `aux` has exactly
  one index.** The members are then not required to agree on their index
  telescopes — the way the kernel *does* require them to agree on their
  parameters and their sort. A block whose members are unindexed is the case
  where every tag constructor is nullary; there is one path and nothing
  branches.
* **The minors are passed through untouched.** `aux.rec`'s minor for `aux.k.c`
  wants `Mot (tag.k p⃗ ι⃗) (aux.k.c p⃗ f⃗)`, and the minor in hand has type
  `Mₖ ι⃗ (C._model p⃗ f⃗)`. Those are δι-equal — `Mot (tag.k p⃗ ι⃗)` reduces
  to `Mₖ ι⃗` by `tag`'s own ι rule, and `ctor_j` δ-unfolds to `aux.k.c` — so no
  transport is built and none is needed.
* **Every `R_k._model` hands `aux.rec` the same motive and the same
  minors**, differing only in the tag. That is why the induction hypothesis a
  rule produces is *literally* what `R_m._model` unfolds to, and why the ι
  theorems are `Eq.refl` rather than a transport.

## The one number that is not read off the declaration

**`W`, the sort the tag lives at.** Its constructors carry the members' index
*values* as fields, so the kernel checks `sⱼ ≤ W` for every index type's own
sort `sⱼ` — and an index of type `N` is at `Sort 1` only because `N`'s
declaration says so. Every `sⱼ` is therefore obtained from `Meta.getLevel` on
the index's type *in scope*, and

```text
W = max 1 s₁ … s_k     over every member's index types
```

It is an over-approximation and does not need to be exact: nothing constrains an
index type's sort from above. The `1` is not padding — the tag's recursor has to
eliminate into `Sort (imax u (v+1))`, which a `Prop`-valued tag could not — and
a block with no indices gets `Sort 1` on the nose.

The cheap guess is `W = 1` and it is right on every shape but one: a constructor
that binds an index as a field forces `sⱼ ≤ u`, and a `Prop`-valued family's
indices are usually `N`. The escape is a **`Prop`-valued family indexed by a
large type**, represented by `SA`/`SB`/`SC` in
`test/fixtures/modelgen/mutual_index.lean`.

## Where the statements come from, and what that costs the oracle

A nested declaration's model states its recursors by reading them off the
**specialised block's** recursors, which Lean minted from a genuinely different
inductive; the recursor audit then compares those against the export's own and
is a real check. A plain mutual block has no second inductive: `aux.rec`
is not `R_k.rec` at any renaming. So the recursors and the ι rules here are the
**export's own, restored** — read off the recursor Lean minted for the input's
block, with the members, their constructors and their recursors rewritten to the
model's names ([`Modelgen.modelTable`]) and nothing else.

That makes the audit's *recursor type* comparison true by construction here.
What is
**not** vacuous, and is where this construction's correctness actually lives:

* **oracle 1, the kernel.** `R_k._model` is checked *at the export's own
  declared type*, so the tag/aux encoding really does implement that recursor;
  and each ι theorem is checked at the export's own rule with `Eq.refl` as its
  proof, so the rule really is definitional in the model.
* **oracle 3's ι half.** [`Modelgen.checkModel`] rebuilds each ι statement
  through its own telescope walk — opening the recursor's binders, reading the
  index vector off the major's inferred type — and compares it syntactically
  with the one emitted here, which is built by a different walk in this file.
  A key filed under the wrong constructor, a level list off by a motive
  universe, or a rule count that does not match the recursor's is caught there.
-/

open Lean Meta

namespace Modelgen

/-- How many leading `∀` binders an expression has, **syntactically**. No
`whnf`: every telescope peeled here is one the export wrote as a literal
`Π`-nest, and unfolding a carrier to find another binder would be a different
question. -/
def numForalls : Expr → Nat
  | .forallE _ _ b _ => numForalls b + 1
  | _ => 0

/-- Open one member's **index** telescope at the block's parameter `fvar`s.

A separate definition rather than a `let` in [`Modelgen.mutualIso`] because it
is used at three different result types and a `do`-bound lambda does not
generalise over them. -/
def withMemberIndices (memberTy : Expr) (ni : Nat) (ps : Array Expr)
    (k : Array Expr → GenM α) : GenM α := do
  forallBoundedTelescope (← instForall memberTy ps) (some ni) fun idxs _ => k idxs

/-- The model of one plain mutual block, or the shape that stopped it.

`all` is the export's own `all`, in the export's order; `memberTys` and
`exportCtors` are that member's declared type and its constructors, in the same
order. **The export's block must already be installed**: the recursors this
restates are the ones Lean minted for it, and there is nothing else to read them
off (see the header).

The whole of the checker interaction is [`Modelgen.addChecked`], once per
generated declaration. Nothing is emitted unchecked. -/
def mutualIso (all : Array Name) (lparams : List Name) (np : Nat)
    (memberTys : Array Expr) (exportCtors : Array (Array (Name × Expr)))
    (reserved : Std.HashSet Name) (buildRoot? : Option Name := none) : GenM Iso := do
  let us := lparams.map Level.param
  let r := all.size
  unless r ≥ 2 && memberTys.size == r && exportCtors.size == r do
    badShape "not a mutual block"
  let root := all[0]!
  let buildRoot := buildRoot?.getD root
  -- Tag, auxiliary carrier and their constructors are implementation details.
  -- Only names obtained directly from an exported declaration through
  -- `Modelgen.Naming` are public contract slots.
  let buildCarrier := Naming.modelName buildRoot
  let exactCarrier := Naming.modelName root
  let impl := Name.str buildCarrier "_impl"
  let tagN := Name.str impl "tag"
  let auxN := Name.str impl "aux"
  let tagCtorN := fun (k : Nat) => Name.num tagN k
  -- `T._model._impl.aux.k.<last component of the original>`. The member index is in
  -- the name because two members of one block may have constructors whose last
  -- components agree — `A.mk` beside `B.mk` is the common case — and the
  -- constructors of every member live on one inductive here.
  let auxCtorN := fun (k : Nat) (cn : Name) => Name.str (Name.num auxN k) (lastStr cn)
  let selfNames := all.map fun n =>
    Naming.modelName (Naming.relocateSource root buildRoot n)
  let ctorN := fun n =>
    Naming.modelName (Naming.relocateSource root buildRoot n)
  let exportRecs := (Array.range r).map (exportRecName all)
  let recN := fun (k : Nat) =>
    Naming.modelName (Naming.relocateSource root buildRoot exportRecs[k]!)
  let iotaN := fun (k j : Nat) =>
    Naming.iotaName (Naming.relocateSource root buildRoot exportRecs[k]!) j
  let ruleKN := fun (k : Nat) =>
    Naming.ruleKName (Naming.relocateSource root buildRoot exportRecs[k]!)

  -- Public collisions are an atomic property of the declaration-local naming
  -- table.  Census the whole table before emitting even implementation
  -- support, including every recursor rule rather than discovering an occupied
  -- iota name halfway through generation.
  let recRuleInfo ← exportRecs.mapM fun recursor => do
    let .recInfo info ← constInfo recursor | badShape s!"{recursor} is not a recursor"
    return (info.rules.length, info.k)
  let publicTable := Id.run do
    let mut table := Naming.Table.empty
    for member in all do table := table.addDeclaration .typeFormer member
    for ctors in exportCtors do
      for (ctor, _) in ctors do table := table.addDeclaration .constructor ctor
    for k in [0:r] do
      table := table.addRecursor exportRecs[k]! recRuleInfo[k]!.1
      if recRuleInfo[k]!.2 then table := table.addMetadata .ruleK exportRecs[k]!
    return table
  let occupied := reserved.fold (fun names name => names.push name) #[]
  let census := publicTable.collisionCensus occupied
  if let some name := census.taken[0]? <|> census.duplicateRequirements[0]? then
    declineWith (.nameTaken name)
  for name in publicTable.requiredNames do
    if (← getEnv).constants.contains name then declineWith (.nameTaken name)

  -- **The whole file, not just the prefix replayed so far.** A model may not
  -- take a name the input introduces later;
  -- `test/fixtures/modelgen/nested_keying.lean` is why the guard looks at
  -- `reserved` and not only at the
  -- environment.
  let taken : Name → GenM Unit := fun n => do
    let exact := if buildCarrier.isPrefixOf n then n.replacePrefix buildCarrier exactCarrier else n
    if reserved.contains exact || (← getEnv).constants.contains exact then
      declineWith (.nameTaken exact)
    if buildRoot != root && (reserved.contains n || (← getEnv).constants.contains n) then
      declineWith (.nameTaken n)
  taken tagN
  taken auxN
  for k in [0:r] do
    taken (tagCtorN k)
    for (cn, _) in exportCtors[k]! do taken (auxCtorN k cn)
  -- The environment also contains declarations generated earlier in a
  -- composed run, which are not part of the input's `reserved` set.
  for name in publicTable.requiredNames do taken name

  -- Each member's index count and resultant sort. **Every member's sort, not
  -- just the first's**: the kernel requires them to agree and the encoding
  -- writes `aux` at the one it read.
  let sortOf : Expr → GenM (Nat × Level) := fun t => do
    let mut cur := t
    for _ in [0:np] do
      match cur with
      | .forallE _ _ b _ => cur := b
      | _ => badShape "a block member has fewer binders than the block has parameters"
    let mut ni := 0
    repeat
      match cur with
      | .forallE _ _ b _ => cur := b; ni := ni + 1
      | _ => break
    let .sort u := cur | badShape "a block member does not land in a sort"
    return (ni, u)
  let shapes ← memberTys.mapM sortOf
  let nidx := shapes.map (·.1)
  let u := shapes[0]!.2
  -- **Compared up to provable equality and not syntactically**, which is not a
  -- nicety: the composition pass hands this Lean's own nested specialisations,
  -- and Lean writes a mimic's sort as the container's own level expression
  -- instantiated at the occurrence. Those agree with the declaration's without
  -- being the same term — `Lean.PrefixTreeNode`'s block has `(max u v)+1`
  -- beside `max (u+1) ((max u v)+1)`, and `Lean.PersistentHashMap.Node`'s has
  -- `(max u v)+1` beside `max (max (u+1) (v+1)) ((max u v)+1)`. Both are the
  -- same level and a syntactic `==` says otherwise; five of Mathlib's 41
  -- declined on it before this read `isLevelDefEq`. An input `mutual` block
  -- cannot show it, because Lean's elaborator makes the members agree on the
  -- nose — so this is a shape only the composition reaches.
  for k in [0:r] do
    unless ← LevelAlgebra.isLevelDefEqComplete shapes[k]!.2 u do
      badShape s!"a mutual block whose members land at different sorts \
        ({all[0]!} at {u}, {all[k]!} at {shapes[k]!.2})"

  -- The block's parameter telescope, opened once off the first member. The
  -- kernel has already required the members to agree on it, so every index
  -- telescope below is read at *these* fvars.
  let withParams := fun {α : Type} (k : Array Expr → GenM α) =>
    forallBoundedTelescope memberTys[0]! (some np) fun ps _ => k ps
  let withIdx := fun {α : Type} (m : Nat) (ps : Array Expr) (k : Array Expr → GenM α) =>
    withMemberIndices memberTys[m]! nidx[m]! ps k

  let (eqi, eqDecls) ← ensureEq reserved
  let mut out : Array Declaration := eqDecls
  let spliced : Array Name := eqDecls.flatMap (·.getNames.toArray)

  -- ── 1. the tag ─────────────────────────────────────────────────────────
  --
  -- One constructor per member, carrying **that member's own index telescope**
  -- as its fields. A block whose members are unindexed gets the enumeration
  -- this would be without them, every constructor nullary; that is the
  -- degeneracy and not a branch.
  let tagCtorTys ← withParams fun ps =>
    (Array.range r).mapM fun k => withIdx k ps fun idxs =>
      mkForallFVars (ps ++ idxs) (mkAppN (.const tagN us) ps)
  -- `W`: see the header. Read off each index type *in scope*, because an index
  -- type may mention a parameter or an earlier index.
  let idxSorts ← withParams fun ps =>
    (Array.range r).mapM fun k => withIdx k ps fun idxs => idxs.mapM fun i => do ilevel (← ityp i)
  let bigW := (idxSorts.foldl (fun w ls => ls.foldl mkLevelMax' w) (Level.succ .zero)).normalize
  let tagTy ← withParams fun ps => mkForallFVars ps (.sort bigW)
  let tagDecl := Declaration.inductDecl lparams np
    [{ name := tagN, type := tagTy
       ctors := (Array.range r).toList.map fun k =>
         { name := tagCtorN k, type := tagCtorTys[k]! } }] false
  addChecked tagDecl
  out := out.push tagDecl

  -- ── 2. the carrier, as one inductive over the tag ──────────────────────
  --
  -- `R_m p⃗ ι⃗` becomes `aux p⃗ (tag.m p⃗ ι⃗)`, everywhere. The member's index
  -- *values* become the tag constructor's arguments, which is the whole of the
  -- generalisation: `aux` has one index and a member with no indices
  -- contributes `aux p⃗ (tag.m p⃗)`.
  let toAux ← withParams fun ps => do
    let mut t : Std.HashMap Name (Nat × Expr) := {}
    for m in [0:r] do
      let e ← withIdx m ps fun idxs => do
        let tagApp := mkAppN (.const (tagCtorN m) us) (ps ++ idxs)
        return (mkAppN (.const auxN us) (ps.push tagApp)).abstract (ps ++ idxs)
      t := t.insert all[m]! (np + nidx[m]!, e)
    return t
  let auxTy ← withParams fun ps =>
    withLocalDeclD `t (mkAppN (.const tagN us) ps) fun t =>
      mkForallFVars (ps.push t) (.sort u)
  let mut auxCtors : Array Constructor := #[]
  for k in [0:r] do
    for (cn, cty) in exportCtors[k]! do
      let ty := restore toAux cty
      -- Every occurrence of a member inside a constructor's type is a **full**
      -- application to the parameters and the indices — the kernel has already
      -- required it — so the rewrite is total. A partial application is a shape
      -- that cannot arise; it is checked anyway, because "cannot arise" is a
      -- property of a check in another file.
      if mentionsAny all ty then
        badShape s!"{cn} mentions a block member at fewer arguments than it declares"
      auxCtors := auxCtors.push { name := auxCtorN k cn, type := ty }
  let auxDecl := Declaration.inductDecl lparams np
    [{ name := auxN, type := auxTy, ctors := auxCtors.toList }] false
  addChecked auxDecl
  out := out.push auxDecl

  -- ── 3. the carriers, one per member ────────────────────────────────────
  --
  -- `⟦R_k⟧ := ⟦R_k._model⟧` is the keying, and it is per member: `A.rec`
  -- and `B.rec` are distinct recursors over distinct majors and a consumer keys
  -- `⟦A⟧` and `⟦B⟧` separately.
  for k in [0:r] do
    let val ← withParams fun ps => withIdx k ps fun idxs =>
      mkLambdaFVars (ps ++ idxs)
        (mkAppN (.const auxN us) (ps.push (mkAppN (.const (tagCtorN k) us) (ps ++ idxs))))
    let d := Declaration.defnDecl
      { name := selfNames[k]!, levelParams := lparams, type := memberTys[k]!, value := val
        hints := ← hintsFor val, safety := .safe }
    addChecked d
    out := out.push d

  let toSelf : Std.HashMap Name (Nat × Expr) :=
    (Array.range r).foldl (fun m k => m.insert all[k]! (0, .const selfNames[k]! us)) {}

  -- ── 4. the block's own constructors ────────────────────────────────────
  --
  -- **Flattened over the members in the export's `all` order**, which is the
  -- order the block's minors arrive in. `fun p⃗ f⃗ => aux.k.c p⃗ f⃗` typechecks
  -- because the field types differ from `aux.k.c`'s only by δ on the carriers
  -- just defined.
  let mut ctors : Array (Name × Name) := #[]
  for k in [0:r] do
    for (cn, cty) in exportCtors[k]! do
      let ty := restore toSelf cty
      let val ← forallBoundedTelescope ty (some (numForalls cty)) fun bs _ =>
        mkLambdaFVars bs (mkAppN (.const (auxCtorN k cn) us) bs)
      let d := Declaration.defnDecl
        { name := ctorN cn, levelParams := lparams, type := ty, value := val
          hints := ← hintsFor val, safety := .safe }
      addChecked d
      out := out.push d
      ctors := ctors.push (cn, ctorN cn)

  -- The restore table every statement below is written with. It is
  -- [`Modelgen.checkModel`]'s own, built from the `Iso` this is on the way to
  -- returning — the recursor names are all that is read out of it here and they
  -- are known before any of them exists.
  let recs := (Array.range r).map recN
  let tbl := modelTable (← getEnv) all
    { decls := #[], levelParams := lparams, members := #[tagN, auxN], selfNames
      numAll := r, ctors, recs, iotas := #[], spliced := #[] }

  -- ── 5. one recursor per member ─────────────────────────────────────────
  --
  -- The tag's recursor eliminates into an arbitrary sort — the tag is at
  -- `Sort W` with `W ≥ 1`, so it is a `Type` at every instantiation — and the
  -- carrier's may or may not, which is a question about *one* `Prop` inductive
  -- and not about the block. Both are read here and neither is assumed.
  let tagRecN := Name.str tagN "rec"
  let auxRecN := Name.str auxN "rec"
  let .recInfo trv ← constInfo tagRecN | badShape s!"{tagRecN} is not a recursor"
  unless trv.levelParams.length == lparams.length + 1 do
    badShape s!"{tagRecN} does not eliminate into an arbitrary sort"
  let .recInfo arv ← constInfo auxRecN | badShape s!"{auxRecN} is not a recursor"
  let auxLarge ←
    if arv.levelParams.length == lparams.length + 1 then pure true
    else if arv.levelParams.length == lparams.length then pure false
    else badShape s!"{auxRecN} carries the level parameters {arv.levelParams}"
  let nc := ctors.size
  let mut recInfos : Array (Nat × Level × List Name × Expr) := #[]
  for k in [0:r] do
    let ern := exportRecName all k
    let .recInfo rv ← constInfo ern | badShape s!"{ern} is not a recursor"
    unless rv.numMotives == r do
      badShape s!"{ern} has {rv.numMotives} motives where the block has {r} members"
    unless rv.numMinors == nc do
      badShape s!"{ern} has {rv.numMinors} minors where the block has {nc} constructors"
    unless rv.numIndices == nidx[k]! do
      badShape s!"{ern} has {rv.numIndices} indices where the member has {nidx[k]!}"
    -- **A block that eliminates only into `Prop` has no motive universe at
    -- all**, and then every level list here is the declaration's own. Read off
    -- the recursor and never off the sort: `Eq` is `Prop`-valued and *does*
    -- support large elimination.
    let large := rv.levelParams.length == lparams.length + 1
    let v := if large then Level.param rv.levelParams[0]! else Level.zero
    unless (if large then rv.levelParams.tail! else rv.levelParams) == lparams do
      badShape s!"{ern} carries the level parameters {rv.levelParams}"
    let ty := restore tbl rv.type
    let val ← forallBoundedTelescope ty (some (np + r + nc + nidx[k]! + 1)) fun bs _ => do
      let ps := bs.extract 0 np
      let motives := bs.extract np (np + r)
      let minors := bs.extract (np + r) (np + r + nc)
      let idxs := bs.extract (np + r + nc) (bs.size - 1)
      let major := bs[bs.size - 1]!
      -- The packed motive, `fun (t : tag p⃗) => aux p⃗ t → Sort v`, folded over
      -- the tag. Its body has no index telescope in front of it — the indices
      -- are inside the tag — so it lives at `imax u (v+1)`, and that is the
      -- level the tag's recursor runs at.
      let packed ← withLocalDeclD `t (mkAppN (.const tagN us) ps) fun t => do
        mkLambdaFVars #[t]
          (← mkArrow (mkAppN (.const auxN us) (ps.push t)) (.sort v))
      let w := (mkLevelIMax' u (mkLevelSucc v)).normalize
      let mot := mkAppN (.const tagRecN (w :: us)) ((ps.push packed) ++ motives)
      let auxLs := if auxLarge then v :: us else us
      -- **`aux.rec` is handed the same motive and the same minors by every
      -- member's recursor, and differs only in the tag.** That is what makes
      -- the induction hypothesis a rule produces literally what
      -- `R_m._model` unfolds to, and the ι theorems below `Eq.refl`.
      let tagApp := mkAppN (.const (tagCtorN k) us) (ps ++ idxs)
      mkLambdaFVars bs
        (mkAppN (.const auxRecN auxLs) (((ps.push mot) ++ minors).push tagApp |>.push major))
    let d := Declaration.defnDecl
      { name := recN k, levelParams := rv.levelParams, type := ty, value := val
        hints := ← hintsFor val, safety := .safe }
    addChecked d
    out := out.push d
    recInfos := recInfos.push (k, v, rv.levelParams, ty)

  -- ── 6. the ι rules ─────────────────────────────────────────────────────
  --
  -- One per rule the **installed** `R_k.rec` carries, in the order it carries
  -- them, keyed by the constructor that rule is filed under — so a consumer
  -- lines ι theorems up with rules by index and checks the key by name.
  --
  -- Every one of them is `Eq.refl`. That is the whole design: the encoding is
  -- arranged so that `R_k._model … (C._model p⃗ f⃗)` and the rule's
  -- own right-hand side reach the same normal form by δ and ι alone, so the
  -- generator proves nothing and the kernel decides everything.
  let mut iotas : Array (Nat × Name × Name) := #[]
  for (k, v, rlp, ty) in recInfos do
    let ern := exportRecName all k
    let .recInfo rv ← constInfo ern | badShape s!"{ern} is not a recursor"
    let recLs := if rlp.length == lparams.length + 1 then v :: us else us
    let ni := nidx[k]!
    let base := (Array.range k).foldl (fun a i => a + exportCtors[i]!.size) 0
    unless rv.rules.length == exportCtors[k]!.size do
      badShape s!"{ern} has {rv.rules.length} rules where {all[k]!} has \
        {exportCtors[k]!.size} constructors"
    for j in [0:rv.rules.length] do
      let rule := rv.rules[j]!
      let (cn, modelC) := ctors[base + j]!
      unless rule.ctor == cn do
        badShape s!"{ern}'s rule {j} is for {rule.ctor}, not {cn}"
      let nm := iotaN k j
      taken nm
      -- As in the simple route, the theorem telescope is part of the literal
      -- exported interface. The installed definition may have a βζ-normalized
      -- type, so walk the restored export constructor rather than reading the
      -- model constructor back from the environment.
      let modelCTy := restore tbl exportCtors[k]![j]!.2
      let d ← forallBoundedTelescope ty (some (np + r + rv.numMinors)) fun pre _ => do
        let ps := pre.extract 0 np
        let motiveK := pre[np + k]!
        let cty ← instForall modelCTy ps
        forallBoundedTelescope cty (some (numForalls modelCTy - np)) fun fields _ => do
          let major := mkAppN (.const modelC us) (ps ++ fields)
          let mas := (← ityp major).getAppArgs
          let idxs := mas.extract (mas.size - ni) mas.size
          let lhs := mkAppN (.const (recN k) recLs) ((pre ++ idxs).push major)
          -- The rule's own right-hand side, at the model's names. Lean states
          -- it as `fun p⃗ M⃗ S⃗ f⃗ => …`, which is this telescope exactly.
          let rhs := (restore tbl rule.rhs).beta (pre ++ fields)
          let α := mkAppN motiveK (idxs.push major)
          let tel := pre ++ fields
          let proposition := eqi.mk' v α lhs rhs
          let some fieldsType := closeForallsExact? cty fields proposition
            | badShape s!"{modelC}'s exported telescope has fewer fields than its installed type"
          let some theoremType := closeForallsExact? ty pre fieldsType
            | badShape s!"{ern}'s exported telescope is shorter than its recursor prefix"
          return Declaration.thmDecl
            { name := nm, levelParams := rlp
              type := theoremType
              value := ← mkLambdaFVars tel (eqi.refl' v α lhs) }
      addChecked d
      out := out.push d
      iotas := iotas.push (k, cn, nm)

  let mut ruleKs : Array (Name × Name) := #[]
  for (k, _, rlp, _) in recInfos do
    let ern := exportRecs[k]!
    let .recInfo rv ← constInfo ern | badShape s!"{ern} is not a recursor"
    if rv.k then
      unless rv.rules.length == 1 do badShape s!"{ern} is K-like with {rv.rules.length} rules"
      let nm := ruleKN k
      taken nm
      let iotaType? := out.findSome? fun declaration => match declaration with
        | .thmDecl value => if value.name == iotaN k 0 then some value.type else none
        | _ => none
      let some iotaType := iotaType?
        | badShape s!"the K-like recursor {ern} has no iota theorem"
      let d ← ruleKDecl eqi rlp (rv.numParams + rv.numMotives + rv.numMinors) nm iotaType
      addChecked d
      out := out.push d
      ruleKs := ruleKs.push (ern, nm)

  let mut aliases := Naming.AliasMap.empty
  if buildRoot != root then
    aliases := Naming.AliasMap.forRetry (Naming.modelName buildRoot) (Naming.modelName root)
      (out.flatMap (·.getNames.toArray))
    for k in [0:r] do
      aliases := aliases.insert selfNames[k]! (Naming.modelName all[k]!)
      aliases := aliases.insert (recN k) (Naming.modelName exportRecs[k]!)
      if recRuleInfo[k]!.2 then
        aliases := aliases.insert (ruleKN k) (Naming.ruleKName exportRecs[k]!)
      for j in [0:exportCtors[k]!.size] do
        let cn := exportCtors[k]![j]!.1
        aliases := aliases.insert (ctorN cn) (Naming.modelName cn)
        aliases := aliases.insert (iotaN k j) (Naming.iotaName exportRecs[k]! j)
  return { decls := out, levelParams := lparams, members := #[tagN, auxN], selfNames
           numAll := r, ctors, recs, iotas, ruleKs, spliced, aliases }

end Modelgen
