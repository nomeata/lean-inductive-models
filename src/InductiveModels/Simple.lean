import InductiveModels.Mutual
import InductiveModels.Naming
import InductiveModels.Projection

-- The construction itself, in dependency order. This module is the facade:
-- `import InductiveModels.Simple` reaches every piece of it, exactly as it did
-- when the whole construction was one file.
import InductiveModels.Simple.Basis
import InductiveModels.Simple.Kit
import InductiveModels.Simple.Box
import InductiveModels.Simple.Chain
import InductiveModels.Simple.Church
import InductiveModels.Simple.Tuple
import InductiveModels.Simple.Graph
import InductiveModels.Simple.Plan
import InductiveModels.Simple.Erasure
import InductiveModels.Simple.WArm
import InductiveModels.Simple.RuleK
import InductiveModels.Simple.Tight
import InductiveModels.Simple.ArmFKit
import InductiveModels.Simple.Analysis
import InductiveModels.Simple.Interface

/-!
# The model of a **simple inductive from four primitives**, generated

The `--simple` construction removes the inductive declaration itself: a plain
(non-mutual, non-nested) inductive's carrier, constructors, recursor and ι
rules are emitted as ordinary `def`s and `theorem`s over a fixed basis of
primitive inductives —

    Eq   PSigma'   Nat   PUnit

— each spliced into the output at Lean's own shape if the input lacks it,
exactly as the existing prelude splice does for `Eq`. A consumer that
recognises the four interface names then needs to implement only the four
primitives (plus `Quot`), not general inductives — and, if the input reaches
[`InductiveModels.graphArm`], `Nonempty` and the `Classical.choice` axiom beside
them. `Nonempty` is not an additional primitive: it is `Classical.choice`'s own
domain, needs no exemption, and self-models by the Church route.

**`False` is not in the basis**: it is *derived* (Church `∀ p : Prop, p`,
with the `Sort w` eliminator from `0 = 1` plus a `Nat.rec`-built family to
transport along — [`InductiveModels.cfalseElim`]), so `False` models like any other
declaration. Its role is derived from **`PSigma'` and `PUnit`** as
`PSigma'.{0,u} (fun _ : p => PUnit.{u})`, a lift of a proposition to a bare
variable sort. Lean's elaborator refuses both exact-sort primitives at their
polymorphic declarations; Lean's kernel accepts them. Core crosses the same
line for `PUnit` and `PEmpty`, with
`set_option bootstrap.inductiveCheckResultingUniverse false`
(`Init/Prelude.lean:123,211`).

The Σ is the tight **`PSigma'`** — `{α : Sort u} → (α → Sort v) →
Sort (max u v)` — because `Subtype`, structures with `Prop` fields, and
every `Prop`-fibred pair in the constructions below need a Σ over `Sort`,
which a `Type`-only `Sigma` cannot give. `PUnit` supplies any deliberate
universe floor instead of baking `1` into every pair.

**`Acc` is not in the basis either, and used to be.** It was there for the
subsingleton-recursive **large** eliminator — the one grant the kernel makes
to a *declaration* that an emitted `def` does not inherit — and that grant is
now derived rather than assumed: [`InductiveModels.graphArm`] defines the recursion
by its *graph* and extracts the value, packaged with its graph proof, with
`Classical.choice`, which gives `Acc.rec`'s exact type with ι a theorem
instead of `rfl`. The derivation is uniform across the supported recursive
shapes, so `Acc` models like any other declaration now.

## The three routes, by the carrier's sort

**Type route** — carrier sort `w` never zero:

```text
T._model.self p⃗ := Σ'(n : Nat), F n        F : a Nat.rec cases tower
F ȷ̄  := the j-th constructor's field chain  (right-nested PSigma',
        boxed and padded to exactly Sort w when the levels demand it)
F n  := PSigma'.{0,w} ⊥ (fun _ => PUnit.{w}), for n ≥ #ctors
```

The recursor destructs the pair, cases on the tag with `Nat.rec` — the large
elimination the basis buys, and the reason `Nat` is in it — and then
destructs the chain. Two level repairs keep the chain at exactly `Sort w`:

A linearly recursive declaration with **no base constructor** is empty rather
than a degenerate case of this tower. Its carrier is the derived lift of `⊥`; each
constructor returns its direct recursive field, and the recursor and ι theorems
eliminate that empty value.  This is arm E below.

* **A pad** closes a level gap. At a `dsingOk` level it is `D`
  ([`InductiveModels.dsingAt`]); at any other level — a bare parameter in the gap,
  `PULift`'s shape — it is the derived lift of `⊤` ([`InductiveModels.unitAt`]), which
  exists at *every* level. **Both are definitionally canonical**, in the one
  sense the construction needs: every element is *defeq to the canonical
  one*, because the canonical one is a literal constructor application and
  eta-for-structures expands the other side against it. So no pad costs a
  transport. This is **not** the stronger claim that two *opaque* inhabitants
  collapse, which is false as a conversion — nothing eta-expands a variable
  on speculation, so the kernel refuses `x ≡ y` for two variables even though
  `x = y` is provable without an axiom.
  Direct kernel checks pin both claims and the gap between them. The `False`-Π
  singleton this replaced was not canonical in *either*
  sense and cost a `funext`.
* **A recursive box** ([`InductiveModels.boxTyOf`]) absorbs an `imax`: a Π-typed
  field's level is an `imax` chain (`Trans.mk`'s shape), and no pad subsumes
  an `imax` under a `max`.  Every exposed Π domain and codomain is recursively
  boxed, with each atomic leaf stored as `Σ'(_ : S), D 1`; all transformed
  codomains are therefore never `Prop`, so every `imax` normalizes to `max`.
  The minor receives the recursively unboxed value, and
  `unbox (box v) ≡ v` by βι, structure eta, proof irrelevance and function
  eta, with no transport.

**Church routes** — carrier sort literally `0`, or **maybe-zero**. One
construction serves both. The carrier is the impredicative Church encoding

```text
T._model.self p⃗ ι⃗ := ∀ C : (∀ ι⃗, Prop), k⃗ → C ι⃗
```

with `k_j` constructor `j`'s telescope, `T p⃗` replaced by `C` at its
recursive fields as well as at its result ([`InductiveModels.churchSwapAt`]); and at
a maybe-zero sort that same proposition under the derived tight-pair/PUnit lift, which puts it at
exactly `Sort w` for any `w`. The constructors are the folds, `up` of the
folds under a lift. There is **no transport between the two**: structure eta
gives `t ≡ up (down t)`, so `motive ι⃗ (up (down t))` and `motive ι⃗ t` are
convertible, and the maybe-zero route is the `Prop` route with a `down` at
one end and an `up` at the other.

Three recursors:

* **small elimination, no indices, no recursion** — the fold at
  `C := motive t`. Every minor's motive is closed by definitional proof
  irrelevance.
* **small elimination, otherwise** — the fold at the Church *pair*
  `Pair ι⃗ := ∀ D : Prop, (Self ι⃗ → (∀ h : Self ι⃗, motive ι⃗ h) → D) → D`
  ([`InductiveModels.pairArm`]). The plain fold does not serve here: a minor premise
  wants `motive ι⃗_j (c_j f⃗)` and the fold offers `C ι⃗_j`, which proof
  irrelevance stops identifying once the index moves; and a *recursive* minor
  premise needs a carrier element to apply itself to, which only the pair's
  first component supplies.
* **large elimination** — zero constructors: Church `⊥`'s `Sort v`
  eliminator. One constructor, no indices: the subsingleton rule that minted
  the recursor says every field is a proposition, so extract each by
  instantiating the encoding at the field's own type, sequentially, with
  proof irrelevance closing the motive. With indices, arm F stores the proof
  fields together with a packed index equation.  A pivot whose type moves is
  recovered by prefix equations in a left-to-right zipper before the final
  full-telescope equation; otherwise only the non-pivot subsequence is packed.
  At a maybe-zero sort, that proposition is carried under the derived lift and the
  same recursor uses `down` before extraction and `up` in its motive.

**Why the maybe-zero collapse is a model and not a cheat.** At a maybe-zero
sort the contract never forces two provably distinct elements: zero
constructors and the subsingleton shape large-eliminate and are subsingletons
anyway, and everything else there small-eliminates, so the motive lands in
`Prop` and cannot discriminate. The lift of a proposition is exactly the
right size — which is also why `PEmpty` models: the lift of `⊥` is *empty*, where
every type the old basis reached at a bare sort was inhabited.

The ordinary tuple and Church routes prove their ι theorems by `Eq.refl`.
On a Church route with a `Prop`-valued motive that is free for a reason
unrelated to reduction: both sides are proofs of one proposition.  Arm E
instead eliminates the constructor's empty recursive field; the graph arm
uses its single-valuedness because its `Classical.choice` recursor reduces to
nothing; and arm W applies the W core's propositional ι theorem.

## Routing boundaries

* **branching and infinitary recursion at a never-zero sort**
  (`Lean.ParserDescr`) routes to arm W. The tuple tower
  ([`InductiveModels.recSlotOf`]) remains deliberately linear; its refusal is the
  dispatcher signal that selects the W/path construction rather than a public
  generation decline.
* **indexed at a never-zero sort whose index erasure contains a nested
  occurrence** — an occurrence inside a container belongs to layer 1, not to
  the simple representation. A recursive occurrence under binders is carried,
  including when βζ-reduction first reveals those binders. **The head is read
  through [`InductiveModels.headNorm`]**, so a field written `(fun x => T p⃗ e⃗) k` — which is
  what Lean's nested specialisation leaves at a container's family parameter —
  is the bare occurrence it reduces to and not a binder; the same head
  normalization is required at layer 1. A field whose type mentions `T`
  **only inside a binder βζ discards** is not recursive at all; arm C uses the
  reduct for that internal skeleton field while preserving the public
  constructor type literally.
  An indexed family whose erasure is bare is no longer a refusal, **however
  many recursive fields its constructors have**: it is **arm C**
  ([`InductiveModels.primIso`]'s `armC`), a skeleton-plus-`good` construction standing
  on a spliced inductive rather than on a W-type — no axioms, no
  per-constructor currying glue, every ι rule `Eq.refl`.
  A *branching* erasure used to decline here, because the spliced skeleton
  branches too and nothing modelled a branching non-indexed inductive; arm W
  does, so the carve now carries every recursive slot and hands the skeleton
  to W.
* **a recursive subsingleton at mixed pivot and non-pivot indices** models by
  [`InductiveModels.graphArm`]. Its inversion carries one equality at the dependent
  tuple of non-pivots and transports the constructor step into the caller's
  fibre. Data-valued constants such as `mk : P 0 → P 0`, proof-valued
  expressions, and the `below` Lean mints beside recursive propositions all
  use this one construction; proof irrelevance makes the proof-only transports
  definitionally trivial.
* **a level gap no recursive box closes** — exposed Π structure is boxed at
  every depth, so a nested domain such as `((α → β) → β)` is supported. A
  genuinely opaque atomic type whose declared sort itself contains an `imax`
  can still leave no structure for boxing to transform. The complete planner
  may prove its padded level extensionally equal to the carrier, but the
  kernel's normal-form conversion can still reject that equality; this remains
  a checked decline rather than a level-normalizer relaxation.
* a field mentioning `T` other than as `∀ z⃗, T p⃗ e⃗` — a **nested**
  occurrence, which is layer 1's business.
* the four ordinary **inductive-basis primitives themselves** — the exemption
  that makes the construction well-founded. `Quot` is the fifth basis member,
  but is a kernel-special quotient declaration rather than an ordinary
  inductive owner.
-/

open Lean Meta

namespace InductiveModels

set_option maxRecDepth 2048 in
/-- The model of one simple inductive from the primitives, or the shape that
stopped it. **The export's declaration must already be installed**: the
recursor this restates is the one Lean minted for it, and the ι rules are
its own, restored — exactly [`InductiveModels.mutualIso`]'s arrangement. -/
def primIsoWithInterface (tname : Name) (root : Name) (lparams : List Name) (np : Nat) (memberTy : Expr)
    (exportCtors : Array (Name × Expr)) (reserved : Std.HashSet Name)
    (sourceRecursor? : Option ERec := none)
    (interface? : Option PrimInterfaceNames := none) : GenM Iso := do
  let us := lparams.map Level.param
  -- **Where the model is built and where it is emitted can differ.** `root` is
  -- the former and `tname` the latter; they are the same name for every
  -- declaration but the handful whose model name is lost to a normalized-name
  -- collision, where [`InductiveModels.genPrim`] retries under an alias root and
  -- renames the export records back. So every *guard*
  -- below is about `tname`'s names — those are what reach the output and what
  -- must not collide with the input — while descendants of `tname` are built
  -- under `root`. An exact raw private constructor need not be a descendant of
  -- its public type name, and then its model name remains raw and exact.
  let interface := interface?.getD (PrimInterfaceNames.standard tname root exportCtors)
  unless interface.ctors.size == exportCtors.size && interface.iotas.size == exportCtors.size do
    badShape s!"{tname}'s implementation name bundle has the wrong constructor arity"
  let model := interface.model
  let impl := interface.impl
  let selfN := interface.self
  let ern := Name.str tname "rec"
  let recN := interface.recursor
  -- `primRuleK` asks for iota slot zero even for a constructorless
  -- declaration, where it immediately observes that K is disabled.  The
  -- historical name function was total; keep this refactoring boundary total
  -- as well so an ordinary declined attempt never emits a caught bounds panic
  -- (and its address-bearing native backtrace) on stderr.
  let ctorN := fun (j : Nat) => interface.ctors[j]?.getD
    (Naming.modelName (Naming.relocateSource tname root
      (exportCtors[j]?.map (·.1) |>.getD (Name.str tname s!"ctor_{j}"))))
  let iotaN := fun (j : Nat) => interface.iotas[j]?.getD
    (Naming.iotaName (Naming.relocateSource tname root ern) j)
  let indN := Name.str impl "ind"
  -- Arm G's **internal** names, guarded exactly like the interface's — but
  -- only when the arm is taken, so a file that declares
  -- `T._model._impl.graph` of its own costs nothing to a declaration this arm
  -- never sees.
  let graphNames : List Name :=
    [indN, Name.str impl "graph", Name.str impl "graph_mk",
     Name.str impl "graph_inv_ty", Name.str impl "graph_inv",
     Name.str impl "graph_unique", Name.str impl "graph_exists",
     Name.str impl "rec_graph"]
  -- Arm C's **internal** names. `skel` is the index erasure, spliced as an
  -- ordinary inductive so that the kernel mints its recursor and its ι is
  -- definitional (the construction uses the real type); `good` is
  -- the carving predicate. Guarded like arm G's, and only when the arm fires.
  let skelN := Name.str impl "skel"
  let goodN := Name.str impl "good"
  let skelCtorN := fun (j : Nat) => Name.str skelN s!"c_{j}"
  let nc := exportCtors.size

  if inductiveBasis.contains tname then declineWith .basisExempt

  -- The guard runs on the **emitted** name and, where the two differ, on the
  -- built one too: the first is the contract this run must not break and the
  -- second is a constant this run is about to add to the environment.
  let taken1 : Name → GenM Unit := fun n => do
    if reserved.contains n || (← getEnv).constants.contains n then declineWith (.nameTaken n)
  let taken : Name → GenM Unit := fun n => do
    let emitted :=
      if model.isPrefixOf n then n.replacePrefix model (Naming.modelName tname) else n
    taken1 emitted
    if root != tname && n != emitted then taken1 n
  taken selfN
  taken recN
  for j in [0:nc] do
    taken (ctorN j)
    taken (iotaN j)

  -- ── shape ──
  -- **A declaration may hide its index telescope behind a definition.** Lean
  -- stores an inductive's type as declared, so `inductive P (X) : Presieve X`
  -- comes back as `(X : C) → Presieve X` with the indices inside the `def`,
  -- and a syntactic peel finds no `Sort` at the end and no indices at all.
  -- Lean's own `numIndices` counts the *unfolded* ones — which is why the
  -- assertion against the recursor below is the cross-check on this and not a
  -- second opinion.
  --
  -- So: peel syntactically first, and only if that does not reach a sort,
  -- re-expose the telescope with a **reducing** telescope and carry on with
  -- the definitionally-equal type that has its binders written out. The retry
  -- is deliberately not the default — every shape that worked before this
  -- reaches the same `memberTy` object it always did, so nothing that was
  -- measured moves.
  let analysis ← analysePrim tname lparams np memberTy exportCtors
  let declaredMemberTy := analysis.declaredMemberTy
  let memberTy := analysis.memberTy
  let ni := analysis.ni
  let w := analysis.w
  let isRec := analysis.isRec
  let rv := analysis.rv
  if let some sourceRecursor := sourceRecursor? then
    validateExactRecursorLayout sourceRecursor rv
  let large := analysis.large
  let v := analysis.v
  let recLs := analysis.recLs
  let nonrecursiveOneConstructor := analysis.nonrecursiveOneConstructor

  let route := analysis.route

  -- **Is the index erasure unnested, and is it linear?** — the two questions arm
  -- C's reach turns on, and the second is the same test the tuple tower
  -- applies ([`InductiveModels.recSlotOf`]). *Unnested* (the historical
  -- `erasureBare` name below): every recursive occurrence reduces to
  -- `∀ z⃗, T p⃗ e⃗`, rather than sitting inside a container. *Linear*:
  -- unnested, and at most one such field per constructor. Erasing the indices
  -- moves neither test — a field `T p⃗ e⃗` erases to `S p⃗`, one field either
  -- way — so both can be asked here, of the family itself, before anything is
  -- built.
  --
  -- Non-throwing on purpose: they are asked of *every* indexed family, and the
  -- ones they say no to are declined with the answer printed, so the Mathlib
  -- census measures the arm's reach instead of estimating it.
  --
  -- **Three reasons, counted apart, and none of the first two still bounds
  -- arm C.** The erasure can fail to be linear by branching (two recursive
  -- fields), by being infinitary (a recursive occurrence under a binder), or
  -- by the occurrence not being an application of `tname` at all. The first
  -- keeps every occurrence bare, which is all that [`InductiveModels.eraseCtorTy`]
  -- and [`InductiveModels.spineSwap`] assume — they replace one recursive field's
  -- occurrence, once per such field, so a constructor with three of them
  -- erases as readily as one. The second keeps the *binders* and moves only
  -- the occurrence under them: `∀ z⃗, T p⃗ e⃗` erases to `∀ z⃗, S p⃗`, and the
  -- three consumers each wrap what they built in the same `z⃗`
  -- ([`InductiveModels.withRecSlot`]). Arm C therefore runs at `erasureBare`, which
  -- is now the third reason alone, and carries **every** recursive slot
  -- through `ctorIdxAt`, `good`'s minor and the constructor's carve proof; the
  -- spliced skeleton that comes out branches and is infinitary, and arm W is
  -- what models *it*.
  --
  -- `erasureLinear` survives because it is what the *decline message* reports,
  -- what the census counts the populations by, and — the load-bearing use —
  -- what says a **non-indexed** declaration is arm W's rather than the tuple
  -- tower's. Relaxing `erasureBare` alone would have taken every infinitary
  -- non-indexed declaration away from arm W and handed it to a tower that
  -- cannot express it, so the infinitary test is split out rather than
  -- deleted.
  let erasureBare := analysis.erasureBare
  let erasureLinear := analysis.erasureLinear

  -- What each route can carry. The Church routes gained indices and recursion
  -- (`churchSwapAt` and the strong-induction fold below); the `Nat`-tagged sum
  -- has neither. At a maybe-zero sort, small elimination uses the Church pair
  -- with `down`/`up` at the carrier boundary, including for indices and
  -- recursion. The lifted arm-F construction below carries the remaining
  -- indexed shape: the large-eliminating nonrecursive singleton.
  -- ── the singleton's index shape, settled before anything is spliced ──
  --
  -- **One analysis for two arms**, because the two limits that used to be
  -- stated separately are one limit. A large-eliminating one-constructor
  -- `Prop` is exactly a declaration each of whose fields is either a *proof*
  -- or a piece of *data that is literally one of the conclusion's index
  -- arguments* — that is the kernel's own subsingleton rule: the
  -- non-`Prop` telescope elements must be a **subset** of the applied
  -- parameters and indices, by identity and not by occurrence), and it is what
  -- makes a model possible at all. A model of a `Prop` can extract its proof
  -- fields by small elimination and has *no way whatever* to extract data, so
  -- the index vector is the only place data can come back from.
  --
  -- Each index position is therefore one of two things:
  --
  -- * a **pivot** — literally one of the constructor's data fields. The model
  --   recovers that field by reading the recursor's own index argument, so it
  --   **substitutes** rather than quantifies. `Acc`'s `x`, `IsHomLift`'s `a`,
  --   `b` and `φ`.
  -- * anything else — an arbitrary expression over the parameters, the data
  --   fields and the *proof* fields: `BadC`'s constant `N.z`, `IsHomLift`'s
  --   `p.obj a`, `Acc.below`'s `Acc.intro x h`, `Inf.below`'s `Inf.mk a`.
  --   Such a position carries nothing the substitution can use and is
  --   discharged instead by a **Henry-Ford equation at the non-pivot
  --   subsequence** — which is what arm F's carrier already was, back when the
  --   arm demanded that *every* position be of this kind.
  --
  -- Read that way the two arms' old refusals were the same refusal seen from
  -- the two ends: arm F took only all-non-pivot index vectors and arm G took
  -- only all-pivot ones, and everything in between — `MixI`, `SvIx`,
  -- `IsHomLift`, every `.below` Lean mints beside a recursive `Prop`, and
  -- `Acc.below` — fell through the gap between them.
  -- `test/fixtures/inductive-models/prim_idx.lean` is the grid.
  let armGRec := (route matches PrimRoute.prop) && large && nc == 1 && isRec
  let armFNonRec := ((route matches PrimRoute.prop) || (route matches PrimRoute.bare)) &&
    large && nc == 1 && ni > 0 && !isRec
  let mut gIsData : Array Bool := #[]
  let mut gIdxPos : Array Nat := #[]
  let mut gRecNb : Array (Option Nat) := #[]
  let mut gNf := 0
  -- Constructor field / pivot-position pairs whose declared index type moves
  -- with a non-pivot. Arm F's zipper transports all of them in field order.
  let mut gPivotTransports : Array (Nat × Nat) := #[]
  -- The index positions that are **not** pivots, in telescope order.
  let mut gNonPiv : Array Nat := #[]
  if armGRec || armFNonRec then
    if armGRec then for n in graphNames do taken n
    let (a, b, cc, npv, pt) ← forallBoundedTelescope memberTy (some np) fun ps _ => do
      let (cn, cty) := exportCtors[0]!
      let tele ← instForall cty ps
      let nfg := numForalls tele
      let flds ← classifyCtor tname nfg tele
      forallBoundedTelescope tele (some nfg) fun fs res => do
        let some args ← ownerAppArgs? tname np ni res
          | badShape s!"{cn} does not end in {tname} at {np} parameters and {ni} indices"
        let idx := args.extract np args.size
        let mut isD : Array Bool := #[]
        let mut pos : Array Nat := #[]
        -- A pivot and the data field which supplies it are one fact, not two.
        -- Keeping the field index here makes the formerly defensive
        -- "pivot with no field" state unrepresentable: an index is a pivot
        -- exactly when this slot is `some i`.
        let mut pivotField : Array (Option Nat) := Array.replicate ni none
        for i in [0:nfg] do
          if (← ilevel (← ityp fs[i]!)).normalize.isZero then
            isD := isD.push false
            pos := pos.push 0
          else
            let mut at? : Option Nat := none
            for k in [0:ni] do
              if at?.isNone && idx[k]! == fs[i]! then at? := some k
            -- **Unreachable from a kernel-accepted declaration, and kept for
            -- inconsistent unchecked exports.** This block is entered only
            -- when the installed recursor is `large`. For a one-constructor
            -- proposition (including the maybe-zero `Sort u` analogue), the
            -- kernel mints that recursor only when every non-proof field is
            -- literally recoverable as a conclusion index. A declaration may
            -- contain an unrecoverable data field and still be accepted, but
            -- its recursor is small and `armFNonRec` / `armGRec` are false.
            -- `arm_f_guards` pins that route boundary. Only a raw export whose
            -- recursor metadata contradicts the installed kernel declaration
            -- can arrive here, and that remains a named decline rather than a
            -- wrong model.
            let some k := at?
              | badShape s!"{cn} has a data field that is not one of the conclusion's \
index arguments, so nothing in the model can recover it — the kernel's own \
subsingleton rule refuses that shape and mints no large eliminator for it"
            isD := isD.push true
            pos := pos.push k
            if pivotField[k]!.isNone then pivotField := pivotField.set! k (some i)
        -- **A pivot's own type may mention an earlier non-pivot index.** Arm
        -- F records every such field.  Its carrier zipper inserts an equality
        -- for the complete earlier index prefix, transports the caller's pivot
        -- back to the constructor field type, and only then binds later proof
        -- fields or recovers another pivot.  `prim_idx`'s `Fmid` and `FChain`
        -- pin the one-pivot cases; `arm_f_zip` adds two pivots, a later proof,
        -- and a final endpoint mentioning the recovered pivot.
        forallBoundedTelescope (← instForall memberTy ps) (some ni) fun is _ => do
          let mut pivotTransports : Array (Nat × Nat) := #[]
          for j in [0:ni] do
            if let some i := pivotField[j]! then
              let jt ← ityp is[j]!
              for m in [0:ni] do
                if pivotField[m]!.isNone && jt.containsFVar is[m]!.fvarId! then
                  unless pivotTransports.contains (i, j) do
                    pivotTransports := pivotTransports.push (i, j)
          return (isD, pos, flds.map (·.rec?),
            (Array.range ni).filter (pivotField[·]!.isNone),
            pivotTransports)
    gIsData := a; gIdxPos := b; gRecNb := cc; gNf := a.size; gNonPiv := npv
    gPivotTransports := pt

  -- **Arm G's half of the index axis.** `GraphInv ι⃗ t val` carries one
  -- equality at the dependent tuple of non-pivot indices.  Its continuation
  -- transports the constructor step from `ι⃗_ctor` to `ι⃗`; pivots stay
  -- fixed because their data fields are supplied from the caller's indices.
  -- Proof-valued non-pivots still reduce for free by proof irrelevance, while
  -- data-valued ones (`BadC`, `Rgd`, and their `.below` declarations) now take
  -- the same explicit packed transport as arm F.
  let armG := armGRec

  let (eqi, eqDecls) ← ensureEq reserved
  let mut out : Array Declaration := eqDecls
  let mut requires : Array Name := #[]
  let mut spliced : Array Name := eqDecls.flatMap (·.getNames.toArray)
  let mut projectionOverrides : Array (Name × Nat × Expr × Expr) := #[]

  let withParams := fun {α : Type} (k : Array Expr → GenM α) =>
    forallBoundedTelescope memberTy (some np) fun ps _ => k ps

  let ctorPairs := (Array.range nc).map fun j => (exportCtors[j]!.1, ctorN j)
  let tbl := modelTable (← getEnv) #[tname]
    { decls := #[], levelParams := lparams, members := #[], selfNames := #[selfN]
      numAll := 1, ctors := ctorPairs, recs := #[recN], iotas := #[], spliced := #[] }
  let installedRecTy := restore tbl rv.type
  -- The one-layer adapter publishes the source interface verbatim modulo
  -- names.  Unlike `restore`, this map retains every source occurrence's
  -- exact universe arguments; installed metadata remains the proof/layout
  -- oracle in `installedRecTy`.
  let exactSource? := interface?.map fun _ => fun expression =>
    mapConstsE (fun name =>
      if name == tname then some selfN
      else if name == ern then some recN
      else ctorPairs.findSome? fun (source, target) =>
        if name == source then some target else none) expression
  let publicSource := fun expression => match exactSource? with
    | some exact => exact expression
    | none => restore tbl expression
  let publicRecTy := publicSource (sourceRecursor?.map (·.type) |>.getD rv.type)

  -- **Arm E**: a linearly recursive, non-indexed `Type` with no base
  -- constructor is empty.  The tuple tower below deliberately starts from a
  -- base-constructor fibre, so this shape is not a degenerate tower: its exact
  -- model is the empty carrier already provided by the derived lift of `False`. Every
  -- constructor has one direct recursive field (linearity plus the absence of
  -- a base constructor), hence maps to that field; the recursor and its iota
  -- rules eliminate the same empty value.  Compute the slots here so the
  -- route branches before the tuple tower asks for its nonexistent fibre.
  let emptySlots : Array (Option Nat) ←
    if (route matches PrimRoute.type) && ni == 0 && isRec && erasureLinear then
      withParams fun ps =>
        exportCtors.mapM fun (cn, cty) => do
          let tele ← instForall cty ps
          recSlotOf tname np ni cn (numForalls tele) tele
            (tagFactored tname np exportCtors)
            w.normalize.dec.isSome (labelFactored tname np exportCtors)
    else
      pure #[]
  let armE := emptySlots.size == nc && nc > 0 && emptySlots.all Option.isSome

  -- A one-field singleton at a maybe-zero sort must retain its field.  The
  -- ordinary Church/lift route records only a proof of inhabitation; at a
  -- positive instantiation two constructor payloads then become equal, so no
  -- intrinsic projection can satisfy both constructor rules.
  --
  -- There are exactly two field-preserving cases using the existing basis.
  -- If the field's sort is definitionally the carrier sort, the field itself
  -- is the carrier (`PI`). If the field is exactly a proposition, the derived
  -- lift raises it to the carrier sort without forgetting its proof (`PF`). Test
  -- identity first: `PI.{0}` has a proposition-valued instantiation, but its
  -- polymorphic field sort is the carrier's `u`, not the constant level zero.
  let directFieldRoute? : Option DirectFieldRoute ←
    if (route matches PrimRoute.bare) && nonrecursiveOneConstructor && ni == 0 &&
        numForalls exportCtors[0]!.2 - np == 1 then
      withParams fun ps => do
        let tele ← instForall exportCtors[0]!.2 ps
        let .forallE _ fieldType _ _ := tele
          | badShape s!"{exportCtors[0]!.1} is not a one-field constructor"
        let fieldLevel ← ilevel fieldType
        if ← isLevelDefEq fieldLevel w then return some .identity
        if fieldLevel.normalize.isZero then return some .propLift
        badShape s!"{exportCtors[0]!.1}'s only field inhabits Sort {fieldLevel}, but the \
          carrier inhabits Sort {w}: neither identity nor the exact-sort lift can retain it"
    else
      pure none

  -- Two or more exact-sort fields are retained by a right-nested `PSigma'`.
  let directTightRoute ← planDirectTightRoute (route matches PrimRoute.bare)
    nonrecursiveOneConstructor np ni memberTy exportCtors w
  let directRoute? : Option DirectRoute := directFieldRoute?.map DirectRoute.field <|>
    if directTightRoute then some .tight else none

  -- The indexed subsingleton has a different carrier from the Church routes —
  -- a packed index equation, not a fold — so it branches before them. At a
  -- maybe-zero sort this proposition is wrapped in the derived lift, just like the
  -- ordinary Church route; the construction below inserts the matching
  -- `up`/`down` at its boundary.
  -- **Any number of fields.** The arm used to decline above one, because at
  -- zero fields (`HEq`) and one (`TagS`) there is nothing to order and no
  -- fixture could catch a threading bug. `prim_shapes`'s `TagS2`, `TagS3` and
  -- `TagS4` are the two- and three-field occupants that were added to ask, and
  -- the sequential extraction below is correct at all three — kernel-accepted,
  -- statements compared, and red under the field-order mutations.
  --
  -- **Any index shape**, too. The arm's index vector used to have to be built
  -- from the parameters alone; it may now carry **pivots** — positions that
  -- are literally one of the constructor's data fields — anywhere in the
  -- telescope, which is what brings `MixI`, `SvIx` and
  -- `CategoryTheory.Functor.IsHomLift` inside. The analysis above is what says
  -- which positions those are; everything below reads `gNonPiv`.
  let armF := armFNonRec

  -- **Arm C**: an indexed family at a never-zero sort, carved out of its own
  -- index erasure. Gated on the erasure being
  -- **bare** — every recursive occurrence a `T p⃗ e⃗` whose whole domain the
  -- erasure can replace — and no longer on its being *linear*: the carve
  -- carries an arbitrary number of recursive slots per constructor, and the
  -- branching skeleton that results is modelled by arm W. A family whose
  -- skeleton does not model is still a decline and never an emission, which is
  -- `Iso.requires`' job and not this guard's.
  let armC := (route matches PrimRoute.type) && ni > 0 && erasureBare

  -- **Arm W**: the tagged W construction. It is the *fallback* for the
  -- non-indexed Type route and not its default, and that is deliberate: the
  -- tuple tower reaches every linear shape with no axiom and no fragment, so
  -- taking W wherever it applies would move six thousand models onto a heavier
  -- construction for nothing. `!erasureLinear` is exactly the complement of
  -- [`InductiveModels.recSlotOf`]'s two refusals — two recursive fields in one
  -- constructor, or a recursive occurrence that is not a bare `T p⃗` — so this
  -- fires precisely where the tower declines and nowhere else.
  --
  -- Three further conditions, each a real limit of the scheme rather than a
  -- convenience:
  --
  -- * **`labelFactored`.** The core is generic in `K`, `B' : K → Type u` and
  --   `tg : A → K`, and the arm runs it at **two** instantiations of one
  --   construction. At `K := Nat`, `tg := PSigma'.fst`
  --   the branch type is a function of the *tag* and cannot see the label's
  --   data, which is [`InductiveModels.tagFactored`]; at `K := A`, `tg := id` it sees
  --   all of it and only an earlier *recursive* field is out of reach, which is
  --   [`InductiveModels.labelFactored`]. The guard is the weaker one and
  --   `tagFactored` picks the column: the tagged instantiation takes
  --   `instDecidableEqNat` and stays at `[propext, Quot.sound]`, the untagged
  --   one takes `WT.decEqAll` and pays `Classical.choice`.
  -- * **the internal carrier is `Type u`.** `WT.W.{u,w}` fixes `A` and `B'`
  --   at `Type u`. Ordinarily the public carrier already has that shape. At a
  --   never-zero carrier with no syntactic predecessor, the fallback runs the
  --   core at `Type` and stores that low carrier in a `PSigma'` whose second
  --   component is the derived lift of `True`. The `PSigma'` itself lands at the exact
  --   public `Sort w`; no cumulative definition conversion is assumed.
  -- * **`isRec`.** A non-recursive declaration has no branching to be stopped
  --   by, so it never reaches here.
  let wTagged := tagFactored tname np exportCtors
  let wShapeEligible := (route matches PrimRoute.type) && ni == 0 && isRec &&
    !erasureLinear && labelFactored tname np exportCtors
  let wPlan ← wCarrierPlan wShapeEligible w
  let armW := wShapeEligible && (w.normalize.dec.isSome || wPlan.lifted)
  let wW := wPlan.coreLevel
  -- Arm W's **internal** names, guarded exactly like arm C's and arm G's, and
  -- only when the arm is taken.
  let wDN := Name.str impl "wD"
  let wTelN := Name.str impl "wTel"
  let wBN := Name.str impl "wB"
  let wAN := Name.str impl "wA"
  let wTgN := Name.str impl "wtg"
  let wFN := Name.str impl "wF"

  -- ── the kit arm C needs: Church conjunction's two projections and its
  -- introduction, built here because [`InductiveModels.andCOf`] gives the type only.
  let andCMk := fun (A B a b : Expr) => withLocalDeclD `D (.sort .zero) fun D => do
    withLocalDeclD `k (.forallE `a A (.forallE `b B D .default) .default) fun kk =>
      mkLambdaFVars #[D, kk] (mkAppN kk #[a, b])
  let andCFst := fun (A B p : Expr) => do
    let sel ← withLocalDeclD `a A fun a => withLocalDeclD `b B fun b =>
      mkLambdaFVars #[a, b] a
    pure (mkAppN p #[A, sel])
  let andCSnd := fun (A B p : Expr) => do
    let sel ← withLocalDeclD `a A fun a => withLocalDeclD `b B fun b =>
      mkLambdaFVars #[a, b] b
    pure (mkAppN p #[B, sel])

  -- ── arm W's builders ──
  -- Defined here rather than inside the arm because the **ι block below needs
  -- them too**: an arm W ι rule is `WT.Wrec_iota` at this declaration's own
  -- `F`, its label and its dispatch, and those have to be rebuilt at the ι
  -- theorem's telescope. Defining a closure costs nothing to a declaration
  -- that never calls it, and every one of these declines rather than returning
  -- a wrong answer when it is called at a shape arm W does not reach.
  let wNatT : Expr := .const `Nat []
  -- `Type u` for the internal `Sort wW` carrier. Meaningless — and unused —
  -- unless `armW`, whose carrier plan proved `wW` successor-shaped.
  let uL := wW.normalize.dec.getD .zero
  -- **The core's `K` level**, and the one place the two instantiations differ
  -- in the level lists rather than in a term: `K = Nat : Type 0` tagged and
  -- `K = A p⃗ : Type u` untagged. The core's own binders are
  -- `WT.W.{u,w}`, `WT.sup.{u,w}`, `WT.Wrec.{u,v,w}` and
  -- `WT.Wrec_iota.{u,v,w}` with `w` last, so every list below gains it there.
  let wKL := if wTagged then Level.zero else uL

  -- **Constructor `k`'s field split**, as positions into its own telescope.
  -- The data tower holds the non-recursive fields and the branch tower the
  -- recursive ones, and the two index *different* subsequences of one
  -- telescope: a generator that took "the fields before the first recursive
  -- one" as the data would silently lose every field that sits after a child.
  --
  -- There is deliberately no second guard for a later data field whose type
  -- mentions an earlier child. A kernel-accepted plain inductive cannot
  -- inspect a recursive value while the inductive is still being declared:
  -- putting that value in a later field's type requires a foreign dependent
  -- family/container application, which Lean classifies as nesting and rejects
  -- when the occurrence depends on a constructor local (the exact rejected
  -- shape documented in `indexed_decl.lean` and `nest_fam_arg.lean`). Nested
  -- input does not reach `genPrim` in any case: `Driver` sends it through
  -- `Plan.plan`, whose `mimicFor` repeats that constructor-local check before
  -- specialising the block. The former `hasLooseBVar` refusal here was thus a
  -- guard for metadata the replaying kernel cannot install, not a model shape.
  let wShapeOf : Nat → GenM (Array Nat × Array Nat) := fun k => do
    let (cn, cty) := exportCtors[k]!
    let mut t := cty
    for _ in [0:np] do
      let .forallE _ _ b _ := t
        | badShape s!"{cn}'s telescope is shorter than {np} parameters"
      t := b
    let mut nrs : Array Nat := #[]
    let mut rcs : Array Nat := #[]
    let mut i := 0
    while t matches .forallE .. do
      let .forallE _ dom b _ := t | unreachable!
      if mentionsAny #[tname] dom then rcs := rcs.push i
      else
        nrs := nrs.push i
      t := b
      i := i + 1
    return (nrs, rcs)
  let wRecCount : Nat → GenM Nat := fun k => return (← wShapeOf k).2.size

  -- The five definitions the core is instantiated at, as applications of the
  -- names declared in the arm. `D` and `Tel` are the towers; `B'`, `A` and
  -- `tg` are one line each and exist as declarations rather than as inlined
  -- terms so that `self`, every constructor and `rec_0` name them instead of
  -- carrying a copy.
  let wDAt : Array Expr → Expr := fun ps => mkAppN (.const wDN us) ps
  let wAAt : Array Expr → Expr := fun ps => mkAppN (.const wAN us) ps
  -- `⟨t, d⟩ : A p⃗`, with the tag as an *expression* — the recursor's cascade
  -- needs it at a variable index. `A` is `Σ' t : Nat, D p⃗ t` in **both**
  -- instantiations: what the untagged one changes is `K`, not the label.
  let wLabel : Array Expr → Expr → Expr → Expr := fun ps t d =>
    psigmaMk (.succ .zero) wW wNatT (wDAt ps) t d
  -- **The core's `K`, and the value in it a constructor's branch type is taken
  -- at.** Tagged: `Nat`, and the value is the tag. Untagged: the label type
  -- itself, and the value is that constructor's whole label — which is why
  -- everything below threads `key` where the tagged transcription threaded a
  -- `Nat` literal. `wKeyOf` is the *only* place the two differ.
  let wKTy : Array Expr → Expr := fun ps => if wTagged then wNatT else wAAt ps
  let wKeyOf : Array Expr → Nat → Expr → Expr := fun ps k d =>
    if wTagged then natNumeral k else wLabel ps (natNumeral k) d
  let wTelFn : Array Expr → Expr → GenM Expr := fun ps key =>
    withLocalDeclD `j wNatT fun j =>
      mkLambdaFVars #[j] (mkAppN (.const wTelN us) (ps ++ #[key, j]))
  let wBAt : Array Expr → Expr → GenM Expr := fun ps key =>
    return psigmaT (.succ .zero) wW wNatT (← wTelFn ps key)
  let wBFn : Array Expr → Expr := fun ps => mkAppN (.const wBN us) ps
  let wTgAt : Array Expr → Expr := fun ps => mkAppN (.const wTgN us) ps
  -- **`DecidableEq K`, and the whole of the second bill.** One declaration,
  -- `[propext, Quot.sound]` on the left of it and
  -- `[propext, Classical.choice, Quot.sound]` on the right.
  let wDecEq : Array Expr → Expr := fun ps =>
    if wTagged then .const wCoreDecEqNat []
    else mkApp (.const wCoreDecEqAll [wW]) (wAAt ps)
  let wSup : Array Expr → Expr → Expr → Expr := fun ps a f =>
    mkAppN (.const wCoreSup [uL, wKL])
      #[wKTy ps, wAAt ps, wBFn ps, wDecEq ps, wTgAt ps, a, f]
  let wLowSelfAt : Array Expr → Expr := fun ps =>
    mkAppN (.const wCoreSelf [uL, wKL]) #[wKTy ps, wAAt ps, wBFn ps, wTgAt ps]
  -- At the constrained-lift instantiation the low W lives in `Type` while the
  -- public carrier must live in the literal `Sort w`. `PSigma'` supplies that
  -- exact result sort; the second field is a canonical inhabitant of
  -- the derived lift of `True`, so wrapping and unwrapping reduce by the structure
  -- projection and eta rules and add no axiom.
  -- `⟨j, tel⟩ : B' p⃗ key`, with the branch index as an expression for the same
  -- reason.
  let wBranch : Array Expr → Expr → Expr → Expr → GenM Expr := fun ps key j tel =>
    return psigmaMk (.succ .zero) wW wNatT (← wTelFn ps key) j tel

  -- The two towers, at a parameter scope.
  let wDataTy : Array Expr → Nat → GenM Expr := fun ps k => do
    let (nrs, _) ← wShapeOf k
    let tele ← instForall exportCtors[k]!.2 ps
    forallBoundedTelescope tele (some (numForalls tele)) fun fs _ =>
      wTowerTyOf wW (nrs.map (fs[·]!))
  -- **The data tower's components, read out of a label's data** — the values
  -- the branch tower's binder types are written in terms of wherever only the
  -- label is in hand, which is everywhere but a constructor's own body.
  let wNrProjs : Array Expr → Nat → Expr → GenM (Array Expr) := fun ps k d => do
    let (nrs, _) ← wShapeOf k
    let tele ← instForall exportCtors[k]!.2 ps
    forallBoundedTelescope tele (some (numForalls tele)) fun fs _ =>
      wTowerProjsOf wW (nrs.map (fs[·]!)) d
  -- **Constructor `k`'s recursive field `r`, at its own non-recursive fields
  -- replaced by `nrv`** — and this substitution is the untagged arm.
  --
  -- Tagged, `Tel` is a function of the tag and `labelFactored`'s stronger
  -- sibling guarantees the domain mentions no field at all, so `replaceFVars`
  -- finds nothing and the tagged transcription is byte-identical. Untagged, the
  -- domain may mention the constructor's non-recursive fields — `WType.mk`'s
  -- `β a → WType β` is the shape — and what stands in their place is whatever
  -- the caller has: the fields themselves inside the constructor, the label's
  -- projections inside `F`.
  let wRecDom : Array Expr → Nat → Nat → Array Expr → GenM Expr := fun ps k r nrv => do
    let (nrs, rcs) ← wShapeOf k
    let tele ← instForall exportCtors[k]!.2 ps
    forallBoundedTelescope tele (some (numForalls tele)) fun fs _ => do
      return (← ityp fs[rcs[r]!]!).replaceFVars (nrs.map (fs[·]!)) nrv
  let wTelTy : Array Expr → Nat → Array Expr → Nat → GenM Expr := fun ps k nrv r => do
    forallTelescope (← wRecDom ps k r nrv) fun zs _ => wTowerTyOf wW zs

  -- **The dispatch cascade at tag `k`**, as a function of the branch index:
  -- `wDispAt ps k child sc : Tel p⃗ k sc → T._model.self p⃗`. `child r zs vs` is
  -- the `r`-th child at the binder values `vs` — the constructor's own field
  -- where a constructor is being built, and `f ⟨r, ⟨z⃗⟩⟩` where the recursor
  -- is. One builder for both is what makes the eta lemma's `rfl` hold: the
  -- term the lemma's left side reduces to is *this* term.
  let wDispAt : Array Expr → Nat → Expr → Array Expr →
      (Nat → Array Expr → Array Expr → GenM Expr) → Expr → GenM Expr :=
    fun ps k key nrv child sc => do
    let (_, rcs) ← wShapeOf k
    let selfTy := wLowSelfAt ps
    let dom := fun (jj : Expr) => mkAppN (.const wTelN us) (ps ++ #[key, jj])
    let s ← ilevel (.forallE `tel (dom (natNumeral 0)) selfTy .default)
    let motAt : Nat → GenM Expr := fun r =>
      withLocalDeclD `j wNatT fun j =>
        mkLambdaFVars #[j] (.forallE `tel (dom (natSuccs r j)) selfTy .default)
    let armAt : Nat → GenM Expr := fun r => do
      forallTelescope (← wRecDom ps k r nrv) fun zs _ => do
        withLocalDeclD `tel (← wTowerTyOf wW zs) fun tel => do
          mkLambdaFVars #[tel] (← child r zs (← wTowerProjsOf wW zs tel))
    let junkAt : Expr → GenM Expr := fun t =>
      withLocalDeclD `tel (dom (natSuccs rcs.size t)) fun tel => do
        mkLambdaFVars #[tel] (← emptyAtElim eqi wW wW selfTy tel)
    natCascade s rcs.size motAt armAt junkAt 0 sc
  -- The same, packaged as `fun b : B' p⃗ key => …`. The eta lemma below is
  -- stated against **these** `b.1` and `b.2`, so the two must be built here.
  let wDispLam : Array Expr → Nat → Expr → Array Expr →
      (Nat → Array Expr → Array Expr → GenM Expr) → GenM Expr :=
    fun ps k key nrv child => do
    let β ← wTelFn ps key
    withLocalDeclD `b (← wBAt ps key) fun b => do
      let b1 := psigmaFst (.succ .zero) wW wNatT β b
      let b2 := psigmaSnd (.succ .zero) wW wNatT β b
      mkLambdaFVars #[b] (mkApp (← wDispAt ps k key nrv child b1) b2)

  -- **The eta lemma** — `dispatch = f`, and the whole of the per-constructor
  -- glue. It is
  -- enough to prove `∀ j tel, dispatch j tel = f ⟨j, tel⟩` and instantiate at
  -- `b.1, b.2`, because `⟨b.1, b.2⟩ ≡ b` is `PSigma'`'s definitional eta — so
  -- **no `PSigma'.rec'` appears in the proof at all**. Every real branch is
  -- `Eq.refl`: at branch `r` the left side reduces to `f ⟨r, ⟨tel.1, …, ⟨⟩⟩⟩`
  -- and the right is `f ⟨r, tel⟩`, and those are the same term by that eta
  -- once more and by the terminating unit's own canonicity. Off the end of the
  -- telescope the branch is uninhabited and the arm is its eliminator.
  let wEtaAt : Array Expr → Nat → Expr → Array Expr → Expr → GenM Expr :=
    fun ps k key nrv f => do
    let (_, rcs) ← wShapeOf k
    let selfTy := wLowSelfAt ps
    let dom := fun (jj : Expr) => mkAppN (.const wTelN us) (ps ++ #[key, jj])
    let child : Nat → Array Expr → Array Expr → GenM Expr := fun r zs vs =>
      return mkApp f (← wBranch ps key (natNumeral r) (← wTowerMkOf wW zs vs))
    let stmt : Expr → Expr → GenM Expr := fun jj tel => do
      let lhs := mkApp (← wDispAt ps k key nrv child jj) tel
      return eqi.mk' wW selfTy lhs (mkApp f (← wBranch ps key jj tel))
    let motAt : Nat → GenM Expr := fun r =>
      withLocalDeclD `j wNatT fun j => do
        let jj := natSuccs r j
        let body ← withLocalDeclD `tel (dom jj) fun tel => do
          mkForallFVars #[tel] (← stmt jj tel)
        mkLambdaFVars #[j] body
    let armAt : Nat → GenM Expr := fun r => do
      forallTelescope (← wRecDom ps k r nrv) fun zs _ => do
        withLocalDeclD `tel (← wTowerTyOf wW zs) fun tel => do
          mkLambdaFVars #[tel]
            (eqi.refl' wW selfTy (mkApp f (← wBranch ps key (natNumeral r) tel)))
    let junkAt : Expr → GenM Expr := fun t => do
      let jj := natSuccs rcs.size t
      withLocalDeclD `tel (dom jj) fun tel => do
        mkLambdaFVars #[tel] (← emptyAtElim eqi .zero wW (← stmt jj tel) tel)
    let β ← wTelFn ps key
    let bTy ← wBAt ps key
    let pointwise ← withLocalDeclD `b bTy fun b => do
      let b1 := psigmaFst (.succ .zero) wW wNatT β b
      let b2 := psigmaSnd (.succ .zero) wW wNatT β b
      mkLambdaFVars #[b] (mkApp (← natCascade .zero rcs.size motAt armAt junkAt 0 b1) b2)
    let cod ← withLocalDeclD `x bTy fun x => mkLambdaFVars #[x] selfTy
    return mkAppN (.const wCoreFunext [wW, wW])
      #[bTy, cod, ← wDispLam ps k key nrv child, f, pointwise]

  -- **One constructor's label and dispatch, from its own field vector** — the
  -- constructor's body, and the two arguments the ι rule hands `Wrec_iota`.
  let wCtorParts : Array Expr → Nat → Array Expr → GenM (Expr × Expr) :=
    fun ps k fields => do
      let (nrs, rcs) ← wShapeOf k
      let nrv := nrs.map (fields[·]!)
      let tower ← wTowerMkOf wW nrv nrv
      let child : Nat → Array Expr → Array Expr → GenM Expr := fun r _ vs =>
        return wPlan.unwrap (wLowSelfAt ps) (mkAppN fields[rcs[r]!]! vs).headBeta
      -- The branch tower is written at the constructor's **own** fields here
      -- rather than at projections of the tower it just built: the two are
      -- definitionally equal by `PSigma'`'s ι rule, and the fields are what the
      -- dispatch's children are applied to anyway.
      return (wLabel ps (natNumeral k) tower,
              ← wDispLam ps k (wKeyOf ps k tower) nrv child)

  -- **`F`, the minor the core's recursor takes** — one `Nat.rec` cascade over
  -- the tag whose motive must be well-typed at *every* tag, the eta lemma's
  -- transport inside each arm, and the junk arm discharged from the emptiness
  -- of `D`. This is the term whose construction validates the emitted shape.
  let wMkF : Array Expr → Expr → Array Expr → GenM Expr := fun ps motive minors => do
    let selfTy := wLowSelfAt ps
    let coreMotive ← wPlan.motive (wLowSelfAt ps) motive
    -- The frame every arm and the motive share: `(d : D p⃗ t)
    -- (f : B' p⃗ key → self) (ih : (b : B' p⃗ key) → C (f b))`, and the label
    -- `⟨t, d⟩` built from `d`.
    --
    -- **`d` is introduced before the branch type is written**, which the
    -- tagged transcription had no reason to do: untagged, `key` *is* the label
    -- and the label holds `d`. The core asks for `B' (tg ⟨t,d⟩)`, and `key` is
    -- that reduced — `t` tagged, `⟨t,d⟩` untagged.
    let frame : Expr → (Expr → Expr → Expr → Expr → Expr → GenM Expr) → GenM Expr :=
      fun tag k => do
        withLocalDeclD `d (mkAppN (.const wDN us) (ps ++ #[tag])) fun d => do
          let a := wLabel ps tag d
          let key := if wTagged then tag else a
          let bt ← wBAt ps key
          withLocalDeclD `f (.forallE `b bt selfTy .default) fun f => do
            let ihT ← withLocalDeclD `b bt fun b =>
              mkForallFVars #[b] (mkApp coreMotive (mkApp f b))
            withLocalDeclD `ih ihT fun ih => k d f ih a key
    let motBody : Nat → Expr → GenM Expr := fun kk t =>
      frame (natSuccs kk t) fun d f ih a _ =>
        mkForallFVars #[d, f, ih] (mkApp coreMotive (wSup ps a f))
    let s ← withLocalDeclD `t wNatT fun t => do ilevel (← motBody 0 t)
    let motAt : Nat → GenM Expr := fun kk =>
      withLocalDeclD `t wNatT fun t => do mkLambdaFVars #[t] (← motBody kk t)
    let armAt : Nat → GenM Expr := fun kk => do
      let (nrs, rcs) ← wShapeOf kk
      let tag := natNumeral kk
      frame tag fun d f ih a key => do
        -- **The data tower's components come first**, because untagged they are
        -- what the branch tower's own binder types are written in terms of —
        -- `WType.mk`'s child is `β a → WType β` and the `a` here is `d.1`.
        let projs ← wNrProjs ps kk d
        -- the children and their induction hypotheses, read off `f` and `ih`
        let child : Nat → Array Expr → Array Expr → GenM Expr := fun r zs vs =>
          return mkApp f (← wBranch ps key (natNumeral r) (← wTowerMkOf wW zs vs))
        let disp ← wDispLam ps kk key projs child
        let tele ← instForall exportCtors[kk]!.2 ps
        let nf := numForalls tele
        let mut kids : Array Expr := #[]
        let mut ihs : Array Expr := #[]
        for r in [0:rcs.size] do
          let (kd, ihv) ← forallTelescope (← wRecDom ps kk r projs) fun zs _ => do
            let bv ← wBranch ps key (natNumeral r) (← wTowerMkOf wW zs zs)
            return (← mkLambdaFVars zs (wPlan.wrap (wLowSelfAt ps) (mkApp f bv)),
              ← mkLambdaFVars zs (mkApp ih bv))
          kids := kids.push kd
          ihs := ihs.push ihv
        -- Lean's minor takes the fields in declaration order and then the
        -- hypotheses, which is what the two towers have to be re-interleaved
        -- into: the data tower's components and the branch tower's children
        -- index different subsequences of one telescope.
        let mut args : Array Expr := #[]
        for i in [0:nf] do
          match nrs.findIdx? (· == i) with
          | some q => args := args.push projs[q]!
          | none =>
            let some r := rcs.findIdx? (· == i)
              | badShape s!"{exportCtors[kk]!.1}'s field {i} is in neither tower"
            args := args.push kids[r]!
        let base := mkAppN minors[kk]! (args ++ ihs)
        -- The minor's result is `C` at the constructor **rebuilt from the
        -- children**, which is `sup ⟨k, d⟩ dispatch` and not `sup ⟨k, d⟩ f`.
        -- The eta lemma is what closes that, and it is the one place this arm
        -- spends anything the tuple tower does not.
        let h ← wEtaAt ps kk key projs f
        let αf := Expr.forallE `b (← wBAt ps key) selfTy .default
        mkLambdaFVars #[d, f, ih]
          (← transportAlong eqi v wW αf disp f h base fun z =>
            pure (mkApp coreMotive (wSup ps a z)))
    let junkAt : Expr → GenM Expr := fun t => do
      let tag := natSuccs nc t
      frame tag fun d f ih a _ => do
        mkLambdaFVars #[d, f, ih]
          (← emptyAtElim eqi v wW (mkApp coreMotive (wSup ps a f)) d)
    withLocalDeclD `a (wAAt ps) fun a => do
      let a1 := psigmaFst (.succ .zero) wW wNatT (wDAt ps) a
      let a2 := psigmaSnd (.succ .zero) wW wNatT (wDAt ps) a
      mkLambdaFVars #[a] (mkApp (← natCascade s nc motAt armAt junkAt 0 a1) a2)

  if let some directRoute := directRoute? then
    let (_, cty0) := exportCtors[0]!
    let modelCtorTy := publicSource cty0
    let (directDecls, directSpliced, overrides) ← emitDirectModel directRoute eqi tname
      lparams np memberTy cty0 modelCtorTy declaredMemberTy selfN (ctorN 0) recN
      rv.levelParams installedRecTy publicRecTy w v reserved
    out := out ++ directDecls
    spliced := spliced ++ directSpliced
    projectionOverrides := projectionOverrides ++ overrides
  else if armF then
    -- ════ arm F: the indexed subsingleton, by one packed index equation ════
    --
    -- Shape: one constructor, every field a `Prop` or a
    -- variable that literally *is* one of the output's indices. The kernel
    -- then grants a `Sort w` motive, and the model has to deliver it — the
    -- Church fold cannot, since it only eliminates into `Prop`.
    --
    -- **Ordinarily the index vector splits in two** (the analysis above): the *pivot*
    -- positions, each literally one of the constructor's data fields, and the
    -- rest. The model **substitutes** at the pivots — that is the only way a
    -- data field can come back at all, since a `Prop`'s proof yields nothing
    -- but proofs — and equates at the rest. So the carrier quantifies the
    -- constructor's `Prop` fields *at the pivots already supplied*, and
    -- Church-conjoins them with **one** `Eq` at the **non-pivot subsequence**
    -- packed into a `PSigma'` ([`InductiveModels.packTyAt`]) — the Henry-Ford
    -- equation, stated once because a later index's type may mention an
    -- earlier one:
    --
    --     T' p⃗ ι⃗ := ∀ r : Prop,
    --                 (∀ h⃗[d⃗ := ι⃗_piv],
    --                    Eq Pk (pack ι⃗_ctor|np) (pack ι⃗|np) → r) → r
    --
    -- If a pivot's declared type moves with an earlier index, direct
    -- substitution is ill-typed.  The zipper variant instead packs each full
    -- prefix before a moving pivot, binds an equality from the constructor
    -- prefix to the caller prefix, transports the pivot back, and continues.
    -- Proof fields are bound at that recovered telescope; one last equation
    -- packs the complete index vector.  The recursor transports a function
    -- over all these premises and applies the extracted premises at the caller
    -- endpoint.  Hence every equation is `refl` at a constructor and the iota
    -- theorem remains definitionally `refl`, including with multiple pivots,
    -- a later proof field, or a later endpoint depending on a pivot.
    --
    -- At **no** pivots this is exactly what the arm was before — the
    -- subsequence is the whole telescope and `h⃗` is every field — which is
    -- what makes the generalisation additive rather than a rewrite. At **no
    -- non-pivots** (`Fall` in `test/fixtures/inductive-models/prim_idx.lean`) there is
    -- nothing left to
    -- equate: the carrier is a bare Church conjunction, the recursor is the
    -- minor applied to the recovered fields, and no `Eq.rec` is built.
    --
    -- Recursor: read the data fields off the recursor's own index arguments,
    -- extract the proof fields by small elimination (their target is a `Prop`,
    -- so no large eliminator for ∃/∧ is consumed), extract the equation the
    -- same way, and discharge the non-pivot indices with a single `Eq.rec`
    -- whose motive rebuilds a carrier proof at each packed point. Every
    -- mismatch between the rebuilt proof and the caller's is closed by proof
    -- irrelevance — and so is every mismatch between a proof field as the
    -- carrier binds it and as the extraction recovers it, which is what lets
    -- the equation mention proof fields (`Inf.below`'s `Inf.mk a`). `pack
    -- (unpack y) ≡ y` by structure eta is what makes the motive typecheck at
    -- all. ι is `Eq.refl`: at the constructor the stored equation *is*
    -- `Eq.refl`, the pivots are the constructor's own fields, and `Eq.rec`'s
    -- own ι rule fires.
    let lift? : Option Level := if route matches PrimRoute.bare then some w else none
    if lift?.isSome then
      for d in ← ensureExactSortLift reserved do out := out.push d; spliced := spliced ++ d.getNames
    for d in ← ensurePSigmaPrime reserved do out := out.push d; spliced := spliced ++ d.getNames
    let (cn0, cty0) := exportCtors[0]!
    let nonPiv := gNonPiv
    let zipRoute := !gPivotTransports.isEmpty
    let packSel := if zipRoute then Array.range ni else nonPiv
    let npack := packSel.size

    -- The index vector a walked result type ends at, at either head: the
    -- export's `T p⃗ ι⃗` or the model's own `T._model.self p⃗ ι⃗`.
    let idxOfRes := fun (hd : Name) (res : Expr) => do
      let some args ← ownerAppArgs? hd np ni res
        | badShape s!"{cn0} does not end in {hd} at {np} parameters and {ni} indices"
      pure (args.extract np args.size)

    -- The constructor's field telescope with the **data fields substituted**
    -- from an index vector — [`InductiveModels.ctorFieldsAux`], the same walk arm G's
    -- `GraphInv` is stated by. `fs` is every field (substituted or bound),
    -- `bnd` only the bound ones, and `res` the conclusion at them.
    let fieldsAt := fun (ps is : Array Expr)
        (k : Array Expr → Array Expr → Expr → GenM Expr) => do
      let tele ← instForall cty0 ps
      ctorFieldsAux true gIsData gIdxPos is (numForalls tele) 0 tele #[] #[] k

    -- **`Pk`, the packed non-pivot type, at a given index vector.** Its
    -- component types may mention the *pivots*, which [`InductiveModels.packTyAt`]
    -- deliberately leaves free, so it is built once at an opened telescope and
    -- then instantiated. `none` when every index is a pivot.
    let pkAt := fun (ps : Array Expr) (vs : Array Expr) => do
      if npack == 0 then return (none : Option (Expr × Level))
      forallBoundedTelescope (← instForall memberTy ps) (some ni) fun is _ => do
        let (pkT, ℓ) ← packTyAt is packSel 0
        pure (some (pkT.replaceFVars is vs, ℓ))

    -- `∀ h⃗, Eq Pk (pack ι⃗_ctor|np) (pack ι⃗|np) → …`, the encoding's one
    -- minor, as a binder-introducing continuation so that the equation is
    -- built at the *bound* proof fields rather than at a stand-in.
    let underMinor := fun (ps is : Array Expr) (pk? : Option (Expr × Level))
        (mk : Array Expr → Expr → GenM Expr)
        (k : Array Expr → Option Expr → GenM Expr) =>
      if zipRoute then
        let (pk, ℓpk) := pk?.get!
        armFZipMinor eqi memberTy cty0 ni gIsData gIdxPos gPivotTransports
          ps is pk ℓpk (idxOfRes tname) mk fun fs h => k fs (some h)
      else
        fieldsAt ps is fun fs bnd res => do
          match pk? with
          | none => mk bnd (← k fs none)
          | some (pk, ℓpk) => do
            let idx ← idxOfRes tname res
            let lhs ← packChain npack pk (packSel.map (idx[·]!)) 0
            let rhs ← packChain npack pk (packSel.map (is[·]!)) 0
            withLocalDeclD `heq (eqi.mk' ℓpk pk lhs rhs) fun h => do
              mk (bnd.push h) (← k fs (some h))
    let allTy : Array Expr → Expr → GenM Expr := fun xs e => mkForallFVars xs e
    let lamF : Array Expr → Expr → GenM Expr := fun xs e => mkLambdaFVars xs e
    let minorTyAt := fun (ps is : Array Expr) (pk? : Option (Expr × Level)) (r : Expr) =>
      underMinor ps is pk? allTy (fun _ _ => pure r)
    let encodedAt := fun (ps is : Array Expr) => do
      let pk? ← pkAt ps is
      withLocalDeclD `r (.sort .zero) fun r => do
        mkForallFVars #[r] (.forallE `k (← minorTyAt ps is pk? r) r .default)

    -- ── the carrier ──
    let selfVal ← withParams fun ps => do
      forallBoundedTelescope (← instForall memberTy ps) (some ni) fun is _ => do
        let encoded ← encodedAt ps is
        mkLambdaFVars (ps ++ is)
          (match lift? with | none => encoded | some ℓ => puliftT ℓ encoded)
    let dSelf := Declaration.defnDecl
      { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfVal
        hints := ← hintsFor selfVal, safety := .safe }
    addChecked dSelf
    out := out.push dSelf

    -- ── the constructor ──
    -- Its own index vector is `ι⃗_ctor` at its own fields, so the pivots the
    -- carrier substitutes come back as exactly those fields and the stored
    -- equation is `Eq.refl`.
    let ty := publicSource cty0
    let cval ← withParams fun ps => do
      let rtele ← instForall ty ps
      let nf := numForalls rtele
      forallBoundedTelescope rtele (some nf) fun fs res => do
        let idx ← idxOfRes selfN res
        let pk? ← pkAt ps idx
        let args ← match pk? with
          | none => pure (((Array.range nf).filter (!gIsData[·]!)).map (fs[·]!))
          | some (pk, ℓpk) =>
            if zipRoute then
              armFZipCtorArgs eqi memberTy ni gIsData gIdxPos gPivotTransports ps idx fs pk ℓpk
            else do
              let bnd := ((Array.range nf).filter (!gIsData[·]!)).map (fs[·]!)
              pure (bnd.push (eqi.refl' ℓpk pk
                (← packChain npack pk (packSel.map (idx[·]!)) 0)))
        let encoded ← encodedAt ps idx
        let proof ← withLocalDeclD `r (.sort .zero) fun r => do
          withLocalDeclD `k (← minorTyAt ps idx pk? r) fun kk =>
            mkLambdaFVars #[r, kk] (mkAppN kk args)
        mkLambdaFVars (ps ++ fs)
          (match lift? with | none => proof | some ℓ => puliftUp ℓ encoded proof)
    let dCtor := Declaration.defnDecl
      { name := ctorN 0, levelParams := lparams, type := ty, value := cval
        hints := ← hintsFor cval, safety := .safe }
    addChecked dCtor
    out := out.push dCtor

    -- ── the recursor ──
    let recVal ← forallBoundedTelescope installedRecTy
        (some (np + 1 + nc + ni + 1)) fun bs _ => do
      let ps := bs.extract 0 np
      let motive := bs[np]!
      let minor := bs[np + 1]!
      let idxs := bs.extract (np + 1 + nc) (np + 1 + nc + ni)
      let t := bs[bs.size - 1]!
      let pk? ← pkAt ps idxs
      let encoded ← encodedAt ps idxs
      let base := match lift? with | none => t | some ℓ => puliftDown ℓ encoded t
      let tele ← instForall cty0 ps
      let nf := numForalls tele
      if zipRoute then
        let (pk, ℓpk) := pk?.get!
        let body ← armFZipModelRec eqi lift? memberTy cty0 ni gIsData gIdxPos
          gPivotTransports ps idxs base pk motive minor ℓpk (idxOfRes tname)
          (fun full r => minorTyAt ps full (some (pk, ℓpk)) r)
          (fun full => encodedAt ps full)
        return ← mkLambdaFVars bs body
      -- **Recover the fields.** Ordinarily a data field is the recursor's own
      -- index argument at that field's pivot position.  When its declared type
      -- depends on a non-pivot, the packed equation canonically transports it
      -- below before it reaches the minor. A proof field is extracted sequentially: a
      -- later field's type is instantiated at the earlier recoveries, and the
      -- projector is written at the carrier's own minor telescope so that a
      -- field whose type mentions a *data* field is asked for at the index and
      -- not at a stand-in.
      let mut es : Array Expr := #[]
      let mut curT := tele
      for i in [0:nf] do
        let .forallE _ ft rest _ := curT | badShape "telescope shorter than its field count"
        let v ←
          if gIsData[i]! then pure idxs[gIdxPos[i]!]!
          else do
            let proj ← underMinor ps idxs pk? lamF fun fs _ => pure fs[i]!
            pure (mkAppN base #[ft, proj])
        es := es.push v
        curT := rest.instantiate1 v
      -- the proof fields alone, in telescope order: what the carrier's minor
      -- binds and what the rebuilt carrier proof below is applied to.
      let esBnd := ((Array.range nf).filter (!gIsData[·]!)).map (es[·]!)
      -- the constructor's index vector at the recovered fields
      let idxE ← idxOfRes tname (← instForall (← instForall cty0 ps) es)
      match pk? with
      | none =>
        -- Every index is a pivot: `ι⃗_ctor` at the recovered fields **is**
        -- `ι⃗`, and `T._model.ctor_0 es` is `t` by proof irrelevance.
        mkLambdaFVars bs (mkAppN minor es)
      | some (pk, ℓpk) => do
        let pkc ← packChain npack pk (packSel.map (idxE[·]!)) 0
        let pki ← packChain npack pk (packSel.map (idxs[·]!)) 0
        let eqTy := eqi.mk' ℓpk pk pkc pki
        let heq := mkAppN base #[eqTy, ← underMinor ps idxs pk? lamF
          fun _ h? => pure h?.get!]
        -- one `Eq.rec` at the packed point: the motive rebuilds a carrier
        -- proof at each `y`, and `pack (unpack y) ≡ y` makes it typecheck.
        -- Only the **non-pivot** slots move with `y`; the pivots are the
        -- recursor's own index arguments throughout, which is why no transport
        -- is needed on the fields.
        let fam := fun (y : Expr) (h : Expr) => do
          let ys ← unpackChain npack pk y
          let mut full := idxs
          for k in [0:npack] do full := full.set! packSel[k]! ys[k]!
          let rebuilt ← withLocalDeclD `r (.sort .zero) fun r => do
            withLocalDeclD `k (← minorTyAt ps full pk? r) fun kk =>
              mkLambdaFVars #[r, kk] (mkAppN kk (esBnd.push h))
          let lifted ← match lift? with
            | none => pure rebuilt
            | some ℓ => pure (puliftUp ℓ (← encodedAt ps full) rebuilt)
          pure (mkAppN motive (full.push lifted))
        let motiveE ← withLocalDeclD `y pk fun y => do
          withLocalDeclD `hy (eqi.mk' ℓpk pk pkc y) fun hy => do
            mkLambdaFVars #[y, hy] (← fam y hy)
        mkLambdaFVars bs (eqi.recAt v ℓpk pk pkc motiveE (mkAppN minor es) pki heq)
    let dRec := Declaration.defnDecl
      { name := recN, levelParams := rv.levelParams, type := publicRecTy, value := recVal
        hints := ← hintsFor recVal, safety := .safe }
    addChecked dRec
    out := out.push dRec
  else if armC then
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
    let goodTy ← withParams fun ps => do
      let (pk, _) ← pkAt ps
      withLocalDeclD `s (skelSelf ps) fun s => withLocalDeclD `y pk fun y =>
        mkForallFVars (ps ++ #[s, y]) (.sort .zero)
    let goodVal ← withParams fun ps => do
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
    let selfVal ← withParams fun ps => do
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
      let val ← withParams fun ps => do
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
  else if armE then
    -- ════ arm E: an exact empty model for recursion without a base ════
    unless large do badShape s!"{ern} is not large-eliminating at a Type-valued carrier"
    for d in ← ensureNat reserved do out := out.push d; spliced := spliced ++ d.getNames
    for d in ← ensureExactSortLift reserved do out := out.push d; spliced := spliced ++ d.getNames

    -- The carrier is empty at exactly the inductive's universe.
    let selfVal ← withParams fun ps =>
      mkLambdaFVars ps (emptyAt w)
    let dSelf := Declaration.defnDecl
      { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfVal
        hints := ← hintsFor selfVal, safety := .safe }
    addChecked dSelf
    out := out.push dSelf

    -- A constructor cannot manufacture an element: its direct recursive
    -- field already inhabits the empty carrier, so return it.
    for j in [0:nc] do
      let (_, cty) := exportCtors[j]!
      let ty := publicSource cty
      let nfj ← withParams fun ps => do pure (numForalls (← instForall cty ps))
      let val ← withParams fun ps => do
        let rtele ← instForall ty ps
        forallBoundedTelescope rtele (some nfj) fun fs _ => do
          let some k := emptySlots[j]!
            | badShape s!"{exportCtors[j]!.1} has no recursive field in the empty route"
          mkLambdaFVars (ps ++ fs) fs[k]!
      let d := Declaration.defnDecl
        { name := ctorN j, levelParams := lparams, type := ty, value := val
          hints := ← hintsFor val, safety := .safe }
      addChecked d
      out := out.push d

    -- The major premise is an inhabitant of the empty carrier.  Eliminating
    -- it gives the recursor's motive at any result universe.
    let recVal ← forallBoundedTelescope installedRecTy (some (np + 1 + nc + 1)) fun bs _ => do
      let motive := bs[np]!
      let major := bs[bs.size - 1]!
      mkLambdaFVars bs (← emptyAtElim eqi v w (mkApp motive major) major)
    let dRec := Declaration.defnDecl
      { name := recN, levelParams := rv.levelParams, type := publicRecTy, value := recVal
        hints := ← hintsFor recVal, safety := .safe }
    addChecked dRec
    out := out.push dRec
  else if armW then
    -- ════ arm W: branching and infinitary, out of the spliced W core ════
    --
    -- The tagged W construction and its untagged instantiation. Six
    -- definitions, the constructors, one `Nat.rec` cascade for `rec_0` and one
    -- `WT.Wrec_iota` per rule. Junk uninhabited in both directions and both
    -- towers ending at exactly the selected `Sort wW`, at either instantiation.
    --
    -- **The two differ in four declarations and nowhere else**:
    -- `Tel`'s and `B'`'s domain (the tag, or the whole label), `tg` (the first
    -- projection, or the identity) and `DecidableEq K`. `D` and `A` are
    -- literally the same term.
    unless large do badShape s!"{ern} is not large-eliminating at a Type-valued carrier"
    for n in [wDN, wTelN, wBN, wAN, wTgN, wFN] do taken n

    -- **The level question, before anything is spliced.** Both towers are
    -- written with codomain level `wW`, so every field and every recursive
    -- field's binder must satisfy `max ℓ wW ≡ wW`. Exposed `imax` components are
    -- measured after the same recursive boxing the towers will use; anything
    -- still too large fails here rather than 528 KB later.
    withParams fun ps => do
      for k in [0:nc] do
        let (cn, cty) := exportCtors[k]!
        let (nrs, rcs) ← wShapeOf k
        let tele ← instForall cty ps
        forallBoundedTelescope tele (some (numForalls tele)) fun fs _ => do
          if let some ℓ ← wTowerLevelOf wW (nrs.map (fs[·]!)) then
            badShape s!"{cn} has a non-recursive field at Sort {ℓ} and the carrier is \
Sort {wW}, so the data tower does not land at the W core's sort"
          for i in rcs do
            forallTelescope (← ityp fs[i]!) fun zs res => do
              -- Lean's recursive-argument test reduces transparent aliases.
              -- Ask the same definitional question here, but use it only for
              -- recognition: `wRecDom`, every public type restored below, and
              -- the iota statement all retain the export's literal syntax.
              -- `AliasW.lim : (N → As AliasW) → AliasW` is the witness: `As`
              -- is not a nested container, and its result is definitionally
              -- the owner at precisely these parameters.
              let self := mkAppN (.const tname us) ps
              unless ← isDefEq res self do
                badShape s!"{cn}'s recursive field {i} does not reduce to {tname} at its \
own parameters under its binders, so it is nested rather than infinitary"
              if let some ℓ ← wTowerLevelOf wW zs then
                badShape s!"{cn}'s recursive field {i} has a binder at Sort {ℓ} and the \
carrier is Sort {wW}, so the branch tower does not land at the W core's sort"

    for d in ← ensureNat reserved do out := out.push d; spliced := spliced ++ d.getNames
    for d in ← ensurePSigmaPrime reserved do out := out.push d; spliced := spliced ++ d.getNames
    for d in ← ensureExactSortLift reserved do out := out.push d; spliced := spliced ++ d.getNames
    -- **The core itself.** `#[]` when it is
    -- already in, which is every W target after the first in a run.
    let core ← ensureWCore reserved
    for d in core do out := out.push d; spliced := spliced ++ d.getNames
    -- **The inductives the core brought with it, which this model may not
    -- leave unmodelled** — `Iso.requires`' rule, and the same one arm C's
    -- skeleton is under. Empty when the fragment was already spliced, and that
    -- is not a hole: [`InductiveModels.genPrim`] rolls the environment back on every
    -- withdrawal and on every decline, so a fragment that is *present* was put
    -- there by an earlier model whose own `requires` were met.
    let wRequires : Array Name := core.flatMap fun d =>
      match d with
      | .inductDecl _ _ types _ =>
        (types.map (·.name)).toArray.filter (!inductiveBasis.contains ·)
      | _ => #[]

    let unitMot : Expr := .lam `x wNatT (.sort wW) .default
    let junkTy : Expr → GenM Expr := fun _ => pure (emptyAt wW)

    -- ── `D` — tag ↦ that constructor's non-recursive fields ──
    let dTy ← withParams fun ps =>
      mkForallFVars ps (.forallE `t wNatT (.sort wW) .default)
    let dVal ← withParams fun ps => withLocalDeclD `t wNatT fun t => do
      mkLambdaFVars (ps.push t)
        (← natCascade (.succ wW) nc (fun _ => pure unitMot) (wDataTy ps) junkTy 0 t)
    let dD := Declaration.defnDecl
      { name := wDN, levelParams := lparams, type := dTy, value := dVal
        hints := ← hintsFor dVal, safety := .safe }
    addChecked dD
    out := out.push dD

    -- ── `A` — the label, tag paired with that constructor's data ──
    -- **Emitted before `Tel` at the untagged instantiation**, because there
    -- `Tel` and `B'` are indexed by the label rather than by the tag and would
    -- name a constant absent from the environment. At the tagged one it
    -- keeps its old place, so nothing about that emission moves.
    let aTyD ← withParams fun ps => mkForallFVars ps (.sort wW)
    let aVal ← withParams fun ps =>
      mkLambdaFVars ps (psigmaT (.succ .zero) wW wNatT (wDAt ps))
    let dA := Declaration.defnDecl
      { name := wAN, levelParams := lparams, type := aTyD, value := aVal
        hints := ← hintsFor aVal, safety := .safe }
    unless wTagged do
      addChecked dA
      out := out.push dA

    -- ── `Tel` — the branch type's telescope, at a key and a branch index ──
    -- Two cascades: a branch index past a constructor's recursive-field count
    -- must be as
    -- empty as a tag past the constructor count, or `W` acquires children no
    -- constructor produces and the model is strictly bigger than the target.
    --
    -- **Untagged, the outer cascade's motive takes the data as an argument.**
    -- This is the whole untagged delta and the one thing the tag scheme has no
    -- analogue of: the cascade is still on the tag — a `Nat`, so
    -- still `Nat.rec` — but each arm receives that constructor's own `D t` and
    -- projects the fields its children's binders mention out of it.
    let telKey : Name := if wTagged then `t else `a
    let telTyD ← withParams fun ps => mkForallFVars ps
      (.forallE telKey (wKTy ps) (.forallE `j wNatT (.sort wW) .default) .default)
    let telVal ← withParams fun ps =>
      withLocalDeclD telKey (wKTy ps) fun a => withLocalDeclD `j wNatT fun j => do
        if wTagged then
          let arm : Nat → GenM Expr := fun k => do
            natCascade (.succ wW) (← wRecCount k) (fun _ => pure unitMot)
              (wTelTy ps k #[]) junkTy 0 j
          mkLambdaFVars (ps ++ #[a, j])
            (← natCascade (.succ wW) nc (fun _ => pure unitMot) arm junkTy 0 a)
        else
          let dAt : Expr → Expr := fun t => mkAppN (.const wDN us) (ps ++ #[t])
          -- `fun t => D p⃗ (succ^kk t) → Nat → Sort wW`, which lands in `Sort wW+1`
          -- exactly as the tagged motive does.
          let motAt : Nat → GenM Expr := fun kk =>
            withLocalDeclD `t wNatT fun t => mkLambdaFVars #[t]
              (.forallE `d (dAt (natSuccs kk t))
                (.forallE `j wNatT (.sort wW) .default) .default)
          let armAt : Nat → GenM Expr := fun k =>
            withLocalDeclD `d (dAt (natNumeral k)) fun d =>
              withLocalDeclD `jj wNatT fun jj => do
                mkLambdaFVars #[d, jj]
                  (← natCascade (.succ wW) (← wRecCount k) (fun _ => pure unitMot)
                    (wTelTy ps k (← wNrProjs ps k d)) junkTy 0 jj)
          -- **The junk tag's arm is a constant and need not be empty**:
          -- `A = Σ' t, D t` and `D`'s own junk arm
          -- is already `PEmpty`, so `Tel` is never asked at a tag no
          -- constructor has. It is written empty anyway; the requirement that
          -- is load-bearing is the *branch index* one above, and that one is
          -- `junkTy`.
          let junkAt : Expr → GenM Expr := fun t =>
            withLocalDeclD `d (dAt (natSuccs nc t)) fun d =>
              withLocalDeclD `jj wNatT fun jj => mkLambdaFVars #[d, jj] (emptyAt wW)
          let a1 := psigmaFst (.succ .zero) wW wNatT (wDAt ps) a
          let a2 := psigmaSnd (.succ .zero) wW wNatT (wDAt ps) a
          mkLambdaFVars (ps ++ #[a, j])
            (mkApp (mkApp (← natCascade (.succ wW) nc motAt armAt junkAt 0 a1) a2) j)
    let dTel := Declaration.defnDecl
      { name := wTelN, levelParams := lparams, type := telTyD, value := telVal
        hints := ← hintsFor telVal, safety := .safe }
    addChecked dTel
    out := out.push dTel

    -- ── `B'` and `tg` ──
    let bTyD ← withParams fun ps =>
      mkForallFVars ps (.forallE telKey (wKTy ps) (.sort wW) .default)
    let bVal ← withParams fun ps => withLocalDeclD telKey (wKTy ps) fun t => do
      mkLambdaFVars (ps.push t) (← wBAt ps t)
    let dB := Declaration.defnDecl
      { name := wBN, levelParams := lparams, type := bTyD, value := bVal
        hints := ← hintsFor bVal, safety := .safe }
    addChecked dB
    out := out.push dB

    if wTagged then
      addChecked dA
      out := out.push dA

    -- `PSigma'.fst` at the tag scheme and the identity at the label scheme. The
    -- latter is the former at `tg := id`, and this line is where that reading
    -- is cashed.
    let tgTyD ← withParams fun ps =>
      mkForallFVars ps (.forallE `a (wAAt ps) (wKTy ps) .default)
    let tgVal ← withParams fun ps => withLocalDeclD `a (wAAt ps) fun a => do
      mkLambdaFVars (ps.push a)
        (if wTagged then psigmaFst (.succ .zero) wW wNatT (wDAt ps) a else a)
    let dTg := Declaration.defnDecl
      { name := wTgN, levelParams := lparams, type := tgTyD, value := tgVal
        hints := ← hintsFor tgVal, safety := .safe }
    addChecked dTg
    out := out.push dTg

    -- ── the carrier ──
    let selfVal ← withParams fun ps => mkLambdaFVars ps
      (wPlan.carrier (wLowSelfAt ps))
    let dSelf := Declaration.defnDecl
      { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfVal
        hints := ← hintsFor selfVal, safety := .safe }
    addChecked dSelf
    out := out.push dSelf

    -- ── the constructors ──
    for j in [0:nc] do
      let ty := publicSource exportCtors[j]!.2
      let val ← withParams fun ps => do
        let rtele ← instForall ty ps
        forallBoundedTelescope rtele (some (numForalls rtele)) fun fs _ => do
          let (a, disp) ← wCtorParts ps j fs
          mkLambdaFVars (ps ++ fs) (wPlan.wrap (wLowSelfAt ps) (wSup ps a disp))
      let d := Declaration.defnDecl
        { name := ctorN j, levelParams := lparams, type := ty, value := val
          hints := ← hintsFor val, safety := .safe }
      addChecked d
      out := out.push d

    -- ── `F`, the core's minor, as its own declaration ──
    -- **Hoisted rather than inlined**, because it is named once by `rec_0` and
    -- once by *every* ι rule while being itself `nc` arms deep, each arm
    -- carrying its own eta lemma: inlined, the emitted output is quadratic in
    -- the constructor count for nothing, and the kernel checks the same
    -- cascade `nc + 1` times. Hoisted, the ι rule's left side and its proof
    -- name the same constant.
    let fTy ← forallBoundedTelescope installedRecTy (some (np + 1 + nc)) fun pre _ => do
      let ps := pre.extract 0 np
      let motive := pre[np]!
      let selfTy := wLowSelfAt ps
      let coreMotive ← wPlan.motive (wLowSelfAt ps) motive
      withLocalDeclD `a (wAAt ps) fun a => do
        let bt ← wBAt ps (mkApp (wTgAt ps) a)
        withLocalDeclD `f (.forallE `b bt selfTy .default) fun f => do
          let ihT ← withLocalDeclD `b bt fun b =>
            mkForallFVars #[b] (mkApp coreMotive (mkApp f b))
          withLocalDeclD `ih ihT fun ih =>
            mkForallFVars (pre ++ #[a, f, ih]) (mkApp coreMotive (wSup ps a f))
    let fVal ← forallBoundedTelescope installedRecTy (some (np + 1 + nc)) fun pre _ => do
      mkLambdaFVars pre
        (← wMkF (pre.extract 0 np) pre[np]! (pre.extract (np + 1) (np + 1 + nc)))
    let dF := Declaration.defnDecl
      { name := wFN, levelParams := rv.levelParams, type := fTy, value := fVal
        hints := ← hintsFor fVal, safety := .safe }
    addChecked dF
    out := out.push dF

    -- ── the recursor ──
    let recVal ← forallBoundedTelescope installedRecTy
        (some (np + 1 + nc + 1)) fun bs _ => do
      let ps := bs.extract 0 np
      let major := bs[bs.size - 1]!
      let coreMotive ← wPlan.motive (wLowSelfAt ps) bs[np]!
      mkLambdaFVars bs (mkAppN (.const wCoreRec [uL, v, wKL])
        #[wKTy ps, wAAt ps, wBFn ps, wDecEq ps, wTgAt ps, coreMotive,
          mkAppN (.const wFN recLs) (bs.extract 0 (np + 1 + nc)),
          wPlan.unwrap (wLowSelfAt ps) major])
    let dRec := Declaration.defnDecl
      { name := recN, levelParams := rv.levelParams, type := publicRecTy, value := recVal
        hints := ← hintsFor recVal, safety := .safe }
    addChecked dRec
    out := out.push dRec
    requires := wRequires
  else if route matches PrimRoute.type then
    -- ════ the Type route ════
    unless large do badShape s!"{ern} is not large-eliminating at a Type-valued carrier"
    for d in ← ensureNat reserved do out := out.push d; spliced := spliced ++ d.getNames
    for d in ← ensurePSigmaPrime reserved do out := out.push d; spliced := spliced ++ d.getNames
    for d in ← ensureExactSortLift reserved do out := out.push d; spliced := spliced ++ d.getNames

    -- Storage decisions — pure level arithmetic, and a decline here costs no
    -- further splice. A chain of one field is that field bare (no `PSigma'`,
    -- so no pair); longer tight chains carry exactly `max ℓ⃗`. A pad at `1`
    -- deliberately raises this to `max 1 ℓ⃗`, and `w` itself covers a raised
    -- carrier — at *any* `w` now, since the derived lift exists at every level.
    -- What no pad absorbs is an `imax` in a field's level: those fields are
    -- recursively boxed ([`InductiveModels.boxTyOf`]) and the plan is retried on the
    -- boxed levels, whose exposed Π codomains are never-zero `max`es.
    let plans : Array CPlan ← withParams fun ps =>
      exportCtors.mapM fun (cn, cty) => do
        let tele ← instForall cty ps
        let nf := numForalls tele
        forallBoundedTelescope tele (some nf) fun fs _ => do
          let tys ← fs.mapM ityp
          let ℓs ← tys.mapM ilevel
          -- The three storage questions, asked with whichever level equality
          -- the caller passes.
          let plan : (Level → Level → GenM Bool) → Array Level →
              GenM (Option (Option Level)) := fun eq ms => do
            let raw := if nf == 1 then ms[0]! else (ms.foldl mkLevelMax' .zero).normalize
            if nf > 0 then
              if ← eq raw w then return some none
            let withOne := (ms.foldl mkLevelMax' (.succ .zero)).normalize
            if ← eq withOne w then return some (some (Level.succ .zero))
            if ← eq (mkLevelMax' withOne w) w then return some (some w)
            return none
          -- bare first, then the same questions again on the boxed levels
          let attempt : (Level → Level → GenM Bool) → GenM (Option CPlan) := fun eq => do
            if let some pad? ← plan eq ℓs then
              return some { boxed := Array.replicate nf false, pad? }
            let boxed := ℓs.map fun ℓ => levelHasIMax ℓ.normalize
            if boxed.any id then
              let ms ← (Array.range nf).mapM fun k => do
                if boxed[k]! then ilevel (← boxTyOf tys[k]!) else pure ℓs[k]!
              if let some pad? ← plan eq ms then
                return some { boxed, pad? }
            return none
          -- **The elaborator gets first refusal, and that ordering is the
          -- whole design.** `LevelAlgebra.isLevelDefEqComplete` is complete
          -- where `isLevelDefEq` is not, but a level equality only the
          -- *complete* procedure can see is one **Lean's kernel cannot see
          -- either** — the kernel's `lean::is_equivalent` is a different
          -- function with the same `max`-does-not-absorb-`imax` gap. So a
          -- plan reached only by the complete procedure is not justified by
          -- the stock kernel equality used by the optional exact generated gate.
          --
          -- Asking completely *first* is therefore actively worse, and was
          -- measured so: `Trans` in `init-prelude` has a bare chain the
          -- complete procedure equates to `w` and the stock kernel does not,
          -- so it took the unboxed plan and the exact generated gate rejected it
          -- — where the elaborator's own refusal had sent it to the boxing
          -- retry, which the stock kernel accepts. Coverage went 125 → 124. Second
          -- refusal costs nothing and cannot lose a plan that already works:
          -- every accepted declaration keeps the route chosen by the first
          -- procedure, and the complete procedure is consulted only where
          -- the alternative is a decline.
          if let some p ← attempt (fun a b => isLevelDefEq a b) then return p
          if let some p ← attempt (fun a b => LevelAlgebra.isLevelDefEqComplete a b) then
            return p
          let raw := if nf == 1 then ℓs[0]! else (ℓs.foldl mkLevelMax' .zero).normalize
          badShape s!"{cn}'s fields reach Sort {raw} and the carrier is Sort {w}: no \
            pad or recursive box closes the gap"

    -- A pad at a level `dsingOk` cannot build is discharged by transport
    -- along the lift's eta ([`InductiveModels.unitAtUniq`]) — a recursor call and
    -- proof irrelevance. The `False`-Π pad this replaces needed `funext`
    -- here, and with it `Quot.sound` and a wait on the input's quotient; the
    -- construction now splices neither.
    let natT : Expr := .const `Nat []
    let fibreAt := fun (ps : Array Expr) => do
      let pads ← padsAt plans
      let cs ← pctorsAt exportCtors plans pads ps
      withLocalDeclD `n natT fun n =>
        return (cs, ← mkLambdaFVars #[n] (← fibreTower w cs 0 n))

    -- Which constructors carry the recursion, and where. Empty for a
    -- non-recursive declaration, in which case everything below degenerates
    -- to the single tag tower the previous tranche had.
    let slots : Array (Option Nat) ← withParams fun ps =>
      exportCtors.mapM fun (cn, cty) => do
        let tele ← instForall cty ps
        recSlotOf tname np ni cn (numForalls tele) tele wTagged
          w.normalize.dec.isSome (labelFactored tname np exportCtors)
    let baseJ := (Array.range nc).filter fun j => slots[j]!.isNone
    let stepJ := (Array.range nc).filter fun j => slots[j]!.isSome
    -- Arm E has already taken every recursive declaration without a base
    -- constructor.  Keep this assertion beside the sole `baseJ[0]` consumer:
    -- reaching it would be an internal route-classification error.
    if isRec && baseJ.isEmpty then
      badShape s!"internal: {tname}'s empty recursive shape missed the empty route"
    -- export constructor index ↦ its tag *within its own tower*
    let tagOf : Array Nat := (Array.range nc).map fun j =>
      let tower := if slots[j]!.isNone then baseJ else stepJ
      (tower.findIdx? (· == j)).getD 0

    -- The tag tower of a set of constructors, at a parameter scope. `sub` is
    -- the shorter spine's fibre `V n`, which a step constructor's chain
    -- stores in place of its recursive field; base constructors never look
    -- at it.
    let towerAt : Array Expr → Array Nat → Expr → GenM (Array PCtor × Expr) :=
      fun ps js sub => do
      let pads ← padsAt plans
      let cs : Array PCtor ← js.mapM fun j => do
        let (_, cty) := exportCtors[j]!
        let tele0 ← instForall cty ps
        let nf := numForalls tele0
        let tele ← spineSwap tname sub nf tele0
        let pl : CPlan := plans[j]!
        let (chain, _) ← chainTy pads[j]! pl.boxed nf tele
        pure { tele, nf, pad? := pads[j]!, boxed := pl.boxed, chain }
      let fib ← withLocalDeclD `tag natT fun tg =>
        do mkLambdaFVars #[tg] (← fibreTower w cs 0 tg)
      return (cs, fib)

    -- `V : Nat → Sort w`, the spine tower: base chains at spine 0, step
    -- chains at every successor, with the predecessor's fibre plugged in.
    let spineAt := fun (ps : Array Expr) => do
      let (_, bfib) ← towerAt ps baseJ (.sort w)
      let zc := psigmaT (.succ .zero) w natT bfib
      let sc ← withLocalDeclD `n natT fun n =>
        withLocalDeclD `R (.sort w) fun R => do
          let (_, sfib) ← towerAt ps stepJ R
          mkLambdaFVars #[n, R] (psigmaT (.succ .zero) w natT sfib)
      withLocalDeclD `n natT fun n =>
        mkLambdaFVars #[n]
          (natRec (.succ w) (.lam `x natT (.sort w) .default) zc sc n)

    -- ── the carrier ──
    -- Non-recursive: one tag tower under a `Nat`. Linearly recursive: the
    -- spine tower, `Σ'(n : Nat), V n`.
    let carrierAt := fun (ps : Array Expr) => do
      if isRec then pure (psigmaT (.succ .zero) w natT (← spineAt ps))
      else do pure (psigmaT (.succ .zero) w natT (← fibreAt ps).2
    )
    let selfVal ← withParams fun ps => do mkLambdaFVars ps (← carrierAt ps)
    let dSelf := Declaration.defnDecl
      { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfVal
        hints := ← hintsFor selfVal, safety := .safe }
    addChecked dSelf
    out := out.push dSelf

    -- ── the constructors ──
    for j in [0:nc] do
      let (_, cty) := exportCtors[j]!
      let ty := publicSource cty
      let val ← withParams fun ps => do
        if !isRec then
          let (cs, fib) ← fibreAt ps
          let c := cs[j]!
          forallBoundedTelescope c.tele (some c.nf) fun fs _ => do
            let tup ← chainTuple c.pad? c.boxed c.nf c.tele fs
            mkLambdaFVars (ps ++ fs)
              (psigmaMk (.succ .zero) w natT fib (natNumeral j) tup)
        else do
          -- The binders come from the **restored** telescope: the recursive
          -- field's type there is `T._model.self p⃗`, i.e. the spine pair, and
          -- what goes into the chain is its second component.
          let spine ← spineAt ps
          let rtele ← instForall ty ps
          let nf := numForalls rtele
          forallBoundedTelescope rtele (some nf) fun fs _ => do
            let mkOuter := fun (n tup : Expr) =>
              psigmaMk (.succ .zero) w natT spine n tup
            match slots[j]! with
            | none =>
              let (bcs, bfib) ← towerAt ps baseJ (.sort w)
              let c := bcs[tagOf[j]!]!
              let tup ← chainTuple c.pad? c.boxed c.nf c.tele fs
              mkLambdaFVars (ps ++ fs) (mkOuter (natNumeral 0)
                (psigmaMk (.succ .zero) w natT bfib (natNumeral (tagOf[j]!)) tup))
            | some k =>
              let r := fs[k]!
              let rn := psigmaFst (.succ .zero) w natT spine r
              let rv2 := psigmaSnd (.succ .zero) w natT spine r
              let (scs, sfib) ← towerAt ps stepJ (mkApp spine rn).headBeta
              let c := scs[tagOf[j]!]!
              let tup ← chainTuple c.pad? c.boxed c.nf c.tele (fs.set! k rv2)
              mkLambdaFVars (ps ++ fs) (mkOuter (.app (.const `Nat.succ []) rn)
                (psigmaMk (.succ .zero) w natT sfib (natNumeral (tagOf[j]!)) tup))
      let d := Declaration.defnDecl
        { name := ctorN j, levelParams := lparams, type := ty, value := val
          hints := ← hintsFor val, safety := .safe }
      addChecked d
      out := out.push d

    -- ── the recursor ──
    let recVal ← forallBoundedTelescope installedRecTy
        (some (np + 1 + nc + 1)) fun bs _ => do
      let ps := bs.extract 0 np
      let motive := bs[np]!
      let minors := bs.extract (np + 1) (np + 1 + nc)
      let major := bs[bs.size - 1]!
      if !isRec then
        let (cs, fib) ← fibreAt ps
        let minor ←
          if nc == 0 then
            withLocalDeclD `n natT fun n => do
              withLocalDeclD `f (emptyAt w) fun f => do
                mkLambdaFVars #[n, f] (← emptyAtElim eqi v w
                  (mkApp motive (psigmaMk (.succ .zero) w natT fib n f)) f)
          else
            withLocalDeclD `n natT fun n => do
              withLocalDeclD `f (mkApp fib n).headBeta fun f => do
                mkLambdaFVars #[n, f]
                  (mkApp (← stepTower v w eqi fib (fun z => mkApp motive z)
                    (fun j vs => mkAppN minors[j]! vs) cs 0 n) f)
        mkLambdaFVars bs (psigmaRec v (.succ .zero) w natT fib motive minor major)
      else do
        -- `PSigma'.rec'` on the outer pair, `Nat.rec` on the spine, the tag
        -- towers inside each level, `PSigma'.rec'` down each chain.
        let spine ← spineAt ps
        let mkOuter := fun (n tup : Expr) => psigmaMk (.succ .zero) w natT spine n tup
        -- the Nat.rec motive: `fun n => (x : V n) → motive ⟨n, x⟩`
        let nmot ← withLocalDeclD `n natT fun n =>
          withLocalDeclD `x (mkApp spine n).headBeta fun x => do
            mkLambdaFVars #[n] (← mkForallFVars #[x] (mkApp motive (mkOuter n x)))
        -- spine 0: the base tower
        let zc ← do
          let (bcs, bfib) ← towerAt ps baseJ (.sort w)
          withLocalDeclD `x (psigmaT (.succ .zero) w natT bfib) fun x => do
            let tgt := fun (tup : Expr) => mkApp motive (mkOuter (natNumeral 0) tup)
            let minorOf := fun (b : Nat) (vs : Array Expr) => mkAppN minors[baseJ[b]!]! vs
            let inner ← withLocalDeclD `tag natT fun tg =>
              withLocalDeclD `f (mkApp bfib tg).headBeta fun f => do
                mkLambdaFVars #[tg, f]
                  (mkApp (← stepTower v w eqi bfib tgt minorOf bcs 0 tg) f)
            let mot ← withLocalDeclD `z (psigmaT (.succ .zero) w natT bfib) fun z =>
              mkLambdaFVars #[z] (mkApp motive (mkOuter (natNumeral 0) z))
            mkLambdaFVars #[x]
              (psigmaRec v (.succ .zero) w natT bfib mot inner x)
        -- spine n+1: the step tower, with the induction hypothesis in hand
        let sc ← withLocalDeclD `n natT fun n =>
          withLocalDeclD `ih (mkApp nmot n).headBeta fun ih => do
            let sub := (mkApp spine n).headBeta
            let (scs, sfib) ← towerAt ps stepJ sub
            let nsucc := Expr.app (.const `Nat.succ []) n
            withLocalDeclD `x (psigmaT (.succ .zero) w natT sfib) fun x => do
              let tgt := fun (tup : Expr) => mkApp motive (mkOuter nsucc tup)
              let minorOf := fun (b : Nat) (vs : Array Expr) =>
                let j := stepJ[b]!
                let k := (slots[j]!).getD 0
                let sv := vs[k]!
                mkAppN minors[j]! ((vs.set! k (mkOuter n sv)).push (mkApp ih sv))
              let inner ← withLocalDeclD `tag natT fun tg =>
                withLocalDeclD `f (mkApp sfib tg).headBeta fun f => do
                  mkLambdaFVars #[tg, f]
                    (mkApp (← stepTower v w eqi sfib tgt minorOf scs 0 tg) f)
              let mot ← withLocalDeclD `z (psigmaT (.succ .zero) w natT sfib) fun z =>
                mkLambdaFVars #[z] (mkApp motive (mkOuter nsucc z))
              mkLambdaFVars #[n, ih, x]
                (psigmaRec v (.succ .zero) w natT sfib mot inner x)
        let minor ← withLocalDeclD `n natT fun n =>
          withLocalDeclD `x (mkApp spine n).headBeta fun x => do
            mkLambdaFVars #[n, x]
              (mkApp (natRec (mkLevelIMax' w v).normalize nmot zc sc n) x)
        mkLambdaFVars bs (psigmaRec v (.succ .zero) w natT spine motive minor major)
    let dRec := Declaration.defnDecl
      { name := recN, levelParams := rv.levelParams, type := publicRecTy, value := recVal
        hints := ← hintsFor recVal, safety := .safe }
    addChecked dRec
    out := out.push dRec
  else
    -- ════ the Church routes: `Prop`, and the maybe-zero sort under a lift ════
    --
    -- One construction serves both. At `Sort 0` the carrier is the
    -- impredicative Church encoding itself; at a **maybe-zero** sort it is
    -- that same encoding under the derived lift, which puts it at exactly `Sort w`
    -- for any `w`. The constructors are the folds, `up` of the folds under a
    -- lift. The recursor is the fold at the right `C`, plus — under a lift —
    -- one transport along [`InductiveModels.puliftEta`], because the lifted `p` is not
    -- itself a proposition and proof irrelevance no longer closes the
    -- "which element" question by itself.
    --
    -- Why this is a model and not a collapse: at a maybe-zero sort the
    -- contract never forces two provably distinct elements. Zero constructors
    -- and the subsingleton shape large-eliminate and are subsingletons
    -- anyway; everything else there small-eliminates, so the motive lands in
    -- `Prop` and cannot discriminate. The lift of a proposition is exactly
    -- the right size.
    let lift? : Option Level := if route matches PrimRoute.bare then some w else none

    -- The index telescope at a parameter scope, and the Church motive's type
    -- `C : ∀ ι⃗, Prop` over it. At `ni = 0` this is just `Prop` and everything
    -- below degenerates to the original non-indexed construction.
    let idxTeleAt := fun (ps : Array Expr) => instForall memberTy ps
    let motiveTyAt := fun (ps : Array Expr) => do
      forallBoundedTelescope (← idxTeleAt ps) (some ni) fun is _ =>
        mkForallFVars is (.sort .zero)

    let churchAt := fun (ps : Array Expr)
        (k : Expr → Array Expr → Array Expr → GenM Expr) => do
      -- `C`, the `k_j` binders, and their types, in one scope. Each `k_j` is
      -- constructor `j`'s telescope with `T p⃗` replaced by `C` — at its
      -- recursive fields as well as at its result.
      withLocalDeclD `C (← motiveTyAt ps) fun C => do
        let kTys ← exportCtors.mapM fun (_, cty) => do
          let tele ← instForall cty ps
          return (← churchSwapAt tname np ni C (numForalls tele) tele).1
        churchBinders kTys 0 #[] (fun ks => k C ks kTys)

    if lift?.isSome then
      for d in ← ensureExactSortLift reserved do out := out.push d; spliced := spliced ++ d.getNames

    -- **Arm G's prelude, asked for before anything is emitted.** The graph
    -- route pairs a value with its graph proof (`PSigma'`) and extracts it with
    -- `Classical.choice`, whose own domain is `Nonempty`; and `Graph.unique`
    -- transports along a `funext` — but only when a recursive field has a
    -- binder, because [`InductiveModels.funextUp`] is the only caller and it is the
    -- identity at none. That is the whole of why the axiom cost is per shape.
    let mut gFx? : Option Name := none
    if armG then
      for d in ← ensurePSigmaPrime reserved do out := out.push d; spliced := spliced ++ d.getNames
      for d in ← ensureNonempty reserved do out := out.push d; spliced := spliced ++ d.getNames
      for d in ← ensureChoice reserved do out := out.push d; spliced := spliced ++ d.getNames
      if (Array.range gNf).any (fun i => (gRecNb[i]!.getD 0) > 0) then
        let (fxN, fxDecls) ← ensureFunext impl eqi reserved
        for d in fxDecls do out := out.push d; spliced := spliced ++ d.getNames
        gFx? := some fxN

    -- The bare Church proposition at a parameter *and index* scope — what
    -- sits under the lift, and the carrier itself when there is none.
    let churchPropAt := fun (ps : Array Expr) (is : Array Expr) =>
      churchAt ps fun C ks _ => mkForallFVars (#[C] ++ ks) (mkAppN C is)

    -- ── the carrier ──
    let selfVal ← withParams fun ps => do
      forallBoundedTelescope (← idxTeleAt ps) (some ni) fun is _ => do
        let pr ← churchPropAt ps is
        mkLambdaFVars (ps ++ is)
          (match lift? with | none => pr | some ℓ => puliftT ℓ pr)
    let dSelf := Declaration.defnDecl
      { name := selfN, levelParams := lparams, type := declaredMemberTy, value := selfVal
        hints := ← hintsFor selfVal, safety := .safe }
    addChecked dSelf
    out := out.push dSelf

    -- ── the constructors ──
    -- The binders come from the **restored** telescope. At `Prop`, a recursive
    -- field's `T._model.self p⃗ e⃗` δ-unfolds to the encoding; under a lift it
    -- is first mapped through `down`. In either case the fold
    -- `fun z⃗ => f z⃗ C k⃗` then typechecks. Classification is positional and
    -- read off the export's telescope.
    for j in [0:nc] do
      let (_, cty) := exportCtors[j]!
      let ty := publicSource cty
      let nfj ← withParams fun ps => do pure (numForalls (← instForall cty ps))
      let flds ← withParams fun ps => do classifyCtor tname nfj (← instForall cty ps)
      let val ← withParams fun ps => do
        let rtele ← instForall ty ps
        forallBoundedTelescope rtele (some nfj) fun fs res => do
          let fold ← churchAt ps fun C ks _ => do
            let args ← (Array.range nfj).mapM fun i => do
              match flds[i]!.rec? with
              | none => pure fs[i]!
              | some nb =>
                -- exactly the field's OWN binders: `forallTelescope` would
                -- whnf through `T._model.self` and open the encoding's Π too.
                forallBoundedTelescope (← ityp fs[i]!) (some nb) fun zs res => do
                  let child := mkAppN fs[i]! zs
                  let base ← match lift? with
                    | none => pure child
                    | some ℓ => do
                      let some args ← ownerAppArgs? selfN np ni res
                        | badShape s!"a recursive field of {ctorN j} does not end in {selfN} \
                            at {np} parameters and {ni} indices"
                      let is := args.extract np args.size
                      pure (puliftDown ℓ (← churchPropAt ps is) child)
                  mkLambdaFVars zs (mkAppN base (#[C] ++ ks))
            mkLambdaFVars (#[C] ++ ks) (mkAppN ks[j]! args)
          match lift? with
          | none => mkLambdaFVars (ps ++ fs) fold
          | some ℓ =>
            let some args ← ownerAppArgs? selfN np ni res
              | badShape s!"{ctorN j}'s result is not {selfN} at {np} parameters and {ni} indices"
            let is := args.extract np args.size
            mkLambdaFVars (ps ++ fs) (puliftUp ℓ (← churchPropAt ps is) fold)
      let d := Declaration.defnDecl
        { name := ctorN j, levelParams := lparams, type := ty, value := val
          hints := ← hintsFor val, safety := .safe }
      addChecked d
      out := out.push d

    -- ── the recursor ──
    if large && nc == 0 then
      for d in ← ensureNat reserved do out := out.push d; spliced := spliced ++ d.getNames
      for d in ← ensureExactSortLift reserved do out := out.push d; spliced := spliced ++ d.getNames
    -- **One fold, two consumers.** Arm G's `ind` — the free `Prop`-motive
    -- recursor the graph route folds at — *is* the strong-induction fold
    -- below at `v := 0`, so the arm forces the small-elimination branches and
    -- takes the result as `ind` instead of as `rec_0`. Building it a second
    -- time by hand would be a second thing to keep in step.
    let installedIndTy :=
      if armG then installedRecTy.instantiateLevelParams [rv.levelParams[0]!] [.zero]
      else installedRecTy
    let publicIndTy :=
      if armG then publicRecTy.instantiateLevelParams [rv.levelParams[0]!] [.zero]
      else publicRecTy
    let large := large && !armG
    let recVal ← forallBoundedTelescope installedIndTy
        (some (np + 1 + nc + ni + 1)) fun bs _ => do
      let ps := bs.extract 0 np
      let motive := bs[np]!
      let minors := bs.extract (np + 1) (np + 1 + nc)
      let idxs := bs.extract (np + 1 + nc) (np + 1 + nc + ni)
      let t := bs[bs.size - 1]!
      -- Under a lift the fold runs on `down t`. Its result lands at
      -- `motive ι⃗ (up (down t))`, which *is* `motive ι⃗ t`: structure eta on
      -- tight-pair/unit eta gives `t ≡ up (down t)`. So there is no transport, and the
      -- two routes differ in exactly the `down` here and the `up` in the
      -- constructors above.
      let body : Expr ←
        match lift? with
        | none => pure t
        | some ℓ => do pure (puliftDown ℓ (← churchPropAt ps idxs) t)
      let goalAt := mkAppN motive (idxs.push t)
      -- `Self ι⃗`, the carrier at an index vector.
      let selfAt := fun (is : Array Expr) => mkAppN (.const selfN us) (ps ++ is)
      if !large && ni == 0 && !isRec then
        -- The plain fold, at `C := goalAt`: every minor's motive is closed by
        -- definitional proof irrelevance — under a lift too, because the two
        -- `up`s differ only in a proof of the encoding's own proposition.
        mkLambdaFVars bs (mkAppN body (#[goalAt] ++ minors))
      else if !large then
        -- ── strong induction ──
        -- The plain fold cannot serve an indexed or recursive declaration: a
        -- minor premise wants `motive ι⃗_j (c_j f⃗)` and the fold only offers
        -- `C ι⃗_j`, which proof irrelevance no longer identifies with it once
        -- the index moves. So fold at the Church **pair**
        --
        --     Pair ι⃗ := ∀ D : Prop, (Self ι⃗ → (∀ h : Self ι⃗, motive ι⃗ h) → D) → D
        --
        -- of a rebuilt carrier element and a proof about *every* element at
        -- that index — the `∀ h` is what proof irrelevance collapses, and the
        -- element component is what a recursive minor premise needs an
        -- argument for. Every ι rule is still `Eq.refl`, and for a reason
        -- that has nothing to do with whether the fold reduces: the motive is
        -- `Prop`-valued, so both sides of every ι equation are proofs of one
        -- proposition.
        let pairTy ← forallBoundedTelescope (← idxTeleAt ps) (some ni) fun is _ => do
          let sf := selfAt is
          let inner ← withLocalDeclD `D (.sort .zero) fun D => do
            let armTy ← withLocalDeclD `e sf fun e => do
              let qTy ← withLocalDeclD `h sf fun h =>
                mkForallFVars #[h] (mkAppN motive (is.push h))
              withLocalDeclD `q qTy fun q => mkForallFVars #[e, q] D
            mkForallFVars #[D] (.forallE `k armTy D .default)
          mkLambdaFVars is inner
        -- one `Pair`-valued premise per constructor
        let pairAt := fun (is : Array Expr) => do
          let sf := selfAt is
          withLocalDeclD `D (.sort .zero) fun D => do
            let armTy ← withLocalDeclD `e sf fun e => do
              let qTy ← withLocalDeclD `h sf fun h =>
                mkForallFVars #[h] (mkAppN motive (is.push h))
              withLocalDeclD `q qTy fun q => mkForallFVars #[e, q] D
            mkForallFVars #[D] (.forallE `k armTy D .default)
        let pairBaseAt := fun (is : Array Expr) => match lift? with
          | none => pure (selfAt is)
          | some _ => churchPropAt ps is
        let cs ← (Array.range nc).mapM fun j => do
          let (_, cty) := exportCtors[j]!
          let tele ← instForall cty ps
          pairArm tname np ni us selfAt pairAt pairBaseAt lift?
            motive (ctorN j) minors[j]! ps
            (numForalls tele) tele #[] #[]
        let cont ← withLocalDeclD `e (selfAt idxs) fun e => do
          let qTy ← withLocalDeclD `h (selfAt idxs) fun h =>
            mkForallFVars #[h] (mkAppN motive (idxs.push h))
          withLocalDeclD `q qTy fun q => mkLambdaFVars #[e, q] (mkApp q t)
        mkLambdaFVars bs (mkAppN (mkAppN body (#[pairTy] ++ cs)) #[goalAt, cont])
      else if nc == 0 then
        -- Church `⊥` at every index: instantiate the encoding at the constant
        -- family. At `ni = 0` this is the encoding itself.
        let cf ← withLocalDeclD `p (.sort .zero) fun pv => do
          let fam ← forallBoundedTelescope (← idxTeleAt ps) (some ni) fun is _ =>
            mkLambdaFVars is pv
          mkLambdaFVars #[pv] (mkApp body fam)
        mkLambdaFVars bs (← cfalseElim eqi v goalAt cf)
      else do
        -- Large elimination: one constructor, every field a proposition
        -- (the subsingleton rule, which minted this recursor, says so) —
        -- extract each by instantiating the encoding at the field's type.
        unless nc == 1 do
          badShape s!"{ern} is large-eliminating with {nc} constructors"
        let (_, cty) := exportCtors[0]!
        let tele ← instForall cty ps
        let nf := numForalls tele
        let mut es : Array Expr := #[]
        let mut curT := tele
        for _ in [0:nf] do
          let .forallE _ ft rest _ := curT | badShape "telescope shorter than its field count"
          unless (← ilevel ft).normalize.isZero do
            badShape s!"{ern} is large-eliminating and a field is not a proposition"
          let i := es.size
          let proj ← forallBoundedTelescope tele (some nf) fun fs _ =>
            mkLambdaFVars fs fs[i]!
          es := es.push (mkAppN body #[ft, proj])
          curT := rest.instantiate1 es[i]!
        mkLambdaFVars bs (mkAppN minors[0]! es)
    if armG then
      -- ════ arm G: the recursive subsingleton, by the graph ════
      -- The carrier and the constructor above are already the graph route's
      -- own — `CAcc` and `CAcc.intro` cost no primitive whatsoever — and so is
      -- the `Prop`-motive recursor just built. What is emitted here is the
      -- large eliminator the kernel granted the *declaration* and an emitted
      -- `def` does not inherit.
      let dInd := Declaration.thmDecl
        { name := indN, levelParams := lparams, type := publicIndTy, value := recVal }
      addChecked dInd
      out := out.push dInd
      let ctx : GraphCtx :=
        { tname, np, ni, nf := gNf, us, recLs, lparams, recLevels := rv.levelParams, v
          selfN, ctorN0 := ctorN 0, recN, indN
          grN := Name.str impl "graph", grMkN := Name.str impl "graph_mk"
          grInvTN := Name.str impl "graph_inv_ty", grInvN := Name.str impl "graph_inv"
          grUniqN := Name.str impl "graph_unique", grExN := Name.str impl "graph_exists"
          recGrN := Name.str impl "rec_graph"
          memberTy, ctorTy := publicSource exportCtors[0]!.2
          isData := gIsData, idxPos := gIdxPos, nonPiv := gNonPiv
          recNb := gRecNb, eqi, fx? := gFx? }
      for d in ← graphArm ctx publicRecTy do out := out.push d
    else
      let dRec := Declaration.defnDecl
        { name := recN, levelParams := rv.levelParams, type := publicRecTy, value := recVal
          hints := ← hintsFor recVal, safety := .safe }
      addChecked dRec
      out := out.push dRec

  -- ── the ι rules ──
  let mut iotas : Array (Nat × Name × Name) := #[]
  unless rv.rules.length == nc do
    badShape s!"{ern} has {rv.rules.length} rules where {tname} has {nc} constructors"
  for j in [0:nc] do
    let rule := rv.rules[j]!
    let publicRule := sourceRecursor?.bind (·.rules[j]?)
    let (cn, modelC) := ctorPairs[j]!
    unless rule.ctor == cn do
      badShape s!"{ern}'s rule {j} is for {rule.ctor}, not {cn}"
    -- Walk the exact exported constructor type at the model's names. Reading
    -- the installed definition back with `constInfo` is not syntax preserving:
    -- the kernel may βζ-normalise a field domain while storing it. The public
    -- constructor declaration still carries the exported redex literally, and
    -- the iota theorem's telescope is part of the same literal interface.
    let modelCTy := publicSource exportCtors[j]!.2
    let d ← forallBoundedTelescope installedRecTy (some (np + 1 + nc)) fun pre _ => do
      let ps := pre.extract 0 np
      let motive := pre[np]!
      let cty ← instForall modelCTy ps
      forallBoundedTelescope cty (some (numForalls modelCTy - np)) fun fields res => do
        let major := mkAppN (.const modelC us) (ps ++ fields)
        -- The constructor's own index expressions, read off its result type
        -- `T._model.self p⃗ ι⃗_j`. The recursor takes them between the minors
        -- and the major, and the motive takes them before it.
        let some args ← ownerAppArgs? selfN np ni res
          | badShape s!"{modelC}'s result is not {selfN} at {np} parameters and {ni} indices"
        let isj := args.extract np args.size
        let lhs := mkAppN (.const recN recLs) (pre ++ isj ++ #[major])
        let rhsSyntax := publicRule.map (·.rhs) |>.getD rule.rhs
        let rhs := (publicSource rhsSyntax).beta (pre ++ fields)
        let α ← match interface?, sourceRecursor? with
          | some _, some sourceRecursor =>
            let some exactResult := exactRecursorMotiveResult? sourceRecursor j pre fields
              | badShape s!"{sourceRecursor.name}'s exported rule {j} has no exact motive result"
            pure (publicSource exactResult)
          | _, _ => pure (mkAppN motive (isj.push major))
        let tel := pre ++ fields
        let proposition := eqi.mk' v α lhs rhs
        let exactFieldTelescope ← match sourceRecursor? with
          | none => pure cty
          | some sourceRecursor =>
            let some telescope := exactRecursorFieldTelescope? sourceRecursor j pre
              | badShape s!"{sourceRecursor.name}'s exported rule {j} has no exact field telescope"
            pure (publicSource telescope)
        let some fieldsType := closeForallsExact? exactFieldTelescope fields proposition
          | badShape s!"{modelC}'s public recursor telescope has fewer fields than its installed type"
        let some theoremType := closeForallsExact? publicRecTy pre fieldsType
          | badShape s!"{ern}'s exported telescope is shorter than its recursor prefix"
        -- **Every ι theorem is `Eq.refl` except arms E, G and W.**
        --
        -- Arm G's value is a `Classical.choice` application, which reduces to
        -- nothing, so the rule is proved instead: both sides are graph points
        -- at this constructor and the graph is single-valued.
        --
        -- Arm W's is `WT.Wrec_iota` and nothing else, at this declaration's own
        -- `F`, label and dispatch — `Wrec` is a well-founded recursion, so its
        -- ι is a theorem rather than a conversion. **That theorem is the pin
        -- for a collapsed tag assignment**, which is the one wrong model no
        -- type error stops: two constructors of the same shape sharing a tag
        -- have minors of the same type, so the two model constructors simply
        -- become the same term and every other check still passes. It is the
        -- narrowest of seven checked mutations.
        --
        -- The *statement* is the shared one in all three cases, which is what
        -- keeps the oracle's syntactic comparison honest across the arms.
        let proof ←
          if armW then do
            let (a, disp) ← wCtorParts ps j fields
            let coreMotive ← wPlan.motive (wLowSelfAt ps) motive
            pure (mkAppN (.const wCoreIota [uL, v, wKL])
              #[wKTy ps, wAAt ps, wBFn ps, wDecEq ps, wTgAt ps, coreMotive,
                mkAppN (.const wFN recLs) pre, a, disp])
          else if armE then do
            let some k := emptySlots[j]!
              | badShape s!"{cn} has no recursive field in the empty route"
            emptyAtElim eqi .zero w (eqi.mk' v α lhs rhs) fields[k]!
          else if !armG then pure (eqi.refl' v α lhs) else do
            let rsI := (Array.range gNf).filter fun i => gRecNb[i]!.isSome
            let atSlot := fun (nm : Name) => rsI.mapM fun i => do
              let fty ← ityp fields[i]!
              forallBoundedTelescope fty (some (gRecNb[i]!.getD 0)) fun zs r2 => do
                let a2 := r2.getAppArgs
                mkLambdaFVars zs (mkAppN (.const nm recLs)
                  (pre ++ a2.extract np a2.size ++ #[mkAppN fields[i]! zs]))
            let ghat ← atSlot recN
            let hhat ← atSlot (Name.str impl "rec_graph")
            let gv := mkAppN (.const (Name.str impl "rec_graph") recLs)
              (pre ++ isj ++ #[major])
            let gw := mkAppN (.const (Name.str impl "graph_mk") recLs)
              (pre ++ fields ++ ghat ++ hhat)
            pure (mkAppN (.const (Name.str impl "graph_unique") recLs)
              (pre ++ isj ++ #[major, lhs, rhs, gv, gw]))
        return Declaration.thmDecl
          { name := iotaN j, levelParams := rv.levelParams
            type := theoremType
            value := ← mkLambdaFVars tel proof }
    addChecked d
    out := out.push d
    iotas := iotas.push (0, cn, iotaN j)

  let (out2, ruleKs, ruleK?) ← primRuleK eqi rv tname root model ern reserved
    (iotaN 0) out

  let aliases := primAliasMap tname root model ern recN exportCtors ctorN iotaN
    ruleK? out2
  return { decls := out2, levelParams := lparams, members := #[], selfNames := #[selfN]
           numAll := 1, ctors := ctorPairs, recs := #[recN], iotas, ruleKs, spliced
           projectionOverrides
           requires := if armC then #[skelN] else requires
           aliases }

/-- Public entry point for the simple construction.

The implementation is factored from this boundary so a selected recursive
family can be built once at private names and then adapted to its public
one-layer interface.  Until that adapter is selected this wrapper is exactly
the historical call, including collision retry and declaration order. -/
def primIso (tname : Name) (root : Name) (lparams : List Name) (np : Nat) (memberTy : Expr)
    (exportCtors : Array (Name × Expr)) (reserved : Std.HashSet Name)
    (sourceRecursor? : Option ERec := none) : GenM Iso :=
  primIsoWithInterface tname root lparams np memberTy exportCtors reserved sourceRecursor?


end InductiveModels
