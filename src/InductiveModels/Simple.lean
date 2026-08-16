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
import InductiveModels.Simple.GraphKit
import InductiveModels.Simple.Graph
import InductiveModels.Simple.Plan
import InductiveModels.Simple.Erasure
import InductiveModels.Simple.WArm
import InductiveModels.Simple.RuleK
import InductiveModels.Simple.Tight
import InductiveModels.Simple.ArmFKit
import InductiveModels.Simple.Analysis
import InductiveModels.Simple.Interface
import InductiveModels.Simple.Site
import InductiveModels.Simple.Direct
import InductiveModels.Simple.ArmF
import InductiveModels.Simple.ArmC
import InductiveModels.Simple.ArmE
import InductiveModels.Simple.ArmW
import InductiveModels.Simple.ArmTuple
import InductiveModels.Simple.ArmChurch
import InductiveModels.Simple.Iota

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
its own, restored — exactly [`InductiveModels.mutualIso`]'s arrangement.

Every fact the routes share is settled once by [`InductiveModels.mkPrimSite`],
and each route is a definition over that site.  The chain below is the route
**order**, and it is the whole of the dispatch: a declaration that satisfies
two of these conditions takes the earlier one, exactly as it did when the
seven bodies were seven branches of one definition. -/
def primIsoWithInterface (tname : Name) (root : Name) (lparams : List Name) (np : Nat) (memberTy : Expr)
    (exportCtors : Array (Name × Expr)) (reserved : Std.HashSet Name)
    (sourceRecursor? : Option ERec := none)
    (interface? : Option PrimInterfaceNames := none) : GenM Iso := do
  let (site, st) ← mkPrimSite tname root lparams np memberTy exportCtors reserved
    sourceRecursor? interface?
  let st ←
    if let some directRoute := site.directRoute? then primDirect site directRoute st
    else if site.armF then primArmF site st
    else if site.armC then primArmC site st
    else if site.armE then primArmE site st
    else if site.armW then primArmW site st
    else if site.route matches PrimRoute.type then primArmTuple site st
    else primArmChurch site st
  let (st, iotas) ← primIotaRules site st

  let (out2, ruleKs, ruleK?) ← primRuleK site.eqi site.rv site.tname site.root site.model
    site.ern site.reserved (site.iotaN 0) st.out

  let aliases := primAliasMap site.tname site.root site.model site.ern site.recN
    site.exportCtors site.ctorN site.iotaN ruleK? out2
  return { decls := out2, levelParams := site.lparams, members := #[]
           selfNames := #[site.selfN]
           numAll := 1, ctors := site.ctorPairs, recs := #[site.recN], iotas, ruleKs
           spliced := st.spliced
           projectionOverrides := st.projectionOverrides
           requires := if site.armC then #[site.skelN] else st.requires
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
