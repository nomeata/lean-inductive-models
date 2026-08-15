import InductiveModels.Mutual
import InductiveModels.Naming
import InductiveModels.Projection

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

/-- The complete trusted basis, by principal name.

`Quot` denotes Lean's kernel-special quotient bundle (`Quot`, `Quot.mk`,
`Quot.lift`, and `Quot.ind`), not an ordinary inductive declaration. It is
nevertheless part of the advertised basis: generated proofs may use it to
derive `funext` from `Quot.sound`. -/
def basis : List Name := [`Eq, `PSigma', `Nat, `PUnit, `Quot]

/-- The ordinary inductive subset of [`InductiveModels.basis`]. Declarations in this
set are not modelled — the exemption that makes the construction
well-founded. `Quot` is handled by the kernel's quotient declaration path
instead, so it does not participate in this owner-exemption test.

**`Acc` was the fifth and is not here any more.** Its one grant — the
subsingleton-recursive large eliminator — is derived by
[`InductiveModels.graphArm`], so `Acc` is an ordinary declaration and models like
one. `Nonempty` never joins this list either, though the graph arm names it:
`Classical.choice`'s domain is not an exemption, and it self-models.

`False` is **not** among them: it is derived (Church `∀ p : Prop, p`, with
its `Sort w` eliminator from `0 = 1` plus a `Nat.rec`-built family to
transport along — [`InductiveModels.cfalseElim`]), so `False` models like any other
declaration. The tight pair and `PUnit` together take its place. -/
def inductiveBasis : List Name := [`Eq, `PSigma', `Nat, `PUnit]

/-- **Lean's `PUnit`**, exactly as `Init/Prelude.lean` declares it:
`inductive PUnit.{u} : Sort u | unit : PUnit`.

Like the tight pair below, this crosses Lean's bootstrap resulting-universe
boundary: at `u = 0` the result is a proposition, while at positive levels it
is a type.  The kernel accepts the declaration and gives its ordinary
universe-polymorphic eliminator.  Paired with `PSigma'`, it supplies the
inhabited exact-sort fibre used by the internally derived propositional lift. -/
def punitDecl : Declaration :=
  let lu := Level.param `u
  .inductDecl [`u] 0
    [{ name := `PUnit, type := .sort lu,
       ctors := [{ name := `PUnit.unit, type := .const `PUnit [lu] }] }] false

/-- **Lean's `Nat`**, as `Init/Prelude.lean` declares it. The models build
tags as `succ` chains, so nothing here depends on literals. -/
def natDecl : Declaration :=
  let nat : Expr := .const `Nat []
  .inductDecl [] 0
    [{ name := `Nat, type := .sort (.succ .zero)
       ctors := [{ name := `Nat.zero, type := nat },
                 { name := `Nat.succ, type := .forallE `n nat nat .default }] }] false

/-! ## The tight dependent-pair primitive

`PSigma'` differs from Lean's `PSigma` only in its resulting universe:
`Sort (max u v)`, with no built-in `1`.  The declaration crosses the same
bootstrap boundary: the result may specialize to `Prop`, so Lean's
surface inductive checker refuses it while the kernel accepts the declaration.

Only the inductive and its constructor are primitive.  The named projections
and the universe-polymorphic eliminator below are ordinary definitions over
primitive `.proj` expressions.  In particular, `PSigma'.rec'` does not add a
second kernel exception: structure eta makes `mk t.1 t.2` convertible to `t`,
so `fun h t => h t.1 t.2` has an arbitrary `Sort w` motive and its constructor
rule is reflexivity. -/

def psigmaPrimeDecl : Declaration :=
  let lu := Level.param `u
  let lv := Level.param `v
  let ty : Expr := .forallE `α (.sort lu)
    (.forallE `β (.forallE `x (.bvar 0) (.sort lv) .default)
      (.sort (mkLevelMax' lu lv)) .default) .implicit
  let mkTy : Expr := .forallE `α (.sort lu)
    (.forallE `β (.forallE `x (.bvar 0) (.sort lv) .default)
      (.forallE `fst (.bvar 1)
        (.forallE `snd (.app (.bvar 1) (.bvar 0))
          (mkAppN (.const `PSigma' [lu, lv]) #[.bvar 3, .bvar 2]) .default)
        .default) .implicit) .implicit
  .inductDecl [`u, `v] 2
    [{ name := `PSigma', type := ty,
       ctors := [{ name := `PSigma'.mk, type := mkTy }] }] false

/-! ## Exact basis-owner validation

A declaration is exempt because a consumer is expected to implement its
*particular kernel interface*, not merely because it owns one of four reserved
names. Validate that interface even when no generated model happens to use the
declaration later in the stream.

The expected record is minted by this same kernel from the canonical
declaration under a disposable fresh alias. Renaming it back gives every piece
of metadata the export carries: the inductive, constructor and recursor types,
their order and counts, recursor rules, flags, and safety bits. -/

private def basisCanonicalDecl? : Name → Option Declaration
  | `Eq => some eqDecl
  | `Nat => some natDecl
  | `PUnit => some punitDecl
  | `PSigma' => some psigmaPrimeDecl
  | _ => none

private def basisRecordFromEnv (env : Environment) (root : Name) : Except String EDecl := do
  let some (.inductInfo type) := env.constants.find? root
    | throw s!"{root} is not an inductive type"
  let mut constructors : Array ECtor := #[]
  for constructorName in type.ctors do
    let some (.ctorInfo constructor) := env.constants.find? constructorName
      | throw s!"{constructorName} is not a constructor"
    constructors := constructors.push
      { name := constructor.name, levelParams := constructor.levelParams,
        type := constructor.type, cidx := constructor.cidx,
        numParams := constructor.numParams, numFields := constructor.numFields,
        induct := constructor.induct, isUnsafe := constructor.isUnsafe }
  let recursorName := Name.str root "rec"
  let some (.recInfo recursor) := env.constants.find? recursorName
    | throw s!"{recursorName} is not a recursor"
  let exportedRecursor : ERec :=
    { name := recursor.name, levelParams := recursor.levelParams, type := recursor.type,
      all := recursor.all, numParams := recursor.numParams,
      numIndices := recursor.numIndices, numMotives := recursor.numMotives,
      numMinors := recursor.numMinors,
      rules := recursor.rules.map fun rule =>
        { ctor := rule.ctor, nfields := rule.nfields, rhs := rule.rhs },
      k := recursor.k, isUnsafe := recursor.isUnsafe }
  let exportedType : EIndType :=
    { name := type.name, levelParams := type.levelParams, type := type.type,
      all := type.all, ctors := type.ctors, numParams := type.numParams,
      numIndices := type.numIndices, numNested := type.numNested,
      isRec := type.isRec, isReflexive := type.isReflexive,
      isUnsafe := type.isUnsafe }
  return .induct [exportedType] constructors.toList [exportedRecursor]

private def basisAliasNames (root alias : Name) : Name → Option Name := fun name =>
  if root.isPrefixOf name then some (name.replacePrefix root alias) else none

private def aliasBasisDeclaration (root alias : Name) : Declaration → Declaration
  | .inductDecl levelParams numParams types isUnsafe =>
    let rename := fun name => (basisAliasNames root alias name).getD name
    let rewrite := mapConstsE (basisAliasNames root alias)
    .inductDecl levelParams numParams (types.map fun type =>
      { name := rename type.name, type := rewrite type.type,
        ctors := type.ctors.map fun constructor =>
          { name := rename constructor.name, type := rewrite constructor.type } }) isUnsafe
  | declaration => declaration

private partial def freshBasisAlias (env : Environment) (root : Name)
    (canonical : Declaration) (attempt : Nat := 0) : Name :=
  let stem := (`_inductive_models_basis_validation).mkNum attempt
  let alias := stem ++ root
  let declarationNames := canonical.getNames.map fun name =>
    if root.isPrefixOf name then name.replacePrefix root alias else name
  let names := Name.str alias "rec" :: declarationNames
  if names.any env.constants.contains then
    freshBasisAlias env root canonical (attempt + 1)
  else alias

private def alignBasisLevelParams (declaration : Declaration) (actual : List Name) : Declaration :=
  match declaration with
  | .inductDecl expected numParams types isUnsafe =>
    if expected.length != actual.length then declaration else
      let levels := actual.map Level.param
      .inductDecl actual numParams (types.map fun type =>
        { type with
          type := type.type.instantiateLevelParams expected levels,
          ctors := type.ctors.map fun constructor =>
            { constructor with
              type := constructor.type.instantiateLevelParams expected levels } }) isUnsafe
  | _ => declaration

/-- Require an encountered basis owner to be the exact canonical declaration
family before it may be reported as an exemption. A noncanonical declaration
is never a successful exemption. -/
def validateBasisOwner (root : Name) (owner : EDecl) : GenM Unit := do
  let .induct (type :: _) _ _ := owner
    | badShape "the basis owner is not a nonempty inductive record"
  let some canonical := basisCanonicalDecl? root
    | badShape s!"{root} is not a basis owner"
  let env ← getEnv
  let canonical := alignBasisLevelParams canonical type.levelParams
  let alias := freshBasisAlias env root canonical
  let canonical := aliasBasisDeclaration root alias canonical
  let expectedEnv ← match env.addDeclCore 0 canonical none true with
    | .ok next => pure next
    | .error exception =>
      badShape s!"cannot mint the canonical {root} interface: \
        {← (exception.toMessageData {}).toString}"
  let expectedAlias ← match basisRecordFromEnv expectedEnv alias with
    | .ok record => pure record
    | .error message => badShape s!"cannot read the canonical {root} interface: {message}"
  let expected := EDecl.mapNames
    (fun name => if alias.isPrefixOf name then name.replacePrefix alias root else name)
    (mapConstsE fun name =>
      if alias.isPrefixOf name then some (name.replacePrefix alias root) else none)
    expectedAlias
  unless owner == expected do
    declineWith (.notLeans root
      "its complete inductive, constructor, and recursor metadata is not canonical")

def psigmaPrimeT (u v : Level) (α β : Expr) : Expr :=
  mkAppN (.const `PSigma' [u, v]) #[α, β]

def psigmaPrimeMk (u v : Level) (α β fst snd : Expr) : Expr :=
  mkAppN (.const `PSigma'.mk [u, v]) #[α, β, fst, snd]

def psigmaPrimeFst (u v : Level) (α β self : Expr) : Expr :=
  mkAppN (.const `PSigma'.fst [u, v]) #[α, β, self]

def psigmaPrimeSnd (u v : Level) (α β self : Expr) : Expr :=
  mkAppN (.const `PSigma'.snd [u, v]) #[α, β, self]

def psigmaPrimeRec (u v w : Level) (α β motive minor self : Expr) : Expr :=
  mkAppN (.const `PSigma'.rec' [u, v, w]) #[α, β, motive, minor, self]

/-- One primitive, checked or spliced. `check` runs on a present declaration
and says what is wrong with it; a missing one is spliced at Lean's shape and
re-checked. The pattern is [`InductiveModels.ensureEq`]'s, and the name guard is
the same one. -/
def ensurePrim (n : Name) (guard : List Name) (d : Declaration)
    (check : Environment → Except String Unit) (reserved : Std.HashSet Name) :
    GenM (Array Declaration) := do
  if (← getEnv).constants.contains n then
    match check (← getEnv) with
    | .ok () => return #[]
    | .error why => declineWith (.notLeans n why)
  for g in guard do
    if reserved.contains g then declineWith (.nameTaken g)
  addChecked d
  match check (← getEnv) with
  | .ok () => return #[d]
  | .error why => badShape s!"the spliced {n} is not Lean's ({why})"

/-- Validate the exact standard polymorphic unit, including its arbitrary-sort
eliminator.  A merely similarly named singleton is not accepted as basis
support. -/
def checkPUnit (env : Environment) : Except String Unit := do
  let some (.inductInfo iv) := env.constants.find? `PUnit
    | throw "it is not an inductive type"
  unless iv.numParams == 0 && iv.numIndices == 0 && iv.ctors == [`PUnit.unit]
      && iv.levelParams.length == 1 do
    throw "it is not a nullary, one-constructor polymorphic unit"
  let [u] := iv.levelParams | throw "it does not have one universe parameter"
  unless iv.type == .sort (.param u) do throw "it does not land in exactly `Sort u`"
  let some (.ctorInfo constructor) := env.constants.find? `PUnit.unit
    | throw "PUnit.unit is not its constructor"
  unless constructor.type == .const `PUnit [.param u] && constructor.numFields == 0 do
    throw "PUnit.unit is not the fieldless canonical constructor"
  let some (.recInfo recursor) := env.constants.find? `PUnit.rec
    | throw "PUnit.rec is not a recursor"
  let [v, u] := recursor.levelParams
    | throw "PUnit.rec is not universe-polymorphic in its motive"
  unless recursor.numParams == 0 && recursor.numMotives == 1 &&
      recursor.numMinors == 1 && recursor.numIndices == 0 &&
      recursor.rules.length == 1 && recursor.rules[0]!.ctor == `PUnit.unit do
    throw "PUnit.rec does not have the standard fieldless-singleton recursor metadata"
  let punit := Expr.const `PUnit [.param u]
  let unit := Expr.const `PUnit.unit [.param u]
  let motiveType := Expr.forallE `self punit (.sort (.param v)) .default
  let expectedRecursor := Expr.forallE `motive motiveType
    (.forallE `unitCase (.app (.bvar 0) unit)
      (.forallE `t punit (.app (.bvar 2) (.bvar 0)) .default) .default) .implicit
  unless recursor.type == expectedRecursor do
    throw "PUnit.rec does not have the exact standard arbitrary-sort statement"

/-- `Nat` at Lean's shape, **including the large elimination the whole Type
route rests on**: `Nat.rec` must carry a motive universe. This property is
checked rather than assumed — on the input's own `Nat` as much as on a
spliced one. -/
def checkNat (env : Environment) : Except String Unit := do
  let some (.inductInfo iv) := env.constants.find? `Nat | throw "it is not an inductive type"
  unless iv.numParams == 0 && iv.numIndices == 0 && iv.ctors == [`Nat.zero, `Nat.succ] do
    throw "it is not zero/succ with 0 parameters and 0 indices"
  unless iv.type == Expr.sort (.succ .zero) do throw "it does not land in Type"
  let some (.recInfo rv) := env.constants.find? `Nat.rec | throw "Nat.rec is not a recursor"
  unless rv.levelParams.length == 1 do
    throw "Nat.rec is not large-eliminating (no motive universe)"

/-- Validate the only trusted part of the tight pair bundle: the kernel
inductive and constructor.  The named projections and `rec'` are checked as
ordinary derived declarations by [`InductiveModels.ensurePSigmaPrime`]. -/
def checkPSigmaPrimeCore (env : Environment) : Except String Unit := do
  let some (.inductInfo iv) := env.constants.find? `PSigma'
    | throw "it is not an inductive type"
  unless iv.numParams == 2 && iv.numIndices == 0 && iv.ctors == [`PSigma'.mk]
      && iv.levelParams.length == 2 do
    throw "it is not a two-parameter, one-constructor tight Sort-polymorphic pair"
  let [u, v] := iv.levelParams | throw "it does not have two universe parameters"
  let expectedType := match psigmaPrimeDecl with
    | .inductDecl _ _ [value] _ =>
      value.type.instantiateLevelParams [`u, `v] [.param u, .param v]
    | _ => unreachable!
  unless iv.type == expectedType do
    throw "its type is not `{α : Sort u} → (α → Sort v) → Sort (max u v)`"
  let some (.ctorInfo constructor) := env.constants.find? `PSigma'.mk
    | throw "PSigma'.mk is not its constructor"
  let expectedConstructor := match psigmaPrimeDecl with
    | .inductDecl _ _ [value] _ =>
      value.ctors[0]!.type.instantiateLevelParams [`u, `v] [.param u, .param v]
    | _ => unreachable!
  unless constructor.type == expectedConstructor && constructor.numFields == 2 do
    throw "PSigma'.mk does not retain exactly its dependent first and second components"

/-- **Lean's `Nonempty`**, as `Init/Prelude.lean` declares it:
`inductive Nonempty (α : Sort u) : Prop | intro (val : α) : Nonempty α`.

**It is not a basis primitive** and it is not on [`InductiveModels.basis`]'s list.
It is here for one reason: `Classical.choice`'s *own domain* is `Nonempty`, so
the graph arm ([`InductiveModels.graphArm`]) cannot state totality without naming it.
Unlike the five it does not need an exemption to keep the construction
well-founded — it is a non-recursive, small-eliminating `Prop`, so where the
input declares one the Church route models it like anything else, and the
model is emitted beside it as usual. What a *spliced* `Nonempty` costs is one
unmodelled inductive in that run's output, which is why the splice is reported
like every other. -/
def nonemptyDecl : Declaration :=
  let lu := Level.param `u
  let ty : Expr := .forallE `α (.sort lu) (.sort .zero) .default
  let introTy : Expr := .forallE `α (.sort lu)
    (.forallE `val (.bvar 0) (.app (.const `Nonempty [lu]) (.bvar 1)) .default) .implicit
  .inductDecl [`u] 1
    [{ name := `Nonempty, type := ty,
       ctors := [{ name := `Nonempty.intro, type := introTy }] }] false

def checkNonempty (env : Environment) : Except String Unit := do
  let some (.inductInfo iv) := env.constants.find? `Nonempty | throw "it is not an inductive type"
  unless iv.numParams == 1 && iv.numIndices == 0 && iv.ctors == [`Nonempty.intro]
      && iv.levelParams.length == 1 do
    throw "it is not a one-parameter, one-constructor lift with a single level parameter"
  match iv.type with
  | .forallE _ (.sort (.param _)) (.sort .zero) _ => pure ()
  | _ => throw "it is not `Sort u → Prop`"

/-- `Classical.choice`'s statement: `{α : Sort u} → Nonempty α → α`. One
builder for both uses — the input's own is compared against it with `isDefEq`
and a spliced one is declared at it, exactly as [`InductiveModels.funextType`] serves
`funext`. -/
def choiceType (lu : Level) : Expr :=
  .forallE `α (.sort lu)
    (.forallE `h (.app (.const `Nonempty [lu]) (.bvar 0)) (.bvar 1) .default) .implicit

def choiceDecl : Declaration :=
  .axiomDecl { name := `Classical.choice, levelParams := [`u]
               type := choiceType (.param `u), isUnsafe := false }

def ensurePUnit (reserved : Std.HashSet Name) : GenM (Array Declaration) :=
  ensurePrim `PUnit [`PUnit, `PUnit.unit, `PUnit.rec] punitDecl checkPUnit reserved
def ensureNonempty (reserved : Std.HashSet Name) : GenM (Array Declaration) :=
  ensurePrim `Nonempty [`Nonempty, `Nonempty.intro] nonemptyDecl checkNonempty reserved

/-- **`Classical.choice`, the one axiom the graph arm asserts.** The input's
own where it declares one at Lean's statement; Lean's, spliced in, where it
does not. `funext` is *derived* from `Quot.sound` rather than asserted and
this one cannot be — it is an axiom in Lean too — so the asymmetry is the
subject matter's and not a shortcut. Axiom-freedom is not a goal of this
construction and the standard axioms may be used. -/
def ensureChoice (reserved : Std.HashSet Name) : GenM (Array Declaration) := do
  match (← getEnv).constants.find? `Classical.choice with
  | some ci =>
    let [su] := ci.levelParams
      | declineWith (.notLeans `Classical.choice
          s!"it has {ci.levelParams.length} level parameters, where Lean's has 1")
    unless ← isDefEq ci.type (choiceType (.param su)) do
      declineWith (.notLeans `Classical.choice "its statement is not Lean's")
    return #[]
  | none =>
    if reserved.contains `Classical.choice then declineWith (.nameTaken `Classical.choice)
    addChecked choiceDecl
    return #[choiceDecl]
def ensureNat (reserved : Std.HashSet Name) : GenM (Array Declaration) :=
  ensurePrim `Nat [`Nat, `Nat.zero, `Nat.succ] natDecl checkNat reserved
/-- The ordinary declarations derived from the tight pair's two primitive
projections. None of these declarations crosses the bootstrap inductive
boundary. -/
def psigmaPrimeDerivedDecls : GenM (Array Declaration) := do
  let u := Level.param `u
  let v := Level.param `v
  let w := Level.param `w
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok value => pure value
    | .error message => badShape s!"PSigma' support needs Lean's Eq ({message})"

  let fstDecl ← withLocalDecl `α .implicit (.sort u) fun α =>
    withLocalDecl `β .implicit (.forallE `x α (.sort v) .default) fun β =>
    withLocalDeclD `self (psigmaPrimeT u v α β) fun self => do
      let type ← mkForallFVars #[α, β, self] α
      let value ← mkLambdaFVars #[α, β, self] (.proj `PSigma' 0 self)
      return .defnDecl
        { name := `PSigma'.fst, levelParams := [`u, `v], type, value,
          hints := ← hintsFor value, safety := .safe }

  let sndDecl ← withLocalDecl `α .implicit (.sort u) fun α =>
    withLocalDecl `β .implicit (.forallE `x α (.sort v) .default) fun β =>
    withLocalDeclD `self (psigmaPrimeT u v α β) fun self => do
      let fst := psigmaPrimeFst u v α β self
      let type ← mkForallFVars #[α, β, self] (mkApp β fst)
      let value ← mkLambdaFVars #[α, β, self] (.proj `PSigma' 1 self)
      return .defnDecl
        { name := `PSigma'.snd, levelParams := [`u, `v], type, value,
          hints := ← hintsFor value, safety := .safe }

  let recDecl ← withLocalDecl `α .implicit (.sort u) fun α =>
    withLocalDecl `β .implicit (.forallE `x α (.sort v) .default) fun β => do
    let pair := psigmaPrimeT u v α β
    withLocalDecl `motive .implicit (.forallE `self pair (.sort w) .default) fun motive => do
      let minorType ← withLocalDeclD `fst α fun fst =>
        withLocalDeclD `snd (mkApp β fst) fun snd =>
          mkForallFVars #[fst, snd] (mkApp motive (psigmaPrimeMk u v α β fst snd))
      withLocalDeclD `minor minorType fun minor =>
        withLocalDeclD `self pair fun self => do
          let type ← mkForallFVars #[α, β, motive, minor, self] (mkApp motive self)
          let body := mkAppN minor
            #[psigmaPrimeFst u v α β self, psigmaPrimeSnd u v α β self]
          let value ← mkLambdaFVars #[α, β, motive, minor, self] body
          return .defnDecl
            { name := `PSigma'.rec', levelParams := [`u, `v, `w], type, value,
              hints := ← hintsFor value, safety := .safe }

  let fstRule ← withLocalDecl `α .implicit (.sort u) fun α =>
    withLocalDecl `β .implicit (.forallE `x α (.sort v) .default) fun β =>
    withLocalDeclD `fst α fun fst =>
      withLocalDeclD `snd (mkApp β fst) fun snd => do
        let pair := psigmaPrimeMk u v α β fst snd
        let lhs := psigmaPrimeFst u v α β pair
        let type ← mkForallFVars #[α, β, fst, snd] (eqi.mk' u α lhs fst)
        let value ← mkLambdaFVars #[α, β, fst, snd] (eqi.refl' u α fst)
        return .thmDecl
          { name := `PSigma'.fst_mk, levelParams := [`u, `v], type, value }

  let sndRule ← withLocalDecl `α .implicit (.sort u) fun α =>
    withLocalDecl `β .implicit (.forallE `x α (.sort v) .default) fun β =>
    withLocalDeclD `fst α fun fst =>
      withLocalDeclD `snd (mkApp β fst) fun snd => do
        let pair := psigmaPrimeMk u v α β fst snd
        let lhs := psigmaPrimeSnd u v α β pair
        let fieldType := mkApp β fst
        let type ← mkForallFVars #[α, β, fst, snd] (eqi.mk' v fieldType lhs snd)
        let value ← mkLambdaFVars #[α, β, fst, snd] (eqi.refl' v fieldType snd)
        return .thmDecl
          { name := `PSigma'.snd_mk, levelParams := [`u, `v], type, value }

  let recRule ← withLocalDecl `α .implicit (.sort u) fun α =>
    withLocalDecl `β .implicit (.forallE `x α (.sort v) .default) fun β => do
    let pairType := psigmaPrimeT u v α β
    withLocalDecl `motive .implicit (.forallE `self pairType (.sort w) .default) fun motive => do
      let minorType ← withLocalDeclD `fst α fun fst =>
        withLocalDeclD `snd (mkApp β fst) fun snd =>
          mkForallFVars #[fst, snd] (mkApp motive (psigmaPrimeMk u v α β fst snd))
      withLocalDeclD `minor minorType fun minor =>
        withLocalDeclD `fst α fun fst =>
          withLocalDeclD `snd (mkApp β fst) fun snd => do
            let pair := psigmaPrimeMk u v α β fst snd
            let lhs := psigmaPrimeRec u v w α β motive minor pair
            let rhs := mkAppN minor #[fst, snd]
            let resultType := mkApp motive pair
            let type ← mkForallFVars #[α, β, motive, minor, fst, snd]
              (eqi.mk' w resultType lhs rhs)
            let value ← mkLambdaFVars #[α, β, motive, minor, fst, snd]
              (eqi.refl' w resultType rhs)
            return .thmDecl
              { name := `PSigma'.rec'_mk, levelParams := [`u, `v, `w], type, value }

  return #[fstDecl, sndDecl, recDecl, fstRule, sndRule, recRule]

private def checkPSigmaPrimeDerived (expected : Array Declaration) : GenM Unit := do
  for declaration in expected do
    let [name] := declaration.getNames
      | badShape "one PSigma' support declaration has several names"
    let some actual := (← getEnv).constants.find? name
      | declineWith (.notLeans name "it is missing from the tight pair support bundle")
    let (expectedLevels, expectedType, expectedValue, expectedTheorem) ← match declaration with
      | .defnDecl value => pure (value.levelParams, value.type, value.value, false)
      | .thmDecl value => pure (value.levelParams, value.type, value.value, true)
      | _ => badShape s!"{name} is not a derived tight-pair declaration"
    let (actualLevels, actualType, actualValue) ← match actual, expectedTheorem with
      | .defnInfo value, false => pure (value.levelParams, value.type, value.value)
      | .thmInfo value, true => pure (value.levelParams, value.type, value.value)
      | _, _ => declineWith (.notLeans name "it has the wrong declaration kind")
    unless actualLevels.length == expectedLevels.length do
      declineWith (.notLeans name
        s!"it has {actualLevels.length} universe parameters, expected {expectedLevels.length}")
    let levels := actualLevels.map Level.param
    let expectedType := expectedType.instantiateLevelParams expectedLevels levels
    let expectedValue := expectedValue.instantiateLevelParams expectedLevels levels
    unless ← isDefEq actualType expectedType do
      declineWith (.notLeans name "its type is not the projection-derived interface type")
    unless ← isDefEq actualValue expectedValue do
      declineWith (.notLeans name "its value is not the projection-derived implementation")

/-- Ensure the exact tight-pair bundle. The inductive is the one new basis
primitive; all named projections, reduction rules, and the large `rec'` are
ordinary checked declarations derived from primitive projections. -/
def ensurePSigmaPrime (reserved : Std.HashSet Name) : GenM (Array Declaration) := do
  let supportNames :=
    [`PSigma', `PSigma'.mk, `PSigma'.rec, `PSigma'.fst, `PSigma'.snd, `PSigma'.rec',
      `PSigma'.fst_mk, `PSigma'.snd_mk, `PSigma'.rec'_mk]
  let mut out ← ensurePrim `PSigma' supportNames psigmaPrimeDecl checkPSigmaPrimeCore reserved
  let expected ← psigmaPrimeDerivedDecls
  for declaration in expected do
    let [name] := declaration.getNames
      | badShape "one PSigma' support declaration has several names"
    if (← getEnv).constants.contains name then continue
    if reserved.contains name then declineWith (.nameTaken name)
    addChecked declaration
    out := out.push declaration
  checkPSigmaPrimeDerived expected
  return out

/-- Ensure the complete shared support for the internally derived exact-sort
propositional lift.  The construction itself is inlined into generated
expressions; only the exact standard `PUnit` and tight-pair bundle persist. -/
def ensureExactSortLift (reserved : Std.HashSet Name) : GenM (Array Declaration) := do
  let pairs ← ensurePSigmaPrime reserved
  let units ← ensurePUnit reserved
  return pairs ++ units

/-! ## Expression kit -/

/-- `succ^j zero` — a tag, as constructor chains so the splice needs no
literal support. -/
def natNumeral : Nat → Expr
  | 0 => .const `Nat.zero []
  | j + 1 => .app (.const `Nat.succ []) (natNumeral j)

/-- `succ^j e`. -/
def natSuccs : Nat → Expr → Expr
  | 0, e => e
  | j + 1, e => .app (.const `Nat.succ []) (natSuccs j e)

def psigmaT (u v : Level) (α β : Expr) : Expr :=
  psigmaPrimeT u v α β

def psigmaMk (u v : Level) (α β fst snd : Expr) : Expr :=
  psigmaPrimeMk u v α β fst snd

def psigmaRec (s u v : Level) (α β motive m t : Expr) : Expr :=
  psigmaPrimeRec u v s α β motive m t

/-- `PSigma'.fst`. Structure eta makes `⟨fst y, snd y⟩ ≡ y`
for a neutral `y`, which is what lets a tuple be taken apart and put back
together with no transport. -/
def psigmaFst (u v : Level) (α β y : Expr) : Expr :=
  psigmaPrimeFst u v α β y

/-- `PSigma'.snd`, at the dependent fibre `β (fst y)`. -/
def psigmaSnd (u v : Level) (α β y : Expr) : Expr :=
  psigmaPrimeSnd u v α β y

def natRec (s : Level) (motive z sc t : Expr) : Expr :=
  mkAppN (.const `Nat.rec [s]) #[motive, z, sc, t]

/-! ### The two Church propositions, and the derived exact-sort lift

`False` is no longer a primitive, so the two propositions the constructions
seed with are written out: `⊥ := ∀ p : Prop, p` and `⊤ := ∀ C : Prop, C → C`.
Both are pure Π — they consume no primitive at all. What they lack is `⊥`'s
`Sort w` eliminator, which [`InductiveModels.cfalseElim`] supplies from `Nat` and
`Eq`. -/

/-- The always-true proposition `∀ C : Prop, C → C`, and its inhabitant. -/
def trueP : Expr :=
  .forallE `C (.sort .zero) (.forallE `c (.bvar 0) (.bvar 1) .default) .default
def trueI : Expr :=
  .lam `C (.sort .zero) (.lam `c (.bvar 0) (.bvar 0) .default) .default

/-- **Church `False`**: `∀ p : Prop, p`. Small elimination is instantiation;
large elimination is [`InductiveModels.cfalseElim`]. -/
def falseP : Expr :=
  .forallE `p (.sort .zero) (.bvar 0) .default

/-- `PUnit.{ℓ}` and its canonical inhabitant. -/
def punitT (ℓ : Level) : Expr := .const `PUnit [ℓ]
def punitUnit (ℓ : Level) : Expr := .const `PUnit.unit [ℓ]

/-- The proposition `p` at exactly `Sort ℓ`, for **any** `ℓ` whatsoever,
empty exactly when `p` is: `PSigma'.{0,ℓ} (fun _ : p => PUnit.{ℓ})`.
No declaration named `PULiftP` is emitted or referenced. -/
def puliftT (ℓ : Level) (p : Expr) : Expr :=
  psigmaPrimeT .zero ℓ p (.lam `h p (punitT ℓ) .default)

/-- The derived lift constructor `⟨h, PUnit.unit⟩`. -/
def puliftUp (ℓ : Level) (p h : Expr) : Expr :=
  let fibre := .lam `h p (punitT ℓ) .default
  psigmaPrimeMk .zero ℓ p fibre h (punitUnit ℓ)

/-- The derived lift's arbitrary-sort eliminator, implemented by
`PSigma'.rec'`.  The ignored `PUnit` field is definitionally canonical. -/
def puliftRec (v ℓ : Level) (p motive m t : Expr) : Expr :=
  let fibre := .lam `h p (punitT ℓ) .default
  let minor := .lam `h p
    (.lam `unit (punitT ℓ) (mkApp m (.bvar 1)) .default) .default
  psigmaPrimeRec .zero ℓ v p fibre motive minor t

/-- The derived lift's `down`, its tight pair's first projection. -/
def puliftDown (ℓ : Level) (p t : Expr) : Expr :=
  psigmaPrimeFst .zero ℓ p (.lam `h p (punitT ℓ) .default) t

/-- **The lift's eta is definitional.** Tight-pair structure eta gives
`t ≡ ⟨t.1,t.2⟩`, and polymorphic-unit structure eta gives
`t.2 ≡ PUnit.unit`; hence `t ≡ up (down t)` at every level, including zero.
This is `Eq.refl`, not a recursor call, and exists only for the one place that
needs an equation rather than a conversion.

**The rule fires on a redex, and only on one.** Eta-for-structures expands one
side when the *other* is already a constructor application. So `t ≡ up (down
t)` holds for an opaque `t`, and `t ≡ canon` holds for a literal `canon = up
h`, but `x ≡ y` for two opaque inhabitants does **not** — the kernel refuses it
even when forced past the unifier with `@Eq.refl _ x`, because neither side
gets expanded. It is refused as a *conversion* only: `x = y` is provable, with
no axiom, by routing through `up (down ·)` where every step is a redex, so the
conversion is simply not transitive at this shape. Direct kernel checks pin all
of it.

Two consequences the construction leans on, **both at a redex**. Every element
of the lifted `⊤` is defeq to [`InductiveModels.unitAtCanon`], which is a literal pair,
so a pad built from it needs no transport — the strict improvement on the
`False`-Π pad, whose uniqueness was `funext`. And `motive (up (down t))` and
`motive t` are convertible, so the maybe-zero route's recursor is the `Prop`
route's with `up`/`down` at the ends and nothing in between. Nowhere does the
construction compare two opaque inhabitants, so nothing rests on the claim
that fails. -/
def puliftEta (eqi : EqInfo) (ℓ : Level) (p t : Expr) : Expr :=
  eqi.refl' ℓ (puliftT ℓ p) t

/-- An **empty** type at exactly `Sort w`, for any `w`: the lift of Church
`False`. This is the fibre beyond a tag tower's last constructor, and — at a
maybe-zero `w` — the whole of `PEmpty`'s carrier. -/
def emptyAt (w : Level) : Expr :=
  puliftT w falseP

/-- `Eq.rec.{v,ℓ} α a (fun z _ => fam z) base b h` — transport
`base : fam a` to `fam b` along `h : Eq a b`. -/
def transportAlong (eqi : EqInfo) (v ℓ : Level) (α a b h base : Expr)
    (fam : Expr → GenM Expr) : GenM Expr := do
  let motive ← withLocalDeclD `z α fun z => do
    withLocalDeclD `hz (eqi.mk' ℓ α a z) fun hz => do
      mkLambdaFVars #[z, hz] (← fam z)
  return eqi.recAt v ℓ α a motive base b h

/-- `Eq b a` from `h : Eq a b`, as one `Eq.rec` at a `Prop` motive. -/
def symmOf (eqi : EqInfo) (ℓ : Level) (α a b h : Expr) : GenM Expr :=
  transportAlong eqi .zero ℓ α a b h (eqi.refl' ℓ α a) fun z => pure (eqi.mk' ℓ α z a)

/-- **Church `False`'s `Sort v` eliminator**, which is what lets `False` leave
the basis: from `h : ∀ p : Prop, p` take `h (0 = 1) : 0 = 1`, build the family
`fun n => Nat.rec (fun _ => Sort v) (lift.{v} ⊤) (fun _ _ => C) n` — whose
value at `0` is an *inhabited* type and at `1` is `C` — and transport the
inhabitant along the equation.

`Nat`'s large elimination is what makes the family; `Eq`'s is what transports;
The tight-pair/PUnit lift puts an inhabited type at `Sort v` for a **bare**
`v`, exactly the gap the old basis filled with `False` itself. -/
def cfalseElim (eqi : EqInfo) (v : Level) (C h : Expr) : GenM Expr := do
  let natT : Expr := .const `Nat []
  let unitAt := puliftT v trueP
  let fam := fun (n : Expr) =>
    natRec (.succ v) (.lam `x natT (.sort v) .default) unitAt
      (.lam `m natT (.lam `ih (.sort v) C .default) .default) n
  let eqn := eqi.mk' (.succ .zero) natT (natNumeral 0) (natNumeral 1)
  transportAlong eqi v (.succ .zero) natT (natNumeral 0) (natNumeral 1)
    (.app h eqn) (puliftUp v trueP trueI) (fun z => pure (fam z))

/-- Anything at all out of an inhabitant of [`InductiveModels.emptyAt`]: project the
Church `⊥` out of the lift, then eliminate it. -/
def emptyAtElim (eqi : EqInfo) (v w : Level) (C e : Expr) : GenM Expr :=
  cfalseElim eqi v C (puliftDown w falseP e)

/-! ## The singleton at an arbitrary level

`Sort ℓ` for a **bare or variable** `ℓ` is out of every *other* basis former's
reach — `Eq` and `Acc` land in `Prop`, `Nat` in `Type`, and a Π lands there
only through an `imax` collapse, which needs
a `Sort ℓ`-valued *body*. The tight-pair/PUnit composite lands there for
**any** `ℓ` whatsoever and — unlike the `False`-Π family the old basis used —
is empty exactly when its proposition is. Thus its lifted `⊤` is the
singleton below and its lifted `⊥` is [`InductiveModels.emptyAt`].

Like [`InductiveModels.dsingAt`]'s pads the singleton **is** definitionally
canonical — *every element is defeq to [`InductiveModels.unitAtCanon`]*, by structure
eta on `PSigma'` and `PUnit` against the literal pair plus proof irrelevance on `⊤` — so
wherever one is destructed the applied minor already has the target type and
no transport rides along. This is where the `False`-Π singleton cost a
`funext`, and it is why the destructor needs no transport at all and ι is
`Eq.refl` with nothing to erase.

**Read "canonical" narrowly.** What holds is `t ≡ canon`, where one side is a
constructor application and eta expands the other. What does *not* hold is
`x ≡ y` for two opaque inhabitants: no side is a redex, so the kernel refuses
it — see [`InductiveModels.puliftEta`].
Every use below is of the first kind. -/

/-- The singleton at exactly `Sort ℓ`: the lift of `⊤`. -/
def unitAt (ℓ : Level) : Expr := puliftT ℓ trueP

/-- Its canonical element. -/
def unitAtCanon (ℓ : Level) : Expr := puliftUp ℓ trueP trueI

/-- `Eq canon t` for `t : unitAt ℓ`. [`InductiveModels.puliftEta`] proves
`Eq (up (down t)) t`, and `up (down t)` is *definitionally* the canonical
element: both components are proofs of `⊤`, and proof irrelevance closes it.
No `funext`.

[`InductiveModels.padsAt`] marks both current pad families `canonical := true`, because
`t ≡ canon` is a conversion the kernel performs (the canonical element is a
literal `up`, so eta expands `t` against it). Consequently
[`InductiveModels.chainDestruct`] takes its no-transport branch for the lift pad as
well as for the `D` pad. This function makes the generic `canonical := false`
branch total, and its behavior is measured rather than assumed: forcing the
lift pad through here by setting
`canonical := false` leaves every `prim_shapes` occupant modelling, and
forcing the `D` pad through here — where the proof is about the wrong type —
is red at `Tri`, `Opt`, `Dec` and `Big`. -/
def unitAtUniq (eqi : EqInfo) (ℓ : Level) (t : Expr) : Expr :=
  puliftEta eqi ℓ trueP t

/-- Is a pad at this level buildable? [`InductiveModels.dsingAt`]'s domain, asked
before anything is spliced so that a decline costs no splice. -/
partial def dsingOk (ℓ : Level) : Bool :=
  match ℓ.normalize with
  | .succ _ => true
  | .max a b => dsingOk a && dsingOk b
  | _ => false

/-- A **definitionally-canonical singleton at exactly `Sort ℓ`**: every
element is *defeq* to the canonical one, by `PUnit` eta, tight-pair eta and
proof irrelevance on the components — so a pad costs no transport and no
`funext`, and ι stays `Eq.refl`.

`D 1 := PUnit.{1}`; `D (a+1) :=
(α : Sort a) → D 1`, whose Π is at `imax (a+1) 1 = a+1`; `D (max a b) :=
Σ'(_ : D a), D b`. -/
partial def dsingAt (ℓ : Level) : GenM (Expr × Expr) := do
  let d1 := punitT (.succ .zero)
  let c1 := punitUnit (.succ .zero)
  match ℓ.normalize with
  | .succ .zero => return (d1, c1)
  | .succ a =>
    return (.forallE `α (.sort a) d1 .default, .lam `α (.sort a) c1 .default)
  | .max a b =>
    let (ta, ca) ← dsingAt a
    let (tb, cb) ← dsingAt b
    let β := Expr.lam `x ta tb .default
    return (psigmaT a b ta β, psigmaMk a b ta β ca cb)
  | _ => badShape s!"no pad at Sort {ℓ}"

/-- A chain's pad: its type, its type's level, and its canonical element.

`canonical` says whether every element is **defeq** to `canon`, in which case
no uniqueness proof rides along. **Both families set it**: the
[`InductiveModels.dsingAt`] pad by `PSigma'`/`PUnit` structure eta, and
the [`InductiveModels.unitAt`] lift — used at a level `dsingOk` cannot build, a bare
parameter in the gap, `PULift`'s shape — by tight-pair and unit structure eta
against the literal pair that `canon` is. Thus current planners do not select
the `false` case; [`InductiveModels.unitAtUniq`] is the generic transport branch, and
the measurement that validates it is in that docstring. -/
structure Pad where
  ty : Expr
  lv : Level
  canon : Expr
  canonical : Bool

/-! ## Boxing a field whose level is an `imax`

A Π-typed field's level is an `imax` chain — `Trans.mk`'s field `(a b c : …) →
r a b → s b c → t a c` reaches `Sort (imax u₁ (imax u₂ (imax u₃ (imax u
(imax v w)))))` — and no pad absorbs an `imax`: level defeq is normal-form
equality, and a `max` does not subsume an `imax` term even when both its sides
are present. What collapses it is making every Π codomain never-`Prop`:
`imax a b = max a b` once `b` cannot be zero.

The boxing below is therefore recursive.  At an atomic type `S` it uses
`Σ' (_ : S), D 1`; at `∀ x : A, B x` it stores a function from the recursively
boxed `A` to the recursively boxed `B (unbox x)`.  The contravariant domain
conversion is essential for a field such as `((α → β) → β)`: boxing only its
outer codomain leaves the inner domain level `imax u v`, while recursive
boxing produces `(Box α → Box β) → Box β` at the literal level `max 1 u v`.

The box pad is `D 1`, every element of which is defeq to canonical.  By
induction over the Π telescope, `unbox (box v) ≡ v` and `box (unbox y) ≡ y`
hold by βι, `PSigma'` structure eta, proof irrelevance and function eta alone:
no transport, no axiom, and ι stays `Eq.refl`. -/

/-- Is there an `imax` anywhere in the level? Asked of normal forms: a level
the pads cannot absorb. -/
partial def levelHasIMax : Level → Bool
  | .imax .. => true
  | .max a b => levelHasIMax a || levelHasIMax b
  | .succ a => levelHasIMax a
  | _ => false

/-- The universe of [`InductiveModels.boxTyOf`] without constructing its `PSigma'`
terms. The W arm asks its tower-level question before primitives are spliced,
so this level-only mirror keeps that early, rollback-free guard while using the
same recursive Π shape as the actual box. -/
partial def boxLevelOf (t : Expr) : GenM Level := do
  match ← whnf t with
  | .forallE name domain body info =>
    let domainLevel ← boxLevelOf domain
    withLocalDecl name info domain fun x => do
      let bodyLevel ← boxLevelOf (body.instantiate1 x)
      return (mkLevelIMax domainLevel bodyLevel).normalize
  | atomic =>
    let level ← ilevel atomic
    return (mkLevelMax' (.succ .zero) level).normalize

mutual

  /-- The recursively boxed type.  Atomic leaves are paired with `D 1`; a Π
  recursively boxes its domain and codomain, substituting the unboxed domain
  value into the dependent codomain. -/
  partial def boxTyOf (t : Expr) : GenM Expr := do
    match ← whnf t with
    | .forallE name domain body info =>
      let boxedDomain ← boxTyOf domain
      withLocalDecl name info boxedDomain fun boxedValue => do
        let value ← unboxValOf domain boxedValue
        let boxedBody ← boxTyOf (body.instantiate1 value)
        mkForallFVars #[boxedValue] boxedBody
    | atomic =>
      let level ← ilevel atomic
      let (d1, _) ← dsingAt (.succ .zero)
      return psigmaT level (.succ .zero) atomic (.lam `x atomic d1 .default)

  /-- Recursively box a value, contravariantly unboxing each Π argument before
  applying the original function. -/
  partial def boxValOf (t v : Expr) : GenM Expr := do
    match ← whnf t with
    | .forallE name domain body info =>
      let boxedDomain ← boxTyOf domain
      withLocalDecl name info boxedDomain fun boxedValue => do
        let value ← unboxValOf domain boxedValue
        let result ← boxValOf (body.instantiate1 value) (mkApp v value)
        mkLambdaFVars #[boxedValue] result
    | atomic =>
      let level ← ilevel atomic
      let (d1, c1) ← dsingAt (.succ .zero)
      return psigmaMk level (.succ .zero) atomic (.lam `x atomic d1 .default) v c1

  /-- Recursively unbox a value, boxing each original Π argument before
  applying the stored function. -/
  partial def unboxValOf (t v : Expr) : GenM Expr := do
    match ← whnf t with
    | .forallE name domain body info =>
      withLocalDecl name info domain fun value => do
        let boxedValue ← boxValOf domain value
        let result ← unboxValOf (body.instantiate1 value) (mkApp v boxedValue)
        mkLambdaFVars #[value] result
    | atomic =>
      let level ← ilevel atomic
      let (d1, _) ← dsingAt (.succ .zero)
      let β := Expr.lam `x atomic d1 .default
      let motive := Expr.lam `p (psigmaT level (.succ .zero) atomic β) atomic .default
      let minor := Expr.lam `fst atomic (.lam `snd d1 (.bvar 1) .default) .default
      return psigmaRec level level (.succ .zero) atomic β motive minor v

end

/-! ## One constructor's chain

A constructor's field telescope becomes a right-nested `PSigma'` at exactly
`Sort w`. The builders below recurse on the (progressively instantiated)
telescope expression, so nothing is stored across scopes. `pad?` closes the
chain when the field levels do not already reach `w` — and always for a
nullary constructor. `boxed` says, per field, whether the field is stored
boxed ([`InductiveModels.boxTyOf`]); a later field's type always depends on the
*unboxed* value, so the recursions instantiate with `unbox` of the bound
variable and the real value stays what the minor is applied to. -/

/-- The chain's type and level. `nf` is the field count; the telescope's
trailing result type is never entered. -/
partial def chainTy (pad? : Option Pad) (boxed : Array Bool) (nf : Nat) (tele : Expr)
    (i : Nat := 0) : GenM (Expr × Level) := do
  if nf == 0 then
    let some p := pad? | badShape "a chain with no fields needs a pad"
    return (p.ty, p.lv)
  let .forallE x t rest _ := tele | badShape "field telescope shorter than the field count"
  let bx := boxed[i]?.getD false
  let st ← if bx then boxTyOf t else pure t
  let ℓt ← ilevel st
  if nf == 1 && pad?.isNone then
    return (st, ℓt)
  withLocalDeclD x st fun xv => do
    let rv ← if bx then unboxValOf t xv else pure xv
    let (inner, ℓi) ← chainTy pad? boxed (nf - 1) (rest.instantiate1 rv) (i + 1)
    return (psigmaT ℓt ℓi st (← mkLambdaFVars #[xv] inner),
      (mkLevelMax' ℓt ℓi).normalize)

/-- The tuple `⟨v₁, ⟨v₂, …⟩⟩` at the given field values — each boxed where its
plan says so — closed by the pad's canonical element when there is one. -/
partial def chainTuple (pad? : Option Pad) (boxed : Array Bool) (nf : Nat) (tele : Expr)
    (vals : Array Expr) (i : Nat := 0) : GenM Expr := do
  if nf == 0 then
    let some p := pad? | badShape "a chain with no fields needs a pad"
    return p.canon
  let .forallE x t rest _ := tele | badShape "field telescope shorter than the field count"
  let bx := boxed[i]?.getD false
  let sv ← if bx then boxValOf t vals[i]! else pure vals[i]!
  if nf == 1 && pad?.isNone then
    return sv
  let st ← if bx then boxTyOf t else pure t
  let ℓt ← ilevel st
  let (β, ℓi) ← withLocalDeclD x st fun xv => do
    let rv ← if bx then unboxValOf t xv else pure xv
    let (inner, ℓi) ← chainTy pad? boxed (nf - 1) (rest.instantiate1 rv) (i + 1)
    return (← mkLambdaFVars #[xv] inner, ℓi)
  let snd ← chainTuple pad? boxed (nf - 1) (rest.instantiate1 vals[i]!) vals (i + 1)
  return psigmaMk ℓt ℓi st β sv snd

/-- The recursor's destructor for one chain: from `scrut : chainTy`, an
element of `target (wrap scrut)` — `wrap` embeds a suffix value into the
full tuple (the identity at the top) and `target` is `fun tup => M ⟨j̄,
tup⟩`. The minor is applied to the collected fields, each unboxed where the
plan boxed it. A canonical pad costs nothing — `scrut` is defeq to its
canonical element. A [`InductiveModels.unitAt`] pad is discharged by transporting
the applied minor along [`InductiveModels.unitAtUniq`], and on a constructor
application that proof is a closed self-equality which K-like reduction on
`Eq.rec` erases — ι stays `Eq.refl` on both. -/
partial def chainDestruct (v : Level) (eqi : EqInfo)
    (pad? : Option Pad) (boxed : Array Bool) (nf : Nat) (tele : Expr) (scrut : Expr)
    (wrap : Expr → Expr) (target : Expr → GenM Expr)
    (minorAt : Array Expr → Expr) (vals : Array Expr := #[]) (i : Nat := 0) : GenM Expr := do
  if nf == 0 then
    let some p := pad? | badShape "a chain with no fields needs a pad"
    if p.canonical then
      -- `scrut` is defeq to the pad's canonical element, so the applied minor
      -- already has the target type.
      return minorAt vals
    -- A lift pad: transport along its eta. No axiom rides along.
    return ← transportAlong eqi v p.lv p.ty p.canon scrut
      (unitAtUniq eqi p.lv scrut) (minorAt vals) (fun z => target (wrap z))
  let .forallE x t rest _ := tele | badShape "field telescope shorter than the field count"
  let bx := boxed[i]?.getD false
  if nf == 1 && pad?.isNone then
    let rv ← if bx then unboxValOf t scrut else pure scrut
    return minorAt (vals.push rv)
  let st ← if bx then boxTyOf t else pure t
  let ℓt ← ilevel st
  let (β, ℓi) ← withLocalDeclD x st fun xv => do
    let rv ← if bx then unboxValOf t xv else pure xv
    let (inner, ℓi) ← chainTy pad? boxed (nf - 1) (rest.instantiate1 rv) (i + 1)
    return (← mkLambdaFVars #[xv] inner, ℓi)
  let motive ← withLocalDeclD `s (psigmaT ℓt ℓi st β) fun s => do
    mkLambdaFVars #[s] (← target (wrap s))
  let m ← withLocalDeclD x st fun xv => do
    let rv ← if bx then unboxValOf t xv else pure xv
    withLocalDeclD `s (mkApp β xv).headBeta fun s => do
      let wrap' := fun (z : Expr) => wrap (psigmaMk ℓt ℓi st β xv z)
      mkLambdaFVars #[xv, s] (← chainDestruct v eqi pad? boxed (nf - 1)
        (rest.instantiate1 rv) s wrap' target minorAt (vals.push rv) (i + 1))
  return psigmaRec v ℓt ℓi st β motive m scrut

/-! ## The Type route's recursor tower -/

/-- What one constructor contributes, at a given parameter scope. -/
structure PCtor where
  /-- The instantiated field telescope. -/
  tele : Expr
  nf : Nat
  pad? : Option Pad
  /-- Which fields are stored boxed ([`InductiveModels.boxTyOf`]). -/
  boxed : Array Bool
  /-- The chain type. -/
  chain : Expr

instance : Inhabited PCtor := ⟨⟨default, 0, none, #[], default⟩⟩

/-- `F`'s cases tower over `scrut`: `chain_j` at tag `j̄`, empty above. -/
partial def fibreTower (w : Level) (cs : Array PCtor) (j : Nat) (scrut : Expr) :
    GenM Expr := do
  if j == cs.size then
    return emptyAt w
  let natT : Expr := .const `Nat []
  let sc ← withLocalDeclD `n natT fun n' => do
    withLocalDeclD `ih (.sort w) fun ih => do
      mkLambdaFVars #[n', ih] (← fibreTower w cs (j + 1) n')
  return natRec (.succ w) (.lam `x natT (.sort w) .default) cs[j]!.chain sc scrut

/-- The recursor's cases tower over the tag: at level `j` the zero case is
constructor `j`'s destructor and the successor case descends; past the last
constructor the fibre is empty and [`InductiveModels.emptyAtElim`] closes it. `scrut`
is the level's own binder; the original tag is `succ^j scrut`. -/
partial def stepTower (v w : Level) (eqi : EqInfo) (fib : Expr)
    (tgt : Expr → Expr) (minorOf : Nat → Array Expr → Expr)
    (cs : Array PCtor) (j : Nat) (scrut : Expr) : GenM Expr := do
  let natT : Expr := .const `Nat []
  let mkAt := fun (tag tup : Expr) => psigmaMk (.succ .zero) w natT fib tag tup
  let mot ← withLocalDeclD `m natT fun m => do
    let tag := natSuccs j m
    withLocalDeclD `f (mkApp fib tag).headBeta fun f => do
      mkLambdaFVars #[m] (← mkForallFVars #[f] (tgt (mkAt tag f)))
  let zc ← do
    let c := cs[j]!
    withLocalDeclD `f c.chain fun f => do
      let target := fun (tup : Expr) => pure (tgt (mkAt (natNumeral j) tup))
      let minorAt := minorOf j
      mkLambdaFVars #[f] (← chainDestruct v eqi c.pad? c.boxed c.nf c.tele f id target minorAt)
  let sc ← withLocalDeclD `m natT fun m => do
    let inner ←
      if j + 1 == cs.size then
        let tag := natSuccs (j + 1) m
        withLocalDeclD `f (emptyAt w) fun f => do
          mkLambdaFVars #[f] (← emptyAtElim eqi v w (tgt (mkAt tag f)) f)
      else
        stepTower v w eqi fib tgt minorOf cs (j + 1) m
    withLocalDeclD `ih (mkApp mot m).headBeta fun ih =>
      mkLambdaFVars #[m, ih] inner
  return natRec (mkLevelIMax' w v).normalize mot zc sc scrut

/-- The Church minor's type: the constructor's field telescope with the
result swapped for `C`. -/
partial def churchSwap (C : Expr) (nf : Nat) (t : Expr) : GenM Expr := do
  if nf == 0 then return C
  let .forallE x d b bi := t | badShape "telescope shorter than its field count"
  withLocalDecl x bi d fun xv => do
    mkForallFVars #[xv] (← churchSwap C (nf - 1) (b.instantiate1 xv))

/-- The `k_j` binders of the Church encoding, opened in one scope. -/
partial def churchBinders (kTys : Array Expr) (j : Nat) (ks : Array Expr)
    (k : Array Expr → GenM Expr) : GenM Expr := do
  if j == kTys.size then k ks
  else withLocalDeclD (Name.mkSimple s!"k{j}") kTys[j]! fun kv =>
    churchBinders kTys (j + 1) (ks.push kv) k

/-! ## Indices and recursion in the Church encoding

Two features the encoding above does not have, and both are one rewrite of the
minor-premise types away.

**Indices.** Quantify `C` over the whole index telescope instead of over
nothing: `T' p⃗ ι⃗ := ∀ C : (∀ ι⃗, Prop), k⃗ → C ι⃗`, with each minor `k_j`
ending in `C` applied to *constructor j's own* index expressions. The
declaration's parameters are only ever context, never analysed.

**Recursion.** A recursive field `f : ∀ z⃗, T p⃗ e⃗` becomes `∀ z⃗, C e⃗` in the
minor's type and `fun z⃗ => f z⃗ C k⃗` in the fold. Strict positivity for a
single non-nested inductive admits exactly that shape, so a field that mentions
`T` in any *other* position is a nested occurrence and is declined rather than
mis-rewritten. -/

/-- A field of a constructor, classified. `rec? = some nb` says the field is a
recursive occurrence under `nb` binders — `nb = 0` for a bare `T p⃗ e⃗`. -/
structure PField where
  /-- The binder telescope's length, for a recursive field. -/
  rec? : Option Nat
  deriving Inhabited

/-- Recognize an application of `owner` through transparent definitional
wrappers, and return its complete argument vector when its arity is exact.

`whnfUntil` is important here: ordinary `whnf` may continue by unfolding the
owner itself, while a syntactic `getAppFn` rejects a field written through a
transparent former such as `At T i := T i`.  This helper stops at the named
owner.  It is used only for route selection and for recovering recursive
indices; the exported constructor, recursor and iota types are never replaced
by the reduced expression. -/
def ownerAppArgs? (owner : Name) (np ni : Nat) (e : Expr) : GenM (Option (Array Expr)) := do
  let some app ← whnfUntil e owner | return none
  let args := app.getAppArgs
  return if args.size == np + ni then some args else none

/-- Rewrite a constructor's telescope for the Church encoding: recursive
fields' types and the result both get `C` in place of `T p⃗`. Returns the
rewritten telescope and the per-field classification.

`ni` is the index count; the arguments after the first `np` of an occurrence
of `T` are its index expressions, and they are copied verbatim. -/
partial def churchSwapAt (tname : Name) (np ni : Nat) (C : Expr) (nf : Nat) (t : Expr)
    (acc : Array PField := #[]) : GenM (Expr × Array PField) := do
  if nf == 0 then
    -- the constructor's result: `T p⃗ ι⃗_j` ↦ `C ι⃗_j`
    let some args ← ownerAppArgs? tname np ni t
      | badShape s!"a constructor of {tname} does not end in {tname} applied to \
        {np} parameters and {ni} indices"
    return (mkAppN C (args.extract np args.size), acc)
  let .forallE x d b bi := t | badShape "telescope shorter than its field count"
  let mut d' := d
  let mut fld : PField := { rec? := none }
  if mentionsAny #[tname] d then
    let (dd, nb) ← forallTelescope d fun zs res => do
      let some args ← ownerAppArgs? tname np ni res
        | badShape s!"a field of {tname} mentions {tname} other than as a recursive \
          occurrence (∀ z, {tname} p e) — a nested occurrence, which is layer 1's business"
      for z in zs do
        if mentionsAny #[tname] (← ityp z) then
          badShape s!"a recursive field of {tname} binds an argument whose type \
            mentions {tname}"
      return (← mkForallFVars zs (mkAppN C (args.extract np args.size)), zs.size)
    d' := dd
    fld := { rec? := some nb }
  withLocalDecl x bi d' fun xv => do
    -- A later field's type never depends on a recursive one (strict
    -- positivity forbids it), so instantiating with the rewritten binder is
    -- safe exactly where it matters and irrelevant elsewhere.
    let (rest, acc') ← churchSwapAt tname np ni C (nf - 1) (b.instantiate1 xv) (acc.push fld)
    return (← mkForallFVars #[xv] rest, acc')

/-! ## Packing an index telescope

The subsingleton arm's degenerate `r := ⊥` case states
its Henry-Ford equations as **one** `Eq` at the whole index telescope packed
into a right-nested `PSigma'`, rather than one `Eq` per index. It has to: a
later index's type may mention an earlier one — `HEq`'s telescope is
`{β : Sort u} (b : β)`, which is already the dependent worst case — and
separate equations cannot be stated, let alone transported along, in that
situation.

The three functions below are driven by the *packed type* rather than by the
telescope. That is deliberate: reading a component's type back off a built
expression is only valid while nothing has beta-reduced it, and that
assumption has already cost this file two attempts (see
[`InductiveModels.pairArm`]). A `PSigma'` application is stable under everything the
elaborator does to it, so destructuring it is safe. -/

/-- `Σ'(x₁ : A₁) … A_n` over a **subsequence** `sel` of an opened index
telescope, right-nested, with the last selected index's *type* as the final
component — so a one-element selection packs to that type alone, with no
`PSigma'` at all. Closed over the *selected* telescope entries and over nothing
else: an unselected index stays free, which is exactly what the subsingleton
arms need when some index positions are **pivots** — positions the model
substitutes rather than equates — whose variables remain in scope while the
rest are packed around them (`Fmid` in
`test/fixtures/inductive-models/prim_idx.lean` is the shape that
pins it: a pivot sitting *between* two dependent non-pivots, so the second
selected type still mentions the first while the pivot between them is
skipped).

`packTyOf` is this at the full telescope, and every call site that packs every
index goes on using it. -/
partial def packTyAt (is : Array Expr) (sel : Array Nat) (k : Nat) :
    GenM (Expr × Level) := do
  let x := is[sel[k]!]!
  let ty ← ityp x
  let ℓ ← ilevel ty
  if k + 1 == sel.size then return (ty, ℓ)
  let (inner, ℓi) ← packTyAt is sel (k + 1)
  let β ← mkLambdaFVars #[x] inner
  return (psigmaT ℓ ℓi ty β,
    (mkLevelMax' ℓ ℓi).normalize)

/-- `Σ'(x₁ : A₁) … A_n` over an opened index telescope, right-nested, with the
last index's *type* as the final component — so a one-index telescope packs to
that type alone, with no `PSigma'` at all. Closed over the telescope. -/
def packTyOf (is : Array Expr) (k : Nat) : GenM (Expr × Level) :=
  packTyAt is (Array.range is.size) k

/-- Read a `PSigma'` application apart: its two levels, its `α` and its `β`. -/
def psigmaParts (R : Expr) : GenM (Level × Level × Expr × Expr) := do
  let args := R.getAppArgs
  unless R.getAppFn.isConstOf `PSigma' && args.size == 2 do
    badShape "the packed index type is not a PSigma' application"
  let [u, v] := R.getAppFn.constLevels! | badShape "PSigma' carries the wrong level list"
  return (u, v, args[0]!, args[1]!)

/-- The packing of a value vector, driven by the packed type. -/
partial def packChain (n : Nat) (R : Expr) (vs : Array Expr) (k : Nat) : GenM Expr := do
  if n <= 1 then return vs[k]!
  let (u, v, α, β) ← psigmaParts R
  let snd ← packChain (n - 1) (Expr.app β vs[k]!).headBeta vs (k + 1)
  return psigmaMk u v α β vs[k]! snd

/-- The `n` components read back out of a packed term. Structure eta makes
`pack (unpack y) ≡ y`, which is what lets the recursor's motive be stated
about a packed variable and still apply to the declaration's own indices. -/
partial def unpackChain (n : Nat) (R : Expr) (y : Expr) : GenM (Array Expr) := do
  if n <= 1 then return #[y]
  let (u, v, α, β) ← psigmaParts R
  let f := psigmaFst u v α β y
  let sn := psigmaSnd u v α β y
  return #[f] ++ (← unpackChain (n - 1) (Expr.app β f).headBeta sn)

/-! ## Linear recursion at a never-zero sort: the tuple tower

A **linearly recursive** declaration is one whose every
constructor has at most one recursive field, with that field not under a
binder. Constructors then split into *base* (no recursive field) and *step*
(exactly one), and the carrier is a spine-indexed tower:

```text
V 0       := Σ'(tag : Nat), Base_tag           -- a Nat.rec tag tower
V (n+1)   := Σ'(tag : Nat), Step_tag (V n)     -- another, at the shorter spine
T         := Σ'(n : Nat), V n

base ctor c_j f⃗            := ⟨0,       ⟨bⱼ, chain f⃗⟩⟩
step ctor c_j pre r post   := ⟨r.1 + 1, ⟨sⱼ, chain (pre, r.2, post)⟩⟩
```

`n` counts recursive depth, so the representation is unique and no carve is
needed. The recursor is `PSigma'.rec'` on the outer pair, `Nat.rec` on the
spine, the existing tag towers inside each level, and `PSigma'.rec'` down each
chain — and **every ι rule is `Eq.refl`**, because at a step constructor the
recursive argument is rebuilt as `⟨n, r.2⟩`, which structure eta makes
definitionally `r`, and the induction hypothesis is the spine's own `Nat.rec`
at `r.1` applied to `r.2`, which is the recursor at `r` for the same reason.
No transport, no `funext`.

What it cannot do is a constructor with **two** recursive fields: the spine is
a single `Nat` and `⟨r.1 + 1, …⟩` has exactly one predecessor to take, so two
sub-terms at spines `n₁` and `n₂` cannot both sit in one fibre `V n` unless
the spine is generalised to a tree — which is the very inductive being built.
That is plan B's territory, and `Lean.ParserDescr` lives there. -/

/-! ### Reading a field's head, at layer 3

**`Expr.getAppFn` on `(fun x => T p⃗ e⃗) k` is a lambda**, so every "is the
recursive occurrence a bare `T p⃗ e⃗`" test in this file answers *no* on a
field whose type is a redex — and reports it as infinitary, which it is not:
there is no binder over the occurrence at all, only an application nobody
reduced.

That is Lean's own nested specialisation and not a hypothetical. A container
with a dependent value field — `Impl α β | inner : … → (k : α) → β k → …` —
specialised at `β := fun _ => T` carries the field as `(fun x => T) k`, and a
`let` in the family's body survives the same way. This same defect at layer 1
cost `Lean.Json` and `Lean.PrefixTreeNode` their
nested models until [`InductiveModels.Gen.occIdx?`] and its two siblings started
reading through [`InductiveModels.headNorm`]. Layer 3 is the same two declarations
one step further on: their `_model.aux` families are what the composition
hands *this* file, and the redex is still in them.

So the repair is the same function and deliberately not a second one — β and
ζ, iterated, no constant unfolded. It is applied where this file asks a
question whose answer is invariant under β and ζ:

* **is the occurrence bare** — [`InductiveModels.recSlotOf`] and `erasureBareWhy`;
* **what are its index arguments, and how many binders is it under** —
  [`InductiveModels.withRecSlot`], which is where arm C's `ctorIdxAt` used to inspect
  only the unreduced head;
* **what binders does a recursive field have** — [`InductiveModels.tagFactored`],
  which has none to peel until the redex is gone.

and at the indexed erasure's internal boundary:
[`InductiveModels.erasureFieldDomain`] head-normalises a field which syntactically
mentions the erased owner. If the occurrence disappears, the field was never
recursive; if binders appear, the skeleton keeps those binders and replaces
the occurrence beneath them. No public declaration type is normalised, and a
declaration whose constructor types are already βζ-normal therefore takes
exactly the path it took before, byte for byte. A genuinely nested occurrence
survives head normalisation under its foreign type former and is still routed
back to layer 1.

`PFunctor.Approx.CofixA`'s `(F.B a → CofixA n)` is a binder that is genuinely
*written*, so none of this touches it — it is arm C's infinitary erasure that
carries it, and `prim_carve`'s `Inf2`, `Cf` and `Bif` are its fixtures. -/

/-- **Does `B` factor through the constructor tag?** — the one question that
decides whether a declaration W can model is *certifiable*.

The untagged W construction uses a path step carrying the whole label, so `mk`
has to decide `x.1 = a` at the label type; that is
`Classical.propDecidable`, and it costs `[propext, Classical.choice,
Quot.sound]` on every constant. The tagged construction uses the same W with a
path step carrying only the **constructor tag**, so the test is `Fin k` equality and
the bill drops to `[propext, Quot.sound]` — the covered set, since
`Classical.choice` has been refuted as a term of the checker's language while
the other two are certified or covered.

The tagged construction needs the branch type to be a function of the tag
alone, which is exactly: **a recursive field's binder types may not mention the
constructor's own non-recursive fields.** They may mention the parameters,
which are fixed for the whole declaration. `DT | mk : (n : Nat) → (Fin n → DT)
→ DT` is the counterexample and `Lean.Expr.app : Expr → Expr → Expr` is the
common case, whose recursive fields have no binders at all and so pass
vacuously.

De Bruijn bookkeeping, since it is what the test actually is: inside a
recursive field's domain at field position `i`, having opened `j` of the
domain's own binders, indices `0 … j-1` are those binders, `j … j+i-1` are the
constructor's earlier fields, and above that the parameters. So a binder type
must have no loose bvar in `[j, j+i)`.

Non-throwing, and asked of every declaration the W arm would take, so that the
census reports the certifiable and uncertifiable populations as two numbers
rather than one. -/
def tagFactored (tname : Name) (np : Nat) (exportCtors : Array (Name × Expr)) : Bool :=
  exportCtors.all fun (_, cty) => Id.run do
    let mut t := cty
    for _ in [0:np] do
      match t with
      | .forallE _ _ b _ => t := b
      | _ => return false
    let mut i := 0
    while t matches .forallE .. do
      let .forallE _ dom b _ := t | unreachable!
      if mentionsAny #[tname] dom then
        -- peel the field's own binder telescope and check each binder type.
        -- Through `headNorm`: a redex has no binders to peel until it is
        -- reduced, and the binders it hides are the ones this is asking about.
        let mut d := headNorm dom
        let mut j := 0
        while d matches .forallE .. do
          let .forallE _ z db _ := d | unreachable!
          for m in [0:i] do
            if z.hasLooseBVar (j + m) then return false
          d := db
          j := j + 1
      t := b
      i := i + 1
    return true

/-- **Does `B` factor through the whole label?** — the same question as
[`InductiveModels.tagFactored`], asked of the *untagged* instantiation of the same
core, and the guard arm W actually runs on.

The untagged form is the tagged construction at `K := A` and `tg := id`, so
there is one construction and two bills. At `K := A` the branch
type is `B' : A → Sort w` and `A` is the tag *paired with that constructor's
non-recursive fields*, so a recursive field's binders may mention those fields
freely — `Tel` reads them back out of the label's own data. What they still may
not mention is an earlier **recursive** field: the label carries no children,
so there is nowhere for `Tel` to read one from.

`tagFactored` implies this, and the difference between the two is exactly the
two columns the report prints. A declaration this admits and `tagFactored`
refuses is modelled at `[propext, Classical.choice, Quot.sound]`, because
`WT.decEqAll` is `Classical.propDecidable`; one it admits *and* `tagFactored`
admits keeps `instDecidableEqNat` and stays at `[propext, Quot.sound]`.

Non-throwing, for the same reason `tagFactored` is. -/
def labelFactored (tname : Name) (np : Nat) (exportCtors : Array (Name × Expr)) : Bool :=
  exportCtors.all fun (_, cty) => Id.run do
    let mut t := cty
    for _ in [0:np] do
      match t with
      | .forallE _ _ b _ => t := b
      | _ => return false
    -- Which of this constructor's own fields are recursive, by position. The
    -- test is `mentionsAny` on the *written* domain, exactly as
    -- [`InductiveModels.eraseCtorTy`] and `wShapeOf` ask it, so all three agree about
    -- which fields the two towers split the telescope into.
    let mut recAt : Array Bool := #[]
    let mut u := t
    while u matches .forallE .. do
      let .forallE _ dom b _ := u | unreachable!
      recAt := recAt.push (mentionsAny #[tname] dom)
      u := b
    let mut i := 0
    while t matches .forallE .. do
      let .forallE _ dom b _ := t | unreachable!
      if recAt[i]! then
        -- Same de Bruijn bookkeeping as `tagFactored`'s: with `j` of the
        -- domain's own binders opened, loose index `j + m` is the field at
        -- position `i - 1 - m`. Only the recursive ones are refused.
        let mut d := headNorm dom
        let mut j := 0
        while d matches .forallE .. do
          let .forallE _ z db _ := d | unreachable!
          for m in [0:i] do
            if recAt[i - 1 - m]! && z.hasLooseBVar (j + m) then return false
          d := db
          j := j + 1
      t := b
      i := i + 1
    return true

/-- The field domain used by an internal erasure or spine.

Usually this is the exported field domain byte for byte. A specialised redex
which syntactically mentions the owner is head-normalised at this internal
boundary. Thus `(fun _ : T i => N) k` becomes the genuinely non-recursive `N`,
while a redex reducing to `∀ z, T i` exposes the binder the erasure must retain.
A nested occurrence remains nested after the same reduction and is declined by
the routing guard. Public declaration types never pass through this function. -/
def erasureFieldDomain (tname : Name) (dom : Expr) : Expr :=
  if mentionsAny #[tname] dom then headNorm dom else dom

/-- Whether an internal erasure or spine field contains an occurrence which
must be replaced, after exposing its βζ head and discarding dead mentions. -/
def erasureRecursive (tname : Name) (dom : Expr) : Bool :=
  mentionsAny #[tname] (erasureFieldDomain tname dom)

/-- Explain why the index erasure cannot replace every recursive occurrence
by its bare skeleton owner.  This walk is monadic solely because a transparent
former around the owner must be recognized by definitional reduction; its
answer remains a diagnostic value and it emits no declaration.

Keeping the early exits in a named `GenM` computation also makes their scope
unambiguous: they return from this analysis, never from the surrounding model
construction. -/
def erasureBareFailure? (tname : Name) (np ni : Nat)
    (exportCtors : Array (Name × Expr)) : GenM (Option String) := do
  for (cn, cty) in exportCtors do
    let mut t := cty
    let mut short := false
    for _ in [0:np] do
      match t with
      | .forallE _ _ b _ => t := b
      | _ => short := true
    if short then return some s!"{cn}'s telescope is shorter than {np} parameters"
    while t matches .forallE .. do
      let .forallE _ dom b _ := t | unreachable!
      let dom := erasureFieldDomain tname dom
      if mentionsAny #[tname] dom then
        -- Peel the field's own binders after βζ head normalization. The
        -- erasure retains those binder types, so an owner mention there would
        -- refer to the wrong carrier after the field itself is retyped.
        let mut core := dom
        let mut inBinder := false
        while core matches .forallE .. do
          let .forallE _ z cb _ := core | unreachable!
          if mentionsAny #[tname] z then inBinder := true
          core := cb
        if inBinder then
          return some s!"binder mention: a binder of {cn}'s recursive field mentions \
{tname}, and the erasure keeps binder types verbatim"
        -- A transparent former around `T p⃗ e⃗` is bare. Reduction is confined
        -- to this route/index analysis; the public model retains `dom`.
        if (← ownerAppArgs? tname np ni core).isNone then
          return some s!"nested: {cn} has a recursive occurrence that is not an \
application of {tname}"
      t := b
  return none

/-- Which field of a constructor is the recursive one, if any. Declines the
shapes the tower cannot express, each by name. -/
def recSlotOf (tname : Name) (np ni : Nat) (cn : Name) (nf : Nat) (tele : Expr)
    (tagged : Bool := true) (typeU : Bool := true) (labelled : Bool := true) :
    GenM (Option Nat) := do
  -- **The W arm's bill, printed at the decline that names W**, and it is two
  -- questions because the arm runs the one core at two
  -- instantiations. `labelled` is [`InductiveModels.labelFactored`] and is the one
  -- that decides *whether* W reaches the declaration; `tagged` is
  -- [`InductiveModels.tagFactored`] and decides only *what it costs* — yes and the
  -- model is `[propext, Quot.sound]`, which is covered; no and it spends
  -- `Classical.choice` on top. Two populations, so the census counts two
  -- numbers, and a decline that reads `through the tag: no` alone is a model
  -- rather than a gap.
  let bill := s!"; B factors through the tag: {if tagged then "yes" else "no"}\
; through the label: {if labelled then "yes" else "no"}\
; carrier is Type u: {if typeU then "yes" else "no"}"
  let mut cur := tele
  let mut slot : Option Nat := none
  for i in [0:nf] do
    let .forallE _ d b _ := cur | badShape "field telescope shorter than its field count"
    let d := erasureFieldDomain tname d
    if mentionsAny #[tname] d then
      if slot.isSome then
        badShape s!"{cn} has two recursive fields: the tuple tower's spine is one \
Nat and a constructor takes one predecessor, so a branching constructor needs the \
W/path construction (plan B){bill}"
      -- A βζ-dead mention was removed above.  Every domain which remains is a
      -- real binder or nesting if its head is not the owner itself.
      unless (← ownerAppArgs? tname np ni d).isSome do
        badShape s!"{cn} has a recursive field that is not a bare occurrence of \
{tname} — under a binder, or nested, neither of which the tuple tower reaches{bill}"
      slot := some i
    cur := b
  return slot

/-- A recursive field's domain with the **occurrence** replaced by `Vn` and the
binders it sits under kept verbatim: `T p⃗ e⃗` becomes `Vn` and `∀ z⃗, T p⃗ e⃗`
becomes `∀ z⃗, Vn`.

The domain is read through [`InductiveModels.headNorm`], so the same operation handles
a binder exposed only by βζ reduction. `Vn` is closed over the parameter scope
and never mentions `z⃗`, which is what
makes keeping the binders and replacing only the core well typed. The binder
types themselves are kept **as written** — they may mention the constructor's
earlier non-recursive fields, and `erasureBareWhy` has already refused a binder
type that mentions `tname`, which is the one shape that would not survive the
retyping of the field it names. -/
partial def swapOcc (Vn : Expr) (d : Expr) : GenM Expr := do
  match headNorm d with
  | .forallE x z b bi =>
    withLocalDecl x bi z fun zv => do mkForallFVars #[zv] (← swapOcc Vn (b.instantiate1 zv))
  | _ => return Vn

/-- The constructor's field telescope with its recursive field's type replaced
by the shorter spine's fibre `V n`. The recursive occurrence sits at `Sort w`
either way, so the storage plan computed on the export's telescope is the
plan for this one too.

The tuple tower only ever calls this at a **bare** occurrence, where
[`InductiveModels.swapOcc`] is the identity on binders and this is the whole-domain
replacement it always was; arm C calls it at an infinitary one too. -/
partial def spineSwap (tname : Name) (Vn : Expr) (nf : Nat) (tele : Expr) :
    GenM Expr := do
  if nf == 0 then return tele
  let .forallE x d b bi := tele | badShape "field telescope shorter than its field count"
  let d := erasureFieldDomain tname d
  let d' ← if mentionsAny #[tname] d then swapOcc Vn d else pure d
  withLocalDecl x bi d' fun xv => do
    mkForallFVars #[xv] (← spineSwap tname Vn (nf - 1) (b.instantiate1 xv))

/-- The same classification as [`InductiveModels.churchSwapAt`] makes, without the
rewrite — used where the *values* are built, since those are bound at the
model's restored telescope and not at the export's. -/
partial def classifyCtor (tname : Name) (nf : Nat) (tele : Expr)
    (acc : Array PField := #[]) : GenM (Array PField) := do
  if nf == 0 then return acc
  let .forallE x d b bi := tele | badShape "telescope shorter than its field count"
  let fld : PField ←
    if mentionsAny #[tname] d then
      forallTelescope d fun zs _ => pure { rec? := some zs.size }
    else pure { rec? := none }
  withLocalDecl x bi d fun xv =>
    classifyCtor tname (nf - 1) (b.instantiate1 xv) (acc.push fld)

/-- **One `Pair`-valued premise of the strong-induction fold.**

Walks constructor `j`'s *export* telescope, binding one variable per field —
a recursive field at `∀ z⃗, Pair e⃗` rather than at its own type — and ends at

    fun D k => k (c_j elems) (fun _h => minor elems ihs)

where, for each recursive slot, `elems` holds the carrier element read out of
that slot's pair and `ihs` the induction hypothesis read out beside it, both
pointwise under the field's own binders. The minor premise takes the fields in
declaration order and then the hypotheses, which is the order Lean's recursors
use.

The index expressions are taken from the export telescope as it is walked, not
read back off the built types: `Pair` is a λ, so `Pair e⃗` is a β-redex and
whether its arguments are still visible is a fact about whoever last touched
the expression. This is the bug that cost the first two attempts.

At a maybe-zero sort, `Self` itself cannot instantiate the pair's `D : Prop`.
`baseAt` is the Church proposition under the derived exact-sort lift; extracting a recursive
element instantiates at that proposition, maps the stored `Self` through
`down`, and maps the result back through `up`. With no lift, `baseAt = Self`
and these two boundary maps are identities. -/
partial def pairArm (tname : Name) (np ni : Nat) (us : List Level)
    (selfAt : Array Expr → Expr) (pairAt : Array Expr → GenM Expr)
    (baseAt : Array Expr → GenM Expr) (lift? : Option Level)
    (motive : Expr) (cN : Name) (minor : Expr) (ps : Array Expr)
    (nf : Nat) (tele : Expr) (elems ihs : Array Expr) : GenM Expr := do
  if nf == 0 then
    let some args ← ownerAppArgs? tname np ni tele
      | badShape s!"a constructor of {tname} does not present {ni} index arguments"
    let isj := args.extract np args.size
    let sfj := selfAt isj
    let built := mkAppN (.const cN us) (ps ++ elems)
    return ← withLocalDeclD `D (.sort .zero) fun D => do
      let armTy ← withLocalDeclD `e sfj fun e => do
        let qTy ← withLocalDeclD `h sfj fun h =>
          mkForallFVars #[h] (mkAppN motive (isj.push h))
        withLocalDeclD `q qTy fun q => mkForallFVars #[e, q] D
      withLocalDeclD `k armTy fun k => do
        let proof ← withLocalDeclD `h sfj fun h =>
          mkLambdaFVars #[h] (mkAppN minor (elems ++ ihs))
        mkLambdaFVars #[D, k] (mkAppN k #[built, proof])
  let .forallE x d b bi := tele | badShape "telescope shorter than its field count"
  if !(mentionsAny #[tname] d) then
    return ← withLocalDecl x bi d fun xv => do
      mkLambdaFVars #[xv] (← pairArm tname np ni us selfAt pairAt baseAt lift?
        motive cN minor ps (nf - 1) (b.instantiate1 xv) (elems.push xv) ihs)
  -- a recursive field `∀ z⃗, T p⃗ e⃗`: bind it at `∀ z⃗, Pair e⃗`
  let nb ← forallTelescope d fun zs _ => pure zs.size
  let dPair ← forallBoundedTelescope d (some nb) fun zs res => do
    let some a ← ownerAppArgs? tname np ni res
      | badShape s!"a recursive field of {tname} does not present {ni} index arguments"
    mkForallFVars zs (← pairAt (a.extract np a.size))
  withLocalDecl x bi dPair fun pv => do
    let (el, ih) ← forallBoundedTelescope d (some nb) fun zs res => do
      let some a ← ownerAppArgs? tname np ni res
        | badShape s!"a recursive field of {tname} does not present {ni} index arguments"
      let ris := a.extract np a.size
      let sf := selfAt ris
      let baseTy ← baseAt ris
      let app := mkAppN pv zs
      let mkArm := fun (k : Expr → Expr → GenM Expr) =>
        withLocalDeclD `e sf fun e => do
          let qTy ← withLocalDeclD `h sf fun h =>
            mkForallFVars #[h] (mkAppN motive (ris.push h))
          withLocalDeclD `q qTy fun q => do mkLambdaFVars #[e, q] (← k e q)
      let elArm ← mkArm fun e _ => pure <| match lift? with
        | none => e
        | some ℓ => puliftDown ℓ baseTy e
      let elBase := mkAppN app #[baseTy, elArm]
      let el := match lift? with
        | none => elBase
        | some ℓ => puliftUp ℓ baseTy elBase
      let ihArm ← mkArm fun _ q => pure (mkApp q el)
      let ih := mkAppN app #[mkAppN motive (ris.push el), ihArm]
      return (← mkLambdaFVars zs el, ← mkLambdaFVars zs ih)
    mkLambdaFVars #[pv] (← pairArm tname np ni us selfAt pairAt baseAt lift? motive cN minor ps
      (nf - 1) (b.instantiate1 el) (elems.push el) (ihs.push ih))

/-! ## Arm G: the recursive subsingleton, by the **graph** of the recursion

This is the arm that emits the graph-and-choice carrier for an arbitrary
supported shape, taking **`Acc` out of the basis** rather than putting it to
use.

The shape: an inductive `Prop` with **one** constructor, each of whose fields
is a proposition (possibly a recursive occurrence `∀ z⃗, T p⃗ e⃗`) or a piece of
data that is *literally* one of the conclusion's indices. Lean's kernel grants
that shape a `Sort v` motive by the subsingleton rule — a grant to a
*declaration* that an emitted `def` does not inherit — and the carrier the
Church route already emits eliminates only into `Prop`. So the large
eliminator has to be built, and it is built by defining the recursion by its
**graph**:

```text
Graph ι⃗ t val  := the least relation closed under "if the value at every
                   recursive sub-argument is g, then the value at (mk f⃗) is
                   step f⃗ g⃗", impredicatively encoded — so a Prop
Graph.mk        : that closure rule, as a theorem (the graph is a fixed
                   point, not merely a pre-fixed point)
GraphInv        : inversion, with the constructor's **proof** fields
                   universally quantified rather than existentially — any two
                   are definitionally equal, so quantifying gives the caller's
Graph.inv       : inversion holds, by folding at `Graph ∧ GraphInv`
Graph.unique    : single-valuedness, by the free `Prop`-motive recursor
Graph.exists    : totality, likewise, picking sub-values with Classical.choice
rec_0 step t    := (Classical.choice (Graph.exists step t)).fst
iota            : both sides are graph points and the graph is single-valued
```

**Do not** try `Classical.choice` at a bare `Nonempty (motive a t)` instead.
That recursor typechecks and is provably *blind to its step function* — the
two `Nonempty` proofs are definitionally equal — so its ι rule is not merely
unproved but derives `False`; expanding the construction gives the refutation.

**ι is propositional here, not `Eq.refl`** — the value is a `Classical.choice`
application, which reduces to nothing — and this is the only arm of the three
routes for which that is true. A consumer must rewrite with `iota_0_0` where
the kernel would have reduced.

**Two lines of the recipe are shape-sensitive**, and both are mechanical:
[`InductiveModels.congrChain`]'s n-ary congruence, one factor per recursive field,
and [`InductiveModels.funextUp`]'s chain, one `funext` per binder of a recursive
field. The recipe is checked across the three shapes that settle them.

**The axiom cost is per shape, not per arm.** `rec_0` is `Classical.choice`
uniformly; ι adds `funext` — hence the quotient and `Quot.sound` — only when
some recursive field has a binder, because that is the only thing
[`InductiveModels.funextUp`] is called for. A recursive field that is a bare
occurrence contributes none, and the degenerate shape's ι costs no
`Quot.sound` at all. -/

/-- `∀ D : Prop, (A → B → D) → D` — Church conjunction, so the folds below
need no `And` and the basis needs no sixth member for one. -/
def andCOf (A B : Expr) : Expr :=
  .forallE `D (.sort .zero)
    (.forallE `k (.forallE `a A (.forallE `b B (.bvar 2) .default) .default)
      (.bvar 1) .default) .default

/-- `Eq α x z` from `Eq α x y` and `Eq α y z`, as one `Eq.rec` at a `Prop`
motive — the companion of [`InductiveModels.symmOf`], and built the same way so that
nothing is added to the input that this module does not need to name. -/
def transOf (eqi : EqInfo) (ℓ : Level) (α x y z h1 h2 : Expr) : GenM Expr :=
  transportAlong eqi .zero ℓ α y z h2 h1 fun w => pure (eqi.mk' ℓ α x w)

/-- Bind a vector of **independent** locals in one scope. Independent is the
precondition and it is met at every call: the value functions `g⃗` depend only
on the constructor's fields, and the graph hypotheses `hg⃗` only on those and
on `g⃗`, which are bound first. -/
partial def withLocalsD (tys : Array (Name × Expr)) (i : Nat) (acc : Array Expr)
    (k : Array Expr → GenM Expr) : GenM Expr := do
  if i == tys.size then k acc
  else withLocalDeclD tys[i]!.1 tys[i]!.2 fun x => withLocalsD tys (i + 1) (acc.push x) k

/-- **Walk the constructor's field telescope**, binding one variable per
field — except that with `subst` set the *data* fields are **supplied** from
`is` rather than bound, because in this shape a data field is literally one of
the conclusion's indices.

That substitution is what `GraphInv` is stated by: inversion at an arbitrary
index `ι⃗` must conclude `val = step f⃗ g⃗`, whose right-hand side lands at the
quantified fields' own index expressions, so those expressions have to *be*
`ι⃗` — **definitionally**, which at a pivot means the same term and at an
index position typed by a `Prop` means proof irrelevance. Quantifying the data
fields instead would need the index's injectivity, which is not uniform.

`k` receives the full field vector, the ones actually bound, and the
telescope's result type. -/
partial def ctorFieldsAux (subst : Bool) (isData : Array Bool) (idxPos : Array Nat)
    (is : Array Expr) (n i : Nat) (tele : Expr) (fs bound : Array Expr)
    (k : Array Expr → Array Expr → Expr → GenM Expr) : GenM Expr := do
  if n == 0 then return ← k fs bound tele
  let .forallE x d b bi := tele | badShape "telescope shorter than its field count"
  if subst && isData[i]! then
    let a := is[idxPos[i]!]!
    ctorFieldsAux subst isData idxPos is (n - 1) (i + 1) (b.instantiate1 a) (fs.push a) bound k
  else
    withLocalDecl x bi d fun xv =>
      ctorFieldsAux subst isData idxPos is (n - 1) (i + 1) (b.instantiate1 xv)
        (fs.push xv) (bound.push xv) k

/-- **The `funext` chain, one per binder of a recursive field.** `pt` proves
`ga z⃗ = gb z⃗` at the field's own binders `z⃗`; this closes them one at a time,
innermost first, into `ga = gb`.

At **zero** binders it is the identity and no `funext` is reached at all —
which is why the degenerate shape's ι costs no `Quot.sound`, and why the
`funext` is asked for lazily and only when some recursive field has a
binder. -/
partial def funextUp (fx? : Option Name) (zs : Array Expr) (k : Nat)
    (ga gb pt : Expr) : GenM Expr := do
  if k == 0 then return pt
  let j := k - 1
  let z := zs[j]!
  let some fxN := fx?
    | badShape "a recursive field under a binder needs funext and none was available"
  let αz ← ityp z
  let lu ← ilevel αz
  let fa := mkAppN ga (zs.extract 0 j)
  let fb := mkAppN gb (zs.extract 0 j)
  let bty ← ityp (mkApp fa z)
  let lv ← ilevel bty
  let β ← mkLambdaFVars #[z] bty
  let h ← mkLambdaFVars #[z] pt
  funextUp fx? zs j ga gb (mkAppN (.const fxN [lu, lv]) #[αz, β, fa, fb, h])

/-- **The n-ary congruence in the recursive fields**, as an `Eq.trans` chain
with one `congrArg` per field:

```text
step f⃗ ga₁ ga₂ … = step f⃗ gb₁ ga₂ … = step f⃗ gb₁ gb₂ … = … = step f⃗ gb⃗
```

The single `congrArg (step x h)` is the `n = 1` case of this and is
insufficient at two recursive fields. Each `congrArg` is one `Eq.rec`, inlined here for the same
reason [`InductiveModels.funextDecl`] inlines its own. -/
def congrChain (eqi : EqInfo) (v : Level) (α : Expr) (mkStep : Array Expr → Expr)
    (ga gb pfs : Array Expr) : GenM Expr := do
  let n := ga.size
  let mixed := fun (j : Nat) => (Array.range n).map fun m => if m < j then gb[m]! else ga[m]!
  let base := mkStep ga
  let mut acc := eqi.refl' v α base
  for j in [0:n] do
    let A ← ityp ga[j]!
    let ℓA ← ilevel A
    let famAt := fun (x : Expr) => mkStep ((mixed j).set! j x)
    let factor ← transportAlong eqi .zero ℓA A ga[j]! gb[j]! pfs[j]!
      (eqi.refl' v α (famAt ga[j]!)) fun z => pure (eqi.mk' v α (famAt ga[j]!) (famAt z))
    acc ← transOf eqi v α base (mkStep (mixed j)) (mkStep (mixed (j + 1))) acc factor
  return acc

/-- Everything [`InductiveModels.graphArm`] needs about the declaration it is
modelling, settled before a single declaration is emitted so that a decline
costs no splice. -/
structure GraphCtx where
  tname : Name
  np : Nat
  ni : Nat
  nf : Nat
  /-- The declaration's own levels, and the recursor's (`v` in front). -/
  us : List Level
  recLs : List Level
  lparams : List Name
  recLevels : List Name
  /-- The motive universe. -/
  v : Level
  selfN : Name
  ctorN0 : Name
  recN : Name
  indN : Name
  grN : Name
  grMkN : Name
  grInvTN : Name
  grInvN : Name
  grUniqN : Name
  grExN : Name
  recGrN : Name
  /-- The declaration's own type, and the model constructor's — **restored**,
  so a recursive field's type is `T._model.self p⃗ e⃗`. -/
  memberTy : Expr
  ctorTy : Expr
  /-- Per field: is it data (rather than a proof), and if so which index
  position it *is*; and, for a recursive field, its binder count. -/
  isData : Array Bool
  idxPos : Array Nat
  /-- Index positions not supplied by a constructor data field.  The graph
  inversion packs exactly this dependent subsequence and transports its step
  value from the constructor indices to the caller indices. -/
  nonPiv : Array Nat
  recNb : Array (Option Nat)
  eqi : EqInfo
  /-- The `funext` the `Graph.unique` congruence transports along, `none` when
  no recursive field has a binder and none is reached. -/
  fx? : Option Name
  deriving Inhabited

/-- **The graph arm**, emitting `graph`, `graph_mk`, `graph_inv_ty`,
`graph_inv`, `graph_unique`, `graph_exists`, `rec_0` and `rec_graph`. The
carrier, the constructor and the `Prop`-motive recursor `ind` are the Church
route's own and are emitted by the caller; the ι theorem is the caller's too,
because its *statement* is shared with every other arm and only its proof is
this one's. -/
def graphArm (c : GraphCtx) (recTy : Expr) : GenM (Array Declaration) := do
  let np := c.np
  let ni := c.ni
  let nf := c.nf
  let nnp := c.nonPiv.size
  -- the recursive slots, in field order
  let rs := (Array.range nf).filter fun i => c.recNb[i]!.isSome
  let nr := rs.size

  -- **One scope for the whole arm**: the parameters, the motive and the step,
  -- read off the recursor's own type rather than rebuilt. `rest` is what is
  -- left of that type — `∀ ι⃗ (t : Self ι⃗), motive ι⃗ t` — and the two
  -- declarations that need the full telescope continue it rather than
  -- reopening.
  forallBoundedTelescope recTy (some (np + 2)) fun bs rest => do
    let mut out : Array Declaration := #[]
    let ps := bs.extract 0 np
    let motive := bs[np]!
    let step := bs[np + 1]!
    let pre := ps ++ #[motive, step]

    let selfAt := fun (is : Array Expr) => mkAppN (.const c.selfN c.us) (ps ++ is)
    let ctorAt := fun (fs : Array Expr) => mkAppN (.const c.ctorN0 c.us) (ps ++ fs)
    let motAt := fun (is : Array Expr) (t : Expr) => mkAppN motive (is.push t)
    let grAt := fun (is : Array Expr) (t val : Expr) =>
      mkAppN (.const c.grN c.recLs) (pre ++ is ++ #[t, val])
    let grInvAt := fun (is : Array Expr) (t val : Expr) =>
      mkAppN (.const c.grInvTN c.recLs) (pre ++ is ++ #[t, val])
    let idxTele ← instForall c.memberTy ps
    let ctorTele ← instForall c.ctorTy ps

    -- The dependent tuple of non-pivot indices at a caller's pivot values.
    -- Pivot types cannot mention non-pivots (the classifier checks that before
    -- entering this arm), so leaving the pivots free while closing exactly the
    -- complementary subsequence is sound even when the two are interleaved.
    let pkAt := fun (is : Array Expr) => do
      if nnp == 0 then return (none : Option (Expr × Level))
      forallBoundedTelescope idxTele (some ni) fun opened _ => do
        let (pk, ℓ) ← packTyAt opened c.nonPiv 0
        pure (some (pk.replaceFVars opened is, ℓ))

    let packedAt := fun (pk : Expr) (is : Array Expr) =>
      packChain nnp pk (c.nonPiv.map (is[·]!)) 0

    let indexEqAt := fun (is ctorIs : Array Expr) => do
      let some (pk, ℓ) ← pkAt is
        | badShape "the graph index equality was requested without a non-pivot"
      let lhs ← packedAt pk ctorIs
      let rhs ← packedAt pk is
      pure (pk, ℓ, lhs, rhs, c.eqi.mk' ℓ pk lhs rhs)

    -- Move a step value from the constructor's fibre to the arbitrary fibre
    -- at which GraphInv is queried.  The motive transports a function over the
    -- proof-valued carrier: after the indices move, proof irrelevance identifies
    -- its argument with the transported constructor proof, so applying it to
    -- the caller's `t` needs no second equality.
    let transportStep := fun (is : Array Expr) (t : Expr) (ctorIs : Array Expr)
        (value heq : Expr) => do
      if nnp == 0 then return value
      let (pk, ℓ, lhs, rhs, _) ← indexEqAt is ctorIs
      let motiveE ← withLocalDeclD `y pk fun y => do
        withLocalDeclD `hy (c.eqi.mk' ℓ pk lhs y) fun hy => do
          let ys ← unpackChain nnp pk y
          let mut full := is
          for k in [0:nnp] do full := full.set! c.nonPiv[k]! ys[k]!
          withLocalDeclD `s (selfAt full) fun s => do
            let body ← mkForallFVars #[s] (motAt full s)
            mkLambdaFVars #[y, hy] body
      let base ← withLocalDeclD `s (selfAt ctorIs) fun s =>
        mkLambdaFVars #[s] value
      pure (mkApp (c.eqi.recAt c.v ℓ pk lhs motiveE base rhs heq) t)

    -- A recursive field's own binders, and the index vector it lands at. The
    -- telescope is opened **bounded**: `forallTelescope` would whnf through
    -- `T._model.self` and open the Church encoding's own Π as well.
    let recAt := fun (f : Expr) (nb : Nat) (k : Array Expr → Array Expr → GenM Expr) => do
      forallBoundedTelescope (← ityp f) (some nb) fun zs res => do
        let some args ← ownerAppArgs? c.selfN np ni res
          | badShape s!"a recursive field of {c.tname} does not land at {c.selfN}"
        k zs (args.extract np args.size)

    -- The constructor's field telescope. `is?` supplies the data fields.
    let fields := fun (is? : Option (Array Expr))
        (k : Array Expr → Array Expr → Expr → GenM Expr) =>
      ctorFieldsAux is?.isSome c.isData c.idxPos (is?.getD #[]) nf 0 ctorTele #[] #[] k

    -- The index vector a walked telescope ends at.
    let idxOfRes := fun (res : Expr) => do
      let some args ← ownerAppArgs? c.selfN np ni res
        | badShape s!"{c.ctorN0}'s result is not {c.selfN} at {np} parameters and {ni} indices"
      pure (args.extract np args.size)

    -- `g_i : ∀ z⃗_i, motive e⃗_i (f_i z⃗_i)`, the value functions.
    let gTysAt := fun (fs : Array Expr) => rs.mapM fun i => do
      let t ← recAt fs[i]! c.recNb[i]!.get! fun zs ris =>
        mkForallFVars zs (motAt ris (mkAppN fs[i]! zs))
      pure (Name.mkSimple s!"g{i}", t)
    -- `hg_i : ∀ z⃗_i, Graph e⃗_i (f_i z⃗_i) (g_i z⃗_i)`.
    let hTysAt := fun (fs gs : Array Expr) => (Array.range nr).mapM fun j => do
      let i := rs[j]!
      let t ← recAt fs[i]! c.recNb[i]!.get! fun zs ris =>
        mkForallFVars zs (grAt ris (mkAppN fs[i]! zs) (mkAppN gs[j]! zs))
      pure (Name.mkSimple s!"hg{i}", t)

    -- ── `Q`, and the graph's one closure rule at it ──
    let qTy ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `s (selfAt is) fun s =>
        withLocalDeclD `m (motAt is s) fun m =>
          mkForallFVars (is ++ #[s, m]) (.sort .zero)
    let qStepTy := fun (Q : Expr) =>
      fields none fun fs bnd res => do
        let e ← idxOfRes res
        withLocalsD (← gTysAt fs) 0 #[] fun gs => do
          let qTys ← (Array.range nr).mapM fun j => do
            let i := rs[j]!
            let t ← recAt fs[i]! c.recNb[i]!.get! fun zs ris =>
              mkForallFVars zs (mkAppN Q (ris ++ #[mkAppN fs[i]! zs, mkAppN gs[j]! zs]))
            pure (Name.mkSimple s!"q{i}", t)
          withLocalsD qTys 0 #[] fun qs =>
            mkForallFVars (bnd ++ gs ++ qs)
              (mkAppN Q (e ++ #[ctorAt fs, mkAppN step (fs ++ gs)]))

    -- ── `Graph` ──
    let grTy ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `val (motAt is t) fun val =>
          mkForallFVars (pre ++ is ++ #[t, val]) (.sort .zero)
    let grVal ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `val (motAt is t) fun val =>
          withLocalDeclD `Q qTy fun Q => do
            let body ← mkForallFVars #[Q]
              (.forallE `q (← qStepTy Q) (mkAppN Q (is ++ #[t, val])) .default)
            mkLambdaFVars (pre ++ is ++ #[t, val]) body
    let dGr := Declaration.defnDecl
      { name := c.grN, levelParams := c.recLevels, type := grTy, value := grVal
        hints := ← hintsFor grVal, safety := .safe }
    addChecked dGr
    out := out.push dGr

    -- ── `Graph.mk` ──
    let grMkTy ← fields none fun fs bnd res => do
      let e ← idxOfRes res
      withLocalsD (← gTysAt fs) 0 #[] fun gs => do
        withLocalsD (← hTysAt fs gs) 0 #[] fun hs =>
          mkForallFVars (pre ++ bnd ++ gs ++ hs)
            (grAt e (ctorAt fs) (mkAppN step (fs ++ gs)))
    let grMkVal ← fields none fun fs bnd _ => do
      withLocalsD (← gTysAt fs) 0 #[] fun gs => do
        withLocalsD (← hTysAt fs gs) 0 #[] fun hs =>
          withLocalDeclD `Q qTy fun Q => do
            withLocalDeclD `q (← qStepTy Q) fun q => do
              let qargs ← (Array.range nr).mapM fun j => do
                let i := rs[j]!
                recAt fs[i]! c.recNb[i]!.get! fun zs _ =>
                  mkLambdaFVars zs (mkAppN (mkAppN hs[j]! zs) #[Q, q])
              mkLambdaFVars (pre ++ bnd ++ gs ++ hs)
                (← mkLambdaFVars #[Q, q] (mkAppN q (fs ++ gs ++ qargs)))
    let dGrMk := Declaration.thmDecl
      { name := c.grMkN, levelParams := c.recLevels, type := grMkTy, value := grMkVal }
    addChecked dGrMk
    out := out.push dGrMk

    -- ── `GraphInv` ──
    -- The `k` argument's type, shared by the definition and by the two places
    -- that build or consume an inhabitant of it.
    let invArmTyAt := fun (is : Array Expr) (t val : Expr) (fs ctorIs : Array Expr)
        (D : Expr) => do
      withLocalsD (← gTysAt fs) 0 #[] fun gs => do
        withLocalsD (← hTysAt fs gs) 0 #[] fun hs => do
          if nnp == 0 then
            let eq := c.eqi.mk' c.v (motAt is t) val (mkAppN step (fs ++ gs))
            mkForallFVars (gs ++ hs) (.forallE `he eq D .default)
          else
            let (_, _, _, _, idxEq) ← indexEqAt is ctorIs
            withLocalDeclD `hidx idxEq fun hidx => do
              let rhs ← transportStep is t ctorIs (mkAppN step (fs ++ gs)) hidx
              let eq := c.eqi.mk' c.v (motAt is t) val rhs
              mkForallFVars (gs ++ hs ++ #[hidx]) (.forallE `he eq D .default)
    let grInvVal ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `val (motAt is t) fun val => do
          let body ← fields (some is) fun fs bnd res => do
            let e ← idxOfRes res
            withLocalDeclD `D (.sort .zero) fun D => do
              mkForallFVars (bnd ++ #[D])
                (.forallE `k (← invArmTyAt is t val fs e D) D .default)
          mkLambdaFVars (pre ++ is ++ #[t, val]) body
    let dGrInvT := Declaration.defnDecl
      { name := c.grInvTN, levelParams := c.recLevels, type := grTy, value := grInvVal
        hints := ← hintsFor grInvVal, safety := .safe }
    addChecked dGrInvT
    out := out.push dGrInvT

    -- ── `Graph.inv` ──
    -- Fold at `Graph ∧ GraphInv`: the graph alone is not closed enough to
    -- rebuild the sub-values' graph facts. The `rfl` at the end is where
    -- proof irrelevance does the work — the fold's own fields and the
    -- inversion's quantified ones are two proofs of one proposition, so
    -- `step f⃗ g⃗` and `step f'⃗ g⃗` are the same term.
    let grInvThmTy ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `val (motAt is t) fun val =>
          mkForallFVars (pre ++ is ++ #[t, val])
            (.forallE `g (grAt is t val) (grInvAt is t val) .default)
    let grInvThmVal ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `val (motAt is t) fun val =>
          withLocalDeclD `g (grAt is t val) fun g => do
            let qArg ← forallBoundedTelescope idxTele (some ni) fun is' _ =>
              withLocalDeclD `s (selfAt is') fun s =>
                withLocalDeclD `w (motAt is' s) fun w =>
                  mkLambdaFVars (is' ++ #[s, w]) (andCOf (grAt is' s w) (grInvAt is' s w))
            let qStepArg ← fields none fun fs bnd res => do
              let e ← idxOfRes res
              withLocalsD (← gTysAt fs) 0 #[] fun gs => do
                let ihTys ← (Array.range nr).mapM fun j => do
                  let i := rs[j]!
                  let t' ← recAt fs[i]! c.recNb[i]!.get! fun zs ris =>
                    mkForallFVars zs
                      (andCOf (grAt ris (mkAppN fs[i]! zs) (mkAppN gs[j]! zs))
                        (grInvAt ris (mkAppN fs[i]! zs) (mkAppN gs[j]! zs)))
                  pure (Name.mkSimple s!"ih{i}", t')
                withLocalsD ihTys 0 #[] fun ihs => do
                  -- the left projection of each `AndC`, pointwise
                  let hgs ← (Array.range nr).mapM fun j => do
                    let i := rs[j]!
                    recAt fs[i]! c.recNb[i]!.get! fun zs ris => do
                      let gt := grAt ris (mkAppN fs[i]! zs) (mkAppN gs[j]! zs)
                      let it := grInvAt ris (mkAppN fs[i]! zs) (mkAppN gs[j]! zs)
                      let proj ← withLocalDeclD `a gt fun a =>
                        withLocalDeclD `b it fun b => mkLambdaFVars #[a, b] a
                      mkLambdaFVars zs (mkAppN (mkAppN ihs[j]! zs) #[gt, proj])
                  let major := ctorAt fs
                  let val' := mkAppN step (fs ++ gs)
                  let aTerm := mkAppN (.const c.grMkN c.recLs) (pre ++ bnd ++ gs ++ hgs)
                  let bTerm ← fields (some e) fun fs' bnd' res' => do
                    withLocalDeclD `D (.sort .zero) fun D => do
                      let e' ← idxOfRes res'
                      withLocalDeclD `k (← invArmTyAt e major val' fs' e' D) fun k' => do
                        let args ← if nnp == 0 then
                            pure (gs ++ hgs ++ #[c.eqi.refl' c.v (motAt e major) val'])
                          else do
                            let (pk, ℓ, lhs, _, _) ← indexEqAt e e'
                            pure (gs ++ hgs ++ #[c.eqi.refl' ℓ pk lhs,
                              c.eqi.refl' c.v (motAt e major) val'])
                        mkLambdaFVars (bnd' ++ #[D, k']) (mkAppN k' args)
                  let aT := grAt e major val'
                  let bT := grInvAt e major val'
                  let pair ← withLocalDeclD `D (.sort .zero) fun D =>
                    withLocalDeclD `k (.forallE `a aT (.forallE `b bT D .default) .default)
                      fun k' => mkLambdaFVars #[D, k'] (mkAppN k' #[aTerm, bTerm])
                  mkLambdaFVars (bnd ++ gs ++ ihs) pair
            let fin ← withLocalDeclD `a (grAt is t val) fun a =>
              withLocalDeclD `b (grInvAt is t val) fun b => mkLambdaFVars #[a, b] b
            mkLambdaFVars (pre ++ is ++ #[t, val, g])
              (mkAppN g #[qArg, qStepArg, grInvAt is t val, fin])
    let dGrInv := Declaration.thmDecl
      { name := c.grInvN, levelParams := c.recLevels, type := grInvThmTy
        value := grInvThmVal }
    addChecked dGrInv
    out := out.push dGrInv

    -- ── `Graph.unique` ──
    -- Single-valuedness, by the free `Prop`-motive recursor. This is the one
    -- place `funext` enters, and only for a recursive field with binders.
    let uniqTy ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `a (motAt is t) fun a =>
          withLocalDeclD `b (motAt is t) fun b =>
            mkForallFVars (pre ++ is ++ #[t, a, b])
              (.forallE `ga (grAt is t a)
                (.forallE `gb (grAt is t b) (c.eqi.mk' c.v (motAt is t) a b) .default)
                .default)
    let indMotUniq ← forallBoundedTelescope idxTele (some ni) fun is' _ =>
      withLocalDeclD `t' (selfAt is') fun t' => do
        let inner ← withLocalDeclD `a' (motAt is' t') fun a' =>
          withLocalDeclD `b' (motAt is' t') fun b' =>
            mkForallFVars #[a', b']
              (.forallE `ga' (grAt is' t' a')
                (.forallE `gb' (grAt is' t' b') (c.eqi.mk' c.v (motAt is' t') a' b')
                  .default) .default)
        mkLambdaFVars (is' ++ #[t']) inner
    let uniqVal ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t =>
        withLocalDeclD `a (motAt is t) fun a =>
          withLocalDeclD `b (motAt is t) fun b =>
            withLocalDeclD `ga (grAt is t a) fun ga =>
              withLocalDeclD `gb (grAt is t b) fun gb => do
                let minor ← fields none fun fs bnd res => do
                  let e ← idxOfRes res
                  let major := ctorAt fs
                  let α := motAt e major
                  let ihTys ← rs.mapM fun i => do
                    let t' ← recAt fs[i]! c.recNb[i]!.get! fun zs ris =>
                      mkForallFVars zs
                        (mkAppN indMotUniq (ris ++ #[mkAppN fs[i]! zs])).headBeta
                    pure (Name.mkSimple s!"ih{i}", t')
                  withLocalsD ihTys 0 #[] fun ihs =>
                    withLocalDeclD `x (motAt e major) fun x =>
                      withLocalDeclD `y (motAt e major) fun y =>
                        withLocalDeclD `gx (grAt e major x) fun gx =>
                          withLocalDeclD `gy (grAt e major y) fun gy => do
                            let goal := c.eqi.mk' c.v α x y
                            -- the fields inversion quantifies are the **proof**
                            -- ones; the data fields are the indices and are
                            -- already fixed by the point `GraphInv` is at.
                            let pf := (Array.range nf).filterMap fun i =>
                              if c.isData[i]! then none else some fs[i]!
                            let withIdxEq := fun (k : Array Expr → GenM Expr) => do
                              if nnp == 0 then k #[]
                              else
                                let (_, _, _, _, eqTy) ← indexEqAt e e
                                withLocalDeclD `hidx eqTy fun hidx => k #[hidx]
                            let contA ←
                              withLocalsD (← gTysAt fs) 0 #[] fun gA => do
                                withLocalsD (← hTysAt fs gA) 0 #[] fun hA =>
                                  withIdxEq fun hidxA =>
                                    withLocalDeclD `ea
                                      (c.eqi.mk' c.v α x (mkAppN step (fs ++ gA))) fun eA => do
                                      let contB ←
                                        withLocalsD (← gTysAt fs) 0 #[] fun gB => do
                                          withLocalsD (← hTysAt fs gB) 0 #[] fun hB =>
                                            withIdxEq fun hidxB =>
                                              withLocalDeclD `eb
                                                (c.eqi.mk' c.v α y (mkAppN step (fs ++ gB)))
                                                fun eB => do
                                                let pfs ← (Array.range nr).mapM fun j => do
                                                  let i := rs[j]!
                                                  recAt fs[i]! c.recNb[i]!.get! fun zs _ => do
                                                    let pt := mkAppN (mkAppN ihs[j]! zs)
                                                      #[mkAppN gA[j]! zs, mkAppN gB[j]! zs,
                                                        mkAppN hA[j]! zs, mkAppN hB[j]! zs]
                                                    funextUp c.fx? zs zs.size gA[j]! gB[j]! pt
                                                let cong ← congrChain c.eqi c.v α
                                                  (fun gv => mkAppN step (fs ++ gv)) gA gB pfs
                                                let sb ← symmOf c.eqi c.v α y
                                                  (mkAppN step (fs ++ gB)) eB
                                                let t2 ← transOf c.eqi c.v α
                                                  (mkAppN step (fs ++ gA))
                                                  (mkAppN step (fs ++ gB)) y cong sb
                                                let whole ← transOf c.eqi c.v α x
                                                  (mkAppN step (fs ++ gA)) y eA t2
                                                mkLambdaFVars
                                                  (gB ++ hB ++ hidxB ++ #[eB]) whole
                                      let invB := mkAppN (.const c.grInvN c.recLs)
                                        (pre ++ e ++ #[major, y, gy])
                                      mkLambdaFVars (gA ++ hA ++ hidxA ++ #[eA])
                                        (mkAppN invB (pf ++ #[goal, contB]))
                            let invA := mkAppN (.const c.grInvN c.recLs)
                              (pre ++ e ++ #[major, x, gx])
                            mkLambdaFVars (bnd ++ ihs ++ #[x, y, gx, gy])
                              (mkAppN invA (pf ++ #[goal, contA]))
                mkLambdaFVars (pre ++ is ++ #[t, a, b, ga, gb])
                  (mkAppN (mkAppN (.const c.indN c.us) (ps ++ #[indMotUniq, minor] ++ is ++ #[t]))
                    #[a, b, ga, gb])
    let dGrUniq := Declaration.thmDecl
      { name := c.grUniqN, levelParams := c.recLevels, type := uniqTy, value := uniqVal }
    addChecked dGrUniq
    out := out.push dGrUniq

    -- ── `Graph.exists` ──
    -- Totality, again by the `Prop`-motive recursor. `Classical.choice` picks
    -- the sub-values here, and single-valuedness above is what makes the
    -- choice harmless. The `Nonempty` is of the **`PSigma'` of value and graph
    -- proof**, never of `motive ι⃗ t`: that is the whole difference from the
    -- route described above refutes.
    let neAt := fun (is : Array Expr) (t : Expr) => do
      let α := motAt is t
      let β ← withLocalDeclD `val α fun val => mkLambdaFVars #[val] (grAt is t val)
      let σ := psigmaT c.v .zero α β
      let ℓσ := c.v.normalize
      pure (mkAppN (.const `Nonempty [ℓσ]) #[σ], σ, α, β, ℓσ)
    let grExTy ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t => do
        let (ne, _, _, _, _) ← neAt is t
        mkForallFVars (pre ++ is ++ #[t]) ne
    let indMotEx ← forallBoundedTelescope idxTele (some ni) fun is' _ =>
      withLocalDeclD `t' (selfAt is') fun t' => do
        let (ne, _, _, _, _) ← neAt is' t'
        mkLambdaFVars (is' ++ #[t']) ne
    let grExVal ← forallBoundedTelescope idxTele (some ni) fun is _ =>
      withLocalDeclD `t (selfAt is) fun t => do
        let minor ← fields none fun fs bnd res => do
          let e ← idxOfRes res
          let ihTys ← rs.mapM fun i => do
            let t' ← recAt fs[i]! c.recNb[i]!.get! fun zs ris => do
              let (ne, _, _, _, _) ← neAt ris (mkAppN fs[i]! zs)
              mkForallFVars zs ne
            pure (Name.mkSimple s!"ih{i}", t')
          withLocalsD ihTys 0 #[] fun ihs => do
            let pick := fun (j : Nat) (snd : Bool) => do
              let i := rs[j]!
              recAt fs[i]! c.recNb[i]!.get! fun zs ris => do
                let (_, σ, α, β, ℓσ) ← neAt ris (mkAppN fs[i]! zs)
                let ch := mkAppN (.const `Classical.choice [ℓσ]) #[σ, mkAppN ihs[j]! zs]
                mkLambdaFVars zs
                  (if snd then psigmaSnd c.v .zero α β ch else psigmaFst c.v .zero α β ch)
            let ghat ← (Array.range nr).mapM fun j => pick j false
            let hhat ← (Array.range nr).mapM fun j => pick j true
            let (_, σ0, α0, β0, ℓσ0) ← neAt e (ctorAt fs)
            let value := mkAppN step (fs ++ ghat)
            let proof := mkAppN (.const c.grMkN c.recLs) (pre ++ fs ++ ghat ++ hhat)
            mkLambdaFVars (bnd ++ ihs)
              (mkAppN (.const `Nonempty.intro [ℓσ0])
                #[σ0, psigmaMk c.v .zero α0 β0 value proof])
        mkLambdaFVars (pre ++ is ++ #[t])
          (mkAppN (.const c.indN c.us) (ps ++ #[indMotEx, minor] ++ is ++ #[t]))
    let dGrEx := Declaration.thmDecl
      { name := c.grExN, levelParams := c.recLevels, type := grExTy, value := grExVal }
    addChecked dGrEx
    out := out.push dGrEx

    -- ── the recursor, and the graph fact about it ──
    let recVal ← forallBoundedTelescope rest (some (ni + 1)) fun bs2 _ => do
      let is := bs2.extract 0 ni
      let t := bs2[ni]!
      let (_, σ, α, β, ℓσ) ← neAt is t
      let ch := mkAppN (.const `Classical.choice [ℓσ])
        #[σ, mkAppN (.const c.grExN c.recLs) (pre ++ is ++ #[t])]
      mkLambdaFVars (pre ++ bs2) (psigmaFst c.v .zero α β ch)
    let dRec := Declaration.defnDecl
      { name := c.recN, levelParams := c.recLevels, type := recTy, value := recVal
        hints := ← hintsFor recVal, safety := .safe }
    addChecked dRec
    out := out.push dRec

    let rgTy ← forallBoundedTelescope rest (some (ni + 1)) fun bs2 _ => do
      let is := bs2.extract 0 ni
      let t := bs2[ni]!
      mkForallFVars (pre ++ bs2)
        (grAt is t (mkAppN (.const c.recN c.recLs) (pre ++ bs2)))
    let rgVal ← forallBoundedTelescope rest (some (ni + 1)) fun bs2 _ => do
      let is := bs2.extract 0 ni
      let t := bs2[ni]!
      let (_, σ, α, β, ℓσ) ← neAt is t
      let ch := mkAppN (.const `Classical.choice [ℓσ])
        #[σ, mkAppN (.const c.grExN c.recLs) (pre ++ is ++ #[t])]
      mkLambdaFVars (pre ++ bs2) (psigmaSnd c.v .zero α β ch)
    let dRg := Declaration.thmDecl
      { name := c.recGrN, levelParams := c.recLevels, type := rgTy, value := rgVal }
    addChecked dRg
    out := out.push dRg

    return out

/-! ## The model -/

/-- One constructor's storage plan, settled by level arithmetic before
anything is spliced: which fields are boxed, and the pad level, `none` where
the chain reaches `Sort w` on its own. The pad level is `1` when that already
closes the gap and `w` otherwise. -/
structure CPlan where
  boxed : Array Bool
  pad? : Option Level
  deriving Inhabited

/-- The pads of every constructor at the given parameter scope, `none` where
the plan needs none. A `dsingOk` level gets the [`InductiveModels.dsingAt`] pad; any
other level — a bare parameter in the gap, `PULift`'s shape — gets the
[`InductiveModels.unitAt`] lift, which exists at every level.

**Both are marked `canonical`**, and that is the measured fact rather than a
symmetry: each family's canonical element is a literal constructor
application, so the kernel converts an opaque element onto it and neither pad
costs a transport. What the lift does *not* give is a conversion between two
opaque elements; nothing here asks for one. -/
def padsAt (plans : Array CPlan) :
    GenM (Array (Option Pad)) := do
  plans.mapM fun plan => do
    let some ℓ := plan.pad? | return none
    if dsingOk ℓ then
      let (t, c) ← dsingAt ℓ
      return some { ty := t, lv := ℓ, canon := c, canonical := true }
    return some { ty := unitAt ℓ, lv := ℓ, canon := unitAtCanon ℓ, canonical := true }

/-- The constructors, analysed at a parameter scope. -/
def pctorsAt (exportCtors : Array (Name × Expr)) (plans : Array CPlan)
    (pads : Array (Option Pad)) (ps : Array Expr) : GenM (Array PCtor) := do
  (Array.range exportCtors.size).mapM fun j => do
    let (_, cty) := exportCtors[j]!
    let tele ← instForall cty ps
    let nf := numForalls tele
    let boxed := plans[j]!.boxed
    let (chain, _) ← chainTy pads[j]! boxed nf tele
    return { tele, nf, pad? := pads[j]!, boxed, chain }

/-- Which route the carrier's sort admits: `Sort 0` is the Church encoding, a
never-zero sort the `Nat`-tagged sum, and a **maybe-zero** sort — `Prop` at
some instantiations, `Type` at others, `PUnit`'s and `PEmpty`'s shape — the
same Church encoding under a [`InductiveModels.puliftT`]. -/
inductive PrimRoute | type | prop | bare

/-- A field-preserving model for the one-field corner of the bare route.
`identity` applies when the field already inhabits the carrier's exact sort;
`propLift` lifts an exactly proposition-valued field to that sort. -/
inductive DirectFieldRoute | identity | propLift

/-- The complete field-preserving direct routes. The one-field cases share
[`InductiveModels.directFieldModel`]; `tight` is the multi-field `PSigma'` tower. -/
inductive DirectRoute
  | field (route : DirectFieldRoute)
  | tight

/-! ## Arm C's index erasure

The skeleton arm C splices is the declaration with its indices dropped: the
carrier loses its index telescope and every recursive field and every
constructor's conclusion loses its index arguments. Nothing else moves except
that a field whose only owner mention βζ-disappears is stored at its reduct;
[`InductiveModels.erasureFieldDomain`] is that one internal exception. Public types
remain literal. This is the whole reason this arm has no currying glue where
the W route has one lemma per constructor.

Both functions below are **raw `Expr` surgery on de Bruijn indices and not a
telescope walk**, and that is forced rather than stylistic: opening a telescope
means `withLocalDecl` at a type mentioning `T._model.skel`, which `MetaM` would
have to `inferType`, and the constant does not exist yet — it is the one being
declared. Asking for it costs an `Unknown constant` and exit 3. -/

/-- `∀ p⃗, Sort w` from the declaration's `∀ p⃗ ι⃗, Sort w`. -/
partial def eraseSelfTy (np : Nat) (w : Level) (e : Expr) : Expr :=
  if np == 0 then .sort w else
  match e with
  | .forallE x d b bi => .forallE x d (eraseSelfTy (np - 1) w b) bi
  | _ => .sort w

/-- One constructor's type with its indices erased. After `np` parameters and
`i` field binders the parameter `p_k` sits at de Bruijn index `np-1-k+i`, which
is what `skelAt` rebuilds `T._model.skel p⃗` from.

A field is recursive exactly when it mentions `tname`, and `erasureBare` has
already established that the occurrence is a bare `T p⃗ e⃗` **under a possibly
empty binder telescope of its own** — so replacing the occurrence and keeping
the binders is right, and a field this would corrupt has been declined.
**Once per such field and no cap on how many**: a branching constructor erases
exactly as a linear one does, which is why arm C is gated on bareness alone.

`eraseOcc` is where the infinitary field is carried. `∀ z⃗, T p⃗ e⃗` erases to
`∀ z⃗, S p⃗` — the binder types are kept from the field's head-normal form.
They may mention the parameters and the constructor's earlier non-recursive
fields, neither of which moves, and each binder crossed pushes the parameters
one index further out, which is what its `d` counts. At zero binders it is the
whole-domain replacement this function has always done, byte for byte. -/
partial def eraseCtorTy (tname skelN : Name) (us : List Level) (np : Nat) (e : Expr) : Expr :=
  let skelAt := fun (d : Nat) => mkAppN (.const skelN us)
    ((Array.range np).map fun k => Expr.bvar (np - 1 - k + d))
  let rec eraseOcc (d : Nat) (t : Expr) : Expr :=
    match t with
    | .forallE x z b bi => .forallE x z (eraseOcc (d + 1) b) bi
    | _ => skelAt d
  let rec fields (i : Nat) (t : Expr) : Expr :=
    match t with
    | .forallE x dom b bi =>
      let dom := erasureFieldDomain tname dom
      .forallE x (if mentionsAny #[tname] dom then eraseOcc i dom else dom) (fields (i + 1) b) bi
    | _ => skelAt i
  let rec params (k : Nat) (t : Expr) : Expr :=
    if k == np then fields 0 t else
    match t with
    | .forallE x dom b bi => .forallE x dom (params (k + 1) b) bi
    | _ => fields 0 t
  params 0 e

/-- **A recursive slot, opened.** A recursive field's type is `∀ z⃗, T p⃗ e⃗`
with `z⃗` possibly empty; this opens the `z⃗` as local declarations and hands
the continuation them and the child's index arguments `e⃗`, which may mention
them. Everything arm C builds per slot — the `good` clause, the constructor's
component, the recursor's induction hypothesis — is a `mkLambdaFVars zs` or a
`mkForallFVars zs` around what the continuation returns, and at `zs = #[]` each
of them is the term the bare case built before this existed.

**Read through [`InductiveModels.headNorm`]**, exactly as `erasureBareWhy`,
[`InductiveModels.eraseCtorTy`], [`InductiveModels.spineSwap`] and [`InductiveModels.swapOcc`] read
it: the guard and every internal consumer must agree about how many binders a
field has and what its index vector is. A domain that arrives as a redex has
neither until it is reduced; only the internal skeleton sees that reduction,
while the public declaration remains literal.

Not a decline path in practice: every refusal it can make, `erasureBareWhy`
has already made before the arm was entered. It is stated rather than
`unreachable!` because the two walks are separate code. -/
partial def withRecSlot [Inhabited α] (tname : Name) (np ni : Nat) (dom : Expr)
    (k : Array Expr → Array Expr → GenM α) (zs : Array Expr := #[]) : GenM α := do
  match headNorm dom with
  | .forallE x z b bi =>
    withLocalDecl x bi z fun zv =>
      withRecSlot tname np ni (b.instantiate1 zv) k (zs.push zv)
  | h =>
    let some args ← ownerAppArgs? tname np ni h
      | badShape s!"a recursive field of {tname} is not a bare application at {np} \
          parameters and {ni} indices"
    k zs (args.extract np args.size)

/-! ## Arm W's kit

This arm directly emits the tagged W scheme. For a declaration at
`Sort w = Type u`
with constructors `c⃗`:

    D   p⃗ t   := Σ' (a : nrᵗ₁), … Σ' (a : nrᵗₖ), 𝟙        -- ⊥ off the end
    Tel p⃗ t j := Σ' (x : Xⱼ,₁), … Σ' (x : Xⱼ,ₘ), 𝟙        -- ⊥ off the end
    B'  p⃗ t   := Σ' j : Nat, Tel p⃗ t j
    A   p⃗     := Σ' t : Nat, D p⃗ t
    tg  p⃗     := PSigma'.fst

**Both towers end in a unit at exactly `Sort w` and neither may collapse**, and
that is what makes the universes come out: the core fixes `A` and `B'` at the
same `Type u`, a tower over the field types alone lands at `Type (max v⃗)` —
below `u` in general — and there is no `ULift` here to close the gap. Ending
every tower at [`InductiveModels.unitAt`] `w`, which is at exactly `Sort w`, makes the
max exactly `w` for free at every arity including zero.

`Σ'` is `PSigma'` rather than the fragment's `Sigma` for a second reason beside
the levels: a non-recursive field may sit at `Prop`, and `Sigma`'s domain may
not. `PSigma'` is on [`InductiveModels.inductiveBasis`] and its eta is the kernel's
structure eta.

**The junk is uninhabited in both directions and that is load-bearing for
elaboration, not only for correctness.** `D p⃗ t` for `t ≥ nc` and `Tel p⃗ t j`
for `j` past that constructor's recursive-field count are
[`InductiveModels.emptyAt`] `w`; the constructors' and the recursor's junk arms are
discharged from that emptiness, so a junk arm sent to the *unit* does not
quietly produce a `W` bigger than the target — it fails to typecheck. -/

/-- **A `Nat.rec` cascade over a tag**: `armAt k` at `k` for `k < n`, and
`junkAt` from `n` on. This is the shape a generator emits where a human writes
a `match`, and it is a cascade rather than a `match` because a `match` would
mint a `T.match_1` that the model would then owe the output.

`motAt k` is the motive **at depth `k`** — a lambda over the *remaining* index,
whose body speaks of `succ^k` of it — and `s` is the sort that motive lands in.
The two `succ` chains meet because `succ^k (succ t)` and `succ^(k+1) t` are the
same term, so the succ-minor built at depth `k+1` already has the type depth
`k` asks for and no transport rides along.

`n = 0` degenerates to `junkAt` with no `Nat.rec` at all, which is the branch
tower of a constructor with no children. -/
partial def natCascade (s : Level) (n : Nat) (motAt : Nat → GenM Expr)
    (armAt : Nat → GenM Expr) (junkAt : Expr → GenM Expr) (k : Nat) (sc : Expr) :
    GenM Expr := do
  if k == n then return ← junkAt sc
  let mot ← motAt k
  let base ← armAt k
  let step ← withLocalDeclD `t (.const `Nat []) fun t =>
    withLocalDeclD `ih (mkApp mot t).headBeta fun ih => do
      mkLambdaFVars #[t, ih] (← natCascade s n motAt armAt junkAt (k + 1) t)
  return natRec s mot base step sc

/-- The W towers box exactly the components whose level retains an `imax`.
The recursive box is the same one the tuple route uses: exposed Π domains and
codomains are transformed all the way to atomic leaves, so a nested domain such
as `((α → β) → β)` does not leave an `imax` hidden contravariantly. -/
def wTowerBoxed (xs : Array Expr) : GenM (Array Bool) :=
  xs.mapM fun x => return levelHasIMax (← ilevel (← ityp x)).normalize

/-- **One tower's type**, over the fields `xs⟦i…⟧` and ending at the unit at
`Sort w`. `pre` are the unboxed values of earlier components. A boxed binder is
unboxed before it is substituted into later component types, preserving the
original dependent telescope. -/
partial def wTowerTy (w : Level) (xs : Array Expr) (boxed : Array Bool)
    (i : Nat) (pre : Array Expr := #[]) : GenM Expr := do
  if i == xs.size then return unitAt w
  let sub := fun (e : Expr) => e.replaceFVars (xs.extract 0 pre.size) pre
  let original := sub (← ityp xs[i]!)
  let stored ← if boxed[i]! then boxTyOf original else pure original
  let ℓ ← ilevel stored
  withLocalDeclD (← xs[i]!.fvarId!.getUserName) stored fun x => do
    let value ← if boxed[i]! then unboxValOf original x else pure x
    let β ← mkLambdaFVars #[x] (← wTowerTy w xs boxed (i + 1) (pre.push value))
    return psigmaT ℓ w stored β

/-- **Is a tower over these fields at `Sort w`?** `max ℓᵢ w ≡ w` at every field,
which is Lean's own constraint on the declaration re-asked as a conversion:
a field of an inductive at `Sort w` sits at some `Sort ℓ` with `max ℓ w = w`.
Asked before anything is spliced, so a declaration this refuses costs no
splice, and asked of the *expression* rather than assumed. Components with an
exposed `imax` are measured after recursive boxing; this still refuses an
opaque atomic type whose level contains an `imax`, because no available box can
inspect that type far enough to normalize its level. -/
def wTowerLevel (w : Level) (xs : Array Expr) (boxed : Array Bool) : GenM (Option Level) := do
  for i in [0:xs.size] do
    let original ← ityp xs[i]!
    let ℓ ← if boxed[i]! then boxLevelOf original else ilevel original
    unless ← isLevelDefEq (mkLevelMax' ℓ w) w do return some ℓ
  return none

/-- **One level of a tower at a substitution** — the `α` and `β` that
[`InductiveModels.wTowerTy`] wrote at field `i`, with the earlier fields replaced by
whatever the caller has in their place (projections when a tower is being taken
apart, values when one is being built).

**The binder type is substituted too**, and that is the whole reason this is a
function rather than two lines at each call site: `β` is `fun (x : Xᵢ) => …`,
`Xᵢ` mentions the earlier fields, and abstracting the field variable closes the
*body* over it while leaving the domain pointing at a variable that is no
longer in scope. A tower whose fields do not depend on each other never notices;
`test/fixtures/inductive-models/prim_w.lean`'s `Dep` is the occupant that does, and it found this as a
kernel `declaration has free variables`. -/
def wTowerAt (w : Level) (xs : Array Expr) (boxed : Array Bool) (i : Nat)
    (pre : Array Expr) : GenM (Level × Expr × Expr × Expr) := do
  let sub := fun (vs : Array Expr) (e : Expr) => e.replaceFVars (xs.extract 0 vs.size) vs
  let original := sub pre (← ityp xs[i]!)
  let stored ← if boxed[i]! then boxTyOf original else pure original
  let ℓ ← ilevel stored
  let β ← withLocalDeclD (← xs[i]!.fvarId!.getUserName) stored fun x => do
    let value ← if boxed[i]! then unboxValOf original x else pure x
    mkLambdaFVars #[x] (← wTowerTy w xs boxed (i + 1) (pre.push value))
  return (ℓ, original, stored, β)

/-- **The components of a tower, read back out of it.** At step `i` the earlier
fields are already projections, so the `α` and `β` this rebuilds are the ones
`wTowerTy` wrote with those substituted in — which is what makes the projection
well-typed when a later field's type mentions an earlier one. -/
partial def wTowerProjs (w : Level) (xs : Array Expr) (boxed : Array Bool)
    (i : Nat) (d : Expr)
    (acc : Array Expr) : GenM (Array Expr) := do
  if i == xs.size then return acc
  let (ℓ, original, stored, β) ← wTowerAt w xs boxed i acc
  let fst := psigmaFst ℓ w stored β d
  let value ← if boxed[i]! then unboxValOf original fst else pure fst
  wTowerProjs w xs boxed (i + 1) (psigmaSnd ℓ w stored β d) (acc.push value)

/-- **A tower built from field values** — the same `α` and `β` as
[`InductiveModels.wTowerProjs`] rebuilds, so `⟨proj⃗ d⟩` and `d` are the same tower and
structure eta closes the round trip with no transport. -/
partial def wTowerMk (w : Level) (xs : Array Expr) (boxed : Array Bool)
    (i : Nat) (vals : Array Expr) : GenM Expr := do
  if i == xs.size then return unitAtCanon w
  let (ℓ, original, stored, β) ← wTowerAt w xs boxed i (vals.extract 0 i)
  let value ← if boxed[i]! then boxValOf original vals[i]! else pure vals[i]!
  return psigmaMk ℓ w stored β value (← wTowerMk w xs boxed (i + 1) vals)

def wTowerTyOf (w : Level) (xs : Array Expr) : GenM Expr := do
  wTowerTy w xs (← wTowerBoxed xs) 0

def wTowerLevelOf (w : Level) (xs : Array Expr) : GenM (Option Level) := do
  wTowerLevel w xs (← wTowerBoxed xs)

def wTowerProjsOf (w : Level) (xs : Array Expr) (d : Expr) : GenM (Array Expr) := do
  wTowerProjs w xs (← wTowerBoxed xs) 0 d #[]

def wTowerMkOf (w : Level) (xs vals : Array Expr) : GenM Expr := do
  wTowerMk w xs (← wTowerBoxed xs) 0 vals

/-- The two universe levels at which arm W exposes and builds its carrier.

Most declarations expose the W core directly, so both levels are the public
carrier level.  A predecessor-free, provably positive public level instead
uses a small `Type` core and stores it in the exact-sort `PSigma'` described by
[`WCarrierPlan.carrier`].  Keeping this plan and its term builders outside
`primIso` is also important: that definition is already close to Lean's
default elaboration budget. -/
structure WCarrierPlan where
  publicLevel : Level
  coreLevel : Level
  lifted : Bool

/-- Choose the constrained lift exactly when `w` has no syntactic predecessor
but `max 1 w` is definitionally `w`. -/
def wCarrierPlan (eligible : Bool) (w : Level) : GenM WCarrierPlan := do
  let lifted ← if eligible && w.normalize.dec.isNone then
      isLevelDefEq (mkLevelMax' (.succ .zero) w) w
    else pure false
  return { publicLevel := w, coreLevel := if lifted then .succ .zero else w, lifted }

def WCarrierPlan.liftFam (p : WCarrierPlan) (lowTy : Expr) : Expr :=
  .lam `low lowTy (puliftT p.publicLevel trueP) .default

/-- Expose `lowTy : Sort core` at the plan's exact public carrier sort. -/
def WCarrierPlan.carrier (p : WCarrierPlan) (lowTy : Expr) : Expr :=
  if p.lifted then
    psigmaT p.coreLevel p.publicLevel lowTy (p.liftFam lowTy)
  else lowTy

/-- Insert the canonical proof carried only to make the constrained lift land
at the exact public sort. -/
def WCarrierPlan.wrap (p : WCarrierPlan) (lowTy low : Expr) : Expr :=
  if p.lifted then
    psigmaMk p.coreLevel p.publicLevel lowTy (p.liftFam lowTy) low
      (unitAtCanon p.publicLevel)
  else low

def WCarrierPlan.unwrap (p : WCarrierPlan) (lowTy value : Expr) : Expr :=
  if p.lifted then
    psigmaFst p.coreLevel p.publicLevel lowTy (p.liftFam lowTy) value
  else value

/-- Pull a public motive back along `wrap`, for the low W recursor. -/
def WCarrierPlan.motive (p : WCarrierPlan) (lowTy motive : Expr) : GenM Expr := do
  if p.lifted then
    withLocalDeclD `low lowTy fun low =>
      mkLambdaFVars #[low] (mkApp motive (p.wrap lowTy low))
  else
    pure motive

/-- Complete the simple generator's explicit retry table. -/
def primAliasMap (tname root model ern recN : Name) (exportCtors : Array (Name × Expr))
    (ctorN iotaN : Nat → Name) (ruleK? : Option Name)
    (out : Array Declaration) : Naming.AliasMap := Id.run do
  if root == tname then return .empty
  let mut aliases := Naming.AliasMap.forRetry model (Naming.modelName tname)
    (out.flatMap (·.getNames.toArray))
  for j in [0:exportCtors.size] do
    aliases := aliases.insert (ctorN j) (Naming.modelName exportCtors[j]!.1)
    aliases := aliases.insert (iotaN j) (Naming.iotaName ern j)
  aliases := aliases.insert recN (Naming.modelName ern)
  if let some name := ruleK? then
    aliases := aliases.insert name (Naming.ruleKName ern)
  return aliases

/-- Emit the simple route's K theorem without adding another large branch to
`primIso`, which is already close to Lean's elaboration recursion limit. -/
def primRuleK (eqi : EqInfo) (rv : RecursorVal)
    (tname root model ern : Name) (reserved : Std.HashSet Name)
    (iotaName : Name)
    (out : Array Declaration) :
    GenM (Array Declaration × Array (Name × Name) × Option Name) := do
  unless rv.k do return (out, #[], none)
  let ruleKN := Naming.ruleKName (Naming.relocateSource tname root ern)
  let emitted :=
    if model.isPrefixOf ruleKN then
      ruleKN.replacePrefix model (Naming.modelName tname)
    else ruleKN
  if reserved.contains emitted || (← getEnv).constants.contains emitted then
    declineWith (.nameTaken emitted)
  if root != tname && ruleKN != emitted &&
      (reserved.contains ruleKN || (← getEnv).constants.contains ruleKN) then
    declineWith (.nameTaken ruleKN)
  unless rv.rules.length == 1 do badShape s!"{ern} is K-like with {rv.rules.length} rules"
  let iotaType? := out.findSome? fun declaration => match declaration with
    | .thmDecl value => if value.name == iotaName then some value.type else none
    | _ => none
  let some iotaType := iotaType?
    | badShape s!"the K-like recursor {ern} has no iota theorem"
  let d ← ruleKDecl eqi rv.levelParams (rv.numParams + rv.numMotives + rv.numMinors)
    ruleKN iotaType
  addChecked d
  return (out.push d, #[(ern, ruleKN)], some ruleKN)

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
telescope walk as another large inline branch. -/
def planDirectTightRoute (bare nonrecursiveOneConstructor : Bool) (np ni : Nat)
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
        badShape s!"{constructorName}'s tight field tower inhabits Sort \
          {towerLevel}, not the carrier's Sort {w}"
      return true

/-- Install tight-pair support and emit the complete exact-sort model branch.
The caller only merges the returned declarations, splice witnesses, and
projection overrides into its route state. -/
def emitDirectTightModel (eqi : EqInfo) (tname : Name) (lparams : List Name) (np : Nat)
    (memberTy constructorType modelConstructorType declaredMemberTy : Expr)
    (selfN constructorN recursorN : Name) (recursorLevelParams : List Name)
    (recursorProofType recursorPublicType : Expr) (v : Level)
    (reserved : Std.HashSet Name) :
    GenM (Array Declaration × Array Name × Array (Name × Nat × Expr × Expr)) := do
  let support ← ensurePSigmaPrime reserved
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
    (recursorProofType recursorPublicType : Expr) (w v : Level)
    (reserved : Std.HashSet Name) :
    GenM (Array Declaration × Array Name × Array (Name × Nat × Expr × Expr)) := do
  match route with
  | .field fieldRoute =>
    let support ← if fieldRoute matches .propLift then ensureExactSortLift reserved else pure #[]
    let (declarations, override) ← directFieldModel fieldRoute eqi tname lparams np
      memberTy constructorType modelConstructorType declaredMemberTy selfN constructorN
      recursorN recursorLevelParams recursorProofType recursorPublicType w v
    let spliced := support.flatMap fun declaration => declaration.getNames.toArray
    return (support ++ declarations, spliced, #[override])
  | .tight =>
    emitDirectTightModel eqi tname lparams np memberTy constructorType modelConstructorType
      declaredMemberTy selfN constructorN recursorN recursorLevelParams
      recursorProofType recursorPublicType v reserved

/-- Walk arm F's constructor telescope while recovering dependent data fields
from the caller's index telescope.  Before each moving pivot, a packed equality
of the complete earlier index prefix transports the caller's pivot back to the
constructor field type.  Proof fields are then bound at the already recovered
constructor prefix. -/
partial def armFZipPrefix (eqi : EqInfo) (memberTy ctorTy : Expr) (ni : Nat)
    (isData : Array Bool) (idxPos : Array Nat) (transports : Array (Nat × Nat))
    (ps is : Array Expr) (ctorIdx : Expr → GenM (Array Expr))
    (bind : Nat → Name → Expr → (Expr → GenM Expr) → GenM Expr)
    (k : Array Expr → Array Expr → Array Expr → GenM Expr) : GenM Expr := do
  let indexPackAt := fun (sel : Array Nat) => do
    forallBoundedTelescope (← instForall memberTy ps) (some ni) fun opened _ => do
      let (pk, ℓ) ← packTyAt opened sel 0
      pure (pk.replaceFVars opened is, ℓ)
  let indexTypeAt := fun (full : Array Expr) (position : Nat) => do
    forallBoundedTelescope (← instForall memberTy ps) (some ni) fun opened _ => do
      pure ((← ityp opened[position]!).replaceFVars opened full)
  let tele ← instForall ctorTy ps
  let nf := numForalls tele
  forallBoundedTelescope tele (some nf) fun raw res => do
    let rawIdx ← ctorIdx res
    let rec go (i slot : Nat) (fields bound : Array Expr) : GenM Expr := do
      if i == nf then
        let resolved := rawIdx.map (·.replaceFVars raw fields)
        return ← k fields bound resolved
      if isData[i]! then
        let position := idxPos[i]!
        if transports.contains (i, position) then
          let sel := Array.range position
          if sel.isEmpty then
            badShape s!"a transported pivot at index {position} has no prefix"
          let (pk, ℓpk) ← indexPackAt sel
          let previous := raw.extract 0 i
          let lhsValues := sel.map fun j => rawIdx[j]!.replaceFVars previous fields
          for value in lhsValues do
            for later in raw.extract i raw.size do
              if value.containsFVar later.fvarId! then
                badShape s!"a transported pivot at index {position} has a constructor prefix depending on an unrecovered field"
          let lhs ← packChain position pk lhsValues 0
          let rhs ← packChain position pk (sel.map (is[·]!)) 0
          bind slot `prefix_eq (eqi.mk' ℓpk pk lhs rhs) fun h => do
            let hs ← symmOf eqi ℓpk pk lhs rhs h
            let base := is[position]!
            let pv ← ilevel (← indexTypeAt is position)
            let field ← transportAlong eqi pv ℓpk pk rhs lhs hs base fun y => do
              let ys ← unpackChain position pk y
              let mut full := is
              for j in [0:position] do full := full.set! j ys[j]!
              indexTypeAt full position
            go (i + 1) (slot + 1) (fields.push field) (bound.push h)
        else
          go (i + 1) slot (fields.push is[position]!) bound
      else
        let ft := (← ityp raw[i]!).replaceFVars (raw.extract 0 i) fields
        bind slot (Name.mkSimple s!"field_{i}") ft fun field =>
          go (i + 1) (slot + 1) (fields.push field) (bound.push field)
    go 0 0 #[] #[]

def armFZipMinor (eqi : EqInfo) (memberTy ctorTy : Expr) (ni : Nat)
    (isData : Array Bool) (idxPos : Array Nat) (transports : Array (Nat × Nat))
    (ps is : Array Expr) (pk : Expr) (ℓpk : Level)
    (ctorIdx : Expr → GenM (Array Expr)) (mk : Array Expr → Expr → GenM Expr)
    (k : Array Expr → Expr → GenM Expr) : GenM Expr := do
  let sel := Array.range ni
  armFZipPrefix eqi memberTy ctorTy ni isData idxPos transports ps is ctorIdx
    (fun _ name ty cont => withLocalDeclD name ty cont)
    fun fs bnd idx => do
      let lhs ← packChain ni pk (sel.map (idx[·]!)) 0
      let rhs ← packChain ni pk (sel.map (is[·]!)) 0
      withLocalDeclD `heq (eqi.mk' ℓpk pk lhs rhs) fun h => do
        mk (bnd.push h) (← k fs h)

def armFZipCtorArgs (eqi : EqInfo) (memberTy : Expr) (ni : Nat)
    (isData : Array Bool) (idxPos : Array Nat) (transports : Array (Nat × Nat))
    (ps idx fields : Array Expr) (pk : Expr) (ℓpk : Level) : GenM (Array Expr) := do
  let nf := isData.size
  let mut args : Array Expr := #[]
  for i in [0:nf] do
    if isData[i]! then
      let position := idxPos[i]!
      if transports.contains (i, position) then
        let sel := Array.range position
        let (prefixPk, ℓprefix) ←
          forallBoundedTelescope (← instForall memberTy ps) (some ni) fun opened _ => do
            let (pk, ℓ) ← packTyAt opened sel 0
            pure (pk.replaceFVars opened idx, ℓ)
        let packed ← packChain position prefixPk (sel.map (idx[·]!)) 0
        args := args.push (eqi.refl' ℓprefix prefixPk packed)
    else
      args := args.push fields[i]!
  let packed ← packChain ni pk ((Array.range ni).map (idx[·]!)) 0
  pure (args.push (eqi.refl' ℓpk pk packed))

/-- Arm F's full-index zipper recursor.  The outer equality moves the entire
dependent index telescope.  Its motive is a function over every prefix
equation and proof field, so the constructor endpoint applies the original
minor while the caller endpoint rebuilds exactly the Church witness stored in
the major premise. -/
def armFZipRec (eqi : EqInfo) (ℓpk : Level) (lift? : Option Level)
    (pk pkc pki heq motive minor : Expr) (idxs : Array Expr)
    (zipAll : Array Expr → (Array Expr → Array Expr → GenM Expr) → GenM Expr)
    (minorTy : Array Expr → Expr → GenM Expr)
    (encodedAt : Array Expr → GenM Expr) (extracted : Array Expr) : GenM Expr := do
  let fam := fun (y : Expr) (_h : Expr) => do
    let full ← unpackChain idxs.size pk y
    zipAll full fun _ args => do
      let rebuilt ← withLocalDeclD `r (.sort .zero) fun r => do
        withLocalDeclD `k (← minorTy full r) fun kk =>
          mkLambdaFVars #[r, kk] (mkAppN kk args)
      let lifted ← match lift? with
        | none => pure rebuilt
        | some ℓ => pure (puliftUp ℓ (← encodedAt full) rebuilt)
      mkForallFVars args (mkAppN motive (full.push lifted))
  let motiveE ← withLocalDeclD `y pk fun y => do
    withLocalDeclD `hy (eqi.mk' ℓpk pk pkc y) fun hy => do
      mkLambdaFVars #[y, hy] (← fam y hy)
  let endpoint ← unpackChain idxs.size pk pkc
  let base ← zipAll endpoint fun fields args =>
    mkLambdaFVars args (mkAppN minor fields)
  let fn := eqi.recAt (← ilevel (← inferType base)) ℓpk pk pkc motiveE base pki heq
  pure (mkAppN fn extracted)

/-- Extract arm F's zipper premises from the Church major and hand them to the
full-index equality recursor.  Kept out of [`InductiveModels.primIso`] so the route
dispatcher remains below the default elaboration heartbeat budget. -/
def armFZipModelRec (eqi : EqInfo) (lift? : Option Level)
    (memberTy ctorTy : Expr) (ni : Nat) (isData : Array Bool) (idxPos : Array Nat)
    (transports : Array (Nat × Nat)) (ps idxs : Array Expr) (base pk motive minor : Expr)
    (ℓpk : Level) (ctorIdx : Expr → GenM (Array Expr))
    (minorTy : Array Expr → Expr → GenM Expr)
    (encodedAt : Array Expr → GenM Expr) : GenM Expr := do
  let packSel := Array.range ni
  let project := fun (slot : Nat) => do
    armFZipPrefix eqi memberTy ctorTy ni isData idxPos transports ps idxs ctorIdx
      (fun _ name ty cont => withLocalDeclD name ty cont)
      fun _ bnd idx => do
        let lhs ← packChain ni pk (packSel.map (idx[·]!)) 0
        let rhs ← packChain ni pk (packSel.map (idxs[·]!)) 0
        withLocalDeclD `heq (eqi.mk' ℓpk pk lhs rhs) fun h => do
          mkLambdaFVars (bnd.push h) (if slot == bnd.size then h else bnd[slot]!)
  armFZipPrefix eqi memberTy ctorTy ni isData idxPos transports ps idxs ctorIdx
    (fun slot _ ty cont => do
      let value := mkAppN base #[ty, ← project slot]
      cont value)
    fun _ args idxE => do
      let pkc ← packChain ni pk (packSel.map (idxE[·]!)) 0
      let pki ← packChain ni pk (packSel.map (idxs[·]!)) 0
      let eqTy := eqi.mk' ℓpk pk pkc pki
      let heq := mkAppN base #[eqTy, ← project args.size]
      armFZipRec eqi ℓpk lift? pk pkc pki heq motive minor idxs
        (fun full kk =>
          armFZipPrefix eqi memberTy ctorTy ni isData idxPos transports ps full ctorIdx
            (fun _ name ty cont => withLocalDeclD name ty cont)
            fun fs bnd idx => do
              let lhs ← packChain ni pk (packSel.map (idx[·]!)) 0
              let rhs ← packChain ni pk (packSel.map (full[·]!)) 0
              withLocalDeclD `heq (eqi.mk' ℓpk pk lhs rhs) fun h =>
                kk fs (bnd.push h))
        minorTy encodedAt (args.push heq)

/-- The declaration facts shared by all primitive-model routes.  Keeping this
phase separate from emission gives the route dispatcher plain data rather than
closures over the declaration telescope. -/
structure PrimAnalysis where
  declaredMemberTy : Expr
  memberTy : Expr
  ni : Nat
  w : Level
  isRec : Bool
  rv : RecursorVal
  large : Bool
  v : Level
  recLs : List Level
  nonrecursiveOneConstructor : Bool
  route : PrimRoute
  erasureBare : Bool
  erasureLinear : Bool

set_option maxRecDepth 2048 in
/-- Analyse the installed declaration and its recursor before any support or
model declarations are installed. -/
def analysePrim (tname : Name) (lparams : List Name) (np : Nat) (memberTy : Expr)
    (exportCtors : Array (Name × Expr)) : GenM PrimAnalysis := do
  let us := lparams.map Level.param
  let nc := exportCtors.size
  let peel : Expr → Option (Nat × Level) := fun ty => Id.run do
    let mut cur := ty
    for _ in [0:np] do
      match cur with
      | .forallE _ _ b _ => cur := b
      | _ => return none
    let mut n := 0
    while cur matches .forallE .. do
      let .forallE _ _ b _ := cur | unreachable!
      cur := b
      n := n + 1
    match cur with
    | .sort w => return some (n, w)
    | _ => return none
  let declaredMemberTy := memberTy
  let (memberTy, ni, w) ←
    match peel memberTy with
    | some (n, w) => pure (memberTy, n, w)
    | none => do
      let exposed ← forallBoundedTelescope memberTy (some np) fun ps rest =>
        forallTelescopeReducing rest fun is res => do
          unless (← whnf res) matches .sort _ do
            badShape "the declaration does not land in a sort, even after unfolding \
              its result type"
          mkForallFVars (ps ++ is) (← whnf res)
      let some (n, w) := peel exposed
        | badShape "the declaration does not land in a sort"
      pure (exposed, n, w)
  let isRec := exportCtors.any fun (_, cty) => Id.run do
    let mut t := cty
    for _ in [0:np] do
      match t with
      | .forallE _ _ b _ => t := b
      | _ => return false
    let mut r := false
    while t matches .forallE .. do
      let .forallE _ dom b _ := t | unreachable!
      if mentionsAny #[tname] dom then r := true
      t := b
    return r

  let ern := Name.str tname "rec"
  let .recInfo rv ← constInfo ern | badShape s!"{ern} is not a recursor"
  unless rv.numMotives == 1 && rv.numMinors == nc && rv.numIndices == ni do
    badShape s!"{ern} does not have 1 motive, {nc} minors and {ni} indices"
  let large := rv.levelParams.length == lparams.length + 1
  unless (if large then rv.levelParams.tail! else rv.levelParams) == lparams do
    badShape s!"{ern} carries the level parameters {rv.levelParams}"
  let v := if large then Level.param rv.levelParams[0]! else Level.zero
  let recLs := if large then v :: us else us
  let nonrecursiveOneConstructor := nc == 1 && !isRec
  let wn := w.normalize
  let route : PrimRoute ←
    if wn.isZero then pure .prop
    else if wn.isNeverZero then pure .type
    else pure .bare

  let erasureBareWhy ← erasureBareFailure? tname np ni exportCtors
  let infinitaryWhy : Option String := Id.run do
    for (cn, cty) in exportCtors do
      let mut t := cty
      for _ in [0:np] do
        match t with
        | .forallE _ _ b _ => t := b
        | _ => pure ()
      while t matches .forallE .. do
        let .forallE _ dom b _ := t | unreachable!
        if erasureRecursive tname dom && (headNorm dom) matches .forallE .. then
          return some s!"infinitary: {cn} has a recursive occurrence under a binder"
        t := b
    return none
  let branchingWhy : Option String := Id.run do
    for (cn, cty) in exportCtors do
      let mut t := cty
      for _ in [0:np] do
        match t with
        | .forallE _ _ b _ => t := b
        | _ => pure ()
      let mut nrec := 0
      while t matches .forallE .. do
        let .forallE _ dom b _ := t | unreachable!
        if erasureRecursive tname dom then nrec := nrec + 1
        t := b
      if nrec > 1 then return some s!"branching: {cn} has {nrec} recursive fields"
    return none
  let erasureWhy : Option String :=
    (erasureBareWhy.orElse fun _ => infinitaryWhy).orElse fun _ => branchingWhy
  let erasureBare : Bool := erasureBareWhy.isNone
  let erasureLinear : Bool := erasureWhy.isNone

  match route with
  | PrimRoute.type =>
    if ni > 0 && !erasureBare then
      badShape s!"an indexed family at a never-zero sort whose index erasure is not \
        bare (arm C splices the erasure and carves the family out of it, \
        so its reach is bounded by whether that erasure \
        models, and an erasure that is not bare has either a binder type naming \
        the declaration or an occurrence that remains under a foreign type \
        former after βζ head normalization; `why` says which this is); \
        erasure linear: no; B factors through the tag: \
        {if tagFactored tname np exportCtors then "yes" else "no"}\
        ; through the label: \
        {if labelFactored tname np exportCtors then "yes" else "no"}\
        ; carrier is Type u: {if w.normalize.dec.isSome then "yes" else "no"}\
        ; why: {erasureWhy.getD "-"}"
  | PrimRoute.bare => pure ()
  | PrimRoute.prop => pure ()

  return {
    declaredMemberTy, memberTy, ni, w, isRec, rv, large, v, recLs,
    nonrecursiveOneConstructor, route, erasureBare, erasureLinear
  }

/-- Complete build-time naming for one simple implementation family.  Public
routes use [`PrimInterfaceNames.standard`]; the one-layer adapter supplies a
private bundle and later publishes the exact source-shaped names. -/
structure PrimInterfaceNames where
  model : Name
  impl : Name
  self : Name
  ctors : Array Name
  recursor : Name
  iotas : Array Name
  deriving Inhabited

def PrimInterfaceNames.standard (tname root : Name)
    (exportCtors : Array (Name × Expr)) : PrimInterfaceNames :=
  let model := Naming.modelName root
  let recursor := Name.str tname "rec"
  { model
    impl := Name.str model "_impl"
    self := model
    ctors := exportCtors.map fun (constructor, _) =>
      Naming.modelName (Naming.relocateSource tname root constructor)
    recursor := Naming.modelName (Naming.relocateSource tname root recursor)
    iotas := (Array.range exportCtors.size).map fun index =>
      Naming.iotaName (Naming.relocateSource tname root recursor) index }

/-- Private fixpoint names for the one-layer adapter.  Every name is below the
collision-safe build model, so the ordinary whole-prefix alias registration
renames it independently of raw/private source constructor spellings. -/
def PrimInterfaceNames.oneLayerImplementation (root : Name)
    (exportCtors : Array (Name × Expr)) : PrimInterfaceNames :=
  let model := Naming.modelName root
  let impl := Name.str model "_impl"
  { model, impl
    self := Name.str impl "self"
    ctors := (Array.range exportCtors.size).map fun index => Name.str impl s!"ctor_{index}"
    recursor := Name.str impl "rec"
    iotas := (Array.range exportCtors.size).map fun index => Name.str impl s!"rec_iota_{index}" }

/-- Source/kernel metadata boundary for the first one-layer production route.
Capability checks which can fail (support, exact recursor layout and carrier
level) still run before this predicate is committed to emission. -/
def phase1DirectTypeOneLayerEligible (tname : Name) (np : Nat) (memberTy : Expr)
    (exportCtors : Array (Name × Expr))
    (sourceRecursor? : Option ERec) : MetaM Bool := do
  let env ← getEnv
  let some (.inductInfo type) := env.constants.find? tname | return false
  let neverZero ← forallBoundedTelescope memberTy (some np) fun _ result => match result with
    | .sort level => pure level.normalize.isNeverZero
    | _ => pure false
  let independentRecursiveFields ← match exportCtors[0]? with
    | some (_, constructorType) =>
      forallBoundedTelescope constructorType (some np) fun parameters _ => do
        match ← (do
          let telescope ← instForall constructorType parameters
          let shape : Array PField ← classifyCtor tname (numForalls telescope) telescope
          let recursive := (Array.range shape.size).filter fun index =>
            (PField.rec? shape[index]!).isSome
          if recursive.isEmpty || recursive.size > 2 then return false
          forallBoundedTelescope telescope (some shape.size) fun fields _ => do
            for recursiveIndex in recursive do
              let .fvar recursiveId := fields[recursiveIndex]!
                | badShape "a phase-1 recursive field is not constructor-local"
              for later in [recursiveIndex + 1:fields.size] do
                if (← inferType fields[later]!).containsFVar recursiveId then
                  return false
            return true).run with
        | .error _ => pure false
        | .ok eligible => pure eligible
    | none => pure false
  return neverZero && independentRecursiveFields && sourceRecursor?.isSome && exportCtors.size == 1 && type.all == [tname] &&
    type.ctors.length == 1 && type.numIndices == 0 && type.numNested == 0 && type.isRec &&
    !type.isUnsafe

/-- Installed-capability half of the indexed fibre adapter boundary.  Exact
source eligibility is replayable through
[`InductiveModels.indexedFibreOneLayerProjectionFamily`]; this check additionally
pins the installed declaration to the bare Arm-C erasure route.

The owner must be indexed, and that is the route boundary rather than a count:
an unindexed owner is the direct-type one-layer route's
([`InductiveModels.phase1DirectTypeOneLayerEligible`], selected first) or is
already literal without an adapter
([`InductiveModels.projectionIotaUsesLiteralField`]).  How *many* indices it
carries is never asked — the certificate's `roll`/`unroll` are the identity at
the owner's whole arity. -/
def phase1IndexedFibreOneLayerEligible (tname : Name) (np : Nat)
    (memberTy : Expr) (exportCtors : Array (Name × Expr))
    (sourceType : EIndType) (sourceConstructor : ECtor)
    (sourceRecursor : ERec) : MetaM Bool := do
  let some (.inductInfo type) := (← getEnv).constants.find? tname | return false
  let erasureBare ← match ← (erasureBareFailure? tname np type.numIndices exportCtors).run with
    | .ok reason => pure reason.isNone
    | .error _ => pure false
  return indexedFibreOneLayerTypeShape np type.numIndices memberTy &&
    indexedFibreOneLayerProjectionFamily sourceType sourceConstructor
      sourceRecursor && erasureBare && exportCtors.size == 1 &&
    type.all == [tname] && type.ctors.length == 1 && type.numIndices > 0 &&
    type.numNested == 0 && type.isRec == sourceType.isRec && !type.isUnsafe

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
