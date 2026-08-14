import Lean
import InductiveModels.Naming
import InductiveModels.Plan

/-!
# The model of a nested inductive, generated

**The first of three constructions in this package**, and the one that keeps mutuality:
the model of a nested declaration is a *mutual block* with one extra member per
nested occurrence. `src/InductiveModels/Mutual.lean` is the second and removes
mutuality; `src/InductiveModels/Simple.lean` reduces a single inductive to the fixed
basis. These are not one construction at three settings. What they share
is the interface, `Decline`, `EqInfo`, the
prelude splice, [`InductiveModels.Iso`], [`InductiveModels.modelTable`] and
[`InductiveModels.addChecked`], all of which live here.

Given a nested declaration and its specialisation ([`InductiveModels.plan`]), this
emits ordinary Lean declarations —
the block under fresh names, a carrier, one `pack`/`unpack` pair per mimic with
**both round trips as theorems**, the declared type's own constructors, one
recursor per block member, one congruence per mimic, and **every one of those
recursors' ι rules, as theorems with proofs**. Declarations are trusted-installed
in a disposable construction environment; the exact serialized island is
kernel-checked once at its close boundary iff generated checking is enabled.

The construction can also be written by hand at `Tree`, which makes the target
shape explicit independently of the generator.

## What the fvar telescope buys

Earlier implementations wrote every term at an explicit de Bruijn depth, where
reading a term at the wrong depth repeatedly caused failures. None of that
arithmetic survives here: an occurrence is stored once, relative
to the block's parameter telescope, and [`InductiveModels.Gen.occAt`] instantiates it
at whatever parameter `fvar`s are in scope. There is no shift in this file, and
every minor's binder telescope is read off the recursor's **own** minor type
rather than reconstructed.

## Two things that are forced, and one that is not a workaround

* **The model may not reuse `T`.** `T` is a primitive inductive and the block
  member `B₀` is a different constant; they are not convertible. So the model
  declares `T._model.self : ∀p⃗, Sort u := B₀ p⃗` and rewrites `T ↦
  T._model.self` everywhere. Identifying the two is the *keying* step and
  belongs to the consumer.
* **`unpack`'s motive vector is forced.** A block recursor carries one motive
  per member at one motive universe, so the members `unpack` does not
  eliminate into still need a motive at that sort: the identity at the root and
  the occurrence at each mimic.
* **An occurrence is the container at its *parameters*, and so is not a type.**
  `Vec T._model.self` is one, and the container's index telescope rides outside
  it: `pack`, `unpack`, both round trips and `congrPack` take it between `p⃗`
  and their argument. Every index vector in this file, the declaration's and
  the container's alike, is read off a type in hand — [`InductiveModels.Gen.idxOf`],
  [`InductiveModels.Gen.occIdx?`], [`InductiveModels.Gen.withOccIndices`] — and none is
  rebuilt. Indexed-container fixtures make this observable by giving the
  container a nonempty index telescope.
* **`congrCtor` cannot be a single named lemma** — each step of the fold
  abstracts a different position of the same constructor — so
  [`InductiveModels.Gen.foldCongr`] builds it inline. `congrPack` per mimic *can* be a
  declaration, because the root's fold moves `pack` and one lemma covers every
  position.

## `pack` is emitted by group and not by mimic

It is tempting to assume nesting strictly decreases and therefore supplies a
topological order, but it does not. When a
container is **itself** a nested inductive, two mimics can each need the
other's `pack`, and then no order over single mimics exists at all.
[`InductiveModels.mimicGroups`] therefore emits strongly connected components in the
condensation's order, and [`InductiveModels.familyFor`] answers a group of more than
one by finding the recursion Lean already generated for it: the container's
own recursor family, over one motive and minor vector, of which each `pack` is
one component. Only `pack` and the retraction change — `unpack` never calls
another `unpack`, and the section already runs on the block's recursor, which
does every member at once.
-/

open Lean Meta

namespace InductiveModels

/-- A positively recognized reason not to emit a requested public interface.

Construction-invariant failures do not belong here; [`InductiveModels.badShape`]
raises an internal tool error for those. -/
inductive Decline where
  /-- **A prelude constant the input declares at something other than Lean's
  statement.** Absence is not this: a prelude constant the input simply does
  not have is *spliced* ([`InductiveModels.ensureEq`], [`InductiveModels.ensureFunext`]).
  This is the case a splice cannot reach, because the name is already bound —
  by the input, in the output, and in every one of the input's own terms — and
  Lean's `Environment` has no way to rebind a constant, so replacing it would
  mean replaying the whole file a second time. The message names the constant
  and what is wrong with it. -/
  | notLeans (n : Name) (why : String)
  | nameTaken (n : Name)
  /-- **The construction environment installed the declaration and then lost it.**
  Distinct from [`InductiveModels.Decline.nameTaken`], which is the input already
  holding the name, because the two want opposite responses. This one is
  Lean's `AsyncConsts.add` refusing a *normalized* duplicate — an export
  flattens many modules, so it holds both `_private.M.0.X` and a public `X`,
  we model both, and `privateToUserName` makes the two model names one. The
  name is ours, nothing in the input is using it,
  and the fix is therefore ours too: regenerate under exact collision-safe
  aliases and translate those names on the way out. The driver does exactly
  that for nested, mutual, and simple generation, and only on this constructor.
  -/
  | nameLost (n : Name)
  /-- **A basis primitive, which is exempt rather than declined.** `Eq`,
  `Nat`, `PSigma'`, and `PUnit` are what the third construction is *written
  in*; modelling one of them would either be circular or would put a second
  `Eq` in the output. Their absence from the models is what makes the
  construction well-founded, so it is not a gap and a census that counts it as
  one is misleading. It is its own constructor so that the *report* can keep it
  in its own
  row ([`InductiveModels.Report.exempt`]) and the decline count can mean what it
  says. -/
  | basisExempt
  deriving Inhabited

/-- The word that reaches a report line, **under the construction's own name**.

There are two models in this package and they share every guard below the
driver — the name reservation, the prelude splice, `constInfo`, `instForall` —
so a decline raised in shared code has to be able to say which construction was
being built. `nested` is the model of a nested declaration
([`InductiveModels.iso`]) and `mutual` is the model of a plain mutual block
([`InductiveModels.mutualIso`]); the prefix is a parameter rather than a second copy of
the enumeration, because a second copy is a second thing to keep in step. -/
def Decline.labelAs (what : String) : Decline → String
  | .notLeans n why => s!"{what} model: the input's {n} is not Lean's ({why})"
  | .nameTaken n => s!"{what} model name taken ({n})"
  | .nameLost n => s!"{what} model name lost to a normalized-name collision ({n})"
  | .basisExempt =>
    s!"{what} model: a basis primitive (the exemption that makes the construction \
well-founded)"

/-- The word that reaches a report line for a **nested** declaration's model. -/
def Decline.label : Decline → String := Decline.labelAs "nested"

/-- `Eq`, `Eq.refl` and `Eq.rec` at the arities the round trips need. The
input's own where it has them, and Lean's spliced in where it does not — see
[`InductiveModels.ensureEq`]. -/
structure EqInfo where
  eqN : Name
  reflN : Name
  recN : Name
  deriving Inhabited

/-- Read the three constants and check the recursor is Lean's shape:
`Eq.rec α a motive base b h`, two parameters and one index. The error says
*which* of them is wrong, because a reason that names where a value stopped
rather than why is the defect class this repository has paid for most. -/
def EqInfo.check (env : Environment) : Except String EqInfo := do
  let eq := `Eq
  let some (.inductInfo iv) := env.constants.find? eq | throw "it is not an inductive type"
  unless iv.numParams == 2 && iv.numIndices == 1 && iv.ctors.length == 1 do
    throw s!"it has {iv.numParams} parameters, {iv.numIndices} indices and \
      {iv.ctors.length} constructors, where Lean's has 2, 1 and 1"
  let rc := Name.str eq "rec"
  let some (.recInfo rv) := env.constants.find? rc | throw "Eq.rec is not a recursor"
  unless rv.numParams == 2 && rv.numMotives == 1 && rv.numMinors == 1 && rv.numIndices == 1 do
    throw s!"Eq.rec has {rv.numParams} parameters, {rv.numMotives} motives, {rv.numMinors} \
      minors and {rv.numIndices} indices, where Lean's has 2, 1, 1 and 1"
  let rf := Name.str eq "refl"
  unless env.constants.contains rf do throw "Eq.refl is not declared"
  return { eqN := eq, reflN := rf, recN := rc }

/-- `Eq.{u} α a b`. -/
def EqInfo.mk' (e : EqInfo) (u : Level) (α a b : Expr) : Expr :=
  mkAppN (.const e.eqN [u]) #[α, a, b]

/-- `Eq.refl.{u} α a`. -/
def EqInfo.refl' (e : EqInfo) (u : Level) (α a : Expr) : Expr :=
  mkAppN (.const e.reflN [u]) #[α, a]

/-- `Eq.rec.{v,u} α a motive base b h`. The motive sits at `Prop` wherever an
*equation* is transported and at the eliminator's own universe wherever a
*value* is; each caller passes `v` explicitly for that reason. -/
def EqInfo.recAt (e : EqInfo) (v u : Level) (α a motive base b h : Expr) : Expr :=
  mkAppN (.const e.recN [v, u]) #[α, a, motive, base, b, h]

/-! ## The prelude this construction depends on

Four constants are reached by the *proofs* this module writes and by none of the
public signatures: `Eq` (with `Eq.refl` and the `Eq.rec` the kernel mints for it),
and — only for a field at a mimic **under a binder** — `Quot`, `Quot.sound` and
`funext`. An export is not obliged to declare any of them:
`test/fixtures/inductive-models/decline_no_eq.lean` omits `Eq`, while the paired
`infinitary` and `funext_binder` fixtures exercise absent and present `funext`.

**A prelude constant the input lacks is spliced, and a spliced constant is
reported.** This is the one place `lean-inductive-models` writes a declaration that is not
*about* the nested type, so three things hold it down:

* **Only when a model is actually being spliced.** Every one of these is built
  inside [`InductiveModels.iso`], so a file with nothing to splice is untouched.
* **Exactly what Lean's prelude declares**, taken from `Init/Prelude.lean`
  (`Eq`, `init_quot`) and `Init/Core.lean` (`Quot.sound`, `funext`), and
  `test/fixtures/inductive-models/funext_binder.lean` is that development written as a
  fixture. Each goes through [`InductiveModels.addChecked`] like everything else here,
  so construction can use it; the exact emitted island is kernel-checked only
  when `--type-check-generated` is enabled.
* **Present beats spliced.** If the input declares one, the input's own is
  used and nothing is written. A splice adds; it never substitutes.

**`funext` is derived, not asserted.** It is a theorem in Lean and it is a
theorem here: `congrArg` — inlined from `Eq.rec`, as
[`InductiveModels.Gen.congrFunFor`] already is — applied to the extensional
application of a `Quot`, at `Quot.sound`. An axiom would have been worse than
useless, because a standard-axiom policy would refuse a fabricated `funext`.

**The names.** `Eq`, `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` and
`Quot.sound` are spliced under **Lean's own names**, because those names are
load-bearing beyond this file: the ι theorems are stated at `Eq`, the
kernel fixes the four quotient names, and standard-axiom recognition selects
the `Quot.sound` clause by that exact name — a namespaced copy would be a
*non-standard axiom* and declined. `funext` appears in **no** emitted
statement, only inside proofs, so it is the one that can be namespaced and is:
`T._model.funext`, following the model naming convention, which is also where
the collision risk
was (a file may declare a `funext` of its own later, and
`test/fixtures/inductive-models/nested_keying.lean` exists because a file can declare a
name the model wants).
-/

/-- **Lean's `Eq`**, as `Init/Prelude.lean` declares it:

```lean
inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a
```

Two parameters and one index — `α` and the left-hand side are parameters, which
is what [`InductiveModels.EqInfo.check`] asserts of the input's own. Written as raw
`Expr` rather than through a telescope because it is a closed term with two
binders and no context. -/
def eqDecl : Declaration :=
  let lu := Level.param `u
  -- `{α : Sort u} → α → α → Prop`
  let eqTy : Expr := .forallE `α (.sort lu)
    (.forallE `a (.bvar 0) (.forallE `b (.bvar 1) (.sort .zero) .default) .default) .implicit
  -- `{α : Sort u} → (a : α) → Eq α a a`
  let reflTy : Expr := .forallE `α (.sort lu)
    (.forallE `a (.bvar 0) (mkAppN (.const `Eq [lu]) #[.bvar 1, .bvar 0, .bvar 0]) .default)
    .implicit
  .inductDecl [`u] 2 [{ name := `Eq, type := eqTy, ctors := [{ name := `Eq.refl, type := reflTy }] }]
    false

/-- **`Quot.sound`'s statement**, as `Init/Core.lean` declares it:
`∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Eq (Quot.mk r a)
(Quot.mk r b)`. Built at a given level so that the same builder both checks the
input's own and types the one this module splices. -/
def quotSoundType (eqN : Name) (lu : Level) : MetaM Expr := do
  withLocalDecl `α .implicit (.sort lu) fun α => do
    let relTy ← mkArrow α (← mkArrow α (.sort .zero))
    withLocalDecl `r .implicit relTy fun r =>
      withLocalDecl `a .implicit α fun a => withLocalDecl `b .implicit α fun b => do
        let mk := fun (x : Expr) => mkAppN (.const `Quot.mk [lu]) #[α, r, x]
        let q := mkAppN (.const `Quot [lu]) #[α, r]
        withLocalDecl `h .default (mkAppN r #[a, b]) fun h =>
          mkForallFVars #[α, r, a, b, h] (mkAppN (.const eqN [lu]) #[q, mk a, mk b])

/-- **`funext`'s statement**, as `Init/Core.lean` declares it: `∀ {α : Sort u}
{β : α → Sort v} {f g : ∀ x, β x}, (∀ x, Eq (f x) (g x)) → Eq f g`. One builder
for both uses — the input's own is compared against it with `isDefEq`, which is
indifferent to binder names and binder info where a syntactic comparison would
not be, and the spliced one is declared at it. -/
def funextType (eqN : Name) (lu lv : Level) : MetaM Expr := do
  withLocalDecl `α .implicit (.sort lu) fun α => do
    withLocalDecl `β .implicit (← mkArrow α (.sort lv)) fun β => do
      let fty ← withLocalDeclD `x α fun x => mkForallFVars #[x] (mkApp β x)
      withLocalDecl `f .implicit fty fun f => withLocalDecl `g .implicit fty fun g => do
        let hyp ← withLocalDeclD `x α fun x =>
          mkForallFVars #[x] (mkAppN (.const eqN [lv]) #[mkApp β x, mkApp f x, mkApp g x])
        withLocalDecl `h .default hyp fun h =>
          mkForallFVars #[α, β, f, g, h]
            (mkAppN (.const eqN [.imax lu lv]) #[fty, f, g])

/-- **`funext`, derived from `Quot.sound`** — Lean's own proof, written out at
the given name and with `congrArg` inlined:

```lean
theorem funext {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}
    (h : (x : α) → Eq (f x) (g x)) : Eq f g :=
  congrArg (fun q x => Quot.lift (fun a => a x) (fun _ _ hab => hab x) q) (Quot.sound h)
```

`E := fun q x => Quot.lift …` is the extensional application of a `Quot` of the
pointwise-equality relation, and `E (Quot.mk eqv f)` is `f`: the `Quot.lift` ι
rule gives `f x` at each point and η closes the lambda. So the base case of the
`Eq.rec` — `Eq.refl f` — has the motive's type at `Quot.mk eqv f`, and the
conclusion `Eq f (E (Quot.mk eqv g))` is the declared `Eq f g`. Both steps are
definitional and the optional generated-island kernel check verifies them.

`congrArg` is **not** emitted as a declaration of its own. It is one `Eq.rec`,
built here the way [`InductiveModels.Gen.congrFunFor`] and [`InductiveModels.Gen.congrOne`]
are built, so nothing is added to the input that this module does not need to
name. -/
def funextDecl (eqi : EqInfo) (nm : Name) : MetaM Declaration := do
  let un := `u
  let vn := `v
  let lu := Level.param un
  let lv := Level.param vn
  let luv := Level.imax lu lv
  let ty ← funextType eqi.eqN lu lv
  let val ← withLocalDecl `α .implicit (.sort lu) fun α => do
    withLocalDecl `β .implicit (← mkArrow α (.sort lv)) fun β => do
      let fty ← withLocalDeclD `x α fun x => mkForallFVars #[x] (mkApp β x)
      -- `eqv a b`, the pointwise equality, as a proposition and as a relation.
      let pw := fun (a b : Expr) => withLocalDeclD `x α fun x =>
        mkForallFVars #[x] (mkAppN (.const eqi.eqN [lv]) #[mkApp β x, mkApp a x, mkApp b x])
      withLocalDecl `f .implicit fty fun f => withLocalDecl `g .implicit fty fun g => do
        withLocalDecl `h .default (← pw f g) fun h => do
          let eqv ← withLocalDeclD `a fty fun a => withLocalDeclD `b fty fun b => do
            mkLambdaFVars #[a, b] (← pw a b)
          let qt := mkAppN (.const `Quot [luv]) #[fty, eqv]
          let mkq := fun (t : Expr) => mkAppN (.const `Quot.mk [luv]) #[fty, eqv, t]
          -- `E : Quot eqv → ∀ x, β x`, the extensional application.
          let ee ← withLocalDeclD `q qt fun q => withLocalDeclD `x α fun x => do
            let lf ← withLocalDeclD `a fty fun a => mkLambdaFVars #[a] (mkApp a x)
            let lh ← withLocalDeclD `a fty fun a => withLocalDeclD `b fty fun b => do
              withLocalDeclD `hab (← pw a b) fun hab => mkLambdaFVars #[a, b, hab] (mkApp hab x)
            mkLambdaFVars #[q, x]
              (mkAppN (.const `Quot.lift [luv, lv]) #[fty, eqv, mkApp β x, lf, lh, q])
          -- `congrArg E`, inlined: `Eq.rec` at the motive `fun z _ => Eq f (E z)`.
          let mot ← withLocalDeclD `z qt fun z =>
            withLocalDeclD `hz (mkAppN (.const eqi.eqN [luv]) #[qt, mkq f, z]) fun hz =>
              mkLambdaFVars #[z, hz]
                (mkAppN (.const eqi.eqN [luv]) #[fty, f, (mkApp ee z).headBeta])
          let sound := mkAppN (.const `Quot.sound [luv]) #[fty, eqv, f, g, h]
          mkLambdaFVars #[α, β, f, g, h]
            (eqi.recAt .zero luv qt (mkq f) mot (eqi.refl' luv fty f) (mkq g) sound)
  return .thmDecl { name := nm, levelParams := [un, vn], type := ty, value := val }

/-- **The name the export gives block index `k`'s recursor**, for a block whose
own members are `all`.

Measured on Lean's own export of
`test/fixtures/inductive-models/nest_mutual_both.ndjson`,
where the mutual block `A`/`B` nesting at `List B` and `Box A` comes back with
`A.rec`, `B.rec`, `A.rec_1` and `A.rec_2`: a **real** member's recursor is in
that member's own namespace and a **mimic**'s is in the first member's,
numbered from 1. For a one-member block that is `T.rec`, `T.rec_1`, … and
nothing has moved.

The whole family is `all.size + numNested` long — Lean mints one recursor per
motive, and the motives are the real members followed by the nested
occurrences. -/
def exportRecName (all : Array Name) (k : Nat) : Name :=
  match all[k]? with
  | some n => .str n "rec"
  | none => .str all[0]! s!"rec_{k - all.size + 1}"

/-! ## Restoring: rewriting the block's names to the model's -/

/-- Rewrite every name the specialisation introduced back to what it stands
for. A head that consumes `p` arguments has them substituted into its
replacement — that is how `Tree._nested.1 α` becomes `List (Tree α)` under a
parameter — and a head that consumes none is a plain rename. -/
partial def restore (heads : Std.HashMap Name (Nat × Expr)) (e : Expr) : Expr :=
  if heads.isEmpty then e else
  match e with
  | .const n _ => match heads[n]? with
    | some (0, repl) => repl
    | _ => e
  | .app .. =>
    let h := e.getAppFn
    let args := e.getAppArgs.map (restore heads)
    match h with
    | .const n _ =>
      match heads[n]? with
      | some (take, repl) =>
        if args.size ≥ take then
          mkAppN (repl.instantiateRev (args.extract 0 take)) (args.extract take args.size)
        else mkAppN h args
      | none => mkAppN h args
    | _ => mkAppN (restore heads h) args
  | .lam n t b bi => .lam n (restore heads t) (restore heads b) bi
  | .forallE n t b bi => .forallE n (restore heads t) (restore heads b) bi
  | .letE n t v b nd => .letE n (restore heads t) (restore heads v) (restore heads b) nd
  | .proj tn i s =>
    let restoredType := match heads[tn]? with
      | some (0, .const name _) => name
      | _ => tn
    .proj restoredType i (restore heads s)
  | .mdata data body => .mdata data (restore heads body)
  | _ => e

/-- Close `body` over the already-opened `values`, taking each binder's name,
domain and binder info from the exact `telescope` rather than from the local
context.  Meta may normalize a local declaration's type when a telescope is
opened; rebuilding a public theorem type with `mkForallFVars` would then lose
literal syntax which the export correspondence deliberately preserves.

The telescope is instantiated left-to-right at the supplied locals, so a
later exact domain may mention earlier locals.  Closing right-to-left then
abstracts those locals through both the body and the exact inner domains. -/
def closeForallsExact? (telescope : Expr) (values : Array Expr) (body : Expr) : Option Expr :=
  Id.run do
    let mut current := telescope
    let mut binders : Array (Name × Expr × BinderInfo × Expr) := #[]
    for value in values do
      let .forallE name domain rest info := current | return none
      binders := binders.push (name, domain, info, value)
      current := rest.instantiate1 value
    let mut result := body
    for binder in binders.reverse do
      let (name, domain, info, value) := binder
      result := .forallE name domain (result.abstract #[value]) info
    return some result

/-- A binder opened without consulting `MetaM`, retaining its exact exported
domain for public recursor and iota statements. -/
private structure ExactRecBinder where
  name : Name
  type : Expr
  info : BinderInfo
  value : Expr

private partial def openExactRecForalls (tag : Name) (expression : Expr) :
    Array ExactRecBinder × Expr :=
  let rec loop (expression : Expr) (binders : Array ExactRecBinder) :=
    match expression with
    | .forallE name type body info =>
      let value := mkFVar (FVarId.mk (tag.mkNum binders.size))
      loop (body.instantiate1 value) (binders.push { name, type, info, value })
    | body => (binders, body)
  loop expression #[]

private def closeExactRecForalls (binders : Array ExactRecBinder) (body : Expr) : Expr :=
  binders.reverse.foldl (fun body binder =>
    .forallE binder.name binder.type (body.abstract #[binder.value]) binder.info) body

/-- Recover the exact constructor-field telescope presented by one exported
recursor minor premise. Installed recursor metadata remains the proof/layout
oracle; this syntax is used only to close a public iota statement. -/
def exactRecursorFieldTelescope? (recursor : ERec) (ruleIndex : Nat)
    (pre : Array Expr) : Option Expr := do
  let rule ← recursor.rules[ruleIndex]?
  if rule.nfields == 0 then
    return .sort .zero
  let (recBinders, _) := openExactRecForalls ((`_exact_rec).append recursor.name)
    recursor.type
  let numPre := recursor.numParams + recursor.numMotives + recursor.numMinors
  unless pre.size == numPre do none
  let sourcePre := recBinders.extract 0 numPre |>.map (·.value)
  let minors := recBinders.extract (recursor.numParams + recursor.numMotives) numPre
  minors.findSome? fun minor => do
    let minorType := minor.type.replace fun expression =>
      sourcePre.findIdx? (fun value => value == expression) |>.map fun index => pre[index]!
    let (minorBinders, motiveResult) :=
      openExactRecForalls ((`_exact_minor).append rule.ctor) minorType
    let major ← motiveResult.getAppArgs.back?
    let .const constructor _ := major.getAppFn | none
    unless constructor == rule.ctor do none
    let majorArgs := major.getAppArgs
    unless majorArgs.size >= rule.nfields do none
    let fieldValues := majorArgs.extract (majorArgs.size - rule.nfields) majorArgs.size
    let mut fields : Array ExactRecBinder := #[]
    for value in fieldValues do
      let some binder := minorBinders.find? (·.value == value) | fields := #[]; break
      fields := fields.push binder
    unless fields.size == rule.nfields do none
    return closeExactRecForalls fields (.sort .zero)

/-- Recover the exact motive application at one exported recursor minor after
substituting the generator's current prefix and constructor fields.  This is
the type of the public iota equality; rebuilding it from installed recursor
locals would preserve meaning while losing source-authored universe syntax. -/
def exactRecursorMotiveResult? (recursor : ERec) (ruleIndex : Nat)
    (pre fields : Array Expr) : Option Expr := do
  let rule ← recursor.rules[ruleIndex]?
  unless fields.size == rule.nfields do none
  let (recBinders, _) := openExactRecForalls ((`_exact_rec_result).append recursor.name)
    recursor.type
  let numPre := recursor.numParams + recursor.numMotives + recursor.numMinors
  unless pre.size == numPre do none
  let sourcePre := recBinders.extract 0 numPre |>.map (·.value)
  let minors := recBinders.extract (recursor.numParams + recursor.numMotives) numPre
  minors.findSome? fun minor => do
    let minorType := minor.type.replace fun expression =>
      sourcePre.findIdx? (fun value => value == expression) |>.map fun index => pre[index]!
    let (minorBinders, motiveResult) :=
      openExactRecForalls ((`_exact_minor_result).append rule.ctor) minorType
    let major ← motiveResult.getAppArgs.back?
    let .const constructor _ := major.getAppFn | none
    unless constructor == rule.ctor do none
    let majorArgs := major.getAppArgs
    unless majorArgs.size >= rule.nfields do none
    let fieldValues := majorArgs.extract (majorArgs.size - rule.nfields) majorArgs.size
    let mut sourceFields : Array Expr := #[]
    for value in fieldValues do
      let some binder := minorBinders.find? (·.value == value)
        | sourceFields := #[]; break
      sourceFields := sourceFields.push binder.value
    unless sourceFields.size == fields.size do none
    return motiveResult.replace fun expression =>
      sourceFields.findIdx? (· == expression) |>.map fun index => fields[index]!

/-! ## The generator -/

/-- The generator's read-only context. -/
structure Gen where
  /-- Exact declaration owner and the collision-safe owner used in this build. -/
  owner : Name
  buildOwner : Name
  /-- The private implementation namespace below the primary carrier. -/
  model : Name
  /-- Original constructors in flattened declaration order. -/
  exportCtors : Array Name
  /-- Original recursors in motive order, including nested recursors. -/
  exportRecs : Array Name
  /-- `R_k._model` for each **real** member `R_k` — the carriers. One
  unless the declaration is a mutual block. -/
  selfNames : Array Name
  /-- How many block members are the export's own; the rest are mimics. Written
  `r` throughout: member `k` is real iff `k < r`, and mimic `k − r` otherwise. -/
  numAll : Nat
  np : Nat
  /-- The block's resultant sort. -/
  u : Level
  /-- **The declaration's own level parameters, as levels.** Every generated
  constant carries exactly these, in the export's own order, so a reference to
  one is written at `g.us` and a block recursor at `v :: g.us`. Empty for a
  monomorphic declaration, which is why nothing in the fixture set noticed
  their absence. -/
  us : List Level
  /-- The block's members, root first: `T._model.0`, `T._model.1`, … -/
  members : Array Name
  /-- Each member's constructor names, in order. -/
  blockCtors : Array (Array Name)
  /-- **How many indices each block member has.** A real member's are the
  export's own and a mimic's are the container's; both are carried. Every index
  vector in this file is *read off a type in hand* using this count and never
  rebuilt, which is what keeps an index telescope from becoming another de
  Bruijn arithmetic. -/
  nidx : Array Nat
  /-- The occurrences, each **the container at its parameters** and at the
  block's parameter telescope depth, with the export's `T` already rewritten to
  the carrier. `Vec T._model.self` is one, and it is a type only once the
  container's index telescope is applied. -/
  occs : Array Expr
  eqi : EqInfo
  /-- **The `funext` this declaration's proofs use.** Asked for lazily and only
  by a declaration with a field at a mimic *under a binder*, because that is
  the one shape whose proofs need it: the block types such a field `∀ x⃗, Bₘ ι⃗`
  and something has to transport along `(fun x⃗ => pack (unpack (f x⃗))) = f`.
  `none` for every other declaration. It is the **input's own** `funext` where
  the input has one and `T._model.funext` — derived from `Quot.sound`, spliced
  into the output — where it does not; [`InductiveModels.ensureFunext`] is the choice
  between them and this field is only its answer. -/
  fx : Option Name
  /-- **Do the block's recursors carry a motive universe?** Lean mints one only
  when the block supports large elimination; `inductive S : Prop | mk : PL S →
  S` eliminates into `Prop` alone and `S.rec` carries the block's own level
  parameters and nothing in front of them. Every level list this module writes
  for a recursor goes through [`InductiveModels.Gen.recLs`] for that reason. -/
  largeElim : Bool

/-- The generator's monad: `MetaM`, with an explicit non-emission result as its
own error. Internal construction failures remain exceptions in the underlying
`MetaM` and are therefore never reported as deliberate declines. -/
abbrev GenM := ExceptT Decline MetaM

def declineWith (d : Decline) : GenM α := throwThe Decline d
/-- Abort generation after an internal construction invariant has failed.

This is deliberately *not* a [`Decline`]. A decline says that the generator
positively recognized a valid shape it has chosen not to support. Once a route
has committed to constructing declarations, malformed intermediate syntax or
missing metadata is a tool failure and must reach the CLI's exit-3 containment
boundary. Optional exact generated kernel rejection is recorded by the
Driver as `Report.generatedKernelRejected` and reaches the CLI's rejection exit;
it is not raised through this trusted construction helper. -/
def badShape (msg : String) : GenM α :=
  ExceptT.lift (show MetaM α from Lean.throwError msg)

/-- Fail closed unless exact exported syntax and installed kernel metadata
describe the same recursor slots. Literal types and rule RHSs may differ: the
former supplies public syntax while the latter supplies checked proofs. -/
def validateExactRecursorLayout (expected : ERec) (actual : RecursorVal) : GenM Unit := do
  unless expected.name == actual.name &&
      expected.levelParams == actual.levelParams && expected.all == actual.all &&
      expected.numParams == actual.numParams && expected.numIndices == actual.numIndices &&
      expected.numMotives == actual.numMotives && expected.numMinors == actual.numMinors &&
      expected.k == actual.k && expected.isUnsafe == actual.isUnsafe &&
      expected.rules.length == actual.rules.length do
    badShape s!"{expected.name}'s exact recursor layout differs from its installed metadata"
  for index in [0:expected.rules.length] do
    let exported := expected.rules[index]!
    let installed := actual.rules[index]!
    unless exported.ctor == installed.ctor && exported.nfields == installed.nfields do
      badShape s!"{expected.name}'s exact rule {index} layout differs from its installed metadata"

/-- `Meta.inferType`, at the generator's monad. -/
def ityp (e : Expr) : GenM Expr := inferType e

/-- The sort a type lives at. -/
def ilevel (e : Expr) : GenM Level := getLevel e

/-- Zeta-reduce the head of a type. Lean accepts a constructor field whose type
is a `let` — `(n : N) → (let m := n; Vec α m) → Let α` is one — and then the
member the field sits at is not the head of the expression as written. Only
`let` is unfolded and no definition is, so nothing else about the type moves. -/
partial def zetaHead : Expr → Expr
  | .letE _ _ v b _ => zetaHead (b.instantiate1 v)
  | e => e

/-- **A type's head, ζ- *and* β-reduced.** [`InductiveModels.zetaHead`] plus the redex
a container's **family** parameter leaves behind, iterated until neither moves.
Only `let` and β move and no constant is unfolded, so this answers "which
member / which occurrence / which index vector" and changes nothing about what
the type *is*. Every reader below goes through it; see the section on reading a
type's head, at [`InductiveModels.Gen.occIdx?`]. -/
partial def headNorm (e : Expr) : Expr :=
  match e with
  | .letE _ _ v b _ => headNorm (b.instantiate1 v)
  | .app .. => let e' := e.headBeta; if e' == e then e else headNorm e'
  | _ => e

/-- **A constructor field's type**, with any leading `let` gone. Every place in
this module that asks which member a field sits at reads it through here. -/
def ftyp (e : Expr) : GenM Expr := return zetaHead (← inferType e)

/-- **The input's own `funext`, if it has one and it is Lean's.** Checked
against the statement Lean's own carries by building that type at the found
declaration's own two level parameters ([`InductiveModels.funextType`]) and asking
`isDefEq`, which is indifferent to binder names and binder info where a
syntactic comparison would not be.

`none` is *not* a decline. It means the model's proofs will use a `funext` of
their own, derived and spliced — [`InductiveModels.ensureFunext`]. This is asked
**lazily**, because `funext` is in no public statement and only one proof shape
needs it. -/
def usableFunext? (eqi : EqInfo) : GenM (Option Name) := do
  let n := `funext
  let some ci := (← getEnv).constants.find? n | return none
  let [u, v] := ci.levelParams | return none
  unless ← isDefEq ci.type (← funextType eqi.eqN (.param u) (.param v)) do return none
  return some n

def constInfo (n : Name) : GenM ConstantInfo := do
  let some ci := (← getEnv).constants.find? n | badShape s!"{n} is not declared"
  return ci

/-- The container's constructors. -/
def ctorsOf (c : Name) : GenM (Array Name) := do
  let .inductInfo iv ← constInfo c | badShape s!"{c} is not an inductive"
  return iv.ctors.toArray

/-- How many fields a constructor has. -/
def numFieldsOf (c : Name) : GenM Nat := do
  let .ctorInfo cv ← constInfo c | badShape s!"{c} is not a constructor"
  return cv.numFields

/-- Peel `args.size` `∀` binders, substituting as it goes. -/
def instForall (ty : Expr) (args : Array Expr) : GenM Expr := do
  let mut cur := ty
  for a in args do
    match cur with
    | .forallE _ _ b _ => cur := b.instantiate1 a
    | _ => badShape "too few binders to instantiate"
  return cur

/-- A constructor's type at the given levels with `qs` substituted for its
leading binders, leaving the field telescope. -/
def instCtor (cn : Name) (ls : List Level) (qs : Array Expr) : GenM Expr := do
  let ci ← constInfo cn
  instForall (ci.type.instantiateLevelParams ci.levelParams ls) qs

/-- Open a type's telescope, with the binder types. -/
def withFields (ty : Expr) (k : Array Expr → Array Expr → GenM α) : GenM α := do
  forallTelescope ty fun fs _ => do k fs (← fs.mapM ftyp)

/-- A constructor's field types, with its binders instantiated left-to-right
by another constructor's corresponding fields. This keeps dependencies on an
earlier field in the caller's local context instead of returning types that
mention the temporary free variables introduced by [`withFields`]. -/
def fieldTypesAt (ty : Expr) (fields : Array Expr) : GenM (Array Expr) := do
  let mut cur := ty
  let mut tys := #[]
  for field in fields do
    match cur with
    | .forallE _ dom body _ =>
      tys := tys.push dom
      cur := body.instantiate1 field
    | _ => badShape "the constructors have different field counts"
  if cur.isForall then badShape "the constructors have different field counts"
  return tys

/-- **The dependency the congruence fold cannot survive, and only that one.**

The fold replaces one *packed* position of a constructor application at a time,
so a field whose type mentions an earlier packed field is ill-typed at every
intermediate stage. A dependency on a field that does **not** move is never
touched by the fold, and Lean supports it — `node : (n : N) → Vec N n → List
DTree → DTree` and `node : List ETree → (n : N) → Vec N n → ETree` are both
`test/fixtures/inductive-models/dependent_fields.lean`, and both are models now.

A dependency *on* a packed field is out of reach for a different reason: Lean
does not support it either. `node : (l : List GTree) → Len l N.z → GTree` fails
Lean's own nested compilation with `unknown constant 'GTree'`, because the
auxiliary block replaces `List GTree` with a fresh member and `Len l` is then
about a constant absent at that point in the block.

**The mention has to survive β**, which is why the type goes through
[`InductiveModels.headNorm`] first.
A container whose parameter is a *family* leaves its field as the redex
`(fun x => …) k`, and `k` is the field before it; when the family is constant —
`RB (RB N (fun _ => Key)) (fun _ => N)`, where the nesting is in the **key** —
the
redex mentions `k` and its reduct does not, so the fold has nothing to survive.
This used to decline that shape as a dependent field, which was a wrong reason
as well as a wrong answer: Lean compiles it. -/
def noDepOnPacked (packed : Array Expr) (fs tys : Array Expr) : GenM Unit := do
  for i in [0:tys.size] do
    let ti := headNorm tys[i]!
    for j in [0:i] do
      if packed.contains fs[j]! && ti.containsFVar fs[j]!.fvarId! then
        badShape "a field type depends on an earlier packed field"

/-- Read `n` minor premise types off a recursor application. -/
def withMinorTypes (recApp : Expr) (n : Nat) (k : Array Expr → GenM α) : GenM α := do
  let ty ← ityp recApp
  forallBoundedTelescope ty (some n) fun mvars _ => do
    k (← mvars.mapM ityp)

namespace Gen

def packName (g : Gen) (i : Nat) : Name := .str g.model s!"pack_{i}"
def unpackName (g : Gen) (i : Nat) : Name := .str g.model s!"unpack_{i}"
def retractName (g : Gen) (i : Nat) : Name := .str g.model s!"unpackPack_{i}"
def sectionName (g : Gen) (i : Nat) : Name := .str g.model s!"packUnpack_{i}"
def ctorName (g : Gen) (j : Nat) : Name :=
  Naming.modelName (Naming.relocateSource g.owner g.buildOwner g.exportCtors[j]!)
def recName (g : Gen) (k : Nat) : Name :=
  Naming.modelName (Naming.relocateSource g.owner g.buildOwner g.exportRecs[k]!)
def congrPackName (g : Gen) (i : Nat) : Name := .str g.model s!"congrPack_{i}"
def iotaName (g : Gen) (k j : Nat) : Name :=
  Naming.iotaName (Naming.relocateSource g.owner g.buildOwner g.exportRecs[k]!) j
def ruleKName (g : Gen) (k : Nat) : Name :=
  Naming.ruleKName (Naming.relocateSource g.owner g.buildOwner g.exportRecs[k]!)

/-- Is block member `k` one of the export's own, rather than a mimic? -/
def isReal (g : Gen) (k : Nat) : Bool := k < g.numAll

/-- The mimic index of a block member that is not real. -/
def mimicOf (g : Gen) (k : Nat) : Nat := k - g.numAll

/-- Occurrence `i` at the parameter `fvar`s in scope — **the container at its
parameters**, so `Vec T._model.self` and not a type. -/
def occAt (g : Gen) (i : Nat) (ps : Array Expr) : Expr := g.occs[i]!.instantiateRev ps

/-- **Mimic `i`'s index count**, which is the container's. In particular it is
not zero for `Vec α : N → Type`. -/
def midx (g : Gen) (i : Nat) : Nat := g.nidx[i + g.numAll]!

/-- Occurrence `i` **at an index vector** — the type `pack_i` takes and
`unpack_i` returns. -/
def occAtIdx (g : Gen) (i : Nat) (ps idxs : Array Expr) : Expr :=
  mkAppN (g.occAt i ps) idxs

/-! ### reading a type's head and its argument vector, through β

**A container's parameter may be a *family*, and then the block's constructor
types hold β-redexes.** `RBNode α β`'s `β : α → Type`, so specialising it at
`fun _ => Json` turns the field `β k` into `(fun _ => B₀) k` — and that
expression is what the block *stores*, because the specialisation is `Expr`
surgery and `Expr.instantiate1` does not reduce. `getAppFn` then answers with a
lambda and `getAppArgs` with the wrong vector: the head test says the field is
at no member, and the index vector reads `k` where the type says `N.z`.

`Lean.Json` and `Lean.PrefixTreeNode` are exactly that shape. The repair is at
the three readers rather than at
their callers — [`InductiveModels.Gen.occIdx?`], [`InductiveModels.Gen.idxOf`],
[`InductiveModels.Gen.memberOf`] and the family's [`InductiveModels.Gen.Family.memberAt?`]
— because *every* question this module asks of a field's type goes through one
of them, and a repair at one caller would leave the rest reading a lambda.
[`InductiveModels.headNorm`] and not `whnf`: β and `let` are the whole of the
difference, and unfolding definitions here would make a carrier look like a
block member. -/

/-- Is `t` occurrence `i` at some index vector, and if so which? The container
is matched at its **parameters**, so `Vec self N.z` and `Vec self (N.s N.z)`
are the same occurrence at two indices and one mimic serves both. -/
def occIdx? (g : Gen) (i : Nat) (ps : Array Expr) (t : Expr) : Option (Array Expr) :=
  let t := headNorm t
  let m := g.midx i
  let as := t.getAppArgs
  if as.size < m then none
  else if mkAppN t.getAppFn (as.extract 0 (as.size - m)) == g.occAt i ps then
    some (as.extract (as.size - m) as.size)
  else none

/-- Which occurrence a type is, and at which indices. -/
def occOf? (g : Gen) (ps : Array Expr) (t : Expr) : Option (Nat × Array Expr) :=
  (Array.range g.occs.size).findSome? fun i => (g.occIdx? i ps t).map ((i, ·))

/-- **The container's own index telescope for mimic `i`**, read off the
occurrence's type — `Vec T._model.self : N → Type` — rather than rebuilt. -/
def withOccIndices (g : Gen) (i : Nat) (ps : Array Expr)
    (f : Array Expr → GenM α) : GenM α := do
  forallBoundedTelescope (← ityp (g.occAt i ps)) (some (g.midx i)) fun idxs _ => f idxs

/-- `Bₖ p⃗`. **Not a type when member `k` is indexed** — an index vector still
has to be applied, and [`InductiveModels.Gen.idxOf`] is where every one of them comes
from. -/
def memAt (g : Gen) (k : Nat) (ps : Array Expr) : Expr := mkAppN (.const g.members[k]! g.us) ps

/-- The index arguments of a value's type at member `k`. `t` is `Bₖ p⃗ idx⃗` in
the block and `Rₖ._model.self p⃗ idx⃗` at the export's side, and either way the
indices are the last `nidx k` arguments. -/
def idxOf (g : Gen) (k : Nat) (t : Expr) : Array Expr :=
  let as := (headNorm t).getAppArgs
  as.extract (as.size - g.nidx[k]!) as.size

/-- The member's index telescope, opened at the parameters in scope. -/
def withIndices (g : Gen) (k : Nat) (ps : Array Expr)
    (f : Array Expr → GenM α) : GenM α := do
  let ty ← instForall (← constInfo g.members[k]!).type ps
  forallBoundedTelescope ty (some g.nidx[k]!) fun idxs _ => f idxs

/-- `f p⃗ ι⃗ x` — every generated map takes the parameters first and then the
**container's** index telescope, which is empty unless the container has
indices. Every caller reads `ι⃗` off a type in hand. -/
def call (g : Gen) (f : Name) (ps idxs : Array Expr) (x : Expr) : Expr :=
  mkAppN (.const f g.us) (ps ++ idxs ++ #[x])

/-- `Bₖ.c p⃗ args`. -/
def blockCtorAt (g : Gen) (k : Nat) (c : Name) (ps args : Array Expr) : Expr :=
  mkAppN (.const (.str g.members[k]! (lastStr c)) g.us) (ps ++ args)

/-- Which block member a field's type is at, if any. -/
def memberOf (g : Gen) (t : Expr) : Option Nat :=
  match (headNorm t).getAppFn with
  | .const n _ => g.members.findIdx? (· == n)
  | _ => none

/-- **Which member a field's induction hypothesis is at**, which is not the
same question as [`InductiveModels.Gen.memberOf`]. Lean gives a field of type
`∀ x⃗, Bₘ …` an induction hypothesis `∀ x⃗, motiveₘ (f x⃗)` — infinitary
constructors are supported and `FTree.branch : (N → FTree) → FTree` is one — so
a minor's hypothesis vector has an entry for it and a treatment that counted
only the fields *at* a member loses its place in that vector.

Read the way Lean reads it, after `whnf` and through the telescope: `(fun x : B₀
=> N) x`, which is `Ctr.mk`'s second field at `Ctr KTree (fun _ => N)`, mentions
a member but is not recursive and gets no hypothesis.

A field that is a bare redex — `(fun _ => B₀) k`, which is what `Lean.Json`
is — needs no telescope at all, and `memberOf` sees it: that reader is
β-transparent, and the kernel's own `is_rec_argument` reduces too, so it gives
such a field a hypothesis and this counts one. -/
def ihMemberOf (g : Gen) (t : Expr) : GenM (Option Nat) := do
  if let some m := g.memberOf t then return some m
  forallTelescope (← whnf t) fun bs res => do
    if bs.isEmpty then return none
    return g.memberOf (← whnf res)

/-- Each field's induction-hypothesis member, and its **position in the
minor's hypothesis vector** — which counts every field that has one, in field
order, and is what `Bₖ.rec` binds. -/
def ihVector (g : Gen) (ftys : Array Expr) : GenM (Array (Option Nat) × Array (Option Nat)) := do
  let ihm ← ftys.mapM g.ihMemberOf
  let mut pos : Array (Option Nat) := #[]
  let mut k := 0
  for m in ihm do
    if m.isSome then pos := pos.push (some k); k := k + 1 else pos := pos.push none
  return (ihm, pos)

/-! ### fields at a mimic under a binder, and the funext they cost

Lean supports `HTree.node : (N → List HTree) → HTree`, and the block types the
field `∀ x⃗, Bₘ ι⃗`. Everything below is the machinery for a *packed position
under a binder*: which fields are one, how to rebuild a value under the
telescope, and how to close a pointwise equation with `funext`. At `nb = 0`
these paths write no lambda and ask for no `funext`. -/

/-- **`funext` for a whole binder telescope**, innermost first: from `p : Eq a
b` in the scope of `x⃗`, `Eq (fun x⃗ => a) (fun x⃗ => b)`. Each step η-reduces
its two sides, so closing over `f x⃗` gives `f` back rather than its
η-expansion and the fold downstream compares equal to the field. -/
def funextFor (g : Gen) (xs : Array Expr) (a b p : Expr) : GenM Expr := do
  -- `g.fx` is set by [`InductiveModels.ensureFunext`] for exactly the declarations
  -- that have a packed position under a binder, which is exactly the
  -- declarations that reach here; `none` is an internal inconsistency and not
  -- an input's shortcoming.
  let some fx := g.fx | badShape "a packed position under a binder without a funext"
  let mut a := a; let mut b := b; let mut p := p
  for i in [0:xs.size] do
    let x := xs[xs.size - 1 - i]!
    let α ← ityp x
    let lu ← ilevel α
    let lv ← ilevel (← ityp a)
    let β ← mkLambdaFVars #[x] (← ityp a)
    let la := (← mkLambdaFVars #[x] a).eta
    let lb := (← mkLambdaFVars #[x] b).eta
    p := mkAppN (.const fx [lu, lv]) #[α, β, la, lb, ← mkLambdaFVars #[x] p]
    a := la; b := lb
  return p

/-- Is `t` a field the block holds at a **mimic**, possibly under a binder
telescope? Returns the member and the telescope's length; `0` is the ordinary
case. `∀ x⃗, Bₘ ι⃗` on the block's side. -/
def mimicUnder? (g : Gen) (t : Expr) : GenM (Option (Nat × Nat)) := do
  if let some m := g.memberOf t then
    return if g.isReal m then none else some (m, 0)
  forallTelescope (← whnf t) fun bs res => do
    let some m := g.memberOf (← whnf res) | return none
    return if g.isReal m then none else some (m, bs.size)


/-- Is `t` occurrence `i` at some index vector, possibly under a binder
telescope? Returns the telescope's length. -/
def occUnder? (g : Gen) (i : Nat) (ps : Array Expr) (t : Expr) : GenM (Option Nat) := do
  if (g.occIdx? i ps t).isSome then return some 0
  forallTelescope (← whnf t) fun bs res => do
    if (g.occIdx? i ps (← whnf res)).isSome then return some bs.size else return none

/-- Which occurrence `t` is at, possibly under a binder telescope, and how deep. -/
def occOfUnder? (g : Gen) (ps : Array Expr) (t : Expr) : GenM (Option (Nat × Nat)) := do
  for i in [0:g.occs.size] do
    if let some nb ← g.occUnder? i ps t then return some (i, nb)
  return none

/-- **Rebuild a field under its binder telescope**: `fun x⃗ => k resTy (f x⃗)`.
`nb = 0` applies `k` to the field itself and writes no lambda. -/
def underBinders (nb : Nat) (ty f : Expr)
    (k : Array Expr → Expr → Expr → GenM Expr) : GenM Expr := do
  if nb == 0 then k #[] ty f
  else forallBoundedTelescope ty (some nb) fun xs res => do
    mkLambdaFVars xs (← k xs res (f.beta xs))

/-- **A moved position and its proof, under the binder telescope.** `k` returns
the moved value and a *pointwise* proof of `Eq (that value) (f x⃗)`; this
abstracts both over `x⃗` and closes the equation with [`InductiveModels.Gen.funextFor`],
which is the only place in this module an equality Lean did not write is used —
and it is read from the export, never fabricated. -/
def underEq (g : Gen) (nb : Nat) (ty f : Expr)
    (k : Array Expr → Expr → Expr → GenM (Expr × Expr)) : GenM (Expr × Expr) := do
  if nb == 0 then k #[] ty f
  else forallBoundedTelescope ty (some nb) fun xs res => do
    let fx := f.beta xs
    let (l, p) ← k xs res fx
    return ((← mkLambdaFVars xs l).eta, ← g.funextFor xs l fx p)

/-- `(member, constructor)` for every constructor of the block, in the order
`Bₖ.rec` binds its minors. -/
def ctorPairs (g : Gen) : Array (Nat × Name) :=
  (Array.range g.members.size).flatMap fun k => g.blockCtors[k]!.map (k, ·)

/-- The total number of the block's constructors — the recursors' minor count. -/
def numMinors (g : Gen) : Nat := g.ctorPairs.size

/-- **A recursor's level list**: the motive universe in front of `ℓ⃗`, or just
`ℓ⃗` when the block eliminates only into `Prop` and Lean minted no motive
universe for it. -/
def recLs (g : Gen) (v : Level) : List Level := if g.largeElim then v :: g.us else g.us

/-- **A *container's* recursor at a motive universe**, or without one. Whether
the container carries a motive universe is its own affair and not the block's —
a `Prop`-valued container without large elimination has none — so it is read
off the recursor rather than assumed. -/
def contRecAt (n : Name) (v : Level) (cls : List Level) : GenM Expr := do
  let .recInfo rv ← constInfo n | badShape s!"{n} is not a recursor"
  if rv.levelParams.length == cls.length + 1 then return .const n (v :: cls)
  else if rv.levelParams.length == cls.length then return .const n cls
  else badShape s!"{n} carries {rv.levelParams.length} level parameters, not {cls.length}"

/-- The same list, for `instantiateLevelParams`. -/
def contRecLs (n : Name) (v : Level) (cls : List Level) : GenM (List Level) := do
  let .recInfo rv ← constInfo n | badShape s!"{n} is not a recursor"
  if rv.levelParams.length == cls.length + 1 then return v :: cls else return cls

/-- `Bₖ.rec`, the block's own. -/
def blockRec (g : Gen) (k : Nat) : Name := .str g.members[k]! "rec"

/-- `Bₖ.rec` at motive universe `v`. Lean puts the motive universe **first**
and the block's own level parameters after it, and it mints the same fresh
name for `T._model.0.rec` as for `T.rec` because both are generated from the
same level parameter list. -/
def blockRecAt (g : Gen) (k : Nat) (v : Level) : Expr :=
  .const (g.blockRec k) (g.recLs v)

/-- The container of occurrence `i` at `ps`: its name, level list and **its
parameters**. An indexed container's index telescope is not here — it rides
outside the occurrence and every use reads it off a type in hand. -/
def container (g : Gen) (i : Nat) (ps : Array Expr) :
    GenM (Name × List Level × Array Expr) := do
  let occ := g.occAt i ps
  let .const c cls := occ.getAppFn | badShape "the occurrence is not headed by a constant"
  let .inductInfo _ ← constInfo c | badShape s!"{c} is not an inductive"
  return (c, cls, occ.getAppArgs)

/-- The real container constructor a mimic's constructor stands for, by its
last name component — the correspondence [`InductiveModels.plan`] built it from. -/
def realCtor (g : Gen) (i : Nat) (ps : Array Expr) (cn : Name) : GenM Name := do
  let (c, _, _) ← g.container i ps
  let last := lastStr cn
  let some r := (← ctorsOf c).find? (fun r => lastStr r == last)
    | badShape s!"no real constructor for {cn}"
  return r

/-- **One congruence per moving argument.** From `pⱼ : Eq lhsⱼ rhsⱼ` at the
positions that move, build `Eq (f lhs⃗) (f rhs⃗)` by transporting one position at
a time: at step `j` the accumulator proves `Eq (f lhs⃗) (f mix(j))`, where
`mix(j)` is `rhs` below `j` and `lhs` at and above it.

This is where a constructor with **two or more** moving positions is paid for,
and it is why the fold exists rather than a single transport. It is also why
`congrCtor` is not a declaration: each step abstracts a *different* position of
the same constructor, so a named lemma would be one per position. -/
def foldCongr (g : Gen) (goalTy : Expr) (fieldTys lhs rhs : Array Expr)
    (proofs : Array (Option Expr)) (rebuild : Array Expr → Expr) : GenM Expr := do
  let n := lhs.size
  let start := rebuild lhs
  let ug ← ilevel goalTy
  let mut acc := g.eqi.refl' ug goalTy start
  for j in [0:n] do
    let some p := proofs[j]! | continue
    if lhs[j]! == rhs[j]! then continue
    let α := fieldTys[j]!
    -- **The moved position's own sort, not the block's.** A packed field under
    -- a binder lands at `imax` of the binder's sort and the block's, and the
    -- two coincide only when there is no binder.
    let uα ← ilevel α
    let mot ← withLocalDeclD `x α fun x => do
      withLocalDeclD `hx (g.eqi.mk' uα α lhs[j]! x) fun hx => do
        let mix := (Array.range n).map fun k =>
          if k < j then rhs[k]! else if k == j then x else lhs[k]!
        mkLambdaFVars #[x, hx] (g.eqi.mk' ug goalTy start (rebuild mix))
    acc := g.eqi.recAt .zero uα α lhs[j]! mot acc rhs[j]! p
  return acc

/-- The value-transport counterpart of [`InductiveModels.Gen.foldCongr`]: from
`v : M (f lhs⃗)` and `pⱼ : Eq lhsⱼ rhsⱼ`, produce `M (f rhs⃗)`, one position at a
time. The motive lands at the eliminator's universe, which is the one place in
this file an `Eq.rec` is not `Prop`-valued. -/
def foldValue (g : Gen) (v : Level) (m0 : Expr) (fieldTys lhs rhs : Array Expr)
    (proofs : Array (Option Expr)) (rebuild : Array Expr → Expr) (base : Expr) :
    GenM Expr := do
  let n := lhs.size
  let mut acc := base
  for j in [0:n] do
    let some p := proofs[j]! | continue
    if lhs[j]! == rhs[j]! then continue
    let α := fieldTys[j]!
    let uα ← ilevel α
    let mot ← withLocalDeclD `x α fun x => do
      withLocalDeclD `hx (g.eqi.mk' uα α lhs[j]! x) fun hx => do
        let mix := (Array.range n).map fun k =>
          if k < j then rhs[k]! else if k == j then x else lhs[k]!
        mkLambdaFVars #[x, hx] (mkApp m0 (rebuild mix))
    acc := g.eqi.recAt v uα α lhs[j]! mot acc rhs[j]! p
  return acc

/-- **`Eq (f x⃗) (g x⃗)` from `h : Eq f g`** — `congrFun`, iterated, and built
from `Eq.rec` alone rather than read from the export.

It is what makes a packed position *under a binder* work at all. The fold
carries one equation for the whole function, closed with `funext`; the
induction hypothesis on the other side is **pointwise**, `fun x⃗ => rec_m (f
x⃗)`, and each of its points transports along `Eq (y x⃗) (f x⃗)`. Instantiated,
that is the same proposition as the retraction at `f x⃗`, so **proof
irrelevance** identifies the two and the rule's two sides meet. Abstracting the
function and transporting it whole does not: `Eq.rec` on the funext'd equation
is not the pointwise transport `T._model.rec_m` δ-unfolds to. -/
def congrFunFor (g : Gen) (α y target h : Expr) (xs : Array Expr) : GenM Expr := do
  let uα ← ilevel α
  let yx := y.beta xs
  let β ← ityp yx
  let uβ ← ilevel β
  let mot ← withLocalDeclD `z α fun z =>
    withLocalDeclD `hz (g.eqi.mk' uα α y z) fun hz => do
      mkLambdaFVars #[z, hz] (g.eqi.mk' uβ β yx (z.beta xs))
  return g.eqi.recAt .zero uα α y mot (g.eqi.refl' uβ β yx) target h

/-- **`Eq (m l₀) (m l)` from `h : Eq l₀ l`, inline.** `congrPack_i` is this at a
position that needs no binder, as a declaration; a position *under* a binder
abstracts a whole function and no one lemma covers it, so it is built here the
way [`InductiveModels.Gen.foldCongr`] builds its steps. `β` is the type of `m l₀`. -/
def congrOne (g : Gen) (α β : Expr) (m : Expr → GenM Expr) (l0 l h : Expr) :
    GenM Expr := do
  let uα ← ilevel α
  let uβ ← ilevel β
  let m0 ← m l0
  let mot ← withLocalDeclD `x α fun x =>
    withLocalDeclD `hx (g.eqi.mk' uα α l0 x) fun hx => do
      mkLambdaFVars #[x, hx] (g.eqi.mk' uβ β m0 (← m x))
  return g.eqi.recAt .zero uα α l0 mot (g.eqi.refl' uβ β m0) l h

/-! ### pack -/

/-- `fun f⃗ ih⃗ => Bᵢ.c p⃗ g⃗`, where a field recursive in the container is its own
induction hypothesis, a field at another mimic is packed, and anything else —
a plain field, or one at the root, which the block types at `B₀ p⃗` and
`T._model.self p⃗` unfolds to — goes through untouched. -/
def packMinor (g : Gen) (i member : Nat) (ps : Array Expr) (cn : Name) (mty : Expr) :
    GenM Expr := do
  forallTelescope mty fun bs _ => do
    let n ← numFieldsOf cn
    let fields := bs.extract 0 n
    let ihs := bs.extract n bs.size
    let ftys ← fields.mapM ftyp
    -- The container's own recursive positions: occurrence `i` at **any** index
    -- vector, because `Vec.vcons`' recursive field sits at `n` and its result
    -- at `N.s n` — and **under any binder telescope**, because `Rose.node :
    -- (N → Rose α) → Rose α` is recursive under one and Lean gives it a
    -- hypothesis all the same.
    let mut recs : Array Nat := #[]
    for x in [0:n] do
      if (← g.occUnder? i ps ftys[x]!).isSome then recs := recs.push x
    -- Every recursive position, infinitary or not, has exactly one hypothesis,
    -- so the two vectors line up. An infinitary one's hypothesis is already
    -- `∀ x⃗, B_{r+i} ι⃗`, which is what the block's constructor wants: no
    -- lambda is written here and no funext is needed.
    unless recs.size == ihs.size do
      badShape s!"{cn}'s recursive positions and hypotheses do not line up"
    let mut args : Array Expr := #[]
    for x in [0:n] do
      if let some t := recs.findIdx? (· == x) then
        args := args.push ihs[t]!
      else if let some (o, nb) ← g.occOfUnder? ps ftys[x]! then
        args := args.push (← underBinders nb ftys[x]! fields[x]! fun _ res v =>
          return g.call (g.packName o) ps ((g.occIdx? o ps res).getD #[]) v)
      else
        args := args.push fields[x]!
    mkLambdaFVars bs (g.blockCtorAt member cn ps args)

/-! ### the container family a cycle of mimics is one recursion over -/

/-- **The recursors Lean minted for the block `c` belongs to**, in block-index
order: `c`'s own members first, then one per nested occurrence of that block.
An ordinary container gives `#[C.rec]`; a container that is **itself** a nested
inductive gives `#[Tree.rec, Tree.rec_1]`, and those two are the simultaneous
recursion a cycle of mimics needs. -/
def familyRecs (c : Name) : GenM (Array Name) := do
  let .inductInfo iv ← constInfo c | badShape s!"{c} is not an inductive"
  let all := iv.all.toArray
  if all.isEmpty then badShape s!"{c} has no block"
  return (Array.range (all.size + iv.numNested)).map (exportRecName all ·)

/-- **One container block, seen as the recursion a group of mimics is.** -/
structure Family where
  /-- The recursor family, in block-index order. -/
  recs : Array Name
  /-- The anchoring occurrence's level list and parameters. -/
  cls : List Level
  qs : Array Expr
  /-- Family member `j`'s **occurrence** at `qs` — the container at its
  parameters, so a type only once its index telescope is applied. -/
  doms : Array Expr
  /-- Family member `j`'s index count. -/
  fidx : Array Nat
  /-- Family member `j` is the group's mimic `mimic[j]`. -/
  mimic : Array Nat
  /-- `(family member, its constructor)` in the order the family's recursors
  bind their minors: every member's rules, member by member. -/
  rules : Array (Nat × Name)

/-- Which family member mimic `i` is. -/
def Family.indexOf (f : Family) (i : Nat) : Nat := (f.mimic.findIdx? (· == i)).getD 0

/-- Family member `j`'s constructors are the real container's at *its* own
parameters, which the member's type carries: `List (Tree α)`'s `cons` is
`List.cons` at `#[Tree α]`. -/
def Family.ctorPrefix (f : Family) (j : Nat) : List Level × Array Expr :=
  match f.doms[j]!.getAppFn with
  | .const _ cls => (cls, f.doms[j]!.getAppArgs)
  | _ => ([], f.doms[j]!.getAppArgs)

/-- Which family member a type is at, and at which indices. Through β, for
[`InductiveModels.Gen.occIdx?`]'s reason. -/
def Family.memberAt? (f : Family) (t : Expr) : Option (Nat × Array Expr) :=
  let t := headNorm t
  (Array.range f.doms.size).findSome? fun j =>
    let m := f.fidx[j]!
    let as := t.getAppArgs
    if as.size < m then none
    else if mkAppN t.getAppFn (as.extract 0 (as.size - m)) == f.doms[j]! then
      some (j, as.extract (as.size - m) as.size)
    else none

/-- Which family member `t` is at, and how deep under a binder — the
[`InductiveModels.Gen.mimicUnder?`] of a cyclic group's own recursion. `Tr.node :
(N → List (Tr α)) → Tr α` is one, and a cycle through it is a binder inside a
simultaneous recursion. -/
def Family.memberUnder? (f : Family) (t : Expr) : GenM (Option (Nat × Nat)) := do
  if let some (j, _) := f.memberAt? t then return some (j, 0)
  forallTelescope (← whnf t) fun bs res => do
    if bs.isEmpty then return none
    let some (j, _) := f.memberAt? (← whnf res) | return none
    return some (j, bs.size)

/-- Family member `j`'s index telescope, read off its occurrence's type. -/
def Family.withIndices (f : Family) (j : Nat) (k : Array Expr → GenM α) : GenM α := do
  forallBoundedTelescope (← ityp f.doms[j]!) (some f.fidx[j]!) fun idxs _ => k idxs

/-- **The family a group of mutually recursive mimics is one recursion over**.

`nest_through_nested`'s `T` nests into `Tree T`, `Tree`'s own `node` field is
`List (Tree T)` and *that* copy's `cons` head is `Tree T` again, so mimics 0
and 1 depend on each other and no emission order exists for them one at a
time. They are not two recursions: they are the two components of **one**, and
Lean already generated it — `Tree.rec` and `Tree.rec_1`, over a single motive
and minor vector. This finds that vector by trying each mimic in the group as
the anchor and asking whether its container's family covers the group exactly.

**Exactly** is required in both directions. A family member the group does not
contain would need a motive this cannot invent, and a group member outside the
family would have no component to be. -/
def familyFor (g : Gen) (grp : Array Nat) (ps : Array Expr) : GenM Family := do
  for anchor in grp do
    let (c, cls, qs) ← g.container anchor ps
    let recs ← familyRecs c
    if recs.size != grp.size then continue
    let .recInfo rv ← constInfo recs[0]! | continue
    let ty ← instForall
      (rv.type.instantiateLevelParams rv.levelParams (← contRecLs recs[0]! g.u cls)) qs
    -- **A motive is `∀ ι⃗ x, Sort v`, and the occurrence is `x`'s type with the
    -- index telescope stripped.** For an unindexed family that is the motive's
    -- single binder domain and nothing has moved; for an indexed one — `XT`'s
    -- cycle runs over `ITr.rec`/`ITr.rec_1`, both indexed — the indices sit in
    -- front of it.
    let doms? ← forallBoundedTelescope ty (some rv.numMotives) fun ms _ =>
      ms.mapM fun m => do
        forallTelescope (← ityp m) fun bs _ => do
          let some last := bs.back? | return none
          let t ← ityp last
          let ni := bs.size - 1
          let as := t.getAppArgs
          if as.size < ni then return none
          return some (mkAppN t.getAppFn (as.extract 0 (as.size - ni)), ni)
    if doms?.any (·.isNone) then continue
    let doms := doms?.map fun d => (d.getD default).1
    let fidx := doms?.map fun d => (d.getD default).2
    -- Every family member is one of the group's occurrences, and every one of
    -- the group's is a family member.
    let mimic? := doms.map fun d => grp.find? (g.occAt · ps == d)
    if mimic?.any (·.isNone) then continue
    let mimic := mimic?.map (·.getD 0)
    if grp.any fun i => !mimic.contains i then continue
    let mut rules : Array (Nat × Name) := #[]
    for j in [0:recs.size] do
      let .recInfo rj ← constInfo recs[j]! | badShape s!"{recs[j]!} is not a recursor"
      for rl in rj.rules do rules := rules.push (j, rl.ctor)
    return { recs, cls, qs, doms, fidx, mimic, rules }
  badShape "a mutually recursive mimic group has no matching recursor family"

/-- The minor types the family's recursors bind at this motive vector. They are
the same for every component, so they are read off component 0 once. -/
def withFamilyMinors (_g : Gen) (f : Family) (v : Level) (motives : Array Expr)
    (k : Array Expr → GenM (Array Expr)) : GenM (Array Expr) := do
  let head : Expr ← contRecAt f.recs[0]! v f.cls
  withMinorTypes (mkAppN head (f.qs ++ motives)) f.rules.size k

/-- One minor of the family's `pack`: a field at **any** member of the family
is its own induction hypothesis — that is what makes the recursion
simultaneous — a field at a mimic outside the family is packed by that mimic's
own `pack`, and everything else goes through. -/
def packFamMinor (g : Gen) (f : Family) (ps : Array Expr) (j : Nat) (cn : Name)
    (mty : Expr) : GenM Expr := do
  forallTelescope mty fun bs _ => do
    let n ← numFieldsOf cn
    let fields := bs.extract 0 n
    let ihs := bs.extract n bs.size
    let ftys ← fields.mapM ftyp
    let mut recs : Array Nat := #[]
    for x in [0:n] do
      if (← f.memberUnder? ftys[x]!).isSome then recs := recs.push x
    let mut args : Array Expr := #[]
    for x in [0:n] do
      if let some t := recs.findIdx? (· == x) then
        -- Its hypothesis is already `∀ x⃗, B ι⃗` when there is a binder, which
        -- is what the block's constructor wants: no lambda, no funext.
        args := args.push ihs[t]!
      else if let some (o, nb) ← g.occOfUnder? ps ftys[x]! then
        args := args.push (← underBinders nb ftys[x]! fields[x]! fun _ res v =>
          return g.call (g.packName o) ps ((g.occIdx? o ps res).getD #[]) v)
      else
        args := args.push fields[x]!
    mkLambdaFVars bs (g.blockCtorAt (f.mimic[j]! + g.numAll) cn ps args)

/-- **`pack` for family member `j`**, as the `j`-th component of one recursion
over the whole family — the same motive and minor vector for every component,
so `pack₀` and `pack₁` never mention each other. -/
def packFamilyValue (g : Gen) (f : Family) (j : Nat) (ps : Array Expr) : GenM Expr := do
  let motives ← (Array.range f.doms.size).mapM fun t =>
    f.withIndices t fun idxs =>
      withLocalDeclD `x (mkAppN f.doms[t]! idxs) fun x =>
        mkLambdaFVars (idxs.push x) (mkAppN (g.memAt (f.mimic[t]! + g.numAll) ps) idxs)
  let minors ← g.withFamilyMinors f g.u motives fun mtys =>
    (Array.range f.rules.size).mapM fun t =>
      g.packFamMinor f ps f.rules[t]!.1 f.rules[t]!.2 mtys[t]!
  return mkAppN (← contRecAt f.recs[j]! g.u f.cls) (f.qs ++ motives ++ minors)

/-- **The retraction for family member `j`**, likewise simultaneous: the same
recursion at `Prop`, whose `j`-th motive is `unpackⱼ ∘ packⱼ = id`. A field at
a sibling member gets the sibling's own induction hypothesis, which is that
sibling's retraction up to proof irrelevance — the same identification the
one-at-a-time path already makes between `ih` and `unpackPack_o f`. -/
def retractFamilyValue (g : Gen) (f : Family) (j : Nat) (ps : Array Expr) : GenM Expr := do
  let trip := fun (o : Nat) (idxs : Array Expr) (x : Expr) =>
    g.call (g.unpackName o) ps idxs (g.call (g.packName o) ps idxs x)
  let motives ← (Array.range f.doms.size).mapM fun t =>
    f.withIndices t fun idxs => do
      let dom := mkAppN f.doms[t]! idxs
      withLocalDeclD `l dom fun l =>
        mkLambdaFVars (idxs.push l) (g.eqi.mk' g.u dom (trip f.mimic[t]! idxs l) l)
  let minors ← g.withFamilyMinors f .zero motives fun mtys =>
    (Array.range f.rules.size).mapM fun t => do
      let (jj, cn) := f.rules[t]!
      forallTelescope mtys[t]! fun bs _ => do
        let n ← numFieldsOf cn
        let fields := bs.extract 0 n
        let ihs := bs.extract n bs.size
        let ftys ← fields.mapM ftyp
        let mut recs : Array Nat := #[]
        for x in [0:n] do
          if (← f.memberUnder? ftys[x]!).isSome then recs := recs.push x
        let mut lhs : Array Expr := #[]
        let mut proofs : Array (Option Expr) := #[]
        for x in [0:n] do
          if let some t' := recs.findIdx? (· == x) then
            let (d, nb) := (← f.memberUnder? ftys[x]!).getD (0, 0)
            let (l, pf) ← g.underEq nb ftys[x]! fields[x]! fun xs res v => do
              let idxs := (f.memberAt? res).map (·.2) |>.getD #[]
              return (trip f.mimic[d]! idxs v, mkAppN ihs[t']! xs)
            lhs := lhs.push l
            proofs := proofs.push (some pf)
          else if let some (o, nb) ← g.occOfUnder? ps ftys[x]! then
            let (l, pf) ← g.underEq nb ftys[x]! fields[x]! fun _ res v => do
              let idxs := (g.occIdx? o ps res).getD #[]
              return (trip o idxs v, g.call (g.retractName o) ps idxs v)
            lhs := lhs.push l
            proofs := proofs.push (some pf)
          else
            lhs := lhs.push fields[x]!
            proofs := proofs.push none
        let (ccls, cqs) := f.ctorPrefix jj
        let rebuild := fun (a : Array Expr) => mkAppN (.const cn ccls) (cqs ++ a)
        -- The constructor application's own type, indices and all: `∀ ι⃗` is
        -- not a type and the family member's indices come from the result.
        let goalTy ← ftyp (rebuild fields)
        mkLambdaFVars bs (← g.foldCongr goalTy ftys lhs fields proofs rebuild)
  return mkAppN (← contRecAt f.recs[j]! .zero f.cls) (f.qs ++ motives ++ minors)

/-- `packᵢ := C.rec q⃗ (fun _ => Bᵢ p⃗) minors…`, partially applied — its type is
`∀ _ : occᵢ, Bᵢ p⃗` on the nose, the motive being constant.

The recursor's level list is `u :: cls` and not `u :: C`'s *declared*
parameters: a polymorphic container instantiated at a concrete level — `List.{0}
Syntax` — is exactly `Lean.Syntax`'s shape, and writing the declared parameter
there leaves a free universe variable. -/
def packValue (g : Gen) (i member : Nat) (ps : Array Expr) : GenM Expr := do
  let (c, cls, qs) ← g.container i ps
  -- The motive binds the container's index telescope in front of its major,
  -- which is where `C.rec` puts it; for an unindexed container the telescope is
  -- empty and this is the constant motive it always was.
  let motive ← g.withOccIndices i ps fun idxs =>
    withLocalDeclD `x (g.occAtIdx i ps idxs) fun x =>
      mkLambdaFVars (idxs.push x) (mkAppN (g.memAt member ps) idxs)
  let head : Expr ← Gen.contRecAt (.str c "rec") g.u cls
  let cs ← ctorsOf c
  let pre := qs.push motive
  let minors ← withMinorTypes (mkAppN head pre) cs.size fun mtys =>
    (Array.range cs.size).mapM fun t => g.packMinor i member ps cs[t]! mtys[t]!
  return mkAppN head (pre ++ minors)

/-! ### unpack -/

/-- A member's minor for `unpack`: at the root, rebuild the constructor; at a
mimic, build the **real** container's constructor, taking each field at another
mimic from its induction hypothesis. -/
def unpackMinor (g : Gen) (k : Nat) (ps : Array Expr) (cn : Name) (mty : Expr) :
    GenM Expr := do
  forallTelescope mty fun bs _ => do
    let n ← numFieldsOf cn
    let fields := bs.extract 0 n
    let ihs := bs.extract n bs.size
    let ftys ← fields.mapM ftyp
    let (ihm, ihPos) ← g.ihVector ftys
    let mut args : Array Expr := #[]
    for x in [0:n] do
      match ihm[x]! with
      | some m =>
        if !g.isReal m then
          -- A field at a *mimic* is unpacked, and its unpacked value is exactly
          -- this recursor's induction hypothesis for it. **Including under a
          -- binder**: the hypothesis for `∀ x⃗, Bₘ ι⃗` is `∀ x⃗, occₘ ι⃗`,
          -- because a mimic's motive is the occurrence, so no lambda is
          -- written here either.
          let some t := ihPos[x]! | badShape "no hypothesis for a mimic field"
          args := args.push ihs[t]!
        else
          -- A field at a **real** member passes through: the block types it at
          -- `Bₘ p⃗`, and the real constructor wants `Rₘ._model.self p⃗`, which is
          -- that by δ.
          args := args.push fields[x]!
      | none =>
        args := args.push fields[x]!
    let body ←
      if g.isReal k then
        pure (g.blockCtorAt k cn ps fields)
      else do
        let (_, cls, qs) ← g.container (g.mimicOf k) ps
        let real ← g.realCtor (g.mimicOf k) ps cn
        pure (mkAppN (.const real cls) (qs ++ args))
    mkLambdaFVars bs body

/-- `unpackᵢ := Bᵢ.rec p⃗ motives… minors…`, partially applied.

The motive at the root is `fun _ => B₀ p⃗` and at each mimic the occurrence:
that is the only choice inhabited for every block whatever its constructors
are, and `fun _ => Bⱼ` would not do because `unpack₁` for `Box BTree` needs
`unpack₂`'s result as its `mk` field. -/
def unpackValue (g : Gen) (member : Nat) (ps : Array Expr) : GenM Expr := do
  let motives ← (Array.range g.members.size).mapM fun k =>
    g.withIndices k ps fun idxs => do
      let mem := mkAppN (g.memAt k ps) idxs
      withLocalDeclD `b mem fun b =>
        mkLambdaFVars (idxs.push b)
          (if g.isReal k then mem else g.occAtIdx (g.mimicOf k) ps idxs)
  let head : Expr := g.blockRecAt member g.u
  let pre := ps ++ motives
  let pairs := g.ctorPairs
  let minors ← withMinorTypes (mkAppN head pre) g.numMinors fun mtys =>
    (Array.range pairs.size).mapM fun t => g.unpackMinor pairs[t]!.1 ps pairs[t]!.2 mtys[t]!
  return mkAppN head (pre ++ minors)

/-! ### the two round trips -/

/-- `unpackPackᵢ : ∀p⃗ l, Eq (unpackᵢ p⃗ (packᵢ p⃗ l)) l`, by the container's own
recursor, one congruence per field the round trip moves. -/
def retractValue (g : Gen) (i : Nat) (ps : Array Expr) : GenM Expr := do
  let (c, cls, qs) ← g.container i ps
  let trip := fun (idxs : Array Expr) (x : Expr) =>
    g.call (g.unpackName i) ps idxs (g.call (g.packName i) ps idxs x)
  let motive ← g.withOccIndices i ps fun idxs => do
    let occ := g.occAtIdx i ps idxs
    withLocalDeclD `l occ fun l =>
      mkLambdaFVars (idxs.push l) (g.eqi.mk' g.u occ (trip idxs l) l)
  let head : Expr ← Gen.contRecAt (.str c "rec") .zero cls
  let cs ← ctorsOf c
  let pre := qs.push motive
  let minors ← withMinorTypes (mkAppN head pre) cs.size fun mtys =>
    (Array.range cs.size).mapM fun t => do
      let cn := cs[t]!
      forallTelescope mtys[t]! fun bs _ => do
        let n ← numFieldsOf cn
        let fields := bs.extract 0 n
        let ihs := bs.extract n bs.size
        let ftys ← fields.mapM ftyp
        let mut recs : Array Nat := #[]
        for x in [0:n] do
          if (← g.occUnder? i ps ftys[x]!).isSome then recs := recs.push x
        unless recs.size == ihs.size do
          badShape s!"{cn}'s recursive positions and hypotheses do not line up"
        let mut lhs : Array Expr := #[]
        let mut proofs : Array (Option Expr) := #[]
        for x in [0:n] do
          if let some t := recs.findIdx? (· == x) then
            -- **Under a binder the induction hypothesis is pointwise**, so it
            -- is closed with funext; with no binder it is the equation itself
            -- and `underEq` writes neither a lambda nor a `funext`.
            let nb := (← g.occUnder? i ps ftys[x]!).getD 0
            let (l, pf) ← g.underEq nb ftys[x]! fields[x]! fun xs res v => do
              let idxs := (g.occIdx? i ps res).getD #[]
              return (trip idxs v, mkAppN ihs[t]! xs)
            lhs := lhs.push l
            proofs := proofs.push (some pf)
          else if let some (o, nb) ← g.occOfUnder? ps ftys[x]! then
            let (l, pf) ← g.underEq nb ftys[x]! fields[x]! fun _ res v => do
              let idxs := (g.occIdx? o ps res).getD #[]
              return (g.call (g.unpackName o) ps idxs (g.call (g.packName o) ps idxs v),
                      g.call (g.retractName o) ps idxs v)
            lhs := lhs.push l
            proofs := proofs.push (some pf)
          else
            lhs := lhs.push fields[x]!
            proofs := proofs.push none
        let rebuild := fun (a : Array Expr) => mkAppN (.const cn cls) (qs ++ a)
        -- The application's own type, indices and all: the occurrence is the
        -- container at its *parameters* and is not a type on its own.
        let goalTy ← ftyp (rebuild fields)
        mkLambdaFVars bs (← g.foldCongr goalTy ftys lhs fields proofs rebuild)
  return mkAppN head (pre ++ minors)

/-- The section's motive at member `k`, applied to `x`. **The round trip only
where the round trip exists**: a mimic this development has not reached yet has
no `pack`, so its motive is reflexivity — which is all its own minors need,
because a field at such a mimic is at one this group does not depend on. The
caller passes the live set: it is the group being emitted together with
everything already emitted, and for a **cyclic** group that is more than one
member at once.

`ty` is the member's type **at its indices**, which the caller has in hand and
`Bₖ p⃗` is not. -/
def sectionMotive (g : Gen) (k : Nat) (ty : Expr) (ps idxs : Array Expr) (x : Expr)
    (live : Nat → Bool) : Expr :=
  if live k then
    let i := g.mimicOf k
    g.eqi.mk' g.u ty (g.call (g.packName i) ps idxs (g.call (g.unpackName i) ps idxs x)) x
  else
    g.eqi.mk' g.u ty x x

/-- `packUnpackᵢ : ∀p⃗ b, Eq (packᵢ p⃗ (unpackᵢ p⃗ b)) b`, by the block's
recursor. -/
def sectionValue (g : Gen) (member : Nat) (ps : Array Expr) (live : Nat → Bool) :
    GenM Expr := do
  let motives ← (Array.range g.members.size).mapM fun k =>
    g.withIndices k ps fun idxs => do
      let mem := mkAppN (g.memAt k ps) idxs
      withLocalDeclD `b mem fun b =>
        mkLambdaFVars (idxs.push b) (g.sectionMotive k mem ps idxs b live)
  let head : Expr := g.blockRecAt member .zero
  let pre := ps ++ motives
  let pairs := g.ctorPairs
  let minors ← withMinorTypes (mkAppN head pre) g.numMinors fun mtys =>
    (Array.range pairs.size).mapM fun t => do
      let (k, cn) := pairs[t]!
      forallTelescope mtys[t]! fun bs _ => do
        let n ← numFieldsOf cn
        let fields := bs.extract 0 n
        let ihs := bs.extract n bs.size
        let ftys ← fields.mapM ftyp
        let (_, ihPos) ← g.ihVector ftys
        let rebuild := fun (a : Array Expr) => g.blockCtorAt k cn ps a
        -- The constructor application's own type, indices and all, rather than
        -- `Bₖ p⃗` — which is not a type when member `k` is indexed.
        let ty ← ftyp (rebuild fields)
        if !live k then
          mkLambdaFVars bs (g.eqi.refl' g.u ty (rebuild fields))
        else
          let mut lhs : Array Expr := #[]
          let mut proofs : Array (Option Expr) := #[]
          for x in [0:n] do
            match ← g.mimicUnder? ftys[x]! with
            | some (m, nb) =>
              if live m then
                let some t := ihPos[x]! | badShape "no hypothesis for a member field"
                let o := g.mimicOf m
                -- Under a binder the hypothesis is pointwise and funext closes
                -- it; with none, `underEq` writes neither.
                let (l, pf) ← g.underEq nb ftys[x]! fields[x]! fun xs res v => do
                  let fidx := g.idxOf m res
                  return (g.call (g.packName o) ps fidx (g.call (g.unpackName o) ps fidx v),
                          mkAppN ihs[t]! xs)
                lhs := lhs.push l
                proofs := proofs.push (some pf)
              else
                lhs := lhs.push fields[x]!
                proofs := proofs.push none
            | none =>
              lhs := lhs.push fields[x]!
              proofs := proofs.push none
          mkLambdaFVars bs (← g.foldCongr ty ftys lhs fields proofs rebuild)
  return mkAppN head (pre ++ minors)

/-! ### the declared type's own constructors -/

/-- `T._model.ctor_j := fun p⃗ f⃗ => B₀.c p⃗ g⃗`, where a field the block types at a
**mimic** is packed on the way in and everything else passes through. The field
telescope is read off the *export's* declared type, so the parameters this binds
are the ones the export declared and not ones reconstructed here. -/
def ctorValue (g : Gen) (k j : Nat) (realTy : Expr) (ps : Array Expr) : GenM Expr := do
  let cn := g.blockCtors[k]![j]!
  let blkTys ← withFields (← instCtor cn g.us ps) fun _ tys => pure tys
  forallTelescope (← instForall realTy ps) fun fields _ => do
    if fields.size != blkTys.size then
      badShape s!"{cn}: the export declares {fields.size} fields, the block {blkTys.size}"
    let mut args : Array Expr := #[]
    for x in [0:fields.size] do
      match ← g.mimicUnder? blkTys[x]! with
      -- The index vector comes from the **export-side** field's own type,
      -- which is the occurrence at those indices; the block's copy is at
      -- the block's own binders and would not name them. Under a binder the
      -- packing happens pointwise — `fun x⃗ => pack (f x⃗)` — which needs a
      -- lambda but no funext: no equation is being moved here.
      | some (m, nb) =>
        let fty ← ftyp fields[x]!
        args := args.push (← underBinders nb fty fields[x]! fun _ res v =>
          return g.call (g.packName (g.mimicOf m)) ps (g.idxOf m res) v)
      | none => args := args.push fields[x]!
    mkLambdaFVars fields (g.blockCtorAt k cn ps args)

/-! ### the recursors -/

/-- **The block's motive vector** — the caller's own at the root, the caller's
composed with `unpack` at each mimic. -/
def blockMotives (g : Gen) (ps motives : Array Expr) : GenM (Array Expr) :=
  (Array.range g.members.size).mapM fun j =>
    if g.isReal j then pure motives[j]!
    else g.withIndices j ps fun idxs =>
      withLocalDeclD `b (mkAppN (g.memAt j ps) idxs) fun b =>
        mkLambdaFVars (idxs.push b)
          (mkAppN motives[j]! (idxs.push (g.call (g.unpackName (g.mimicOf j)) ps idxs b)))

/-- One minor of the block's recursor, built from the caller's own.

The caller's minor wants the fields at their **real** types, so a field the
block holds at a mimic is unpacked on the way in; the induction hypotheses pass
through, because the block's are already at the composed motive. **Only a root
constructor with a packed field transports**, and it transports along
`packUnpack`, one position at a time. -/
def recMinor (g : Gen) (j : Nat) (cn : Name) (mty sT : Expr) (ps motives : Array Expr)
    (v : Level) : GenM Expr := do
  forallTelescope mty fun bs _ => do
    let n ← numFieldsOf cn
    let fields := bs.extract 0 n
    let ihs := bs.extract n bs.size
    let ftys ← fields.mapM ftyp
    let mut real : Array Expr := #[]
    for x in [0:n] do
      match ← g.mimicUnder? ftys[x]! with
      | some (m, nb) =>
        real := real.push (← underBinders nb ftys[x]! fields[x]! fun _ res v =>
          return g.call (g.unpackName (g.mimicOf m)) ps (g.idxOf m res) v)
      | none => real := real.push fields[x]!
    let body := mkAppN sT (real ++ ihs)
    if !g.isReal j then
      mkLambdaFVars bs body
    else
      -- The caller's minor lands at `Mⱼ (T._model.ctor f⃗_real)`, which unfolds
      -- to `Mⱼ (Bⱼ.c (pack (unpack f⃗)))`, and the block hands it `Mⱼ (Bⱼ.c f⃗)`.
      let mut lhs : Array Expr := #[]
      let mut proofs : Array (Option Expr) := #[]
      for x in [0:n] do
        match ← g.mimicUnder? ftys[x]! with
        | some (m, nb) =>
          let o := g.mimicOf m
          let (l, pf) ← g.underEq nb ftys[x]! fields[x]! fun _ res v => do
            let fidx := g.idxOf m res
            return (g.call (g.packName o) ps fidx (g.call (g.unpackName o) ps fidx v),
                    g.call (g.sectionName o) ps fidx v)
          lhs := lhs.push l
          proofs := proofs.push (some pf)
        | none =>
          lhs := lhs.push fields[x]!
          proofs := proofs.push none
      let rebuild := fun (a : Array Expr) => g.blockCtorAt j cn ps a
      -- `Mⱼ` at the indices this constructor's result carries. They cannot
      -- mention a moved field — Lean rejects a nested field a later type
      -- depends on, and it rejects a *result index* about one for the
      -- same reason: `C α (llen l)` with `l : Lst α` nested fails Lean's own
      -- compilation with `application type mismatch: llen TT l ... has type
      -- _nested.Lst_2`. So they are constant across every fold in this file.
      let m0 := mkAppN motives[j]! (g.idxOf j (← ftyp (rebuild fields)))
      mkLambdaFVars bs (← g.foldValue v m0 ftys lhs fields proofs rebuild body)

/-- **The block's minor vector**, in the block's own order — every member's
constructors, member by member, which is the order `Bₖ.rec` binds them in and
the order the caller's own minors arrive in. -/
def blockMinors (g : Gen) (ps motives minors : Array Expr) (v : Level) :
    GenM (Array Expr) := do
  let bm ← g.blockMotives ps motives
  let head : Expr := g.blockRecAt 0 v
  let pairs := g.ctorPairs
  withMinorTypes (mkAppN head (ps ++ bm)) g.numMinors fun mtys =>
    (Array.range pairs.size).mapM fun t =>
      g.recMinor pairs[t]!.1 pairs[t]!.2 mtys[t]! minors[t]! ps motives v

/-- **One member's recursor, as the model restates it.** Read once and used by
both the recursor and its ι rules, which share the `np + nm + nmin` binders and
differ only past them. -/
structure RecShape where
  k : Nat
  /-- `Bₖ.rec`, the block's own. -/
  src : Name
  /-- The motive universe, the recursor's single level parameter. -/
  v : Level
  lparams : List Name
  nm : Nat
  nmin : Nat
  /-- The member's index count — the export's own for a real member and the
  container's for a mimic. -/
  nidx : Nat
  /-- The declared type, at the model's names. -/
  ty : Expr
  deriving Inhabited

/-- `Bₖ.rec`'s statement at the model's names — the same table `nested::add`
restores the *export's* recursor with, one set of names along, so
`T._model.rec_k` and `T.rec_k` are the same statement about different
constants. -/
def recShape (g : Gen) (k : Nat) (heads : Std.HashMap Name (Nat × Expr)) :
    GenM RecShape := do
  let src := g.blockRec k
  let .recInfo rv ← constInfo src | badShape s!"{src} is not a recursor"
  -- **A mimic's indices are the container's, and they are carried too.** The
  -- block member's count and the container's agree by construction — the mimic
  -- is the container at the occurrence's parameters — and this is where a
  -- disagreement would show.
  unless rv.numIndices == g.nidx[k]! do
    badShape s!"{src} has {rv.numIndices} indices where the block member has {g.nidx[k]!}"
  -- The motive universe first, the block's own after it — and the block's own
  -- are the declaration's, because that is what the block was declared with.
  -- **A block that eliminates only into `Prop` has no motive universe at all**,
  -- and then the motive is `Prop`-valued and every level list is just `ℓ⃗`.
  let v ←
    if g.largeElim then do
      let lp :: rest := rv.levelParams | badShape s!"{src} has no motive universe"
      unless rest.map Level.param == g.us do
        badShape s!"{src} carries the level parameters {rv.levelParams}"
      pure (Level.param lp)
    else do
      unless rv.levelParams.map Level.param == g.us do
        badShape s!"{src} carries the level parameters {rv.levelParams}"
      pure Level.zero
  if rv.numMotives != g.members.size then badShape s!"{src} has {rv.numMotives} motives"
  return { k, src, v, lparams := rv.levelParams
           nm := rv.numMotives, nmin := rv.numMinors, nidx := rv.numIndices
           ty := restore heads rv.type }

/-- The value of `T._model.rec_k`: the block's recursor at a **shifted motive
vector** — the caller's own at the root, the caller's composed with `unpack` at
each mimic. At a mimic the major itself has to move: the block eliminates `Bₖ`
and the export eliminates `occₖ`, so the recursor runs at `pack major` and the
result comes back along the **retraction** `unpackPack`. -/
def recValue (g : Gen) (sh : RecShape) : GenM Expr := do
  forallBoundedTelescope sh.ty (some (g.np + sh.nm + sh.nmin + sh.nidx + 1)) fun bs _ => do
    let ps := bs.extract 0 g.np
    let motives := bs.extract g.np (g.np + sh.nm)
    let minors := bs.extract (g.np + sh.nm) (g.np + sh.nm + sh.nmin)
    -- The indices sit between the minors and the major, which is where the
    -- recursor's own telescope puts them.
    let idxs := bs.extract (g.np + sh.nm + sh.nmin) (bs.size - 1)
    let major := bs[bs.size - 1]!
    let bm ← g.blockMotives ps motives
    let bmin ← g.blockMinors ps motives minors sh.v
    let head : Expr := g.blockRecAt sh.k sh.v
    let pre := ps ++ bm ++ bmin
    let value ←
      if g.isReal sh.k then
        pure (mkAppN head ((pre ++ idxs).push major))
      else do
        let o := g.mimicOf sh.k
        -- **The recursor's own index binders are the container's.** They sit
        -- between the minors and the major, and `pack`, `unpack` and the
        -- retraction all take them there too.
        let occ := g.occAtIdx o ps idxs
        let pk := g.call (g.packName o) ps idxs major
        let base := mkAppN head ((pre ++ idxs).push pk)
        let trip := g.call (g.unpackName o) ps idxs pk
        let mot ← withLocalDeclD `x occ fun x =>
          withLocalDeclD `h (g.eqi.mk' g.u occ trip x) fun h =>
            mkLambdaFVars #[x, h] (mkAppN motives[sh.k]! (idxs.push x))
        pure (g.eqi.recAt sh.v g.u occ trip mot base major
          (g.call (g.retractName o) ps idxs major))
    mkLambdaFVars bs value

/-! ### the congruence the ι rules are stated along -/

/-- **`congrPackᵢ : ∀p⃗ l₀ l, Eq l₀ l → Eq (packᵢ l₀) (packᵢ l)`.**

Needed for a reason that is not obvious. The ι rule of a **root** constructor
with a packed field has, on its left, the transport `recₖ`'s minor performs —
along `packUnpack (pack f)`. Proving it means `Eq.rec` on `unpackPack f`, whose
motive has to name a proof of `Eq (pack (unpack (pack f))) (pack x)` for the
abstracted `x`, and only a *congruence* of `pack` is that. Proof irrelevance
then identifies the two at `x := f`, which is where the triangle identity would
otherwise have to be proved. -/
def congrPackDecl (g : Gen) (i : Nat) (ps : Array Expr) : GenM (Expr × Expr) := do
  g.withOccIndices i ps fun idxs => do
    let occ := g.occAtIdx i ps idxs
    let mem := mkAppN (g.memAt (i + g.numAll) ps) idxs
    let pk := fun (x : Expr) => g.call (g.packName i) ps idxs x
    withLocalDeclD `l0 occ fun l0 => withLocalDeclD `l occ fun l =>
      withLocalDeclD `h (g.eqi.mk' g.u occ l0 l) fun h => do
        let tel := ps ++ idxs ++ #[l0, l, h]
        let ty ← mkForallFVars tel (g.eqi.mk' g.u mem (pk l0) (pk l))
        let mot ← withLocalDeclD `x occ fun x =>
          withLocalDeclD `hx (g.eqi.mk' g.u occ l0 x) fun hx =>
            mkLambdaFVars #[x, hx] (g.eqi.mk' g.u mem (pk l0) (pk x))
        let base := g.eqi.refl' g.u mem (pk l0)
        let val ← mkLambdaFVars tel (g.eqi.recAt .zero g.u occ l0 mot base l h)
        return (ty, val)

end Gen

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

/-! ## The driver -/

/-- The public names of one modeled inductive interface.

Most constructions implement and expose the same family, so [`Iso`] keeps its
historical fields as the public interface and leaves `implementation?` empty.
The one-layer recursive construction is different: it implements the fixpoint
at private names and exposes a separate, exact source-shaped public layer.
Keeping that distinction explicit prevents later consumers from accidentally
publishing the private recursor or using the public wrapper as the recursive
proof oracle. -/
structure IsoInterface where
  selfNames : Array Name
  ctors : Array (Name × Name)
  recs : Array Name
  iotas : Array (Nat × Name × Name)
  deriving Inhabited

/-- One member of a simultaneous private/public family boundary.

Every association is carried by its source name.  In particular, constructors
and recursor rules are not zipped with exporter arrays: mutual recursors need
not be serialized in member order.  `changed` records whether the public
carrier is a genuine one-layer representation or the identity alias used to
keep an ineligible sibling inside the simultaneous certificate. -/
structure IsoFamilyMember where
  owner : Name
  changed : Bool
  publicSelf : Name
  privateSelf : Name
  privateRecursor : Name
  privateConstructors : Array (Name × Name)
  privateIotas : Array (Name × Name × Name)
  privateRules : Array (Name × Name × Name)
  roll : Name
  unroll : Name
  unrollRoll : Name
  rollUnroll : Name
  deriving Inhabited

/-- Complete certificate for a partial simultaneous family adapter.

`support` names the declaration-local mutual implementation support (currently
the tag and auxiliary carrier).  Consumers accept the new literal projection
contract only after validating every support and member slot. -/
structure IsoFamilyImplementation where
  root : Name
  support : Array Name
  members : Array IsoFamilyMember
  deriving Inhabited

/-- One already checked equivalence between a source-shaped nested container
and the corresponding named private mimic member. `parameterArity` and `indexArity`
describe the exact prefix of all four declarations; neither is an eligibility
bound. The declaration types are retained so a later shadow can compare the
installed constants and target carrier before assigning maps to source keys. -/
structure IsoContainerImplementation where
  parameterArity : Nat
  indexArity : Nat
  implementationCarrier : Name
  forward : Name
  backward : Name
  backwardForward : Name
  forwardBackward : Name
  forwardType : Expr
  backwardType : Expr
  backwardForwardType : Expr
  forwardBackwardType : Expr
  implementationCarrierType : Expr
  deriving Inhabited, BEq, Repr

/-- Everything one nested declaration's model came to. -/
structure Iso where
  /-- Every generated declaration, in dependency order and already accepted. -/
  decls : Array Declaration
  /-- The declaration's own level parameters — the export's, in the export's
  order. Every generated constant carries these; a recursor and its ι theorems
  carry their motive universe in front of them. -/
  levelParams : List Name
  /-- The block's members: the export's own in `all` order, then the mimics. -/
  members : Array Name
  /-- `R_k._model.self` per **real** member, in `all` order. One unless the
  declaration is a mutual block. -/
  selfNames : Array Name
  /-- How many of `members` are the export's own. -/
  numAll : Nat
  /-- `(the export's constructor, the model's)`, in declaration order. -/
  ctors : Array (Name × Name)
  /-- `T._model.rec_k`, in member order. -/
  recs : Array Name
  /-- `(member, the rule's constructor as the export names it, the theorem)`. -/
  iotas : Array (Nat × Name × Name)
  /-- Private fixpoint interface when it differs from the public fields above.
  `none` means the implementation and public interface are identical.  This is
  name-only and does not retain a second declaration array. -/
  implementation? : Option IsoInterface := none
  /-- Owner-keyed simultaneous implementation certificate for a partial mutual
  one-layer family.  This is separate from the historical singleton
  `implementation?` so legacy consumers cannot accidentally interpret a
  partial mutual prefix as a complete certificate. -/
  familyImplementation? : Option IsoFamilyImplementation := none
  /-- Checked nested-container maps, one per private mimic. They are assigned
  to exact source occurrence keys by `FamilyAdapterShadow`; array position is
  not a consumer contract. -/
  containerImplementations : Array IsoContainerImplementation := #[]
  /-- `(member, theorem)` for the real members on which Lean's kernel enables
  its unit-like equality shortcut. -/
  unitlikes : Array (Nat × Name) := #[]
  /-- `(member, theorem)` for the non-propositional members on which Lean's
  kernel enables structure eta.  The theorem reconstructs the value with the
  exact modeled constructor and the intrinsic modeled projections in field
  order. -/
  etas : Array (Nat × Name) := #[]
  /-- `(source recursor, rule-K theorem)` for exactly those exported recursors
  whose literal kernel metadata has `k = true`. -/
  ruleKs : Array (Name × Name) := #[]
  /-- `(type former, zero-based field index, projection, reduction theorem)`.
  Empty when no intrinsic projection has yet been attached.  The generated names may temporarily
  use an alias build root until serialization. -/
  projections : Array (Name × Nat × Name × Name) := #[]
  /-- Route-specific, closed implementations for intrinsic projections whose
  model recursor cannot eliminate into the field sort.  Each entry stores the
  source owner, zero-based field index, complete projection value and complete
  reduction-proof value.  The common driver remains responsible for the
  public types, names, collision checks and declaration ordering. -/
  projectionOverrides : Array (Name × Nat × Expr × Expr) := #[]
  /-- **Prelude constants the input did not declare and this model spliced in**
  — a subset of `Eq`, `Eq.refl`, the four quotient names, `Quot.sound` and
  `T._model.funext`, in the order they were emitted, and **empty** for every
  declaration whose input already had what it needed. The report prints it:
  a splice is a decision on record and not a silent one. -/
  spliced : Array Name
  /-- **Spliced inductives this model is not allowed to leave unmodelled.**
  Arm C splices the *index erasure* of the family it is
  modelling and carves the family out of it, so its output contains an
  inductive declaration that was in nobody's input. If the prim pass then
  cannot model that skeleton, the emission would put an additional unmodelled
  inductive in front of a consumer, so the whole model is
  withdrawn and the declaration declines instead.

  The check is **after** the splice-and-model descent rather than a prediction
  before it, because a prediction is the shape of "skip is not pass": a
  cheap test that says the skeleton will model, and an emission that leaves it
  unmodelled when it does not. [`InductiveModels.genPrim`] is where the withdrawal
  happens. Empty for every other arm, so nothing else changes shape. -/
  requires : Array Name := #[]
  /-- Exact build-name to export-name aliases used only after a normalized-name
  collision.  This is a whole-name table: raw private constructor names need
  not share any prefix with their owner. -/
  aliases : Naming.AliasMap := .empty
  deriving Inhabited

/-- The exact public family consumed by correspondence, serialization, and
the statement checker. -/
def Iso.publicInterface (is : Iso) : IsoInterface :=
  { selfNames := is.selfNames, ctors := is.ctors, recs := is.recs, iotas := is.iotas }

/-- The family whose recursor and iota proofs implement the public model.
Ordinary routes share the public family structurally. -/
def Iso.implementationInterface (is : Iso) : IsoInterface :=
  match is.implementation? with
  | some implementation => implementation
  | none => is.publicInterface

/-- **The export's names rewritten to the model's**: `T._model` for each real
member, `C._model` for each constructor, and `R._model` for each recursor.

The mutual and simple constructions share this table when writing restored
recursor types and rules. A plain mutual block has no second inductive to read a
statement from, so its public recursors and ι rules are the export's own with
this simultaneous renaming. The independent structural checker later rebuilds
the correspondence directly from serialized export records. -/
def modelTable (env : Environment) (all : Array Name) (is : Iso) :
    Std.HashMap Name (Nat × Expr) := Id.run do
  let us := is.levelParams.map Level.param
  let mut t : Std.HashMap Name (Nat × Expr) := {}
  for k in [0:is.numAll] do
    t := t.insert all[k]! (0, .const is.selfNames[k]! us)
  for (exportC, modelC) in is.ctors do
    t := t.insert exportC (0, .const modelC us)
  for k in [0:is.recs.size] do
    let ern := exportRecName all k
    let ls := match env.constants.find? ern with
      | some ci => ci.levelParams.map Level.param
      | none => []
    t := t.insert ern (0, .const is.recs[k]! ls)
  return t

/-- The extra reduction certified by a recursor's literal `k` flag.

Unlike an iota theorem, the major is an arbitrary inhabitant of the unique
constructor's result fiber. Lean's K reduction replaces it by that nullary
constructor and then applies the sole ordinary rule.  Starting from the iota
statement pins any indices to exactly that fiber without reconstructing them. -/
def ruleKDecl (eqi : EqInfo) (recLevelParams : List Name) (numPre : Nat)
    (theoremName : Name) (iotaType : Expr) : GenM Declaration := do
  forallBoundedTelescope iotaType (some numPre) fun pre body => do
    let .const eqName [v] := body.getAppFn
      | badShape s!"{theoremName}'s source iota does not conclude at Eq"
    unless eqName == eqi.eqN do badShape s!"{theoremName}'s source iota uses {eqName}"
    let eqArgs := body.getAppArgs
    unless eqArgs.size == 3 do badShape s!"{theoremName}'s source iota has malformed Eq"
    let α := eqArgs[0]!
    let lhs := eqArgs[1]!
    let rhs := eqArgs[2]!
    let some major := lhs.getAppArgs.back? | badShape s!"{theoremName}'s iota has no major"
    let majorType ← inferType major
    withLocalDeclD `major majorType fun arbitrary => do
      let replaceMajor := fun expression => expression.replace fun sub =>
        if sub == major then some arbitrary else none
      let α := replaceMajor α
      let lhs := replaceMajor lhs
      let binders := pre.push arbitrary
      let type := ← mkForallFVars binders (eqi.mk' v α lhs rhs)
      let value := ← mkLambdaFVars binders (eqi.refl' v α lhs)
      return .thmDecl { name := theoremName, levelParams := recLevelParams, type, value }

def hintsFor (v : Expr) : GenM ReducibilityHints := do
  return .regular (getMaxHeight (← getEnv) v + 1)

/-- Trusted-install a generated declaration in the disposable construction
environment. Exact serialized records cross the optional kernel boundary only
once, when their completed island closes.

**A declaration the construction environment accepts but then loses is a
decline.** `Environment.addDeclCore` installs the declaration and afterwards
registers each name in the *async* constant map, which keys on
`privateToUserName` — the name with its private prefix stripped.
`AsyncConsts.add` `panic!`s on a duplicate normalized name and returns the map
**unchanged**, so the constant is in the trusted construction map and invisible to
`Environment.find?`. That is not survivable here: `MetaM`'s `inferType` goes
through `find?`, so the very next declaration that names the lost one dies with
`Unknown constant` — an exit 3, the tool's own failure, with nothing emitted.

It is our own names that collide. An export is many modules flattened into one
file, so it can hold both `_private.M.0.X` and a public `X`; we model both, and
`_private.M.0.X._model.self` and `X._model.self` normalize alike. Checking
membership *after* the add catches it however the two are ordered, which no
check on the name alone can do — neither ordering has the other's name in hand
at the time. Costs one map lookup per emitted name.

`Declaration.getNames` omits the auxiliary recursors the kernel computes for
nested inductives, which are legitimately absent from `find?`; that is exactly
the set this must not ask about, and it is why the loop is over `getNames`
rather than over the environment's diff. -/
def addChecked (d : Declaration) : GenM Unit := do
  -- This is the disposable construction view, not the generated kernel gate.
  -- Exact emitted records are checked once at the island boundary when
  -- `typeCheckGenerated` is enabled; construction declarations are otherwise
  -- trusted in exactly the same way as replayed input declarations.
  match (← getEnv).addDeclCore 0 d none false with
  | .ok e =>
    setEnv e
    -- **`find?`, not `constants`.** `Environment.constants` is the trusted
    -- construction kernel map; `Environment.find?` also consults the async
    -- map used by MetaM, so it is the visibility boundary generation needs.
    -- The test suite's `runEnvProbe` pins the same distinction from the other
    -- side.
    for n in d.getNames do
      if ((← getEnv).find? n).isNone then
        declineWith (.nameLost n)
  | .error ex =>
    badShape s!"{d.getTopLevelNames} could not be installed for construction: \
      {← (ex.toMessageData {}).toString}"

/-- **The `Eq` the round trips are written at.** The input's own if it declares
one; Lean's, spliced in, if it does not.

An `Eq` the input *does* declare and that is not Lean's is the one case a
splice cannot reach — the name is already bound in the output and in the
input's own terms, and Lean's `Environment` cannot rebind a constant — so it
declines and says which part of the shape is wrong. -/
def ensureEq (reserved : Std.HashSet Name) : GenM (EqInfo × Array Declaration) := do
  if (← getEnv).constants.contains `Eq then
    match EqInfo.check (← getEnv) with
    | .ok e => return (e, #[])
    | .error why => declineWith (.notLeans `Eq why)
  -- **A name the file itself introduces later is not ours to write.** The
  -- guard is the same one the model's own names go through, and
  -- `test/fixtures/inductive-models/nested_keying.lean` is why it looks at the whole
  -- file rather than the prefix replayed so far.
  for n in [`Eq, `Eq.refl] do
    if reserved.contains n then declineWith (.nameTaken n)
  addChecked eqDecl
  match EqInfo.check (← getEnv) with
  | .ok e => return (e, #[eqDecl])
  | .error why => badShape s!"the spliced Eq is not Lean's ({why})"

/-- **The `funext` a packed position under a binder transports along**, and
whatever it takes to have one.

The input's own is used when it declares a `funext` at Lean's statement. When
it does not, this derives one from `Quot` (the kernel's quotient, four names)
and `Quot.sound` (Lean's axiom, at Lean's statement). Only the declarations the
input is missing are emitted; the completed exact island is kernel-checked iff
the generated-declaration gate is enabled.

`T._model.funext` is namespaced and the quotient names are not, and that
asymmetry is forced rather than chosen: standard-axiom recognition selects the
`Quot.sound` clause by that exact name, and the kernel fixes `Quot`,
`Quot.mk`, `Quot.lift` and `Quot.ind`, so a namespaced copy of either would be
refused downstream. `funext` is in no emitted statement at all, so it is free
to sit under the model's namespace — and that is where the collision was. -/
def ensureFunext (model : Name) (eqi : EqInfo) (reserved : Std.HashSet Name) :
    GenM (Name × Array Declaration) := do
  if let some n ← usableFunext? eqi then return (n, #[])
  let mut out : Array Declaration := #[]
  -- ── the quotient ──
  -- Recognised **structurally**, by the record kind the kernel gives it, and
  -- not by name.
  match (← getEnv).constants.find? `Quot with
  | some (.quotInfo _) => pure ()
  | some _ => declineWith (.notLeans `Quot "it is declared and is not the kernel's quotient type")
  | none =>
    for n in [`Quot, `Quot.mk, `Quot.lift, `Quot.ind] do
      if reserved.contains n then declineWith (.nameTaken n)
    addChecked .quotDecl
    out := out.push .quotDecl
  -- ── Quot.sound ──
  match (← getEnv).constants.find? `Quot.sound with
  | some ci =>
    let [su] := ci.levelParams
      | declineWith (.notLeans `Quot.sound
          s!"it has {ci.levelParams.length} level parameters, where Lean's has 1")
    unless ← isDefEq ci.type (← quotSoundType eqi.eqN (.param su)) do
      declineWith (.notLeans `Quot.sound "its statement is not Lean's")
  | none =>
    if reserved.contains `Quot.sound then declineWith (.nameTaken `Quot.sound)
    let d := Declaration.axiomDecl
      { name := `Quot.sound, levelParams := [`u], type := ← quotSoundType eqi.eqN (.param `u)
        isUnsafe := false }
    addChecked d
    out := out.push d
  -- ── funext, under the model's namespace ──
  let nm := Name.str model "funext"
  if reserved.contains nm || (← getEnv).constants.contains nm then declineWith (.nameTaken nm)
  let d ← funextDecl eqi nm
  addChecked d
  out := out.push d
  return (nm, out)

/-! ## The W core, spliced

The tagged W construction is the only thing this tool generates that it does not
*build*: `Wrec`'s well-founded recursion, `canon`, `sub_wf` and `Wrec_key` are
thirty-line tactic proofs over `List`, `Option`, `Sigma`, `Subtype`, `Acc` and
`WellFounded`, and writing them as `Expr` builders is not a bigger version of
what `Simple.lean` already does. So the construction's whole constant closure
is carried as an **export fragment** and spliced.

**It is spliced through [`InductiveModels.addChecked`] into the disposable
construction view.** That view is deliberately trusted: the exact records
serialized from the completed island are the sole generated kernel
boundary, and are checked there iff `--type-check-generated` is enabled.
Compiling the closure in and copying its `ConstantInfo`s would bypass that
exact emitted-record boundary. -/

/-- The fragment: what `lean4export` emits for `WT.W WT.sup WT.Wrec
WT.Wrec_iota instDecidableEqNat` over the W core. 528 KB, 163
records over 206 names — 19 inductive blocks, 78 definitions, 60 theorems, 4
quotient records and 2 axioms. It splices as **160** `Declaration`s, three
fewer than the record count, because the four quotient records are one
`Declaration.quotDecl`.

**The fifth root is the tag scheme's one demand on the fragment.** The generic
construction fixes `K := Nat` for every declaration rather than minting an
enumeration inductive per declaration, and the core's
`DecidableEq K` is then `instDecidableEqNat`. The closure of the other four
roots cannot reach it — all four take the instance as a *parameter* — so it has
to be named. It costs 11 ordinary declarations (`Nat.decEq`, `Nat.beq`'s two
soundness lemmas, the two `noConfusion` pairs and their match auxiliaries) and
**no new inductive**, which is what keeps the `w_core` test row unchanged:
the arm still leaves nothing unmodelled in front of a consumer.

`include_str` rather than a file read: it costs nothing at run time (the string
is in the binary's data), and the alternative — locating the `.ndjson` relative
to `IO.appPath` — would make the binary depend on its own build layout.

**And `include_str` is not in Lake's trace for this module.** Re-exporting
`test/fixtures/inductive-models/w_core.ndjson` and rebuilding leaves the binary carrying
the *previous*
fragment, with no diagnostic: `lake build` reports success, and neither a
`touch` nor a changed mtime forces the issue, because Lake hashes content and
the content it hashes is `Model.lean`'s. Measured, not inferred — a re-export
that added 11 declarations still spliced the old 149. The test suite's
`runWSpliceProbe` therefore compares this string against the file on disk, and
that comparison is the only thing standing between a fragment change and a
silently stale tool. -/
def wCoreText : String := include_str "../../test/fixtures/inductive-models/w_core.ndjson"

/-- Fixed public support which a generated model of the fragment's `Acc` may
use. The source fixture deliberately keeps some of these records after `Acc`
to exercise raw-input decline semantics; the embedded fragment is itself a
producer, so it must place the complete support before the generated owner. -/
private def wCoreModelReadinessNames : Array Name := #[
  `Quot, `Quot.mk, `Quot.lift, `Quot.ind, `Quot.sound,
  `Nonempty, `Nonempty.intro, `Nonempty.rec, `Classical.choice,
  `Iff, `Iff.intro, `Iff.rec, `propext]

/-- Producer-local order for the embedded fragment. Preserve the entire raw
prefix and the relative order of every record; only readiness records that the
fixture intentionally placed after `Acc` move to the boundary immediately
before its complete inductive record. This is not a general output reorder. -/
private def wCoreGenerationOrder (declarations : Array EDecl) : Except String (Array EDecl) := do
  let some accIndex := declarations.findIdx? (fun declaration =>
      declaration.names.contains `Acc)
    | throw "the W core fragment has no Acc declaration"
  for name in wCoreModelReadinessNames do
    unless declarations.any (fun declaration => declaration.names.contains name) do
      throw s!"the W core fragment has no model-readiness declaration {name}"
  let prefix := declarations.extract 0 accIndex
  let tail := declarations.extract accIndex declarations.size
  let isReadiness := fun declaration =>
    declaration.names.any wCoreModelReadinessNames.contains
  let readiness := tail.filter isReadiness
  let remainder := tail.filter fun declaration => !isReadiness declaration
  return prefix ++ readiness ++ remainder

/-- The prefix every fragment name gets, bar the shared ones below. The
fragment's names are Lean core's, so splicing its `List` into an input that
already declares one is a kernel rejection; prefixing makes the core
self-contained and costs only duplicates. -/
def wCoreRoot : Name := `_wcore

/-- **The twenty names the fragment shares with the input under Lean's own —
and the list is exactly these because of what the three axioms' statements
mention.**

The first version of this list had six names: the four quotient names, which
the kernel special-cases, and `Quot.sound` and `propext`, which standard-axiom
recognition selects **by exact name**. A namespaced copy is therefore a
non-standard axiom. That much is right and unchanged.

What the sizing missed is that an axiom's *statement* is renamed too. The
fragment's `Quot.sound` mentions `Eq`, `Quot` and `Quot.mk`; its `propext`
mentions `Eq` and `Iff`. Prefixing `Eq` and `Iff` while sharing the two axiom
names would emit

```text
propext    : ∀ {a b : Prop}, _wcore.Iff a b → _wcore.Eq a b
Quot.sound : ∀ {α r a b}, r a b → _wcore.Eq (Quot.mk r a) (Quot.mk r b)
```

— two axioms **under Lean's exact names whose statements are not Lean's**. On
an input that declares `propext` (which is every real one) that is a kernel
rejection and the arm reaches nothing; on an input that does not, it is worse
than a decline, because the name is what recognition keys on and it would take
a statement that is not `propext`'s as the standard `propext` clause. So `Eq`
and `Iff` are shared for the same reason the axioms are, one level down.

Sharing `Eq` also *removes* work rather than adding it: a renamed `Eq` would
cost one `_wcore.Eq → Eq` conversion per ι rule. At the shared `Eq`, the
fragment's `Wrec_iota` and the contract's ι
theorems are already the same equality.

**`Nat` is the fourth shared root, and the kernel forces that one outright.**
The fragment holds two `Expr.lit (.natVal _)`, and a literal's type is the
kernel's own `Nat` by fiat — nothing renames it. A prefixed `_wcore.Nat` leaves
`_wcore.Bool.ctorIdx` returning it while the literal in its body is at `Nat`,
and that is `(kernel) unknown constant 'Nat'`. Sharing costs nothing anyone
was counting on: `Nat` is already one of [`InductiveModels.inductiveBasis`]'s four, so it
was never going to be modelled, and sharing it takes an unmodelled inductive
*out* of the output rather than putting one in. `Nat.beq` and the rest of the
namespace stay prefixed — they are ordinary definitions and only the type
former and its two constructors are what the literal needs.

Everything else stays prefixed, and that is deliberate down to the
sub-namespaces: the fragment carries `Eq.symm`, `Eq.mpr`, `Eq.subst`,
`Quot.liftOn`, `Nat.brecOn` and nine more under those roots, and sharing
*those* would redeclare constants a real input has. The list is names, not
prefixes.

**`Classical.choice` is the third axiom and `Nonempty` is its `Iff`.** The
untagged instantiation of the W core decides equality at the label
with `Classical.propDecidable`, so the fragment's closure now reaches
`Classical.choice` — and standard-axiom recognition selects it by that exact
name, so
a `_wcore.Classical.choice` is a non-standard axiom and is declined downstream.
Its *statement* is `∀ {α : Sort u}, Nonempty α → α`, and the same argument one
level down puts `Nonempty` and its two names here beside `Iff`'s: a
`Classical.choice` under Lean's name whose antecedent is `_wcore.Nonempty`
would be worse than a decline, because the name is what the clause keys on.
Everything else the closure gained — `Classical.em`, `Classical.propDecidable`,
`Classical.choose` and twenty more — is an ordinary declaration and stays
prefixed. -/
def wCoreShared : Std.HashSet Name := Std.HashSet.ofList
  [`Eq, `Eq.refl, `Eq.rec, `Iff, `Iff.intro, `Iff.rec,
   `Quot, `Quot.mk, `Quot.lift, `Quot.ind, `Quot.sound, `propext,
   `Nat, `Nat.zero, `Nat.succ, `Nat.rec,
   `Classical.choice, `Nonempty, `Nonempty.intro, `Nonempty.rec]

/-- One fragment name as it is spliced. -/
def wCoreName (n : Name) : Name := if wCoreShared.contains n then n else wCoreRoot ++ n

/-- The same, inside an expression — constant heads **and** the `typeName` of
every `Expr.proj`, which is what [`InductiveModels.mapConstsE`] exists for. The
fragment is a *closure*, every constant it mentions is one of its own 195
names, so rewriting every one is right and there is nothing else it could
refer to. -/
def wCoreExpr (e : Expr) : Expr :=
  mapConstsE (fun n => if wCoreShared.contains n then none else some (wCoreRoot ++ n)) e

/-- The carrier the fragment defines, `WT.W` under the prefix. Doubles as the
**sentinel**: once the reserved-name guard below has passed, nothing but this
function can have put it in the environment, so its presence means the fragment
is already spliced and this run must not splice it twice. -/
def wCoreSelf : Name := wCoreRoot ++ `WT.W

/-- Names whose generated declarations are reusable support rather than part
of one model's disposable implementation forest.  These are exact fixed
interfaces (or the fixed `_wcore` namespace); declaration-local funext and
arm-C skeleton names deliberately do not qualify. Callers must additionally
require an explicit [`Iso.spliced`] witness: this namespace predicate alone is
not ownership evidence. -/
def persistentSupportRoot (name : Name) : Bool :=
  [`Eq, `Nat, `PSigma', `PUnit, `Nonempty, `Iff, `Quot].contains name

def persistentSupportName (name : Name) : Bool :=
  persistentSupportRoot name ||
    (`PSigma').isPrefixOf name ||
    (`PUnit).isPrefixOf name ||
    [`Quot.mk, `Quot.lift, `Quot.ind, `Quot.sound,
      `Classical.choice, `propext].contains name ||
    wCoreRoot.isPrefixOf name
/-- `WT.sup` under the prefix — the node former. -/
def wCoreSup : Name := wCoreRoot ++ `WT.sup
/-- `WT.Wrec` under the prefix — the large recursor. -/
def wCoreRec : Name := wCoreRoot ++ `WT.Wrec
/-- `WT.Wrec_iota` under the prefix — its one ι rule. -/
def wCoreIota : Name := wCoreRoot ++ `WT.Wrec_iota
/-- **The `DecidableEq K` every one of the four takes as a parameter**, at the
one `K` the scheme uses. Prefixed like any other ordinary definition: the
instance is not a name anything downstream keys on, unlike the axioms, and a
`_wcore` copy of it cannot collide with an input that has its own. -/
def wCoreDecEqNat : Name := wCoreRoot ++ `instDecidableEqNat
/-- **`DecidableEq` at any type at all** — `Classical.propDecidable` behind one
name, and the untagged instantiation's entire price.
Prefixed for the same reason `instDecidableEqNat` is; what may *not* be
prefixed is the `Classical.choice` underneath it, which is why that name is on
[`InductiveModels.wCoreShared`]. -/
def wCoreDecEqAll : Name := wCoreRoot ++ `WT.decEqAll
/-- **`funext` under the prefix** — the arm's one per-constructor cost, and the
reason it is taken from the fragment rather than derived beside the model:
[`InductiveModels.funextDecl`] would splice a second `funext` at the same `Eq`, and
the fragment already carries Lean's own (`WT.mk_sub` and `WT.canon` use it) at
the *shared* `Eq`, so the eta lemma and the contract's ι theorems are one
equality throughout. Prefixed like any other ordinary definition: nothing
downstream keys on the name. -/
def wCoreFunext : Name := wCoreRoot ++ `funext

/-- **The W core in the environment, and the declarations that had to be added
to put it there** — `#[]` when it is already in, which is every call after the
first in a run.

Three things can happen to a fragment record:

* every name it introduces is already in the environment — it is one of the
  shared twelve and the input had it, so it is the *input's* and this skips it;
* it is new — the reserved guard runs and it is installed in the disposable
  construction environment;
* some of its names are present and some are not, which can only happen to a
  shared declaration and means the input has half of a quotient or of `Eq`.
  That is a shape this cannot repair, and it says so.

**No shared declaration is separately checked against Lean's statement, and it
does not need to be.** If the input's `Eq` or `Iff` or `propext` is not Lean's,
the fragment's 200-odd proofs are stated and proved against it. With output
checking enabled, the exact generated island is then checked once at its close
boundary. -/
def ensureWCore (reserved : Std.HashSet Name) : GenM (Array Declaration) := do
  if (← getEnv).constants.contains wCoreSelf then return #[]
  let ex ←
    match InductiveModels.parse wCoreText with
    | .ok ex => pure ex
    | .error msg => badShape s!"the W core fragment does not parse ({msg})"
  let declarations ← match wCoreGenerationOrder ex.decls with
    | .ok declarations => pure declarations
    | .error msg => badShape msg
  let mut out : Array Declaration := #[]
  for d0 in declarations do
    let d := EDecl.mapNames wCoreName wCoreExpr d0
    let ns := d.names
    let env ← getEnv
    let present := ns.filter (env.constants.contains ·)
    if !present.isEmpty then
      unless ns.all wCoreShared.contains do
        badShape s!"the W core's {ns} would redeclare {present}"
      continue
    -- **A name the input introduces later is not ours to write**, exactly as
    -- in [`InductiveModels.ensureEq`], and for the shared twelve as much as for the
    -- prefixed rest: `reserved` is the whole file's names, so this is the
    -- case where the input declares `propext` below the target being modelled.
    for n in ns do
      if reserved.contains n then declineWith (.nameTaken n)
    if let some dcl := toDeclaration env d then
      addChecked dcl
      out := out.push dcl
  return out

/-- **The ι rules of one member's recursor**, one per rule `Bₖ.rec` carries, in
the order it carries them.

Each comes back as `(the export's constructor, the theorem's name, the
theorem)`. The constructor is the key the *installed* `T.rec_k` files its rule
under — `Tree.node` at the root, `List.cons` at a mimic — so a consumer can line
the two up without knowing how the block was named. -/
def Gen.iotaDecls (g : Gen) (sh : Gen.RecShape) (ctorTys : Array (Name × Name × Expr))
    (sourceRecursor? : Option ERec := none) (exactSource : Expr → Expr := id) :
    GenM (Array (Name × Name × Declaration)) := do
  let minorBase := (Array.range sh.k).foldl (fun a i => a + g.blockCtors[i]!.size) 0
  -- The export's constructors are flattened in `all` order, so a **real**
  -- member's `j`-th is at this offset; a mimic's key is the real container's.
  let ctorBase := (Array.range (min sh.k g.numAll)).foldl
    (fun a i => a + g.blockCtors[i]!.size) 0
  let cs := g.blockCtors[sh.k]!
  (Array.range cs.size).mapM fun j =>
    forallBoundedTelescope sh.ty (some (g.np + sh.nm + sh.nmin)) fun pre _ => do
      let ps := pre.extract 0 g.np
      let motives := pre.extract g.np (g.np + sh.nm)
      let minors := pre.extract (g.np + sh.nm) pre.size
      let bcn := cs[j]!
      let key : Name × Name × List Level × Array Expr × Expr ←
        if g.isReal sh.k then do
          let (exportC, modelC, mty) := ctorTys[ctorBase + j]!
          pure (exportC, modelC, g.us, ps, ← instForall mty ps)
        else do
          let real ← g.realCtor (g.mimicOf sh.k) ps bcn
          let (_, cls, qs) ← g.container (g.mimicOf sh.k) ps
          pure (real, real, cls, qs, ← instCtor real cls qs)
      let (exportKey, head, hls, hpre, ectorTy) := key
      withFields ectorTy fun fields extTys => do
        -- Open the block constructor at the **same field variables** as the
        -- export constructor. Opening it independently and returning its
        -- field types leaks temporary binders whenever a later field type
        -- depends on an earlier one (`C.step`'s nested field is indexed by its
        -- preceding `j`). Those leaked variables made the generated iota
        -- theorem fail the kernel's closedness check.
        let blkTys ← fieldTypesAt (← instCtor bcn g.us ps) fields
        if fields.size != blkTys.size then
          badShape s!"{bcn}: the export binds {fields.size} fields, the block {blkTys.size}"
        let mem := blkTys.map g.memberOf
        let packed ← blkTys.mapM g.mimicUnder?
        -- **The hypothesis vector, in the minor's own order.** `Bₖ.rec` gives a
        -- field of type `∀ x⃗, Bₘ …` an induction hypothesis too — Lean supports
        -- infinitary constructors and `FTree.branch : (N → FTree) → FTree` is
        -- one — so the vector has an entry for it and the right-hand side below
        -- writes `fun x⃗ => T._model.rec_m … (f x⃗)` there.
        let (ihAt, _) ← g.ihVector blkTys
        let moving := (Array.range blkTys.size).filter fun x => packed[x]!.isSome
        -- **The hypothesis types, read off the minor and not rebuilt.** The
        -- minor binds the export-side fields, so instantiating it at `fields`
        -- leaves the hypothesis telescope in their terms; taking the binder
        -- names from there is what makes `fun (a_1 : N) => rec_0 … (a a_1)`
        -- compare equal to the rule the export carries.
        let minorIx := minorBase + j
        let nIh := (ihAt.filter (·.isSome)).size
        let ihTyVec ← forallBoundedTelescope
          (← instantiateForall (← ityp minors[minorIx]!) fields) (some nIh)
          fun vs _ => vs.mapM ityp
        let mut ihTys : Array (Option Expr) := #[]
        let mut t := 0
        for a in ihAt do
          if a.isSome then ihTys := ihTys.push ihTyVec[t]?; t := t + 1
          else ihTys := ihTys.push none
        let r : Rule :=
          { g, k := sh.k, v := sh.v, ps, motives, minors, minorIx
            head, headLevels := hls, headPrefix := hpre
            fields, extTys, bcn, blkTys, mem, packed, ihAt, ihTys, moving }
        let tel := pre ++ fields
        let installedStatement ← r.statement
        let (statement, fieldTelescope, recursorTelescope) ← match sourceRecursor? with
          | none => pure (installedStatement, ectorTy, sh.ty)
          | some sourceRecursor => do
            let some sourceRule := sourceRecursor.rules[j]?
              | badShape s!"{sourceRecursor.name} has no exported rule {j}"
            unless sourceRule.ctor == exportKey do
              badShape s!"{sourceRecursor.name}'s exported rule {j} is for {
                sourceRule.ctor}, not {exportKey}"
            unless sourceRule.nfields == fields.size do
              badShape s!"{sourceRecursor.name}'s exported rule {j} has {
                sourceRule.nfields} fields, not {fields.size}"
            let some exactFields := exactRecursorFieldTelescope? sourceRecursor j pre
              | badShape s!"{sourceRecursor.name}'s exported rule {j} has no exact field telescope"
            let equality := installedStatement.getAppFn
            let arguments := installedStatement.getAppArgs
            unless arguments.size == 3 do
              badShape s!"{g.iotaName sh.k j}'s installed statement is not a binary equality"
            let rhs := (exactSource sourceRule.rhs).beta (pre ++ fields)
            pure (mkAppN equality #[arguments[0]!, arguments[1]!, rhs],
              exactSource exactFields, exactSource sourceRecursor.type)
        let some fieldsType := closeForallsExact? fieldTelescope fields statement
          | badShape s!"{head}'s exact exported telescope has fewer fields than its installed type"
        let some ty := closeForallsExact? recursorTelescope pre fieldsType
          | badShape s!"{sh.src}'s exact exported telescope is shorter than its recursor prefix"
        let val ← mkLambdaFVars tel (← r.value)
        let nm := g.iotaName sh.k j
        return (exportKey, nm,
          .thmDecl { name := nm, levelParams := sh.lparams, type := ty, value := val })

/-- **The mimics, grouped into strongly connected components and put in an
order that emits a group's dependencies before it.**

Assuming that nesting strictly decreases would imply a topological order, but
that is false in two different ways, and the second is the one that
matters:

* **A backward edge without a cycle.** Discovery is breadth first, so a mimic
  may perfectly well mention one discovered before it. Descending index is then
  not a topological order, and the check this replaces called that a cycle.
* **A real cycle.** `T` nests into `Tree T`; `Tree`'s own `node` field is `List
  (Tree T)`; *that* copy's `cons` head is `Tree T` again. `pack₀` and `pack₁`
  are mutually recursive and **no** emission order exists for them one at a
  time.

A group of size one is emitted the way it always was. A larger one is one
simultaneous recursion, and [`InductiveModels.familyFor`] finds the recursors Lean
already generated for it. -/
def mimicGroups (pl : Plan) : Except String (Array (Array Nat)) := Id.run do
  let m := pl.mimics.size
  let r := pl.numAll
  let mut adj : Array (Array Bool) := Array.replicate m (Array.replicate m false)
  for i in [0:m] do
    for (_, cty) in pl.types[i + r]!.ctors do
      for j in [0:m] do
        if j != i && mentions pl.mimics[j]!.name cty then
          adj := adj.modify i (·.set! j true)
  -- Reachability, and then mutual reachability: the components.
  let mut re := adj
  for k in [0:m] do
    for i in [0:m] do
      if re[i]![k]! then
        for j in [0:m] do
          if re[k]![j]! then re := re.modify i (·.set! j true)
  let mut seen : Array Bool := Array.replicate m false
  let mut groups : Array (Array Nat) := #[]
  for i in [0:m] do
    unless seen[i]! do
      let mut grp := #[i]
      seen := seen.set! i true
      for j in [i + 1:m] do
        if !seen[j]! && re[i]![j]! && re[j]![i]! then
          grp := grp.push j
          seen := seen.set! j true
      groups := groups.push grp
  -- The condensation is a DAG; emit a group only once everything it depends on
  -- has been emitted.
  let ng := groups.size
  let dependsOn := fun (a b : Nat) =>
    groups[a]!.any fun i => groups[b]!.any fun j => adj[i]![j]!
  let mut order : Array (Array Nat) := #[]
  let mut placed : Array Bool := Array.replicate ng false
  for _ in [0:ng] do
    for a in [0:ng] do
      if !placed[a]! then
        if (Array.range ng).all fun bb => bb == a || placed[bb]! || !dependsOn a bb then
          order := order.push groups[a]!
          placed := placed.set! a true
          break
  if order.size != ng then return .error "the mimic condensation graph is cyclic"
  return .ok order

/-- **Build the model, or say which shape stopped it.**

Generated declarations are first installed through [`InductiveModels.addChecked`]
in the disposable construction view. The exact serialized island is checked
once at its close boundary iff generated kernel checking is enabled. -/
def iso (all : Array Name) (lparams : List Name) (numParams : Nat)
    (exportCtors : Array (Array (Name × Expr))) (exportRecursors : Array ERec) (pl : Plan)
    (reserved : Std.HashSet Name) (buildRoot? : Option Name := none) : GenM Iso := do
  -- **The declaration's own level parameters are carried, not refused.** Every
  -- generated constant is declared at `lparams` and referenced at `us`; a
  -- recursor is declared at its motive universe *followed by* `lparams`, which
  -- is the order Lean itself writes.
  -- `test/fixtures/inductive-models/poly_nested.lean` is the fixture, and it
  -- is arranged so that a generator writing a container's *declared* parameter
  -- where the occurrence's instantiation belongs cannot pass.
  let us := lparams.map Level.param
  let np := numParams
  let r := pl.numAll
  let some root := all[0]? | badShape "the declaration has no members"
  let buildRoot := buildRoot?.getD root
  let some rootT := pl.types[0]? | badShape "the plan has no members"
  -- The block's resultant sort and each member's index count. **The
  -- declaration's indices are carried**: what is left after the parameters is
  -- an index telescope, and every index vector in the model is read off a type
  -- in hand rather than rebuilt. **Every real member's sort, not just the
  -- first's**: a mutual block whose members land at different sorts would give
  -- `Eq` two universes and one `g.u` to write them at.
  let sortOf : Expr → GenM (Nat × Level) := fun t => do
    let mut cur := t
    for _ in [0:np] do
      match cur with
      | .forallE _ _ b _ => cur := b
      | _ => badShape "the declaration has fewer binders than parameters"
    let mut ni := 0
    repeat
      match cur with
      | .forallE _ _ b _ => cur := b; ni := ni + 1
      | _ => break
    let .sort u := cur | badShape "a block member does not land in a sort"
    return (ni, u)
  let nidx ← pl.types.mapM fun t => do return (← sortOf t.type).1
  let u := (← sortOf rootT.type).2
  for k in [0:r] do
    unless (← sortOf pl.types[k]!.type).2 == u do
      badShape "a mutual block whose members land at different sorts"
  let primaryCarrier := Naming.modelName buildRoot
  let exactPrimaryCarrier := Naming.modelName root
  let model := Name.str primaryCarrier "_impl"
  let b := fun (i : Nat) => Name.num model i
  let exportCtorNames := exportCtors.flatMap fun ctors => ctors.map (·.1)
  let exportRecs := (Array.range pl.types.size).map (exportRecName all)
  -- **One carrier per real member.** `A.rec` and `B.rec` are distinct
  -- recursors over distinct majors, and a consumer keys `⟦A⟧` and `⟦B⟧`
  -- separately; a single carrier could stand for only one of them. For a
  -- one-member block this is exactly `T._model`.
  let selfNames := all.extract 0 r |>.map fun n =>
    Naming.modelName (Naming.relocateSource root buildRoot n)
  let blockCtors := (Array.range pl.types.size).map fun i =>
    pl.types[i]!.ctors.map fun (cn, _) => Name.str (b i) (lastStr cn)

  -- The public contract is declaration-local. Census its exact names as one
  -- atomic request, including every nested recursor's rule theorems, before
  -- adding any implementation declaration to the environment.
  let mut publicNames : Naming.Table := .empty
  for name in all.extract 0 r do
    publicNames := publicNames.addDeclaration .typeFormer name
  for name in exportCtorNames do
    publicNames := publicNames.addDeclaration .constructor name
  for k in [0:exportRecs.size] do
    publicNames := publicNames.addRecursor exportRecs[k]! pl.types[k]!.ctors.size
    if (exportRecursors.find? (·.name == exportRecs[k]!)).any (·.k) then
      publicNames := publicNames.addMetadata .ruleK exportRecs[k]!
  let mut helpers : Array Name := (Array.range pl.types.size).map b
  helpers := helpers ++ blockCtors.flatten
  for k in [0:pl.types.size] do helpers := helpers.push (Name.str (b k) "rec")
  for i in [0:pl.mimics.size] do
    for suffix in [s!"pack_{i}", s!"unpack_{i}", s!"unpackPack_{i}",
        s!"packUnpack_{i}", s!"congrPack_{i}"] do
      helpers := helpers.push (Name.str model suffix)
  helpers := helpers.push (Name.str model "funext")
  let exactHelper := fun n =>
    if primaryCarrier.isPrefixOf n then n.replacePrefix primaryCarrier exactPrimaryCarrier else n
  let helperNames := helpers.foldl
    (fun names helper => names.insert (exactHelper helper)) ({} : Std.HashSet Name)
  let census := publicNames.collisionCensusReservedWith reserved helperNames
  if let some name := census.duplicateRequirements[0]? then
    badShape s!"the public naming contract requires {name} more than once"
  if let some name := census.taken[0]? then declineWith (.nameTaken name)
  for name in publicNames.requiredNames do
    if (← getEnv).constants.contains name then declineWith (.nameTaken name)
  -- **The whole file, not just the prefix.** A contract name may be declared
  -- after its source declaration. A guard that only looked at the environment
  -- as it stands would then emit a duplicate declaration.
  let taken : Name → GenM Unit := fun n => do
    let exact := exactHelper n
    if reserved.contains exact || (← getEnv).constants.contains exact then
      declineWith (.nameTaken exact)
    if buildRoot != root && (reserved.contains n || (← getEnv).constants.contains n) then
      declineWith (.nameTaken n)
  for i in [0:pl.types.size] do taken (b i)
  for n in selfNames do taken n
  -- **The `Eq` first, because everything downstream is written at it** — and
  -- spliced in when the input has none, which is the whole of what
  -- `test/fixtures/inductive-models/decline_no_eq.lean` used to refuse. It goes at the
  -- head of `out`, ahead
  -- of the block, so that it precedes its first use in the round trips no
  -- matter how the rest of the emission is ordered.
  let (eqi, eqDecls) ← ensureEq reserved
  let mut out : Array Declaration := eqDecls
  let mut spliced : Array Name := eqDecls.flatMap (·.getNames.toArray)

  -- ── 1. the block, renamed ──────────────────────────────────────────────
  --
  -- Member 0 is the export's own `T` and must not keep that name: `T` is a
  -- primitive inductive in the caller's environment and this development is
  -- about a different constant.
  let ren : Std.HashMap Name (Nat × Expr) :=
    (Array.range pl.types.size).foldl
      (fun m i => m.insert pl.types[i]!.name (0, .const (b i) us)) {}
  let its : List InductiveType := (Array.range pl.types.size).toList.map fun i =>
    { name := b i, type := pl.types[i]!.type
      ctors := (Array.range pl.types[i]!.ctors.size).toList.map fun j =>
        { name := blockCtors[i]![j]!, type := restore ren pl.types[i]!.ctors[j]!.2 } }
  let blockDecl := Declaration.inductDecl lparams np its false
  addChecked blockDecl
  out := out.push blockDecl

  -- ── 2. the carriers, one per real member ───────────────────────────────
  let b0ty := (← constInfo (b 0)).type
  let withParams := fun {α : Type} (k : Array Expr → GenM α) =>
    forallBoundedTelescope b0ty (some np) fun ps _ => k ps
  for k in [0:r] do
    let carrier ← withParams fun ps => mkLambdaFVars ps (mkAppN (.const (b k) us) ps)
    let selfDecl := Declaration.defnDecl
      { name := selfNames[k]!, levelParams := lparams, type := pl.types[k]!.type, value := carrier
        hints := ← hintsFor carrier, safety := .safe }
    addChecked selfDecl
    out := out.push selfDecl

  -- Every occurrence, with the export's own members rewritten to their carriers.
  let toSelf : Std.HashMap Name (Nat × Expr) :=
    (Array.range r).foldl (fun m k => m.insert all[k]! (0, .const selfNames[k]! us)) {}
  let occs := pl.mimics.map fun m => restore toSelf m.occ
  -- **Does the block support large elimination?** Read off the recursor Lean
  -- just minted for it rather than inferred from the sort: `Eq` is `Prop` and
  -- has a motive universe, `S : Prop | mk : PL S → S` is `Prop` and has none.
  let largeElim ← do
    let .recInfo rv ← constInfo (.str (b 0) "rec") | badShape "the block has no recursor"
    pure (rv.levelParams.length == us.length + 1)
  let g0 : Gen := { owner := root, buildOwner := buildRoot,
                    model, exportCtors := exportCtorNames, exportRecs,
                    selfNames, numAll := r, np, u, us
                    members := (Array.range pl.types.size).map b
                    blockCtors, nidx, occs, eqi, fx := none, largeElim }

  -- **Dependent fields, checked once and only where they bite.** Every
  -- congruence fold in this file moves the *packed* positions of one of the
  -- block's constructors, so the condition is the same for all of them and is
  -- settled here rather than at each telescope: no field's type may mention an
  -- earlier field the block holds at a mimic. See [`InductiveModels.noDepOnPacked`].
  --
  -- **And whether any packed position sits under a binder**, which is the one
  -- shape whose proofs need `funext`: the block types such a field `∀ x⃗, Bₘ ι⃗`
  -- and the round trips, the recursor's minor and the ι rules all transport
  -- along `(fun x⃗ => pack (unpack (f x⃗))) = f`. `funext` is read from the
  -- export **only when a declaration has such a field** — it is in no public
  -- statement, only in these proofs, so requiring it of every export would
  -- decline every otherwise-supported declaration. Lean accepts all three places
  -- the binder can sit: the root (`HTree`), the container's own recursive
  -- field (`RTree` over `Rose`) and a container's field into another mimic
  -- (`OTree` over `Outer`), and `test/fixtures/inductive-models/infinitary.lean` has all
  -- three.
  let anyUnderBinder ← withParams fun ps => do
    let mut any := false
    for k in [0:pl.types.size] do
      for cn in blockCtors[k]! do
        any := any || (← forallTelescope (← instCtor cn us ps) fun fs _ => do
          let tys ← fs.mapM ftyp
          -- **The positions the folds move**, which is
          -- [`InductiveModels.Gen.mimicUnder?`] and not a bare head test: a field at a
          -- mimic under a binder is one, and so is the redex `(fun x => Bₘ) k`
          -- a family parameter leaves behind. Both questions below are about
          -- that same set, so both read it the same way.
          let under ← tys.mapM g0.mimicUnder?
          let packed := (Array.range fs.size).filterMap fun x =>
            if under[x]!.isSome then some fs[x]! else none
          noDepOnPacked packed fs tys
          -- A binder, and only a binder, costs a `funext`; `nb = 0` — including
          -- the redex, which reduces to the mimic with no telescope at all —
          -- writes no lambda and transports nothing pointwise.
          return under.any fun u => (u.getD (0, 0)).2 > 0)
    return any
  let (fxName?, fxDecls) ←
    if anyUnderBinder then do
      let (n, ds) ← ensureFunext model eqi reserved
      pure (some n, ds)
    else pure (none, #[])
  for d in fxDecls do
    out := out.push d
    spliced := spliced ++ d.getNames.toArray
  let g : Gen := { g0 with fx := fxName? }
  -- Raw public recursor syntax names the original declaration.  Rewrite only
  -- those constant names: unlike `restore`, `mapConstsE` retains every level
  -- expression on the occurrence itself. Installed block names remain the
  -- proof/layout oracle and never enter this public statement map.
  let mut sourceNames : Std.HashMap Name Name := {}
  for k in [0:r] do sourceNames := sourceNames.insert all[k]! selfNames[k]!
  for j in [0:exportCtorNames.size] do
    sourceNames := sourceNames.insert exportCtorNames[j]! (g.ctorName j)
  for k in [0:exportRecs.size] do
    sourceNames := sourceNames.insert exportRecs[k]! (g.recName k)
  let exactSource := mapConstsE (fun name => sourceNames[name]?)

  -- ── 3. pack, unpack, and the two round trips, group by group ───────────
  --
  -- **A group of mimics, not a mimic.** `packᵢ` for a container whose field is
  -- another occurrence calls that occurrence's `pack`, so the emission has to
  -- follow the dependency order — and when the dependency is *mutual*, no such
  -- order exists and the group is one simultaneous recursion instead
  -- ([`InductiveModels.mimicGroups`], [`InductiveModels.familyFor`]). Only `pack` and the
  -- retraction change: `unpack` never calls another `unpack`, and the section
  -- already goes through the block's own recursor, which does every member at
  -- once.
  let groups ← match mimicGroups pl with
    | .ok gs => pure gs
    | .error message => badShape message
  let mut done := Array.replicate pl.mimics.size false
  let emit := fun (nm : Name) (ty val : Expr) (isThm : Bool) => do
    let hint ← hintsFor val
    let d : Declaration :=
      if isThm then .thmDecl { name := nm, levelParams := lparams, type := ty, value := val }
      else .defnDecl { name := nm, levelParams := lparams, type := ty, value := val
                       hints := hint, safety := .safe }
    addChecked d
    return d
  for grp in groups do
    let solo := grp.size == 1
    for i in grp do
      for n in [g.packName i, g.unpackName i, g.retractName i, g.sectionName i] do taken n
    -- pack, every component of the group before anything reads one
    -- **The container's index telescope sits between `p⃗` and the argument**, in
    -- all five signatures, and is empty unless the container has indices — so
    -- nothing about an unindexed container's contract has moved.
    for i in grp do
      let (ty, val) ← withParams fun ps => do
        let ty ← g.withOccIndices i ps fun idxs =>
          mkForallFVars (ps ++ idxs)
            (.forallE `l (g.occAtIdx i ps idxs) (mkAppN (g.memAt (i + r) ps) idxs) .default)
        let val ← mkLambdaFVars ps (←
          if solo then g.packValue i (i + r) ps
          else do let f ← g.familyFor grp ps; g.packFamilyValue f (f.indexOf i) ps)
        return (ty, val)
      out := out.push (← emit (g.packName i) ty val false)
    for i in grp do
      let (ty, val) ← withParams fun ps => do
        let ty ← g.withIndices (i + r) ps fun idxs =>
          mkForallFVars (ps ++ idxs)
            (.forallE `b (mkAppN (g.memAt (i + r) ps) idxs) (g.occAtIdx i ps idxs) .default)
        let val ← mkLambdaFVars ps (← g.unpackValue (i + r) ps)
        return (ty, val)
      out := out.push (← emit (g.unpackName i) ty val false)
    for i in grp do
      let (ty, val) ← withParams fun ps => do
        let ty ← g.withOccIndices i ps fun idxs => do
          let occ := g.occAtIdx i ps idxs
          withLocalDeclD `l occ fun l =>
            mkForallFVars (ps ++ idxs ++ #[l])
              (eqi.mk' u occ
                (g.call (g.unpackName i) ps idxs (g.call (g.packName i) ps idxs l)) l)
        let val ← mkLambdaFVars ps (←
          if solo then g.retractValue i ps
          else do let f ← g.familyFor grp ps; g.retractFamilyValue f (f.indexOf i) ps)
        return (ty, val)
      out := out.push (← emit (g.retractName i) ty val true)
    -- The section is proved by the **block's** recursor, so the whole group is
    -- live at once and one call proves every component.
    let live := fun (k : Nat) =>
      !g.isReal k && (grp.contains (g.mimicOf k) || done[g.mimicOf k]!)
    for i in grp do
      let (ty, val) ← withParams fun ps => do
        let ty ← g.withIndices (i + r) ps fun idxs => do
          let mem := mkAppN (g.memAt (i + r) ps) idxs
          withLocalDeclD `b mem fun x =>
            mkForallFVars (ps ++ idxs ++ #[x])
              (eqi.mk' u mem
                (g.call (g.packName i) ps idxs (g.call (g.unpackName i) ps idxs x)) x)
        let val ← mkLambdaFVars ps (← g.sectionValue (i + r) ps live)
        return (ty, val)
      out := out.push (← emit (g.sectionName i) ty val true)
    for i in grp do done := done.set! i true

  -- ── 4. the declared type's own constructors ────────────────────────────
  --
  -- After the maps, because a field at a mimic is packed on the way in. The
  -- model's constructor carries the **export's** declared type with `T`
  -- rewritten to the carrier, so that the keying is an alias.
  --
  -- **Flattened over the real members, in the export's `all` order** so the
  -- constructor table remains aligned with the order of the block's minors.
  let mut ctors : Array (Name × Name) := #[]
  let mut ctorTys : Array (Name × Name × Expr) := #[]
  for k in [0:r] do
    for jj in [0:exportCtors[k]!.size] do
      let (cn, cty) := exportCtors[k]![jj]!
      let j := ctorTys.size
      let nm := g.ctorName j
      taken nm
      let ty := restore toSelf cty
      let val ← withParams fun ps => do mkLambdaFVars ps (← g.ctorValue k jj ty ps)
      let d := Declaration.defnDecl
        { name := nm, levelParams := lparams, type := ty, value := val
          hints := ← hintsFor val, safety := .safe }
      addChecked d
      out := out.push d
      ctors := ctors.push (cn, nm)
      ctorTys := ctorTys.push (cn, nm, ty)

  -- ── 5. one recursor per block member ───────────────────────────────────
  let mut heads : Std.HashMap Name (Nat × Expr) := {}
  for k in [0:r] do
    heads := heads.insert (b k) (0, .const selfNames[k]! us)
  for k in [0:r] do
    let base := (Array.range k).foldl (fun a i => a + exportCtors[i]!.size) 0
    for jj in [0:exportCtors[k]!.size] do
      heads := heads.insert (Name.str (b k) (lastStr exportCtors[k]![jj]!.1))
        (0, .const (g.ctorName (base + jj)) us)
  for i in [0:pl.mimics.size] do
    heads := heads.insert (b (i + r)) (np, occs[i]!)
    for (mc, real) in pl.mimics[i]!.ctors do
      -- The real constructor's own parameters mention the **export's** members,
      -- because the mimic table is built before the model exists.
      heads := heads.insert (Name.str (b (i + r)) (lastStr mc)) (np, restore toSelf real)
  for k in [0:pl.types.size] do
    taken (g.recName k)
    heads := heads.insert (Name.str (b k) "rec") (0, .const (g.recName k) us)
  let mut shapes : Array Gen.RecShape := #[]
  for k in [0:pl.types.size] do
    let sh ← g.recShape k heads
    let val ← g.recValue sh
    let d := Declaration.defnDecl
      { name := g.recName k, levelParams := sh.lparams, type := sh.ty, value := val
        hints := ← hintsFor val, safety := .safe }
    addChecked d
    out := out.push d
    shapes := shapes.push sh

  -- ── 6. the congruences the ι rules are stated along ────────────────────
  for i in [0:pl.mimics.size] do
    taken (g.congrPackName i)
    let (ty, val) ← withParams fun ps => g.congrPackDecl i ps
    let d := Declaration.thmDecl
      { name := g.congrPackName i, levelParams := lparams, type := ty, value := val }
    addChecked d
    out := out.push d

  -- ── 7. the ι rules themselves ──────────────────────────────────────────
  let mut iotas : Array (Nat × Name × Name) := #[]
  for k in [0:shapes.size] do
    -- Exact raw syntax is authoritative for the block's real public
    -- recursors. Nested mimic recursors have a different generated field/IH
    -- telescope; beta-applying the source rule to that telescope can shift a
    -- deeper container field (for example `DTree.rec_2`'s `List.cons`) into
    -- the element slot. Their installed statement is the public contract and
    -- was already constructed at the exact emitted names.
    let sourceRecursor? := if g.isReal k then
        exportRecursors.find? (·.name == exportRecs[k]!)
      else none
    for (key, nm, d) in ← g.iotaDecls shapes[k]! ctorTys sourceRecursor? exactSource do
      taken nm
      addChecked d
      out := out.push d
      iotas := iotas.push (k, key, nm)

  -- ── 8. K-like reduction at the constructor's index fiber ──────────────
  let mut ruleKs : Array (Name × Name) := #[]
  for k in [0:shapes.size] do
    let some exported := exportRecursors.find? (·.name == exportRecs[k]!)
      | badShape s!"the export has no recursor record for {exportRecs[k]!}"
    if exported.k then
      let sh := shapes[k]!
      let .recInfo rv ← constInfo sh.src | badShape s!"{sh.src} is not a recursor"
      unless rv.k do badShape s!"{exported.name} is K-like but {sh.src} is not"
      unless rv.rules.length == 1 do
        badShape s!"{sh.src} is K-like with {rv.rules.length} rules"
      let nm := g.ruleKName k
      taken nm
      let iotaType? := out.findSome? fun declaration => match declaration with
        | .thmDecl value => if value.name == g.iotaName k 0 then some value.type else none
        | _ => none
      let some iotaType := iotaType?
        | badShape s!"the K-like recursor {exported.name} has no iota theorem"
      let d ← ruleKDecl eqi sh.lparams (rv.numParams + rv.numMotives + rv.numMinors)
        nm iotaType
      addChecked d
      out := out.push d
      ruleKs := ruleKs.push (exported.name, nm)

  let mut aliases := Naming.AliasMap.empty
  if buildRoot != root then
    aliases := Naming.AliasMap.forRetry primaryCarrier (Naming.modelName root)
      (out.flatMap (·.getNames.toArray))
    for k in [0:r] do
      aliases := aliases.insert selfNames[k]! (Naming.modelName all[k]!)
    for j in [0:exportCtorNames.size] do
      aliases := aliases.insert (g.ctorName j) (Naming.modelName exportCtorNames[j]!)
    for k in [0:exportRecs.size] do
      aliases := aliases.insert (g.recName k) (Naming.modelName exportRecs[k]!)
      if (exportRecursors.find? (·.name == exportRecs[k]!)).any (·.k) then
        aliases := aliases.insert (g.ruleKName k) (Naming.ruleKName exportRecs[k]!)
      for j in [0:pl.types[k]!.ctors.size] do
        aliases := aliases.insert (g.iotaName k j) (Naming.iotaName exportRecs[k]! j)
  let containerImplementations ← (Array.range pl.mimics.size).mapM fun i => do
    let implementationCarrier := g.members[r + i]!
    let forward := g.packName i
    let backward := g.unpackName i
    let backwardForward := g.retractName i
    let forwardBackward := g.sectionName i
    return {
      parameterArity := np
      indexArity := g.midx i
      implementationCarrier
      forward
      backward
      backwardForward
      forwardBackward
      forwardType := (← constInfo forward).type
      backwardType := (← constInfo backward).type
      backwardForwardType := (← constInfo backwardForward).type
      forwardBackwardType := (← constInfo forwardBackward).type
      implementationCarrierType := (← constInfo implementationCarrier).type }
  return { decls := out, levelParams := lparams, members := g.members, selfNames
           numAll := r, ctors
           recs := (Array.range pl.types.size).map g.recName, iotas, ruleKs, spliced, aliases,
           containerImplementations }

end InductiveModels
