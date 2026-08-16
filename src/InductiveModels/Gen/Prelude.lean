import Lean
import InductiveModels.EqKit
import InductiveModels.Gen.Monad

/-!
# The prelude constants the proofs need, spliced when the input lacks them

`Eq`, `Quot.sound` and `funext` as Lean's own `Init` declares them, together
with the two `ensure*` entry points that hand a construction either the
input's own or a freshly spliced copy. Shared by all three constructions.
-/

open Lean Meta

namespace InductiveModels
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

/-- **The `Eq` the round trips are written at.** The input's own if it declares
one; Lean's, spliced in, if it does not.

An `Eq` the input *does* declare and that is not Lean's is the one case a
splice cannot reach — the name is already bound in the output and in the
input's own terms, and Lean's `Environment` cannot rebind a constant — so it
declines and says which part of the shape is wrong. -/
def ensureEq : GenM (EqInfo × Array Declaration) := do
  if (← getEnv).constants.contains `Eq then
    match EqInfo.check (← getEnv) with
    | .ok e => return (e, #[])
    | .error why => declineWith (.notLeans `Eq why)
  -- **A name the file introduces later is still ours to write here.** `Eq` is
  -- a canonical basis name: waiting for the input's own record would emit this
  -- island against a constant the output declares afterwards. The input's own
  -- later record is dropped against this declaration instead
  -- ([`InductiveModels.canonicalBasisRecordMatches`]).
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

end InductiveModels
