import Lean
import InductiveModels.Format
import InductiveModels.Gen.Monad

/-!
# The W core, spliced

The embedded `lean4export` fragment over the W type, and the splice that puts
it in the construction environment when a target needs it. The simple
construction's W arm is its main consumer; it is shared core rather than part
of any one rung.
-/

open Lean Meta

namespace InductiveModels
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
def wCoreText : String := include_str "../../../test/fixtures/inductive-models/w_core.ndjson"

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
  let rawPrefix := declarations.extract 0 accIndex
  let tail := declarations.extract accIndex declarations.size
  let isReadiness := fun declaration =>
    declaration.names.any wCoreModelReadinessNames.contains
  let readiness := tail.filter isReadiness
  let remainder := tail.filter fun declaration => !isReadiness declaration
  return rawPrefix ++ readiness ++ remainder

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
  [`Eq, `Nat, `PSigma', `PProd', `PUnit, `Nonempty, `Iff, `Quot].contains name

/-- **`PProd'` is listed by its exact members and not by its prefix**, unlike
`PSigma'` and `PUnit` above.  The binder-free pair is not a basis primitive, so
it is modelled like any other spliced inductive, and its model's public
interface is `PProd'._model`, `PProd'.mk._model`, `PProd'.rec._model` and their
ι rules — every one of them under the `PProd'` prefix.  A prefix test would
call that interface reusable shared support and retain it past its island,
which is what the `Iso.spliced` witness alone would not catch: the descent that
builds the model splices `Eq` and `PSigma'` under `PProd'`'s own name, so the
witness is present. -/
def persistentSupportName (name : Name) : Bool :=
  persistentSupportRoot name ||
    (`PSigma').isPrefixOf name ||
    (`PUnit).isPrefixOf name ||
    [`PProd'.mk, `PProd'.rec, `PProd'.rec',
      `Quot.mk, `Quot.lift, `Quot.ind, `Quot.sound,
      `Classical.choice, `propext].contains name ||
    wCoreRoot.isPrefixOf name
/-- `WT.sup` under the prefix — the node former. -/
def wCoreSup : Name := wCoreRoot ++ `WT.sup
/-- **`WT.root` under the prefix — the node's label, and the one part of a `W`
node that comes back out of it definitionally.**

`root w` is `(w.1 []).get (isSome_root w)`, and on a node it reduces by βιπ
alone: `(sup a f).1 []` is `mk tg a _ []`, whose `[]` arm is literally
`some a`, and `Option.get (some a) _` selects `a`. So `root (sup a f) ≡ a`
with no appeal to `WT.Wrec` and no transport — `test/fixtures/inductive-models/w_dependent_field.lean`
is the family that rests on it. The sibling `WT.kids` does **not** reduce this
way (`WT.kids_sup` is a theorem carrying a `cast`), which is exactly why arm W
selects its *stored* fields definitionally and its *children* through the
recursor. -/
def wCoreRootFn : Name := wCoreRoot ++ `WT.root
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
    -- **A name the input introduces later is not ours to write** — for the
    -- prefixed rest. The shared names are canonical basis names and are
    -- exactly the exception, as in [`InductiveModels.ensureEq`]: the fragment
    -- writes its `Iff` and `propext` here, at the point the target needs them,
    -- and the input's own later record is dropped against them
    -- ([`InductiveModels.canonicalBasisRecordMatches`]).
    for n in ns do
      if !wCoreShared.contains n && reserved.contains n then declineWith (.nameTaken n)
    if let some dcl := toDeclaration env d then
      addChecked dcl
      out := out.push dcl
  return out

end InductiveModels
