import InductiveModels.EqKit
import InductiveModels.Naming
import InductiveModels.Plan
import InductiveModels.Gen
import InductiveModels.Nested

/-!
# The model of a nested inductive, generated

**The first of three constructions in this package**, and the one that keeps mutuality:
the model of a nested declaration is a *mutual block* with one extra member per
nested occurrence. `src/InductiveModels/Mutual.lean` is the second and removes
mutuality; `src/InductiveModels/Simple.lean` reduces a single inductive to the fixed
basis. These are not one construction at three settings. What they share
is the interface, `Decline`, `EqInfo`, the
prelude splice, [`InductiveModels.Iso`], [`InductiveModels.modelTable`] and
[`InductiveModels.addChecked`], all of which live here — except `EqInfo`, which
lives in `src/InductiveModels/EqKit.lean` and is re-exported by this module's
import of it. It is separate because it is pure name-and-`Expr` plumbing with
no generator in it, and `src/InductiveModels/Projection.lean` needs that much
and nothing else; the structural checker reaches `EqInfo` through `EqKit`
without importing this file.

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

## Where this module's contents went

This file is a facade. The construction it used to hold is split along the
tower it is the top of:

* `InductiveModels.Gen.*` — the **shared generator core**: the monad and its
  declines, the `MetaM` helpers, the pure export-shape readers, the spliced
  prelude, [`InductiveModels.Iso`] and [`InductiveModels.modelTable`], and the
  W core. All three constructions are built on it, and none of them reaches
  the others through it.
* `InductiveModels.Nested.*` — the **nested construction itself**, rung three:
  `InductiveModels.Gen` (the context and its terms),
  `InductiveModels.Nested.Rules` (the ι rules) and
  `InductiveModels.Nested.Iso` (the driver).

Importing this module still brings all of it into scope, so nothing
downstream had to change. What did change is that the *lower* rungs no longer
import it: `Mutual.lean` and `Simple/*` import `InductiveModels.Gen.*`
directly, so the import graph now reads simple → mutual → nested rather than
the inversion it used to.
-/
