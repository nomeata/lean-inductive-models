# Lean inductive models

`modelgen` is a Lean 4 NDJSON-to-NDJSON filter. It adds a propositional model
of each supported inductive declaration: ordinary Lean declarations for its
type former, constructors, and recursors, together with equality theorems for
the recursor reduction rules. The original inductive declaration remains in
the export.

There are two reasons to use these models:

- A proof checker can check a proof through both the inductive declaration and
  its separately represented model. This gives additional protection against
  mistakes in inductive handling.
- A checker that does not implement general inductive declarations can use the
  models as a front end, while implementing only a small trusted basis.

The basis is:

```text
Eq  Nat  PULiftP  PSigma
```

These four inductives are not modeled. Generated developments may use the
standard axioms `Classical.choice`, `propext`, and `Quot.sound`.

## Command line

```console
modelgen [OPTIONS] IN.ndjson
```

With no options, `modelgen` generates all supported inductive models, checks
models in both the input and final output, and writes the transformed export to
standard output. Equivalently, its model-generation and checking defaults are
`--inductives --check`; output is enabled and `--mono-levels` is disabled.

Diagnostics go to standard error.

| Option | Default | Meaning |
| --- | --- | --- |
| `--nested` / `--no-nested` | on | Enable or disable models for nested inductives. |
| `--mutual` / `--no-mutual` | on | Enable or disable models for mutual inductives. |
| `--simple` / `--no-simple` | on | Enable or disable models for ordinary non-mutual inductives. |
| `--basic` / `--no-basic` | on | Enable or disable models for the bootstrap inputs `Acc` and `Nonempty` and generated support inductives needed by simple models. |
| `--inductives` / `--no-inductives` | on | Enable or disable all four generation branches above. |
| `--check-input` / `--no-check-input` | on | Check model families already present in the input export. |
| `--check-output` / `--no-check-output` | on | Check model families in the final transformed export. |
| `--check` / `--no-check` | on | Enable or disable both checks. |
| `--mono-levels` / `--no-mono-levels` | off | Enable or disable the optional universe-level monomorphization pass. |
| `--output` / `--no-output` | on | Enable or suppress writing the transformed export. |
| `-o PATH` | `-` | Write to `PATH`; `-` means standard output. This also enables output. |
| `--quiet` / `--no-quiet` | off | Suppress or enable successful-pass diagnostics. |

Options are applied from left to right. Bundle options and individual options
therefore override one another in command-line order. For example,
`--no-inductives --simple` enables only the simple branch, whereas
`--simple --no-inductives` disables every generation branch. Similarly,
`--no-check --check-output` enables only the final-output check.

`--no-output` suppresses only the final write. Parsing, enabled checks,
monomorphization, ordering, and generation still run. This validates an input
without generating models or writing an export:

```console
modelgen --check --no-inductives --no-output IN.ndjson
```

The processing order is:

1. Parse the input export.
2. If enabled, check model families in the unmodified input.
3. If enabled, monomorphize the input universe levels and order the result.
4. Generate the selected inductive models.
5. Put the complete result in dependency and model-before-owner order.
6. If enabled, check model families in that final result.
7. If enabled, write the result.

Thus `--mono-levels` runs before inductive-model generation. It is an optional
secondary pass rather than part of the model correspondence.

## Public model declarations

The public interface is attached to exact exported declaration names. For an
inductive type former `T`, a constructor whose actual name is `C`, and a
recursor whose actual name is `R`, the model declarations are:

| Original declaration | Model declaration |
| --- | --- |
| `T` | `T._model` |
| `C` | `C._model` |
| `R` | `R._model` |
| exported rule `j` of `R` | `R._model.iota_j` |
| eligible zero-based field `j` of `T` | `T._model.proj_j` |
| constructor reduction of field `j` | `T._model.proj_j.iota` |

For example, `C` may be named `Vec.nil` or `Vec.cons`; it is not the word
`ctor` followed by an index. Likewise, `R` is the exported recursor name—for
the example below, `Vec.rec`. Only `j` is numeric: it is the zero-based
position in that recursor's exported rule array.

This contract does not expose mutual-group bookkeeping. If `Even` and `Odd`
are declared together, their carriers are still named independently as
`Even._model` and `Odd._model`, and every constructor, recursor, and eligible
field projection is attached to its own type former. A declaration type may mention
a sibling model when the original type mentions the sibling; that dependency
is part of the declaration-local types, not a separate public group interface.

The generator may add private implementation support. Consumers locate the
public interface through the names above and do not need to recognize that
support.

### Example: length-indexed vectors

Consider:

```lean
inductive Vec.{u} (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (Nat.succ n)
```

Its public model interface has these types. They are written as axioms here
only to display the interface; the generator emits definitions and proved
theorems.

```lean
axiom Vec._model.{u} (α : Type u) : Nat → Type u

axiom Vec.nil._model.{u} {α : Type u} :
  Vec._model α 0

axiom Vec.cons._model.{u} {α : Type u} {n : Nat} :
  α → Vec._model α n → Vec._model α (Nat.succ n)

axiom Vec.rec._model.{v, u} {α : Type u}
    {motive : (n : Nat) → Vec._model α n → Sort v}
    (nil : motive 0 Vec.nil._model)
    (cons : ∀ {n : Nat} (head : α) (tail : Vec._model α n),
      motive n tail →
      motive (Nat.succ n) (Vec.cons._model head tail))
    {n : Nat} (x : Vec._model α n) : motive n x

axiom Vec.rec._model.iota_0.{v, u} {α : Type u}
    {motive : (n : Nat) → Vec._model α n → Sort v}
    (nil : motive 0 Vec.nil._model)
    (cons : ∀ {n : Nat} (head : α) (tail : Vec._model α n),
      motive n tail →
      motive (Nat.succ n) (Vec.cons._model head tail)) :
    Vec.rec._model nil cons Vec.nil._model = nil

axiom Vec.rec._model.iota_1.{v, u} {α : Type u}
    {motive : (n : Nat) → Vec._model α n → Sort v}
    (nil : motive 0 Vec.nil._model)
    (cons : ∀ {n : Nat} (head : α) (tail : Vec._model α n),
      motive n tail →
      motive (Nat.succ n) (Vec.cons._model head tail))
    {n : Nat} (head : α) (tail : Vec._model α n) :
    Vec.rec._model nil cons (Vec.cons._model head tail) =
      cons head tail (Vec.rec._model nil cons tail)
```

The modeled constructor and recursor retain the index `n`, and the second
reduction theorem exposes both the recursive call in the `n` fiber and the
result in the `Nat.succ n` fiber.

## Intrinsic projections

Projection modeling is determined from the exported kernel declarations, not
from source-level `structure` syntax or named projection functions. A member
`T` is projection-eligible when it has exactly one constructor `C` and the
export contains the constructor record for `C`, owned by `T`.

This is the kernel boundary for `Expr.proj`: recursive and indexed
one-constructor families are included. The test is per type former, so a
mutual block may have several independently eligible members. For every
zero-based constructor field
`j` for which the kernel expression `Expr.proj T j self` is well typed,
`modelgen` adds:

```text
T._model.proj_j
T._model.proj_j.iota
```

The type of `T._model.proj_j` is derived from `C`'s field telescope. It takes
the family parameters, family indices, and
`self : T._model parameters indices`; its result is field `j`'s type after the
simultaneous original-to-model
substitution. References to an earlier field `i` in a dependent result become
`T._model.proj_i parameters indices self`. The definition does not use a primitive
projection on the model carrier. It eliminates the carrier with the model
recursor, using the field result as its motive and returning field `j` from the
corresponding minor premise.

For a `Prop`-valued `T`, Lean's kernel imposes two further conditions. The
selected field must be a proposition. Moreover, if the remaining constructor
telescope depends on an earlier field, that earlier field must also be a
proposition. Only fields satisfying this exact kernel projection rule receive
an intrinsic projection. Thus `Iff` receives projections for both proof fields,
whereas `Nonempty α` does not receive a projection from `Nonempty α` to `α`.

For a constructor application `C._model parameters fields`, the reduction
theorem is the literal proposition:

```text
T._model.proj_j.iota :
  T._model.proj_j parameters constructor-result-indices
    (C._model parameters fields) = fields[j]
```

The theorem preserves the constructor's complete parameter and field
telescope, binder information, and declaration universes. Its outer relation
is the standard `Eq`, and the universe argument of that `Eq` is the exact sort
of the constructor field result. It is not copied from a candidate theorem
and is not replaced by `Eq._model`.

For example, the model of

```lean
structure Pair (α β : Type) where
  first : α
  second : β
```

contains declarations with the following interface, written as axioms here
only to display their types:

```lean
axiom Pair._model.proj_0 {α β : Type} : Pair._model α β → α

axiom Pair._model.proj_0.iota {α β : Type} (first : α) (second : β) :
  Pair._model.proj_0 (Pair.mk._model first second) = first
```

The projection model and its reduction theorem occur before the atomic
inductive record containing `T`. Named convenience definitions whose values
contain `Expr.proj` have no role in this interface and may be absent. If a
required basis declaration occurs later, final ordering places that basis
declaration first, then the projection interface, then the modeled inductive
record. Intrinsic projections are emitted in increasing field order so a
dependent field can use earlier intrinsic projections.

## Unit-like inductives

For each member `T` with Lean's kernel unit-like treatment, the generator adds:

```text
T._model.unitlike
```

The predicate is read directly from the exported inductive metadata and
constructor records. It holds exactly when all of these conditions hold for
that member:

- `T` is non-recursive;
- `T` has no indices;
- `T` has exactly one constructor; and
- that constructor belongs to `T` and has no fields.

The test is per type former, including for members declared in a mutual block.
For parameters `p` of `T`, the theorem type is:

```lean
∀ p (x y : T._model p), x = y
```

with the original parameter telescope and universe parameters preserved. For
example, a model of

```lean
inductive UnitBox.{u} (α : Type u) : Type u where
  | mk : UnitBox α
```

contains:

```lean
theorem UnitBox._model.unitlike.{u} (α : Type u)
    (x y : UnitBox._model α) : x = y
```

The checker requires exactly that name and literal substituted proposition for
every qualifying member. It rejects a missing or duplicate theorem, a changed
universe arity or proposition, and a `T._model.unitlike` theorem attached to a
member that does not satisfy the predicate.

## Recursor rule K

If an exported recursor `R` has its literal `k` flag set, the generator adds:

```text
R._model.ruleK
```

This is a property of `R`, not of its inductive type former. A K recursor has
one exported rule for a constructor with no fields. Start with the ordinary
model iota proposition for that rule:

```text
∀ Γ, R._model ... C._model = rhs
```

where `Γ` contains the recursor parameters, motives, and minor premises. The
rule-K theorem replaces the constructor major on the left by an arbitrary
inhabitant of that constructor's exact result fiber:

```text
∀ Γ (major : T._model parameters constructor-result-indices),
  R._model ... major = rhs
```

In particular, indexed families do not gain a theorem over arbitrary indices:
the major remains in the same index fiber as the nullary constructor.

The checker requires `R._model.ruleK` exactly when the exported `k` flag is
set. It reconstructs the proposition from the recursor's first ordinary rule,
verifies the one-rule, zero-field shape, substitutes the public model names,
and compares the result literally. Missing, duplicate, differently typed, or
wrong-universe theorems are rejected. A theorem at that name is also rejected
when `R` does not have the `k` flag.

## Structural check

The check is deliberately stricter than type checking or definitional
equality. An inductive record determines the declaration correspondence and
its intrinsic field slots directly:

```text
T  ↦ T._model
C  ↦ C._model
R  ↦ R._model
(T, j) ↦ T._model.proj_j
```

Every member of an atomic mutual record contributes its own entries to this
single simultaneous substitution. That is only how sibling references are
rewritten; it does not add a public mutual-group interface.

If any exact public slot for an inductive record is present, the checker
validates the complete model family:

1. Every declaration record containing a public model slot occurs before the
   inductive record containing its owner.
2. The modeled inductive record does not refer to any declaration introduced
   by its model family. This includes references in names, declaration types,
   recursor rules, and nested expression fields.
3. Every type former and constructor has exactly one declaration at its
   declaration-local model name, and every kernel-eligible field `j` has
   exactly one declaration at `T._model.proj_j`.
4. Every exported recursor rule has exactly one theorem at
   `R._model.iota_j`. A direct iota slot with a nonexistent or noncanonical
   index is rejected.
5. Every required intrinsic projection-iota, unit-like, and rule-K theorem is present
   exactly once. Unit-like and rule-K metadata names are also rejected when
   the corresponding kernel feature is absent.
6. Each model declaration has the same number of universe parameters as its
   original. Parameter names are aligned by position.
7. After that universe alignment and the one simultaneous constant
   substitution, the type of each modeled type former, constructor, and
   recursor is literally equal to the corresponding model declaration type.
   Each intrinsic projection type is reconstructed literally from the
   constructor field telescope, substituting earlier intrinsic projections.
8. The equality proposition determined by each exported recursor rule is
   instantiated with its specified parameters and fields, rewritten by the
   same substitution, and compared literally with its iota theorem type.
9. For an intrinsic projection, the checker reconstructs the kernel field
   eligibility, the selected constructor field, and its exact sort, then
   compares the complete `T._model.proj_j.iota` proposition literally. It rejects a changed `Eq`
   universe even when the changed proposition remains kernel-valid. The
   unit-like and rule-K propositions are checked literally as well.

The outer equality in a generated theorem remains the export's `Eq`; modeling
the `Eq` inductive does not turn the theorem relation itself into `Eq._model`.
The checker does not unfold definitions, invoke typeclass search, use proof
irrelevance, or ask Lean for definitional equality. It compares declaration
types, not declaration values or proof terms.

`--check-input` applies this check before any transformation.
`--check-output` applies it after monomorphization, generation, and final
ordering. The absence of all public model slots for an inductive is not itself
an error: unsupported or disabled generation may leave an original inductive
without a model.

Every generated declaration is also submitted to Lean's kernel before it is
emitted. In addition, the generator compares its generated recursor statements
against the recursor rules installed by Lean; a mismatch is an internal error
and no output is written.

## Scope

- The tool is not a verifier for arbitrary NDJSON input. It adds and checks
  model interfaces; it does not establish the provenance of the original
  declarations.
- Unsupported inductive shapes are reported as declines and pass through
  without a model.
- A checker consuming the models as an inductive front end must implement the
  four basis inductives and admit the standard axioms `Classical.choice`,
  `propext`, and `Quot.sound` when a generated development uses them.
- Universe monomorphization is optional, off by default, and is exposed only
  through `modelgen --mono-levels`. Its library-level correctness suite is
  `monotest`.

## Build and test

The Lean version is pinned by [`lean-toolchain`](lean-toolchain).

```console
mkdir -p _tmp/build-tmp
TMPDIR="$PWD/_tmp/build-tmp" lake build modelgen
```

Representative focused suites are:

```console
TMPDIR="$PWD/_tmp/build-tmp" lake build \
  test clitest generationflagstest checktest rulektest mainclitest
TMPDIR="$PWD/_tmp/build-tmp" lake exe clitest
TMPDIR="$PWD/_tmp/build-tmp" lake exe generationflagstest
TMPDIR="$PWD/_tmp/build-tmp" lake exe checktest "$PWD"
TMPDIR="$PWD/_tmp/build-tmp" lake exe rulektest
TMPDIR="$PWD/_tmp/build-tmp" lake exe mainclitest "$PWD"
TMPDIR="$PWD/_tmp/build-tmp" lake exe test "$PWD"
```

The optional universe-level suite is:

```console
TMPDIR="$PWD/_tmp/build-tmp" lake build modelgen monotest
TMPDIR="$PWD/_tmp/build-tmp" lake exe monotest "$PWD"
```

Human-readable Lean fixture sources and committed NDJSON exports live under
[`tests/`](tests/). Regenerating a fixture requires the pinned exporter:

```console
TMPDIR="$PWD/_tmp/build-tmp" tests/export.sh prim_shapes
```

All scratch data is kept under the repository-local `_tmp/` directory.

The focused workflow [`.github/workflows/ci.yml`](.github/workflows/ci.yml)
runs the fixture and universe-level suites with a per-process memory limit. The
full-Mathlib workflow
[`.github/workflows/mathlib.yml`](.github/workflows/mathlib.yml) generates and
checks a pinned Mathlib export under a cgroup memory limit and records
instruction counts with `perf`.

## Copyright and license

This project is licensed under the Apache License, Version 2.0
([`Apache-2.0`](LICENSE)). Copyright information is in [`NOTICE`](NOTICE).
