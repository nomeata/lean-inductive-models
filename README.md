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

The trusted basis is:

```text
Eq  Nat  PUnit  PSigma'  Quot
```

The first four are ordinary inductive owners and are not modeled. `PSigma'` is
the tight dependent pair
`{α : Sort u} → (α → Sort v) → Sort (max u v)`; its named projections and
arbitrary-sort `rec'` are ordinary definitions derived from primitive
projections. Together with `PUnit`, it derives the exact-sort propositional
lift `PSigma'.{0,u} (fun _ : P => PUnit.{u})`. `Quot` is the special fifth
member: it denotes Lean's kernel quotient bundle `Quot`, `Quot.mk`,
`Quot.lift`, and `Quot.ind`, rather than an ordinary inductive owner. Generated
developments use it only on routes that derive function extensionality from
the standard axiom `Quot.sound`; other routes need no quotient. They may also
use the standard axioms `Classical.choice` and `propext` when required.

## Command line

```console
modelgen [OPTIONS] IN.ndjson
```

`IN.ndjson` may be `-` to read standard input.

With no options, `modelgen` generates all supported inductive models, checks
models in both the input and final output, and writes the transformed export to
standard output. Equivalently, its model-generation and checking defaults are
`--inductives --check`; output is enabled and `--mono-levels` is disabled.
The explicit whole-stream kernel gates `--type-check-input` and
`--type-check-output` are disabled by default.

Diagnostics go to standard error. Every enabled successful structural check
reports its exact number of discovered model families as, for example,
`input check: 37 model families checked`; `--quiet` suppresses these success
lines together with the other successful-pass diagnostics.

| Option | Default | Meaning |
| --- | --- | --- |
| `--nested` | on | Generate models for nested inductives. |
| `--mutual` | on | Generate models for mutual inductives. |
| `--simple` | on | Generate models for ordinary non-mutual inductives. |
| `--basic` | on | Generate models for the bootstrap inputs `Acc` and `Nonempty` and generated support inductives needed by simple models. |
| `--inductives` | on | Enable all four generation branches above. |
| `--check-input` | on | Structurally check model families already present in the input export. |
| `--check-output` | on | Structurally check model families in the final transformed export. |
| `--check` | on | Enable both structural model-family checks. |
| `--type-check-input` | off | Submit the complete parsed input to Lean's kernel. |
| `--type-check-output` | off | Submit the complete final transformed export to Lean's kernel. |
| `--mono-levels` | off | Run the optional universe-level monomorphization pass. |
| `--output` | on | Write the transformed export. |
| `-o PATH` | `-` | Write to `PATH`; `-` means standard output. This also enables output. |
| `--quiet` | off | Suppress successful-pass diagnostics. |

Every boolean long option has a `--no-...` form that disables it. Options are
applied from left to right, so bundle and individual options override one
another in command-line order. For example, `--no-inductives --simple`
enables only the simple branch, whereas `--simple --no-inductives` disables
every generation branch. Similarly, `--no-check --check-output` enables only
the final structural check. `--check` does not change either whole-stream
kernel gate.

`--no-output` suppresses only the final write. Parsing, enabled checks,
monomorphization, ordering, and generation still run. This validates an input
structurally without generating models or writing an export:

```console
modelgen --check --no-inductives --no-output IN.ndjson
```

For the full model-building Lean Kernel Arena job, pass the supplied path or
pipe the same NDJSON on standard input:

```console
modelgen --inductives --check-input --check-output --type-check-input --type-check-output --no-output "$IN"
modelgen --inductives --check-input --check-output --type-check-input --type-check-output --no-output - < "$IN"
```

All four generation branches remain enabled. The input is checked structurally
and by Lean's kernel before generation; the generated, ordered result is then
checked structurally and by Lean's kernel. `--no-output` suppresses only the
final write, so generation and every requested verdict gate still run.

The process exit codes follow the
[Lean Kernel Arena checker contract](https://github.com/leanprover/lean-kernel-arena#contributing-checkers):

| Code | Outcome |
| --- | --- |
| `0` | Accepted. |
| `1` | Rejected as invalid, including rejection by Lean's kernel or a requested structural check. |
| `2` | Declined because a requested generation operation does not support an owner. Basis exemptions in a successful run are not declines. |
| any other code | Parser, I/O, CLI, or internal tool error (`modelgen` uses `3`). |

The processing order is:

1. Parse the input export.
2. If enabled, submit the unmodified input to Lean's kernel.
3. If enabled, structurally check model families in the unmodified input.
4. If enabled, monomorphize the input universe levels and order the result.
5. Generate the selected inductive models.
6. If a transformation ran, put the complete result in dependency and
   model-before-owner order.
7. If enabled, structurally check model families in that final result.
8. If enabled, submit the final result to Lean's kernel.
9. If enabled, write the result.

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

Constructor and recursor model names preserve their exact exported declaration
names, such as `Vec.nil`, `Vec.cons`, and `Vec.rec`. Numeric suffixes identify
only intrinsic slots: `j` is a zero-based position in a recursor's exported
rule array or in a type former's eligible projection fields.

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
the public interface has these two entries:

```text
T._model.proj_j
T._model.proj_j.iota
```

The type of `T._model.proj_j` is derived from `C`'s field telescope. It takes
the family parameters, family indices, and
`self : T._model parameters indices`; its result is field `j`'s type after the
simultaneous original-to-model
substitution. References to an earlier field `i` in a dependent result become
`T._model.proj_i parameters indices self`. The definition does not use a
primitive projection on the model carrier. The general construction eliminates
the carrier with the model recursor, using the field result as its motive and
returning field `j` from the corresponding minor premise. Two tight
one-field models have specialized definitions: an exact-sort payload uses the
payload itself as the carrier, while a proposition-valued payload uses the
derived tight-pair/PUnit lift. The underlying Lean edge case—sort-polymorphic inductives whose
primitive projections can be stronger than their generated recursors—is
tracked as [lean4#7637](https://github.com/leanprover/lean4/issues/7637).

For a `Prop`-valued `T`, Lean's kernel imposes two further conditions. The
selected field must be a proposition. Moreover, if the remaining constructor
telescope depends on an earlier field, that earlier field must also be a
proposition. Only fields satisfying this exact kernel projection rule receive
an intrinsic projection. Thus `Iff` receives projections for both proof fields,
whereas `Nonempty α` does not receive a projection from `Nonempty α` to `α`.

For a constructor application `C._model parameters fields`, an independent
field has the literal reduction proposition:

```text
T._model.proj_j.iota :
  T._model.proj_j parameters constructor-result-indices
    (C._model parameters fields) = fields[j]
```

For a single nonrecursive, unindexed, unnested owner, and for an unindexed
member of a plain mutual block, every field uses this literal equation,
including dependent fields: those carrier routes make the modeled projections
compute definitionally on the modeled constructor. Other simple-recursive,
indexed, and source nested-specialization routes may recover an earlier field only
propositionally. In those cases a dependent
field's right-hand side is the canonical transport of `fields[j]`, using the
already generated projection-iota equalities for the minimal transitive set of
earlier fields on which its type depends, in increasing field order. The
transport is represented by nested applications of `Eq.rec`. The generator
and checker construct the same expression; no transport is added when the
dependency set is empty.

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
axiom Pair._model.proj_0 (α β : Type) : Pair._model α β → α

axiom Pair._model.proj_0.iota (α β : Type) (first : α) (second : β) :
  Pair._model.proj_0 α β (@Pair.mk._model α β first second) = first
```

The projection model and its reduction theorem occur before the atomic
inductive record containing `T`. Named convenience definitions whose values
contain `Expr.proj` have no role in this interface and may be absent. If a
required basis declaration occurs later, final ordering places that basis
declaration first, then the projection interface, then the modeled inductive
record. Intrinsic projections are emitted in increasing field order so a
dependent field can use earlier intrinsic projections.

## Structure eta

For every non-propositional member `T` to which Lean's kernel gives
structure-like treatment, the generator adds:

```text
T._model.eta
```

The kernel predicate is per type former: `T` is non-recursive, has no indices,
and has exactly one constructor `C` owned by `T`. The additional
non-propositional condition reflects the kernel reduction path: proof
irrelevance handles proposition-valued members before structure eta applies.
A non-recursive mutual block may therefore have several independently
qualifying members.

The theorem preserves `T`'s complete parameter telescope and universe
parameters. Its literal type is:

```text
∀ parameters (x : T._model parameters),
  x = C._model parameters
    (T._model.proj_0 parameters x)
    …
    (T._model.proj_n parameters x)
```

where the intrinsic projections occur in zero-based constructor-field order.
For a dependent constructor telescope, each later projection has the result
type obtained using the earlier intrinsic projections, exactly as specified
in the preceding section. For a zero-field constructor the type specializes
to:

```text
∀ parameters (x : T._model parameters), x = C._model parameters
```

For example, the `Pair` model above also contains:

```lean
theorem Pair._model.eta (α β : Type) (x : Pair._model α β) :
    x = @Pair.mk._model α β
      (Pair._model.proj_0 α β x)
      (Pair._model.proj_1 α β x)
```

The proof eliminates `x` with the modeled recursor. In the constructor case,
the intrinsic projection definitions reduce the reconstruction to the same
modeled constructor application.

The checker requires `T._model.eta` exactly for members satisfying the kernel
structure-like predicate and the non-propositional condition. It reconstructs
the parameter telescope and proposition literally from the modeled type,
constructor, and intrinsic `proj_j` slots. The declaration must have the exact
name and universe arity, must be a theorem, and must have exactly that type.
Missing, duplicate, renamed, differently typed, or non-theorem eta slots are
rejected; an eta-looking declaration is also rejected for an ineligible
member.

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
2. The modeled inductive record does not refer to any public model declaration,
   or to another name co-recorded with a public slot. This includes its mutual
   member and constructor name arrays, declaration types, recursor rules, and
   primitive-projection owner fields. A private implementation declaration in
   its own record is not part of this public-interface check.
3. Every type former and constructor has exactly one declaration at its
   declaration-local model name, and every kernel-eligible field `j` has
   exactly one declaration at `T._model.proj_j`.
4. Every exported recursor rule has exactly one theorem at
   `R._model.iota_j`. A direct iota slot with a nonexistent or noncanonical
   index is rejected.
5. Every required intrinsic projection-iota, structure-eta, unit-like, and
   rule-K theorem is present exactly once. Structure-eta, unit-like, and
   rule-K metadata names are also rejected when the corresponding kernel
   feature is absent.
6. Each model declaration has the same number of universe parameters as its
   original. Parameter names are aligned by position.
7. After that universe alignment and the one simultaneous constant
   substitution, the type of each modeled type former, constructor, and
   recursor is literally equal to the corresponding model declaration type.
   Each intrinsic projection type is reconstructed literally from the
   constructor field telescope, substituting earlier intrinsic projections.
8. The equality proposition determined by each exported recursor rule is
   instantiated with its specified parameters and fields, rewritten by the
   same substitution, and compared literally with its iota theorem type. The
   definitional single-owner and plain-mutual routes use the constructor field
   itself; other simple-recursive, indexed, and source nested-specialization routes use the
   canonical dependent transport when required.
9. For an intrinsic projection, the checker reconstructs the kernel field
   eligibility, the selected constructor field, and its exact sort, then
   compares the complete `T._model.proj_j.iota` proposition literally,
   including the canonical dependent-field transport. It rejects a changed
   `Eq` universe even when the changed proposition remains kernel-valid. The
   structure-eta, unit-like, and rule-K propositions are checked literally as
   well.
10. Public implementation slots must be safe definitions, and proof slots
    must be theorem declarations. An unsafe or partial implementation, an
    axiom in an implementation slot, or a definition in a theorem slot is
    rejected even when its type is otherwise exact. The independently built
    model may remain safe when the modeled inductive itself is unsafe.

The outer equality in a generated theorem remains the export's `Eq`; modeling
the `Eq` inductive does not turn the theorem relation itself into `Eq._model`.
The literal declaration-type comparisons do not unfold definitions, invoke
typeclass search, use proof irrelevance, or ask Lean for definitional equality.
The checker compares declaration types and declaration kind/safety metadata,
not declaration values or proof terms. Its separate eligibility analysis may
reduce a transparent type-former alias to determine whether structure eta is
required.

`--check-input` applies this check before any transformation.
`--check-output` applies it after monomorphization, generation, and final
ordering. The absence of all public model slots for an inductive is not itself
an error: unsupported or disabled generation may leave an original inductive
without a model.

These structural checks do not submit declaration values to Lean's kernel.
`--type-check-input` and `--type-check-output` are the independent
whole-stream kernel verdict gates. The first replays the parsed input in an
empty kernel environment; the second does the same with the complete final
result, whether or not `--output` writes that result. Both also compare the
serialized declaration metadata exactly. For inductives this includes every
type-former, constructor, recursor, and recursor-rule field regenerated by
Lean's kernel.

Every generated declaration is submitted to Lean's kernel before it is
emitted. Construction may inspect the owner in a disposable environment, but
that is not the acceptance environment. The exact serialized model records are
ordered with their owner, separated from it, and replayed with kernel checking
in a fork of the persistent source-prefix environment where the owner is
absent. A model that depends on its owner is therefore rejected before output.
Only explicitly witnessed shared support is copied to the persistent
environment; the model fork is discarded, and replay then continues there with
the owner but without the model declarations.

This checked construction is mandatory and independent of the two CLI kernel
gates. Disabling `--type-check-input` or `--type-check-output` never permits the
generator to emit a declaration that failed its owner-free kernel replay.

Statement correspondence is an independent, format-only gate. The generator
reconstructs the complete expected public interface from the exact exported
owner records and compares it syntactically with the already serialized model
records. This comparison does not consult the replay environment or a recursor
minted by the kernel. A mismatch is an internal error and no output is written.

For canonical input, ordinary generation serializes each accepted model island
to a private workspace and retains only compact ordering and checking
certificates until final output. The source bytes and staged declaration spans
are then composed transactionally in the certified final order. A failed raw
certificate or unavailable compact certificate safely selects the full in-memory
path. `--mono-levels` and `--type-check-output` also retain the complete final
export because they respectively rewrite the source and replay the final stream
through Lean's kernel. This architecture is intended to bound generated-model
retention; no full-corpus memory bound is claimed without a measured run.

## Scope

- Structural model checks do not verify arbitrary declaration values.
  `--type-check-input` and `--type-check-output` explicitly request complete
  Lean-kernel replay of their respective streams; they do not establish the
  provenance of those declarations.
- Unsupported inductive shapes are reported as declines and pass through
  without a model.
- A checker consuming the models as an inductive front end must implement the
  five-member basis: its four ordinary inductives and the special kernel
  quotient bundle. It must also admit the
  standard axioms `Classical.choice`, `propext`, and `Quot.sound` when a
  generated development uses them.
- Universe monomorphization is optional, off by default, and is exposed only
  through `modelgen --mono-levels`. Its library-level correctness suite is
  `monotest`.

## Build and test

The Lean version is pinned by [`lean-toolchain`](lean-toolchain).

```console
mkdir -p _tmp/build-tmp
build_serially() {
  local target
  for target in "$@"; do
    TMPDIR="$PWD/_tmp/build-tmp" lake -Kjobs=1 build "$target"
  done
}
build_serially modelgen
```

Each target is built in its own Lake invocation so their final native links do
not overlap. `lake test` runs only the fixture-backed `test` executable; it is
not the complete correctness matrix. The complete matrix is:

```console
correctness_targets=(
  test monotest clitest generationflagstest checktest ordertest
  incrementalordertest namingtest drivernamingtest privatealiastest
  simplenamingtest rulektest defaultctoriotatest sourcestructuresyntaxtest
  composedrecursorsyntaxtest
  mainclitest projectiontest structureetatest
  deepimaxboxtest psigmaprimetest exactsortlifttest
  tightpsigmaprimeroutetest vanishingerasuretest
  transparentowneraliasestest exportsyntaxnormalizationtest
  basisvalidationtest stagedwritertest
)
build_serially "${correctness_targets[@]}"
TMPDIR="$PWD/_tmp/build-tmp" lake exe test "$PWD"
TMPDIR="$PWD/_tmp/build-tmp" lake exe monotest "$PWD"
TMPDIR="$PWD/_tmp/build-tmp" lake exe clitest
TMPDIR="$PWD/_tmp/build-tmp" lake exe generationflagstest
TMPDIR="$PWD/_tmp/build-tmp" lake exe checktest "$PWD"
TMPDIR="$PWD/_tmp/build-tmp" lake exe ordertest "$PWD"
TMPDIR="$PWD/_tmp/build-tmp" lake exe incrementalordertest "$PWD"
TMPDIR="$PWD/_tmp/build-tmp" lake exe namingtest
TMPDIR="$PWD/_tmp/build-tmp" lake exe drivernamingtest
TMPDIR="$PWD/_tmp/build-tmp" lake exe privatealiastest
TMPDIR="$PWD/_tmp/build-tmp" lake exe simplenamingtest
TMPDIR="$PWD/_tmp/build-tmp" lake exe rulektest
TMPDIR="$PWD/_tmp/build-tmp" lake exe defaultctoriotatest "$PWD"
TMPDIR="$PWD/_tmp/build-tmp" lake exe sourcestructuresyntaxtest "$PWD"
TMPDIR="$PWD/_tmp/build-tmp" lake exe composedrecursorsyntaxtest "$PWD"
TMPDIR="$PWD/_tmp/build-tmp" lake exe mainclitest "$PWD"
TMPDIR="$PWD/_tmp/build-tmp" lake exe projectiontest
TMPDIR="$PWD/_tmp/build-tmp" lake exe structureetatest
TMPDIR="$PWD/_tmp/build-tmp" lake exe deepimaxboxtest
TMPDIR="$PWD/_tmp/build-tmp" lake exe psigmaprimetest
TMPDIR="$PWD/_tmp/build-tmp" lake exe exactsortlifttest
TMPDIR="$PWD/_tmp/build-tmp" lake exe tightpsigmaprimeroutetest
TMPDIR="$PWD/_tmp/build-tmp" lake exe vanishingerasuretest
TMPDIR="$PWD/_tmp/build-tmp" lake exe transparentowneraliasestest
TMPDIR="$PWD/_tmp/build-tmp" lake exe exportsyntaxnormalizationtest
TMPDIR="$PWD/_tmp/build-tmp" lake exe basisvalidationtest
TMPDIR="$PWD/_tmp/build-tmp" lake exe stagedwritertest "$PWD"
TMPDIR="$PWD/_tmp/build-tmp" test/scripts/check_arena_corpus.py
TMPDIR="$PWD/_tmp/build-tmp" test/scripts/check-hard-nested-a.sh
TMPDIR="$PWD/_tmp/build-tmp" test/scripts/check-hard-nested-c.sh
TMPDIR="$PWD/_tmp/build-tmp" test/scripts/check-mathlib-result.sh
test/scripts/check-ci-serialized-builds.sh
```

`mainclitest` executes the built `modelgen` binary and covers the complete
`--mono-levels` process path. `monotest` exercises the underlying pass directly.
`check_arena_corpus.py` downloads the published Lean Kernel Arena corpus and
requires every `good/` case to exit 0. Every `bad/` case must either be rejected
with exit 1 or stop at the tool's exit-3 internal-invariant boundary; the report
keeps those Arena outcomes separate. Exit 2 is a failure because this checker
claims to handle the corpus, and a signal is never accepted as a verdict. It
checks both the input and generated output structurally and through Lean's
kernel without publishing the output. Its counts follow the live corpus and
are not hard-coded.
The `memoryprobe` target compares whole-file and streaming parser retention in
fresh processes. It and the `envprobe` and `levelfuzz` targets under `tools/`
are diagnostics, not correctness suites.

Human-readable Lean fixture sources and committed NDJSON exports live under
[`test/fixtures/modelgen/`](test/fixtures/modelgen/) and
[`test/fixtures/mono/`](test/fixtures/mono/). Regenerating a model-generator
fixture requires the pinned exporter:

```console
TMPDIR="$PWD/_tmp/build-tmp" test/scripts/export-modelgen.sh prim_shapes
TMPDIR="$PWD/_tmp/build-tmp" test/scripts/export-mono.sh mono_proj
```

All scratch data is kept under the repository-local `_tmp/` directory.

The focused workflow [`.github/workflows/ci.yml`](.github/workflows/ci.yml)
runs the fixture and universe-level suites and the published Arena corpus with
a per-process memory limit. The
full-Mathlib workflow
[`.github/workflows/mathlib.yml`](.github/workflows/mathlib.yml) generates and
checks a pinned Mathlib export under a cgroup memory limit and records
instruction counts with `perf`. Its artifact gate requires positive generation,
statement-comparison, output-check, universe-planning, and serialized-reread
work; zero statement differences and universe escapes; exemptions for the
three ordinary-inductive basis members owned by that pinned input (`Eq`, `Nat`,
and `PUnit`); a spliced `PSigma'`; the kernel `Quot` bundle when required; and
no unexpected basis declarations. The observed counts
are intentionally not hard-coded.

## Copyright and license

This project is licensed under the Apache License, Version 2.0
([`Apache-2.0`](LICENSE)). Copyright information is in [`NOTICE`](NOTICE).
