# Lean inductive models

`lean-inductive-models` is a Lean 4 NDJSON-to-NDJSON filter and standalone
model checker. It adds an ordinary-declaration model of each supported
inductive while retaining the original declaration.

Lean's kernel verifies that each declaration is well typed, but it does not
know that a declaration named `T._model` is meant to reproduce `T`. The
standalone structural checker verifies that extra contract: exact names,
complete families, declaration kinds and safety, universe arities, recursor
rules, projections, and literal statement syntax. It can therefore reject
model-correspondence errors that an official-kernel replay alone accepts.

## Status

**Work in progress**. Do not look too closely yet.

## Idea

The filter represents a supported inductive family with ordinary definitions
and theorems while retaining the source declarations. This gives downstream
tools an explicit interface they can inspect without treating a generated
name as evidence that it really models the source.

The structural checker supplies that missing evidence: it relates the public
model declarations to exact exported kernel metadata and literal source
syntax. Private declarations may implement the model, but they are not an
additional public interface.

The small trusted basis is:

```text
Eq  Nat  PUnit  PSigma'  Quot
```

The first four are ordinary inductive owners. `Quot` denotes Lean's kernel
quotient bundle. Routes that derive function extensionality may additionally
use `Quot.sound`; generated developments may use the standard axioms
`Classical.choice` and `propext` when required.

Each of these is written by the tool itself, at a fixed declaration, wherever a
generated island needs one — never taken from a record the input declares later
in the stream. See the output contract below for what happens to such a record.

## Output contract

For a modeled source type former `T`, constructor `C`, recursor `R`, and
zero-based slot `j`, the public interface is:

| Source | Generated declaration |
| --- | --- |
| `T` | `T._model` |
| `C` | `C._model` |
| `R` | `R._model` |
| rule `j` of `R` | `R._model.iota_j` |
| eligible field `j` of `T` | `T._model.proj_j` |
| projection reduction rule | `T._model.proj_j.iota` |

Generated type formers, constructors, recursors, and intrinsic projections are
safe definitions; iota declarations are theorems. Type-former, constructor,
recursor, and recursor-iota statements are exact simultaneous public-name
rewrites of the exported source declarations. Intrinsic projections come from
kernel declaration metadata rather than source `structure` syntax. An atomic
mutual block still exposes one interface per member; private mutual bookkeeping
and support declarations are not public slots.

The following theorem slots are part of the public family exactly when the
exported kernel metadata makes them applicable:

| Condition | Generated theorem | Contract |
| --- | --- | --- |
| rule `j` of modeled recursor `R` | `R._model.iota_j` | The literal exported iota proposition after the same simultaneous public-name rewrite. |
| `T` is kernel-unit-like: nonrecursive, unindexed, with one zero-field constructor | `T._model.unitlike` | Any two inhabitants of the modeled `T` are equal. |
| exported recursor `R` has literal `k = true` (with its one zero-field rule) | `R._model.ruleK` | The K-like reduction at the constructor-result fibre; indexed results retain that exact fibre. |
| `T` is non-propositional and kernel-structure-like: nonrecursive, unindexed, with one constructor | `T._model.eta` | Reconstruct an inhabitant with the modeled constructor and every intrinsic modeled projection in field order. |
| eligible field `j` of `T` | `T._model.proj_j.iota` | The intrinsic modeled projection applied to the modeled constructor equals constructor field `j`. The right-hand side is that field binder itself, never a transported term. |

Generation consumes source declarations in their original order. At an
accepted inductive owner it emits the complete generated island immediately
before that source owner; all other source declarations retain their relative
order. Dependencies generated recursively inside an island precede the
generated declarations that consume them. There is no final global reorder or
whole-output kernel replay.

**Every record therefore declares each name it references before referencing
it**, so any prefix of the output that ends at a record boundary is itself a
complete export. This is checked over the whole fixture corpus by
`emissionordercensustest`.

**One class of source record is dropped rather than retained.** Generation
writes a fixed set of declarations of its own — the basis inductives above,
the tight pair's six derived declarations, `Nonempty`, `Iff`, the kernel
quotient, `Quot.sound`, `Classical.choice` and `propext` — at the first point
one is needed, whatever the input reserves. When the input declares one of
those names later in the stream, its record is compared against the
declaration that was written: an identical record is dropped, since the output
already carries it, and a record that is *not* that declaration rejects the
run rather than being silently replaced. Every other source declaration is
retained.

Actual generated output is serialized declaration by declaration through one
persistent standard arena writer, so its declaration order is the order above.
A named output is a sibling transaction and becomes visible only after every
requested final semantic and structural verdict succeeds. Standard output is
direct and may therefore contain a valid declaration prefix when a later
transition fails.
The no-generation write path continues to write the retained input export.

`--type-check-generated` kernel-checks each exact generated island once, in
process and before it is emitted. Source declarations are trusted dependencies
for that check and never enter the generated-declaration gate.
`--type-check-input` separately checks only input declarations. Disabling
either flag performs no kernel check for that declaration class. The default
`--check-output` structural check validates compact incremental/final
certificates; it does not reconstruct and replay the complete output.
Parsing, generation, structural checking, and both optional kernel gates all
run in the invoking process; the executable neither starts a checker worker
nor re-executes itself under a supervisor.

## Checker contract

The structural checker discovers a family whenever any public model slot for
an inductive record is present. It then requires the complete corresponding
family and checks:

- model-before-owner ordering and absence of public backreferences;
- unique type-former, constructor, recursor, rule, projection, and metadata
  slots at their exact names;
- matching universe arities and literal declaration types after simultaneous
  source-to-model renaming;
- exact recursor-iota and projection-iota propositions; every projection-iota
  right-hand side is the constructor field binder itself, on every route, and
  the checker recomputes exactly that;
- safe definitions in implementation slots and theorem declarations in proof
  slots.

The checker is a pure function of the export text: it never asks Lean for
definitional equality, never appeals to proof irrelevance, and never compares a
declaration's value. Every correspondence verdict is literal syntactic equality
of declaration types after simultaneous source-to-model renaming, so an
accepted slot is exact rather than merely definitionally right, and the verdict
is independent of the kernel's.

Deciding what to compare against is a separate matter. Enumerating a
constructor's parameters and fields, deciding whether an owner or a field type
is a proposition, and deciding which fields admit an intrinsic projection apply
the kernel's own projection rules; that shape analysis does unfold transparent
definitions and read their values. It settles which slots must exist and how
their statements are spelled. It never loosens the comparison itself.

`--check-input` runs it on models already in the input. `--check-output` runs
it on the final transformed stream. An input with no model slots is not
rejected merely because an inductive is unsupported or generation is disabled.

`--type-check-input` and `--type-check-generated` govern disjoint declaration
classes. The former checks only input declarations. The latter, enabled by
default, checks each exact generated model island incrementally as it is
produced; input declarations are trusted dependencies in that environment,
not checked a second time. With either flag off, that declaration class is not
kernel-checked.

## Constructions

Three constructions share one generator core, one decline vocabulary and one
public correspondence. The driver picks one from the exported declaration's own
shape; none of them calls the others, and they are not one construction at
three settings.

- **Nested** — a block the exporter marked nested. The model is a mutual block
  with one extra member per nested occurrence, a `pack`/`unpack` pair per mimic
  with both round trips as theorems, and one recursor and ι rule per member. It
  removes nesting and keeps mutuality.
- **Mutual** — a plain mutual block with no nesting. One *tag* enumeration
  carrying each member's index telescope, one indexed auxiliary family over it,
  and one carrier per member. It removes mutuality.
- **Simple** — a single non-mutual inductive, reduced to the fixed basis. This
  is the construction with the routes and arms below.

`Eq`, `Nat`, `PUnit` and `PSigma'` are what the simple construction is
*written in*, and `Quot` is the kernel's. They are not modelled. That is an
exemption rather than a gap — it is what makes the construction well-founded —
and it is reported in its own row, outside the decline count.

### The universe route

The simple construction first splits on the carrier's sort `w`, three ways,
with no preference order between them:

- `w` normalizes to zero — the **`Prop`** route;
- `w` is never zero — the **`Type`** route;
- otherwise — the **maybe-zero** route, a `Sort w` that is a proposition at some
  instantiations of its level parameters and is not at others.

The split is forced by what the two ends need. The Church encoding is
impredicative and is well formed only at `Sort 0`, or at any `Sort w` under the
derived exact-sort lift. The tuple tower needs the large eliminator the kernel
mints for `Nat` only at a `Type`, and it pads its fields to land at exactly
`Sort w`. A maybe-zero owner has neither, so it is its own route rather than an
instance of one of the others.

### The arms, in the order the route dispatcher tries them

- **Direct** — field-preserving storage for a one-constructor nonrecursive
  owner at a maybe-zero sort. The two exact one-field answers come first —
  *identity* where the single field's sort is already the carrier's, *prop lift*
  where it is exactly a proposition — and everything else is stored in a
  right-nested `PSigma'` tower at any field count, ending at the exact-sort pad
  where the fields' own levels do not reach the carrier's sort. The *indexed*
  case wraps that same tower in a `Prop`-valued packed Henry-Ford equation
  saying which fibre the storage sits in, and is disjoint from the other two by
  its own guard; the two exact answers are taken before the tower so that their
  carriers stay the field itself and the bare lift.
- **F** — the indexed subsingleton, for a large-eliminating one-constructor
  nonrecursive indexed owner at a `Prop` or maybe-zero sort. The carrier is one
  packed equation on the index positions that are not pivots; a *pivot* is an
  index position that is literally one of the constructor's data fields, and the
  arm recovers that field by **substituting** at it. It recovers data and cannot
  store it.
- **C** — an indexed family at a `Type` sort, carved out of its own index
  erasure. A **stepping stone**: it splices the index-erased skeleton as a real
  inductive, and that skeleton re-enters the pipeline and is modelled by **arm
  W**. `Type` is intrinsic rather than incidental — the carve spends the
  skeleton's large eliminator twice, and a maybe-zero skeleton has none to mint.
  If the skeleton does not model, the whole island is withdrawn and the owner
  declines.
- **E** — every constructor has a *bare* recursive field, so no constructor can
  be applied and the declaration is empty. Serves the `Type` and maybe-zero
  routes. The carrier is the empty type at exactly `Sort w`, or — where
  projections are wanted — a right-nested `PSigma'` tower over the non-recursive
  fields ending at that emptiness, which is uninhabited because of its tail
  while genuinely storing everything in front of it.
- **W** — the tagged W construction, for a non-indexed recursive `Type` owner
  whose recursion branches or is infinitary. It splices a `_wcore` fragment,
  which is itself modelled by the same descent arm C's skeleton takes.
- **Tuple** — the `Nat`-tagged tuple tower, the `Type` route's last arm. Its
  spine is deliberately linear: one bare recursive field per constructor. That
  is the whole of what separates it from arm W, and the two are split by cost
  rather than by reach — the tower costs `Nat`, `PSigma'` and no axiom, and
  every one of its ι rules is `Eq.refl`.
- **Church**, with **G** inside it — the fallback for the `Prop` and maybe-zero
  routes, which is why neither of those routes has an unreached shape. The
  carrier is the impredicative Church encoding, under the derived lift at a
  maybe-zero sort. Arm **G** replaces the fold with a recursion by its *graph*,
  and it fires only at a literal `Prop` whose one-constructor recursive owner
  the kernel granted a large eliminator; at a maybe-zero sort there is no such
  grant, so the restriction is the kernel's and not a choice. G pays
  `Classical.choice`, and function extensionality when a recursive field has a
  binder.

An inductive a construction splices — arm C's skeleton, arm W's `_wcore`
fragment, the mutual construction's tag and auxiliary family — re-enters the
simple pipeline under `--basic` and is modelled there. **A model may not leave
an inductive it introduced unmodelled**: if a spliced inductive does not model,
the island is withdrawn and the owner declines carrying that inner reason. With
`--basic` on, the five-member basis is therefore the only unmodelled inductive
residue in the output.

Above the arms sit two **presentation adapters**. They change what the public
interface looks like rather than how the shape is represented. A one-constructor
recursive unindexed `Type` owner, none of whose recursive fields is named by a
later field's type, is published as one constructor layer over a private
fixpoint; the indexed bare-erasure case of the same owner is published as an
indexed fibre. Both exist so that the intrinsic projections select literally.

### What is covered, and what is not

A decline is not a failure: the source declaration passes through unchanged and
the run reaches exit code 2. What follows is the whole ledger.

**One known gap** — a shape an arm ought to reach and does not. There is one
site in the code.

- *Arm W's guards*. A non-indexed recursive owner at a never-zero sort whose
  recursion is not linear is arm W's or it is nobody's, and arm W refuses two
  things that are limits of the arm rather than boundaries of the construction:
  a syntactic loose-variable test on a binder type inside a recursive field's
  own telescope, and a carrier plan that could not put the W core's `Type u` at
  the declared sort.

That is a gap, in those words. The message names the arm and the guard, so the
gap stays addressable instead of being recorded and forgotten.

**Two stated boundaries**, which are not gaps.

- *A nested occurrence*. A field mentioning the owner as anything other than
  `∀ z⃗, T p⃗ e⃗` after βζ head normalization is declined as out of scope: that
  is nesting, and nesting is the nested construction's business. Nothing is
  missing; a model built here would be the wrong layer's.
- *Storage that no pad or box can land on the carrier's sort*. A field whose
  level falls short of `Sort w` has to be padded into it, and the pad is the
  derived exact-sort lift of `⊤` — a `PSigma'.{0,w}`, so it sits at exactly
  `Sort w` at every `w`, maybe-zero included. The storing towers end there and
  land at `Sort (max ℓ⃗ w)`, which is `Sort w` whenever the kernel's own
  `is_geq(w, ℓᵢ)` on the input survives being re-asked as a *conversion*. Where
  it does not, the field's level retains an `imax` that no `max`-shaped carrier
  absorbs, and neither side can close it: the recursive box that removes an
  `imax` exposed by a Π leaves an opaque atomic type carrying one, and at a
  maybe-zero sort the box is unavailable outright, because every boxed level
  carries a `max 1 ·` floor and no `max 1 ·` is ever `Prop`. There is no third
  pad to build — one that cleared the `imax` would miss `Prop`, one that
  reached `Prop` would not clear the `imax` — so this is a limit of Lean's
  definitional equality on levels and not an unfinished arm. It is the same
  fact as the projection decline below, met where storage is the whole carrier
  rather than an addition to one.

**One projection decline.** A field whose type names an earlier field the model
does not select definitionally has no well-formed intrinsic projection ι rule to
state, so the owner declines that rule. The occupant is an owner with a field at
an opaque `imax` level under a `max`-shaped carrier. This is a limit of **Lean's
definitional equality on levels**, and not a gap in this tool's level procedure,
which is strictly stronger. The inequality is not in doubt: the kernel admitted
the input by `is_geq`, which splits an `imax` into a stronger `max`-shaped
bound and so never reasons about `imax` at all. But level conversion is
normal-form equality with no ordering test and no absorption across differing
bases — `max (max u v) w` normalizes to `w` and `max (imax u v) w` does not,
because an `imax` atom absorbs into no `max` — and the storing tower has to
*land* at `Sort w` under that equality. The recursive box removes the `imax`
wherever the field's type can be inspected; at an opaque atomic type nothing
can. The model is otherwise complete for such an owner: carrier, constructors,
recursor and every recursor ι rule are built and check. Only the intrinsic
projection *rules* are unstatable.

**One accepted limitation.** Where the alternative is a decline, the planner
decides a level gap with a complete decision procedure for Lean's level
algebra, used only to widen the elaborator's answer and never to narrow it. A
model admitted on that basis can be one Lean's stock kernel will not verify,
because the stock kernel's level conversion is the incomplete normal-form test
above. That is accepted and it is not a wrong model — it is correct under a
complete level theory, and a checker with one accepts it. Every use of the
widening is made visible instead: `--type-check-generated` is the gate that
turns such a plan into a reported generated-kernel rejection, the stderr line
`levels: N planner comparisons, M escapes` counts every pair the widening
decided and the elaborator would not, and the Mathlib gate requires `M = 0` —
the corpus condition under which the limitation was accepted.

## Usage

```console
lean-inductive-models [OPTIONS] IN.ndjson
```

`IN.ndjson` may be `-` for standard input. With no options, all generation
routes and both structural checks run, each generated island is kernel-checked
as it is produced, and the transformed export is written to standard output.
Diagnostics go to standard error.

```console
# Generate, check generated islands, and write to a file.
lean-inductive-models -o OUT.ndjson IN.ndjson

# Check an input without generating or writing anything.
lean-inductive-models --no-inductives --check --no-output IN.ndjson

# Also request a separate kernel check of the input declarations.
lean-inductive-models --type-check-input --no-output "$IN"
```

| Option | Default | Meaning |
| --- | --- | --- |
| `--nested` | on | Generate models for nested inductives. |
| `--mutual` | on | Generate models for plain mutual inductives. |
| `--simple` | on | Generate models for ordinary non-mutual inductives. |
| `--basic` | on | Generate bootstrap and generated-support models. |
| `--inductives` | on | Set all four generation options. |
| `--check-input` | on | Structurally check input model families. |
| `--check-output` | on | Structurally check final model families. |
| `--check` | on | Set both structural-check options. |
| `--type-check-input` | off | Replay the parsed input through Lean's kernel. |
| `--type-check-generated` | on | Kernel-check each generated model island as it is produced. |
| `--output` | on | Write the transformed export. |
| `-o PATH` | `-` | Select the output path and enable output. |
| `--quiet` | off | Suppress successful-pass diagnostics. |

Every boolean long option has a `--no-...` form. Options apply left to right,
so `--no-inductives --simple` enables only simple generation, while
`--simple --no-inductives` disables every generation route. `--no-output`
suppresses only the final write; enabled transformations and checks still run.

Exit codes follow the Lean Kernel Arena checker contract:

| Code | Outcome |
| --- | --- |
| `0` | Accepted. |
| `1` | Rejected by a requested structural or kernel check. |
| `2` | A requested generation route declined an unsupported owner. |
| `3` | Parser, I/O, CLI, or internal tool error. |

## Implementation notes

Nested, mutual, simple, and basis generation are independent routes sharing
one public correspondence; [Constructions](#constructions) says what each of
them represents and when it fires. The generator keeps exact source records as the
syntax authority and uses installed kernel metadata only as a layout and proof
oracle. Each accepted model island is appended immediately before its source
owner, while all other source declarations retain input order. Input
validation rejects a model declaration that occurs after its owner.

Canonical generation retains compact structural certificates while model
islands are live. Actual generated output receives the exact island and then
its source owner at that transition and feeds each declaration into one
persistent standard arena writer. The writer retains global interning maps but
no cumulative output declaration array.

Those interning maps are what the output path costs. The export format
addresses names, levels and expressions by ID, and any record may back-
reference a node emitted anywhere earlier in the file, so the writer must
remember every node it has emitted for as long as it is writing. Measured on
the pinned Mathlib export with generation disabled, that is **40.5 bytes per
interned arena node** — 393 MB of peak resident set on a 10-million-line
prefix, 856 MB on 20 million, growing linearly with the *output*. With
generation enabled the maps additionally hold every generated island's
expressions live for the rest of the file, where `--no-output` lets them die
at island close; enabling output then costs 820 MB on the same 10-million-line
prefix, against 864 MB for the whole rest of the pass. Nothing here can be
pruned: forgetting an ID would re-emit its node under a fresh one, which is a
valid export but not the same export. Making the map cheaper than a
`Std.HashMap Expr Nat`, not making it smaller, is the available lever.

Named output remains in a
private sibling until the final compact semantic/structural verdict commits it;
standard output is direct and can therefore contain a parseable declaration
prefix after a late failure. When input kernel checking is disabled, both actual
output and eligible checked no-output generation first build a compact source
census; each exact source declaration is trusted-installed for construction,
and each generated island is optionally checked directly in process while its
compact certificate is live. The input is parsed exactly once and the parsed
declarations are kept, so nothing is ever re-read, re-parsed or spooled to
disk: the tool opens no file it was not given on the command line. Generated
logical declarations are checked directly as values, never through JSON, an
output parser or a writer. With both `--no-output` and
`--no-type-check-generated`, accepted islands are summarized while live and
then discarded without any kernel check, and no cumulative generated
declaration array is retained. No-generation writing preserves the existing
whole-export path.

Unsupported shapes pass through unchanged and are reported as declines;
[Constructions](#constructions) is the complete ledger of which shapes those
are. A consumer using models as an inductive front end must implement the
five-member basis and admit the standard axioms used by the selected generated
route. With `--basic` on, that basis is the only unmodelled inductive residue,
because an inductive a construction splices is itself modelled or the island is
withdrawn.

## Building

The Lean version is pinned by [`lean-toolchain`](lean-toolchain).

```console
lake build
lake test
```

`lake test` is the quick fixture suite. Run the complete correctness interface
with:

```console
test/scripts/run-correctness.sh
```

Detailed target matrices, CI envelopes, fixture regeneration, and diagnostic
tools are documented in [Maintainer testing](docs/maintainers/Testing.md).

## Copyright and license

This project is licensed under the Apache License, Version 2.0
([`Apache-2.0`](LICENSE)). Copyright information is in [`NOTICE`](NOTICE).
