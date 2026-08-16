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
one public correspondence. The generator keeps exact source records as the
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

Unsupported shapes pass through unchanged and are reported as declines. A
consumer using models as an inductive front end must implement the five-member
basis and admit the standard axioms used by the selected generated route.

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
