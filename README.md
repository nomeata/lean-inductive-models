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
| eligible field `j` of `T` | `T._model.proj_j.iota` | The intrinsic modeled projection reduces on the modeled constructor. |

Generation consumes source declarations in their original order. At an
accepted inductive owner it emits the complete generated island immediately
before that source owner; all other source declarations retain their relative
order. Dependencies generated recursively inside an island precede the
generated declarations that consume them. There is no final global reorder or
whole-output kernel replay.

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
- exact recursor-iota and projection-iota propositions, including dependent
  transport syntax where the route requires it;
- safe definitions in implementation slots and theorem declarations in proof
  slots.

These checks intentionally do not unfold definitions, use proof irrelevance,
ask Lean for definitional equality, or inspect arbitrary declaration values.
That makes the correspondence check independent of the kernel verdict.

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
no cumulative output declaration array. Named output remains in a
private sibling until the final compact semantic/structural verdict commits it;
standard output is direct and can therefore contain a parseable declaration
prefix after a late failure. When input kernel checking is disabled, both actual
output and eligible checked no-output generation first build a compact source
census; each exact source declaration is trusted-installed for construction,
and each generated island is optionally checked directly in process while its
compact certificate is live. The parser transfers one declaration replay arena instead of reparsing; at parse
completion its dense expression-ID table is replaced by the exact expression
roots referenced by declarations, while the expression DAGs and name/level
tables needed for declaration replay remain available. An input-only
project-local snapshot preserves stdin/FIFO bytes for parser-compatible
fallback and is released once that compact arena is replay-certified; it is
not a generated-output representation. Generated logical declarations are
checked directly as values, never through JSON, an output parser, a writer, or
a spool. With both `--no-output` and `--no-type-check-generated`, accepted islands
are summarized while live and then discarded without any kernel check: no
workspace is opened and no cumulative generated declaration array is retained.
Input kernel checking may retain the parsed source, but generated actual output
still uses the declaration stream. No-generation writing preserves the existing
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
