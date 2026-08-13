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

## Idea and output contract

For a source type former `T`, constructor `C`, recursor `R`, and zero-based
slot `j`, the public model interface is:

| Source | Generated declaration |
| --- | --- |
| `T` | `T._model` |
| `C` | `C._model` |
| `R` | `R._model` |
| rule `j` of `R` | `R._model.iota_j` |
| eligible field `j` of `T` | `T._model.proj_j` |
| projection reduction rule | `T._model.proj_j.iota` |

The generated type formers, constructors, and recursors are safe definitions;
reduction rules are theorems. Their public statements are exact simultaneous
name rewrites of the exported source declarations. An atomic mutual block
still exposes one interface per member; private mutual bookkeeping is not a
public API.

Intrinsic projections are derived from kernel declaration metadata, not from
source `structure` syntax. The output may also contain exact structure-eta,
unit-like, and recursor-rule-K theorems when the exported kernel metadata calls
for them. Private implementation support may be present, but consumers locate
the interface only through the public names above.

The small trusted basis is:

```text
Eq  Nat  PUnit  PSigma'  Quot
```

The first four are ordinary inductive owners. `Quot` denotes Lean's kernel
quotient bundle. Routes that derive function extensionality may additionally
use `Quot.sound`; generated developments may use the standard axioms
`Classical.choice` and `propext` when required.

Every generated declaration is kernel-checked before emission in an
owner-free replay environment. The final serialized output is then checked
structurally and, by default, replayed through Lean's kernel as a complete
stream before it is written.

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

`--type-check-input` and `--type-check-output` are separate whole-stream kernel
gates. They replay declaration values and compare serialized inductive
metadata with what Lean regenerates. Output replay is on by default; use
`--no-type-check-output` only when the caller deliberately accepts that the
complete final stream will not receive this additional verdict. This opt-out
does not weaken the mandatory per-declaration kernel checks performed during
generation.

## Usage

```console
lean-inductive-models [OPTIONS] IN.ndjson
```

`IN.ndjson` may be `-` for standard input. With no options, all generation
routes and both structural checks run, the final output is replayed through
Lean's kernel, and the transformed export is written to standard output.
Diagnostics go to standard error.

```console
# Generate, check, kernel-replay, and write to a file.
lean-inductive-models -o OUT.ndjson IN.ndjson

# Check an input without generating or writing anything.
lean-inductive-models --no-inductives --check --no-output IN.ndjson

# Full Lean Kernel Arena path, with input replay enabled as well.
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
| `--type-check-output` | on | Replay the complete final output through Lean's kernel. |
| `--mono-levels` | off | Monomorphize universe levels before generation. |
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
oracle. Final ordering places each complete model family before its source
owner and rejects dependency cycles or ambiguous ownership.

Canonical generation can stage model islands and retain compact ordering and
structural-check certificates. Operations that need the complete transformed
AST—currently universe monomorphization and published named/stdout output
kernel replay—use the full-memory path. With generated `--no-output`, the
default output kernel gate instead stages a private candidate, terminates the
generation worker, and replays that serialization in a fresh worker. Thus the
generation and whole-output kernel heaps do not overlap. Inputs unavailable to
compact staging retain the ordinary full-oracle producer fallback, but that
producer likewise terminates before replay. With both `--no-output` and
`--no-type-check-output`, accepted islands are checked and summarized while
live and then discarded: no workspace is opened and no cumulative generated
declaration array is retained. Monomorphization and deliberate legacy/planner
diagnostic modes remain on the full-memory path.

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
