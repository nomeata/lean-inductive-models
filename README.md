# lean-inductive-modules

This is a standalone, provisional extraction of a Lean-export transformation
tool. It is the baseline for further cleanup; the command-line interface and
public specification are not final yet.

`modelgen` reads a Lean 4 NDJSON export and adds ordinary Lean declarations
that model inductive type formers, constructors, recursors, and recursor
reduction rules. Nested and mutual inductives are handled by default. Models
for simple inductives over the tool's primitive basis are currently opt-in.
Generated declarations are checked by Lean before they are emitted.

The repository also contains the experimental `monomorph` universe-level pass
from the extracted package. It is a separate executable and is not part of the
default `modelgen` run.

## Build

The Lean toolchain is pinned in `lean-toolchain`.

```console
lake build
```

## Current command line

```console
.lake/build/bin/modelgen IN.ndjson [-o OUT.ndjson|-] \
  [--check-recursors] [--prim-models] [--quiet]

.lake/build/bin/monomorph IN.ndjson [-o OUT.ndjson] \
  [--mono-recursors] [--default N[,N...]] [--check] [--quiet]
```

Reports from `modelgen` go to standard error. Passing `-o -` writes only the
transformed export to standard output. Without `-o`, the tool checks and
reports but does not write an export.

## Tests

The committed fixtures allow the core suite to run without regenerating Lean
exports:

```console
lake test
lake exe monotest .
```

Some optional corpus checks are skipped when `vendor/arena-tests` is absent.
Fixture regeneration uses `scripts/export-fixture.sh` and may download the
pinned exporter into the repository-local `_tmp/` directory.

## Copyright

See `NOTICE`. No license grant is currently included in this extracted
baseline.
