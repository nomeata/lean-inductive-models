# The output path

Internal notes on how the transformed export is produced and what it costs.
None of this is part of the public contract; for that, see the output contract
and checker contract sections of [`README.md`](../../README.md).

## The writer

Actual generated output is serialized declaration by declaration through one
persistent standard arena writer
([`InductiveModels.DeclarationStreamWriter`](../../src/InductiveModels/Format/Write.lean)),
so its declaration order is the constructive emission order: each accepted
model island immediately before its source owner, every other source
declaration in input order. There is no final global reorder. The writer
retains global interning maps but no cumulative output declaration array.

The no-generation write path continues to write the retained input export.

## What the interning maps cost

Those interning maps are what the output path costs. The export format
addresses names, levels and expressions by ID, and any record may
back-reference a node emitted anywhere earlier in the file, so the writer must
remember every node it has emitted for as long as it is writing. Nothing here
can be pruned: forgetting an ID would re-emit its node under a fresh one, which
is a valid export but not the same export.

What one remembered node costs is set by `Interner` in
[`Format/Write.lean`](../../src/InductiveModels/Format/Write.lean), and it is
**arithmetic off that structure rather than a measurement**: an 8-byte key slot
in a dense array that doubles, plus a 4-byte slot in a probe table that doubles
at a 3/4 load factor. The key array therefore holds 1 to 2 entries per node and
the probe table 1.33 to 2.67 slots per node, so a node costs **13 to 27 bytes**
depending on where the corpus falls between two doublings. At the pinned
Mathlib export's ~99.9M expression nodes both tables sit at 2^27 — 1.07 GB of
keys and 0.54 GB of probe, so **about 16 bytes per node**. A corpus that crossed
2^27 nodes would double both and add about 1.6 GB in one step, and the key
array's doubling is a copy, so both halves are briefly resident. Both growth
rules were checked against the running code rather than read off it: the probe
table's slot count at 10^3, 10^5 and 10^6 entries, and the key array's doubling
from a 10M-element push, whose peak matched the predicted table plus the copy.

The maintained whole-run peaks are the per-phase table in
[`Testing.md`](Testing.md); nothing in CI measures the writer
in isolation, and there is no current in-isolation figure for it.

## Historical: what the `Std.HashMap` writer cost

These are the numbers the interner was built against. **None of them describes
the current writer.** Measured 2026-08-16, recorded in commit `058ff35`, on
prefixes of the pinned Mathlib export, and superseded 37 minutes later by
`d74b872`:

* Generation disabled: **40.5 bytes per interned arena node**. On a
  10-million-line prefix, parse-only peaked at 739,520 KB and parse-plus-write
  at 1,130,860 KB, so 393 MB of peak resident set was the writer's, over 9.9M
  interned nodes; 856 MB on 20 million, growing linearly with the *output*.
* Generation enabled, where the maps additionally hold every generated island's
  expressions live for the rest of the file while `--no-output` lets them die at
  island close: enabling output cost 820 MB on the same 10-million-line prefix,
  against 864 MB for the whole rest of the pass.

Those measurements identified the lever — a cheaper entry, not a smaller
table, since nothing may be forgotten — and `d74b872` pulled it. The comparison
against `Std.HashMap`'s 32-byte `AssocList.cons` cell plus a machine word per
bucket is kept in `Write.lean`, where it is the justification for the structure
that replaced it.

## Transactions and retention

Named output remains in a private sibling until the final compact
semantic/structural verdict commits it; standard output is direct and can
therefore contain a parseable declaration prefix after a late failure. This is
the one part of this file that is user-visible, and it is stated in the README's
Usage section.

When input kernel checking is disabled, both actual output and eligible checked
no-output generation first build a compact source census; each exact source
declaration is trusted-installed for construction, and each generated island is
optionally checked directly in process while its compact certificate is live.
The input is parsed exactly once and the parsed declarations are kept, so
nothing is ever re-read, re-parsed or spooled to disk: the tool opens no file it
was not given on the command line.

Generated logical declarations are checked directly as values, never through
JSON, an output parser or a writer. With both `--no-output` and
`--no-type-check-generated`, accepted islands are summarized while live and then
discarded without any kernel check, and no cumulative generated declaration
array is retained.
