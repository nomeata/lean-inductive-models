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
remember every node it has emitted for as long as it is writing. Measured on
the pinned Mathlib export with generation disabled, that is **40.5 bytes per
interned arena node** — 393 MB of peak resident set on a 10-million-line
prefix, 856 MB on 20 million, growing linearly with the *output*. With
generation enabled the maps additionally hold every generated island's
expressions live for the rest of the file, where `--no-output` lets them die
at island close; enabling output then costs 820 MB on the same 10-million-line
prefix, against 864 MB for the whole rest of the pass.

Nothing here can be pruned: forgetting an ID would re-emit its node under a
fresh one, which is a valid export but not the same export. Making the map
cheaper than a `Std.HashMap Expr Nat`, not making it smaller, is the available
lever.

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
