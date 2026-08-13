# Pinned lean4export patch

`compact-expr-interner.patch` applies only to lean4export revision
`caccfbebbc99077962b3321125b2375bb3fa22db`. Its SHA-256 is
`151c25f6adbfd915ce62786da33352c089653f62d5d3445cc3b38879de19deeb`.

The patch replaces only the expression-ID dictionary. Names, universe levels,
declaration traversal, JSON serialization, and the output format are unchanged.
The compact table uses the same cached `Expr.hash` and exact `Expr.eqv`, and its
array position is the first-seen expression ID. A fixed 100,000,000-entry limit
is above the pinned Mathlib export's observed 95,334,373 expression IDs. It
fails before publishing a new expression record if that limit or the packed
UInt32 link space is exhausted.

At that observed size, the chunked keys use about 763 MiB, packed next links
about 364 MiB, and the fixed 2^25 packed heads 128 MiB. Chunks are at most
8 MiB for keys and 4 MiB for links, so allocation never overlaps two complete
tables. The replaced standard table's 2^27 pointer buckets and roughly
95 million association nodes have a 3.8 GiB lower bound before resize overlap.
This reduction restores the exporter to the workflow's 12 GiB process limit.

Run `test/scripts/check-lean4export-patch.sh` for the pin/integrity gate. Set
`LEAN4EXPORT_DIFFERENTIAL=1` to additionally build the stock and patched pinned
exporters and compare their bytes on the small committed source fixture.
