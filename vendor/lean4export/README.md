# Pinned lean4export patch

`compact-expr-interner.patch` applies only to lean4export revision
`caccfbebbc99077962b3321125b2375bb3fa22db`. Its SHA-256 is
`6f3ea993887612d4e7417c7fc23efe0f8777e05cda992ec90aa22d6afe60e1bc`.

The patch replaces only the expression-ID dictionary. Names, universe levels,
declaration traversal, JSON serialization, and the output format are unchanged.
The compact table uses the same cached `Expr.hash` and exact `Expr.eqv`, and its
array position is the first-seen expression ID. A fixed 100,000,000-entry limit
is above the pinned Mathlib export's observed 95,334,373 expression IDs. It
fails before publishing a new expression record if that limit or the packed
UInt32 link space is exhausted.

Run `test/scripts/check-lean4export-patch.sh` for the pin/integrity gate. Set
`LEAN4EXPORT_DIFFERENTIAL=1` to additionally build the stock and patched pinned
exporters and compare their bytes on the small committed source fixture.
