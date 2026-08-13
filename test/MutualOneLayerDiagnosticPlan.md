# Plain-mutual partial one-layer implementation plan

The diagnostic fixture has two members in one unindexed recursive SCC.
`MutualLayerA` is the changed member: it has a one-constructor layer with an
ordinary key, a recursive `MutualLayerB`, and a payload depending only on the
key. `MutualLayerB` closes the SCC but has two constructors, so it is an
unchanged, projection-ineligible sibling.

## Adapter boundary

1. Classify the entire installed/source block once, but select changed members
   independently. A changed member must satisfy the existing direct one-layer
   field analysis; an unchanged sibling receives the identity public carrier
   `P_k := M_k`. Reject an empty changed set and fail closed if a selected
   member's exact source recursor/rules cannot be associated.
2. Generate the existing mutual tag/aux block as the private implementation
   `M`. Build one public carrier `P_k` per member: the one-layer carrier for
   changed members and a definitionally identical alias of `M_k` for unchanged
   siblings. Public source names continue to denote `P`, never the private
   implementation.
3. Construct `roll_k : P_k -> M_k` and `unroll_k : M_k -> P_k` simultaneously
   for every owner in the SCC, with `unroll_roll_k` and `roll_unroll_k` laws.
   The unchanged sibling's maps and laws are identity/reflexivity, but remain
   explicit certificate entries so checker and generator agree on the same
   complete family boundary.
4. Rebuild every constructor across the vector of maps. A changed member packs
   its layer after mapping recursive fields with the callee owner's `roll`;
   an unchanged sibling keeps its current public type/value but maps any field
   crossing to a changed member. Derive every public recursor from the private
   simultaneous recursors and prove all source iotas together, using the
   owner-indexed section/retraction laws.

## Exact syntax and keying

- Thread the raw source `EDecl` and raw `ERec` records into the adapter. Public
  carrier, constructor, recursor, recursor-iota, projection, and projection-iota
  statements are exact name-only rewrites of those records. Installed metadata
  remains the proof/layout oracle, not the public syntax oracle.
- Key members by source owner name, constructors by `(owner, constructor)`, and
  rules by `(recursor owner, rule constructor)`. Never associate motives,
  minors, rules, maps, or laws by array position: Lean may emit mutual recursors
  in a different order from the member array.
- Extend `Iso.implementation?` from one interface to an owner-keyed partial
  family certificate. The serialized checker recognizes the tranche only when
  every member's private carrier, both maps, and both laws are uniquely present
  and exact. A partial prefix is malformed, not a request to accept literal
  rules under the legacy classifier.

## Projection boundary

`MutualLayerA`'s key, cross-member recursive child, and dependent payload use
literal projection RHSs. The payload depends only on the ordinary key, so no
generated dependency transport is needed. Its theorem telescope must retain
the source beta-redex. `MutualLayerB` remains multi-constructor and receives no
intrinsic projections. The diagnostic also mutates the payload RHS with an
identity `Eq.rec`; the current checker rejects that old transported spelling,
which must remain true after the family certificate is introduced.
