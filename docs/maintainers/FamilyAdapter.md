# Generic family-adapter design

`InductiveModels.FamilyAdapterPlan` is currently an inert schema. No driver,
checker, or exporter imports it. Its purpose is to give the future one-layer
adapter one source-derived representation instead of a collection of
unary/binary, singleton, indexed, nested, and mutual routes.

## Input and identity

The builder consumes the exact source declaration together with the existing
kernel-checked private `Iso`. It records source names as member, constructor,
rule, and SCC keys. Array positions preserve declaration and telescope order,
but are never identities and never decide eligibility.

Each member also retains the exact rule-key sequence read from its source
`ERec`. In a mutual family that sequence includes sibling constructors. Plan
validation compares the installed `RulePlan` sequence against this snapshot;
the later semantic checker must in turn compare the snapshot with the source
metadata in the environment.

Every recursive occurrence is keyed by its constructor, literal field offset,
expression path, binder depth, minor-hypothesis offset, and target member. A
field may contain any finite number of occurrences; a component may contain
any finite number of source or mimic members. Parameter and result-index
telescopes are arrays retained separately for each member and constructor.

Certificates stay as `Name` and `Expr` values in the incremental Lean
environment. They are not serialized through JSON. Before installation, the
semantic checker must infer the recorded declaration types in that same
environment and compare them with the exact types derived from the plan.

## Proof construction

The proof is structural, with no clause selected by a cardinality.

1. Traverse the condensation graph of source and mimic SCCs. Build members of
   one SCC simultaneously, using the already kernel-checked private family as
   the recursion oracle.
2. For each constructor, induct over its literal binder telescope. Package the
   whole dependent telescope, including result indices, and generate
   `encode`, `decode`, `decodeEncode`, and `encodeDecode`. Later binder types
   are transported by the accumulated package equality rather than rebuilt by
   an arity-specific template.
3. At a recursive occurrence, use the target member correspondence. At a
   nested occurrence, compose the generated `G(P) <-> G(M)` correspondence
   with the existing mimic `pack`/`unpack` laws. The expression path identifies
   the occurrence; its syntactic category does not choose a separate route.
4. For each exact recursor rule, fold equality transport over the keyed minor
   hypotheses in telescope order. Each fold step abstracts the current
   occurrence and applies `Eq.rec`; the induction is on the finite occurrence
   array, not on a unary/binary case split.
5. Accept the adapter only after all member, constructor, telescope,
   occurrence, round-trip, and iota declarations have been kernel checked.
   Publish the complete family atomically; a partial certificate never enables
   a partial public route.

## Constraints versus implementation caps

Genuine Lean or mathematical constraints remain checks: strict positivity;
universe and sort correctness; the kernel's elimination restrictions; and the
single-constructor requirement for intrinsic structure projections. Exact key
coverage is also required: one source occurrence key must identify exactly one
slot in its constructor telescope. This says nothing about how many distinct
occurrences the telescope may contain.

Counts such as one or two recursive fields, one result index, one constructor,
one changed mutual member, or a bounded SCC size are implementation caps. None
belongs in plan validation or route selection. If construction for any finite
dimension is not implemented, the generic adapter remains disabled rather
than falling through to another bounded corpus classifier.

## Regression generation

`test/scripts/generate_family_adapter_fixtures.py` accepts arbitrary finite
parameter samples for occurrence arities, member counts, constructor counts,
and index arities. Its defaults include 0, 1, 2, 3, 5, and 8 only to cross old
implementation boundaries. `FamilyAdapterPlanTest` independently varies every
plan dimension and includes a larger non-default point, while malformed-key
tests exercise structural rejection. These are property-style regression
samples, not a supported-shape list.
