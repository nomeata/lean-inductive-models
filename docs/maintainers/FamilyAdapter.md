# Generic family-adapter design

`InductiveModels.FamilyAdapterPlan` is the source-derived representation for a
future one-layer adapter. It replaces unary/binary, singleton, indexed, nested,
and mutual shape cases with keyed finite arrays. `FamilyAdapterShadow` now
derives this plan from every successfully generated exact source block and its
existing kernel-checked private `Iso`. `Driver.serialiseIso` does not use the
result for route selection, rejection, serialized output, logs, or normal
reports. `runFilterWithFamilyAdapterShadow` is the test-only value observer;
ordinary filtering retains no observations.

The shadow is deliberately incomplete for an exact nested block until its
extra mimic recursors are represented as plan members. Every omitted exact
recursor produces `unrepresentedSourceRecursor`; such a report is not
`complete`. This is an explicit next construction obligation, not a bounded
fallback route.

## Input and identity

The shadow builder consumes an exact source `EDecl`, the private/public names
recorded by `Iso` (including family-member metadata), and installed declaration
types. Source names identify members, constructors, rules, occurrences, and
SCCs. Array positions preserve declaration and telescope order; they do not
decide eligibility.

Each member retains the exact rule-key sequence read from its source `ERec`.
In a mutual family that sequence includes sibling constructors. The validator
requires exact agreement between that sequence and the keyed rule array.

Every recursive occurrence is keyed by its constructor, literal field offset,
expression path, binder depth, minor-hypothesis offset, and target member. A
field may contain any finite number of occurrences; a component may contain
any finite number of source or mimic members. Parameter and result-index
telescopes are arrays retained separately for each member and constructor.
The minor-hypothesis offset is read from the exact `ERec` minor telescope. In
particular, multiple syntactic occurrences inside one nested field share the
single hypothesis Lean provides for that field; source syntax does not invent
additional hypothesis slots.
If that exact association cannot be recovered, the affected occurrence and
rule are omitted from `ShadowCoverage` and a keyed minor-telescope reason is
reported; a dummy ordinal never counts as covered evidence.

The plan contains no fabricated proof names. `FamilyAdapterConstruction` is a
disabled prototype seam that now builds `FamilyAdapterCertificate`: private
member maps, dependent-telescope packers, `encode`/`decode`, both round trips,
one packed result-index equality, and exact installed minor/IH associations.
Construction starts only from a complete exact-source shadow. Every reused
member map and inverse law has its exact installed type checked, and every new
declaration is accepted by the kernel before its name enters the certificate.
Certificates stay as `Name` and `Expr` values in the incremental Lean
environment; they are never serialized through JSON.

The prototype closes direct and infinitary occurrences through arbitrary
finite binder telescopes. A definitionally unchanged nested field is reused
directly. `Iso.containerImplementations` now exposes every generated mimic's
pack, unpack, and two inverse laws together with their named private mimic,
exact installed types, and finite parameter/index prefix arities. The shadow
unifies those types with the whole source field beneath its exact binder path,
requires the inferred target head to be that installed mimic, and assigns a
unique map to each matching `OccurrenceKey`. Construction descends the same
binder path before consuming that key and installed law, so a changed nested
field closes without recognizing `List` or any other container name. Missing,
ambiguous, wrong-target, or changed installed metadata remains a keyed
incomplete report rather than selecting a fallback route.

## Proof construction

The proof is structural, with no clause selected by a cardinality.

1. Traverse the condensation graph of source and mimic SCCs. Build members of
   one SCC simultaneously, using the already kernel-checked private family as
   the recursion oracle.
2. For each constructor, induct over its literal binder telescope. The
   prototype packages the whole dependent telescope, including result indices,
   and generates
   `encode`, `decode`, `decodeEncode`, and `encodeDecode`. It substitutes every
   already-mapped value into later binder types. If the resulting types are
   not definitionally equal, construction returns the keyed
   `dependentFieldTransport` obligation; the current metadata supplies no
   general action of an arbitrary dependent family across distinct carriers.
3. At a recursive occurrence, the prototype uses the target member
   correspondence. At a nested occurrence it composes the source-derived field
   telescope with the existing mimic `pack`/`unpack` laws. All recursive keys
   within that container node must resolve to the same installed equivalence.
   The expression path identifies the occurrence; its syntactic category does
   not choose a separate route.
4. For each exact recursor rule, installed recursor metadata is opened using
   the source-recorded motive and minor arities. Constructor keys select the
   minor and occurrence keys select the literal IH binder, including shared
   hypotheses for multiple occurrences in one field. The remaining recursor
   proof will fold equality transport over those keyed minor hypotheses in
   telescope order. Each fold step abstracts the current
   occurrence and applies `Eq.rec`; the induction is on the finite occurrence
   array, not on a unary/binary case split.
5. Enable the adapter only after all member, constructor, telescope,
   occurrence, round-trip, and iota declarations have been kernel checked.
   Publish the complete family atomically; a partial certificate never enables
   a partial public route.

The current `indexFibre` certificate similarly closes an exact finite index
vector only when the mapped and public vectors are definitionally equal. A
non-definitional moving fibre returns `indexFibreMismatch`; closing it requires
an installed, keyed equality relating the two index vectors. Lean rejects the
stronger source shapes where a constructor result index, or a later field
type, depends directly on a recursive constructor value. Those are kernel
boundaries, not adapter eligibility guards.

## Constraints versus implementation caps

Genuine Lean or mathematical constraints remain checks: strict positivity;
universe and sort correctness; the kernel's elimination restrictions; and the
single-constructor requirement for intrinsic structure projections. Exact key
coverage is also required: one source occurrence key must identify exactly one
slot in its constructor telescope. This says nothing about how many distinct
occurrences the telescope may contain.

Counts such as one or two recursive fields, one result index, one constructor,
one changed mutual member, or a bounded SCC size are implementation caps. None
appears in plan validation, shadow coverage, or route selection. Until proof
construction handles the general finite plan, this adapter remains disabled.

## Regression generation

`test/scripts/generate_family_adapter_fixtures.py` accepts arbitrary finite
parameter samples for occurrence arities, member counts, constructor counts,
and index arities. Its defaults include 0, 1, 2, 3, 5, and 8 only to cross old
implementation boundaries. `FamilyAdapterPlanTest` independently varies every
plan dimension and includes a larger non-default point, while malformed-key
tests exercise structural rejection. These are property-style regression
samples, not a supported-shape list. `FamilyAdapterConstructionTest` also
checks distinct public/private direct and indexed carriers, one real
`mutualOneLayerIso` family, definitionally unchanged nesting, and a distinct
carrier nested field under a function binder closed by an exact keyed
container equivalence. The
shadow regression also requires maps exposed by real nested-model generation.
Source-level guards pin Lean's rejection of a later field or result index that
depends on a recursive constructor value.
