# One-layer projection prototype: implementation route

The compile-checked companion is `OneLayerProjectionPrototype.lean`.  Its
private `M` represents the recursive model generated today and its public
`P A = Layer A (M A)` represents one source-constructor layer.  The recursive
projection rule has the literal input function as its right-hand side and its
elaborated type contains no `Eq.rec`.

Status: production implements the unindexed, unnested, source-simple
never-zero `Type` subset for one or two independent recursive fields. The
indexed, nested, and mutual sections below remain prospective design notes.
Exact-source simple `Prop` projection literals are implemented separately
through proof irrelevance.

## Production boundary

Keep the current construction as an implementation fixpoint `M_k`.  Add a
second carrier per real block member:

```
P_k p⃗ i⃗ = { layer : F_k M⃗ p⃗ // resultIndex layer = i⃗ }
```

The equality fibre is omitted for a non-indexed member.  Here `F_k` is the
one-layer constructor telescope: ordinary fields are unchanged and every
recursive occurrence of member `m` contains `M_m`.  It can use the same tight
`PSigma'`/tower machinery already used to hold arbitrary-sort constructor
telescopes; this does not require adding another primitive inductive.

The generated public name `R_k._model` should denote `P_k`; fresh private
implementation names denote `M_k`.  This requires splitting `Iso.selfNames`
into implementation carriers and public carriers.  Route construction and
its existing constructors/recursors initially target the former.  The
correspondence table and final aliases target the latter.  Do this at the
`Iso` boundary rather than teaching each existing simple arm a different
one-layer representation.

For each member generate internal operations

```
roll_k   : P_k p⃗ i⃗ → M_k p⃗ i⃗
unroll_k : M_k p⃗ i⃗ → P_k p⃗ i⃗
unroll_roll_k : ∀ x, unroll_k (roll_k x) = x
roll_unroll_k : ∀ x, roll_k (unroll_k x) = x
```

`roll_k` opens the layer, calls the current private constructor, and, in the
indexed case, transports only that result along the fibre equality.
`unroll_k` runs the current private recursor at motive `P_k`, ignores the
induction hypotheses, stores the original recursive `M` fields, and uses
reflexivity for the result-index fibre.  `unroll_roll_k` follows from the
private constructor iota theorem plus proof irrelevance.  `roll_unroll_k`
follows from the private induction principle.  Thus transport remains inside
the equivalence implementation and never enters a public iota proposition.

## Public declarations

Rebuild each public constructor at its existing mapped type.  It traverses
each recursive field from `P_m` to `M_m` with `roll_m`, packs the resulting
one-layer telescope, and supplies a reflexive result-index equality.

Build intrinsic projections from the layer, not through the private recursor.
An ordinary field is read literally.  A direct or infinitary recursive field
is read and transformed pointwise with `unroll_m`.  Its constructor rule is
proved pointwise with `unroll_roll_m`; the theorem statement is

```
projection (publicConstructor ... field ...) = field
```

with the source field as the literal RHS.  All earlier fields on which a later
field may genuinely depend are ordinary layer fields and reduce directly.
Consequently the `ProjectionField.normalizeProjectionField` transport path in
`Driver.addProjectionModels` is unnecessary for owners using the one-layer
interface.  Keep it during migration for old-route owners, then make
`Check.checkProjection` expect the literal source field for every converted
owner.

## Indexed, nested, and mutual cases

- **Indexed:** store the constructor's computed result indices and an equality
  to the ambient indices in `P_k`.  Constructor packing uses reflexivity.
  Projections do not consume this equality: constructor fields precede the
  result and cannot depend on the ambient result index.  Only `roll_k` uses
  the fibre equality.
- **Nested:** a recursive occurrence under a container needs generated maps
  `mapRoll : G P⃗ → G M⃗` and `mapUnroll : G M⃗ → G P⃗`, plus the pointwise
  section/retraction laws.  Reuse the occurrence traversal and the
  `pack`/`unpack` congruence infrastructure in `InductiveModels.Model`; a recursive
  projection's literal iota proof is the container section law instead of
  bare `funext`.
- **Mutual:** define the vector of `P_k = F_k M⃗` after the current private
  mutual block.  Generate `roll_k`/`unroll_k` for every real member and prove
  both laws by the current simultaneous recursors.  Each constructor maps
  occurrences to the corresponding member's `roll_m`; each projection maps
  them back with `unroll_m`.  Mimic/container members stay implementation
  details and only contribute the nested maps above.

## Recursor consequences

The public recursor cannot simply be renamed from the current one after the
carrier split.  Define it by running the private recursor on `roll_k x` with
the transported motive

```
fun i⃗ m => motive i⃗ (unroll_k m)
```

and convert each private minor's recursive `M_m` argument with `unroll_m`.
The minor-result cast is justified by `roll_unroll` over all recursive fields;
the final result cast is justified by `unroll_roll_k x`.  Public recursor iota
theorems retain the source's literal RHS.  Their proofs compose the private
iota theorem with these equivalence laws and the required `funext`/nested
congruence; proof irrelevance removes equality-proof coherence.  This is a
proof-generation change, not a public statement change.  Rule-K and structure
eta should be re-proved at `P`, while unit-like facts transfer across
`roll`/`unroll`.

## Positivity boundary

The negative test declares an opaque family and tries a later field of type
`Family child` after `child : T`.  Lean rejects the later binder because it
contains an invalid occurrence of the datatype being declared.  Therefore a
kernel-accepted constructor cannot have a genuine later-field dependency on a
recursive value.  Lean may accept a syntactic dependency through a reducible
family that erases the value; after reduction it is definitionally irrelevant
and cannot require transport.  Dependencies on earlier *ordinary* fields are
allowed and are exactly why those fields must be literal layer projections.
