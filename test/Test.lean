import InductiveModels.Driver
import InductiveModels.Mono
import InductiveModels.Order

/-!
# The tool's own oracles, as a test

Run from the repository root: `lake exe test [ROOT]`.

Four axes, and each one has an occupant that would pass the other three:

1. **The counts.** The construction's carrier, constructor, recursor, and
   **one ι theorem per rule of every recursor**, plus two declarations for
   each intrinsic projection (the definition and its reduction theorem) and
   one for each unit-like, structure-eta, or rule-K theorem. Generated support
   records are counted with the first model that needs them. A generator that quietly
   emitted fewer — dropping a round trip, or a mimic, or one constructor's rule
   — still typechecks and measures nothing, so the table is pinned.
2. **The kernel.** Every generated declaration is checked while it is built,
   and the exact serialized model records are checked again in a fork of the
   persistent source-prefix environment with the owner absent. An `ok` here is
   Lean's answer that the emitted model is well typed and owner-independent,
   not the generator's.
3. **The statements.** [`InductiveModels.Check.checkStatementsFor`] rebuilds the
   complete public interface from the exact exported owner records and compares
   it syntactically with the serialized model records. It does not consult the
   replay environment or a kernel-minted owner recursor. Well-typedness is not
   the claim: a generator that stated a different well-typed equation — the
   rule of the wrong member, the hypothesis at one recursor where the export
   names another — would satisfy axis 2.
4. **The round trip.** `parse (render (parse t)) = parse t`, structurally, and
   a file with no nested inductive comes out byte for byte.

-/

open Lean Meta InductiveModels

/-- `(fixture, [(declaration, model size)], [(declaration, decline)])`. -/
abbrev Row := String × List (String × Nat) × List (String × String)

/-- Nested fixtures whose filtered outputs are also committed under
`test/fixtures/inductive-models/filtered`. `cross := true` checks that generation from
the raw export produces the filtered export and that filtering it again is an
identity. -/
def expectedShared : List Row :=
  [ ("nested_iota",
      [("Tree", 15), ("Tree._model._impl.0", 14), ("BTree", 24),
       ("BTree._model._impl.0", 30), ("PT", 15), ("PT._model._impl.0", 14)], [])
  , ("nested_deep", [("DTree", 23), ("DTree._model._impl.0", 20)], [])
  , ("nested_shapes",
      [("Tree", 15), ("Tree._model._impl.0", 14), ("PTree", 14),
       ("PTree._model._impl.0", 24), ("DTree", 23), ("DTree._model._impl.0", 20),
       ("BTree", 14), ("BTree._model._impl.0", 16)], [])
  , ("nested_iota_arm", [("Tree", 15), ("Tree._model._impl.0", 14)], [])
    -- `nested_keying.lean` deliberately declares the legacy-looking name
    -- `UTree._model.self`. Exact declaration-local keying must ignore it:
    -- both nested declarations and their implementation blocks model.
  , ("nested_keying",
      [("Tree", 15), ("Tree._model._impl.0", 14), ("UTree", 15),
       ("UTree._model._impl.0", 14)], [])
  ]

/-- **Accepted routing boundaries, each with a fixture that reaches it.** These
fixtures keep accepted input shapes attached to the exact generator guard that
handles them. `test/scripts/export-inductive-models.sh` rebuilds their exports.

**A decline is compared by prefix**, so that a fixture may pin *which shape*
stopped the generator without pinning the wording of a kernel diagnostic
quoted inside it.

Every `.lean` source here is accepted by Lean's kernel. As a separate source
replay audit, the fixture suite compares the recursors it minted against the
export's on every run; this is independent of the format-only model-statement
gate. Fixtures are named for the shape rather than a transient refusal:
`poly_nested`, `dependent_fields`,
`indexed_decl`, `indexed_container`, `nest_index_cross` and `funext_binder`
are all models now.

**`indexed_container` and `nest_index_cross` are the indexed-container axis.**
`VTree` is the shape; `WTree` says one mimic serves two index values, because
the occurrence is the container at its *parameters*; `UTree` is the
non-degenerate one, since a single index at a constant value cannot distinguish
a telescope that is threaded from one that is dropped — `Tab α : N → N → Type`
has two, `UTree.node` sits at two differing values, and `Tab`'s own recursion
moves them one at a time. `nest_index_cross` is that shape crossed with the
*declaration's* own indices (`CTree`), with a mutual block (`PA`/`PB`), and
with a cycle of mimics whose family recursors are themselves indexed (`XT` over
`ITr`).

**`funext_binder` is a field at a mimic under a binder**, and `infinitary`'s
`HTree`/`RTree`/`OTree` are the same three shapes in a file with no `funext` in
it. **Neither declines any more, and neither does `decline_no_eq`**: a prelude
constant the input does not declare is now *spliced* rather than refused
by the generator, so these two files are the fixtures for the splice and
the polarity they pin has flipped, not gone:

* `decline_no_eq` — the input declares no `Eq`, so `Tree`'s model carries
  Lean's own `Eq`, `Eq.refl` and the `Eq.rec` the kernel mints for it. The
  file's name is now about what it *lacks* rather than what it gets. 15
  declarations plus one for the `Eq`.
* `infinitary` — the input declares no `funext`, so `HTree` splices the
  quotient, `Quot.sound` and `HTree._model._impl.funext` (three declarations on top
  of its 15, the quotient counting once) and `RTree` and `OTree` splice only
  their own `funext`, the quotient being installed by then. This is the file
  that says a splice happens **once**: three declarations need `funext` and
  only the first pays for `Quot`. Intrinsic projection pairs contribute to the
  affected model counts independently of that support splice.
* `funext_binder` is the control. It declares Lean's development itself, so
  no `funext` support is spliced — the input's own `funext` beats a derived
  one — while the same projection roles are still counted.

**`nest_through_mutual` and `nest_mutual_both` cover mutual blocks whose members
nest.** `nest_mutual_both` is the non-degenerate fixture for it — `A`
nests at `List B` and `B` at `Box A`, four block members, two mimics at two
distinct containers, and four recursors `A.rec`, `B.rec`, `A.rec_1`, `A.rec_2`
over one shared motive and minor vector — because with only one member nesting
a single carrier and a per-member carrier family are the same object.
**`nest_through_nested` and `nest_cycle_group` are no longer refusals either.**
Nesting through a container that is *itself* a nested inductive refutes the
assumption that nesting strictly decreases and therefore has a topological
order. `T` nests into `Tree
T`; `Tree`'s own `node` field is `List (Tree T)`; *that* copy's `cons` head is
`Tree T` again, so `pack₀` and `pack₁` are mutually recursive and no emission
order exists. They are not two recursions but one, and Lean already generated
it: `Tree.rec` and `Tree.rec_1`, over a single motive and minor vector.

`nest_cycle_group` is the non-degenerate fixture for that, because
`nest_through_nested`'s single cycle cannot distinguish two things.
`U.mk : List (Tree U) → U` puts a container that anchors **nothing** (`List`
is not nested) at mimic 0, so the family has to be found from mimic 1 and the
mimic-to-family mapping is the transposition rather than the identity.
`V.mk : Box (Tree V) → V` puts an ordinary mimic **outside** the cycle and
depending on it, so the condensation is a real DAG and the cycle has to be
emitted first.

**`nest_mutual_cycle` is the two family axes at once**, because nothing says
they compose. `P`/`Q` is a mutual block that nests through a nested container:
five block members, five recursors over one shared vector, a cyclic pair of
mimics beside an ordinary one, and a carrier family. `R`/`S` crosses the mutual
axis with a level parameter of the declaration's own.

**`nest_family_edges` is the pair of edges two members cannot reach.** A mutual
block of **three** — with two, `A.rec_1` is equally "the first member's
namespace" and "the previous member's", and only three say which. And a cycle
whose family is a **mutually recursive pair of containers** rather than a
nested one, which is the other arm of the family lookup: `C`'s block has two
real members and no nesting where `Tree`'s has one and one.

**`nest_mutual_index` is the mutual axis crossed with the declaration's own
indices**, which nothing tested: `nest_mutual_both` has no index anywhere and
`indexed_decl` is not mutual, so a treatment that read the first member's index
count for every member passes both. `MA : N → Type` and `MB : N → N → Type`
have index telescopes of **different lengths** and the two mimics have none, so
one motive vector carries three distinct arities; each member has a recursive
field whose index differs from its result's, and both members nest. -/
def expectedOwn : List Row :=
  [ ("poly_nested",
      [("PTree", 15), ("PTree._model._impl.0", 14), ("QTree", 22),
       ("QTree._model._impl.0", 28)], [])
    -- **`poly_nested` with use sites**, because `poly_nested` has none: nothing
    -- in it instantiates `PTree.{u}` or `QTree.{u,v}`, so the monomorphization pass
    -- downstream gives every group in it exactly one copy and the pipeline's
    -- per-instantiation behaviour is unobservable. Here `PTree.{u}` is used at
    -- 0, 1 and 2. For `lean-inductive-models` alone it is one more polymorphic nested shape;
    -- it exists to verify that a model does **not** survive monomorphization.
  , ("poly_nested_used", [("PTree", 15), ("PTree._model._impl.0", 14)], [])
  , ("indexed_decl",
      [("ITree", 15), ("ITree._model._impl.0", 14), ("I2", 15), ("I2._model._impl.0", 14),
       ("I3", 15), ("I3._model._impl.0", 14)], [])
  , ("indexed_container",
      [("VTree", 15), ("VTree._model._impl.0", 14), ("WTree", 17),
       ("WTree._model._impl.0", 16), ("UTree", 16), ("UTree._model._impl.0", 16)], [])
  , ("nest_index_cross",
      [("ITr", 15), ("ITr._model._impl.0", 14), ("CTree", 15), ("CTree._model._impl.0", 14),
       ("PA", 29), ("PA._model._impl.0", 26), ("XT", 31), ("XT._model._impl.0", 20)], [])
  , ("dependent_fields",
      [("DTree", 15), ("DTree._model._impl.0", 14), ("ETree", 15),
       ("ETree._model._impl.0", 14), ("KTree", 15), ("KTree._model._impl.0", 14)], [])
    -- **The three places a binder can sit relative to the nesting, without a
    -- `funext` in the export.** All three are shapes Lean accepts and all
    -- three are models in `funext_binder.lean`, which is the same three with
    -- one; here the input declares none and the model derives one from
    -- `Quot.sound` and splices it in. Relative to `funext_binder`, `HTree` pays for the
    -- quotient (one declaration, four records), `Quot.sound` and its own
    -- `funext`; `RTree` and `OTree` find the quotient already installed and
    -- pay for a `funext` alone. A treatment that spliced the quotient once per
    -- declaration would be rejected by the kernel on the second, so these
    -- rows pin the "once" as well as the
    -- derivation.
  , ("infinitary",
      [("FTree", 17), ("FTree._model._impl.0", 16), ("GTree", 15),
       ("GTree._model._impl.0", 14), ("ZTree", 22), ("ZTree._model._impl.0", 30),
       ("HTree", 18), ("HTree._model._impl.0", 14), ("RTree", 16),
       ("RTree._model._impl.0", 14), ("OTree", 22), ("OTree._model._impl.0", 20)], [])
    -- **A field at a mimic under a binder, with a `funext` to prove it with.**
    -- The three positions again — the root (`HTree`), the container's own
    -- recursive field (`RTree`), a container's field at another mimic
    -- (`OTree`) — plus the two that say the treatment is not a one-off: `H2`
    -- has a **two-binder** telescope, so closing only the innermost `funext`
    -- is caught, and `H3.node : List H3 → (N → List H3) → H3` puts a moving
    -- position with a binder beside one without in the *same* constructor,
    -- where the fold builds the two congruences differently.
  , ("funext_binder",
      [("HTree", 15), ("HTree._model._impl.0", 14), ("RTree", 23),
       ("RTree._model._impl.0", 14), ("OTree", 21), ("OTree._model._impl.0", 20),
       ("H2", 15), ("H2._model._impl.0", 14), ("H3", 15), ("H3._model._impl.0", 14)], [])
    -- **That shape crossed with the rest**, because nothing about it on its
    -- own says it survives them — and the cycle in particular does not come
    -- for free: `packFamMinor`/`retractFamilyValue` are a second copy of the
    -- one-at-a-time path and were measured refusing `CycB` before they were
    -- taught the same telescope. `DTel` is a **dependent** two-binder
    -- telescope, `IdxB` puts the binder at an indexed container, `MutB`/`MutC`
    -- inside a mutual block, `CycB` inside a cyclic group of mimics.
  , ("nest_binder_cross",
      [("Tr", 15), ("Tr._model._impl.0", 14), ("DTel", 23), ("DTel._model._impl.0", 14),
       ("IdxB", 15), ("IdxB._model._impl.0", 14), ("MutB", 28), ("MutB._model._impl.0", 26),
       ("CycB", 23), ("CycB._model._impl.0", 20)], [])
    -- **The sort the block lands in.** `PTree : Prop` eliminates only into
    -- `Prop`, so `PTree.rec` and the container's `PL.rec` have **no motive
    -- universe at all**; every recursor's level list is read off the recursor
    -- for that reason, and before it was this file raised `incorrect number of
    -- universe levels PL.rec` — an uncaught exception rather than a decline.
    -- `Eq` is the atom that says the guard is not "the sort is `Prop`": `Eq` is
    -- `Prop`-valued and *does* have a motive universe. `STree` nests through a
    -- container polymorphic over `Sort` rather than `Type`.
  , ("nest_sorts",
      [("PTree", 22), ("PTree._model._impl.0", 14), ("STree", 15),
       ("STree._model._impl.0", 14)], [])
    -- **The sweep.** A claim that there is no shape Lean accepts and this
    -- refuses is worth what was swept for it, so these were written by asking
    -- what else `inductive` allows rather than by a failure arriving. A
    -- container with **no constructors** (`EmpT`), one with an **implicit**
    -- binder (`ImpT`), one with a **`let` in a constructor field's type**
    -- (`LetT` — measured refusing twice before `Gen.zetaHead`), a declaration
    -- **parameter that is a function type** (`FunP`), **depth three** with the
    -- binder deepest (`Deep3`), and `EvT`/`EvU`: a mutual block with a
    -- parameter and an index nesting through an indexed container and through
    -- `List`, one of them under a binder — every axis at once.
  , ("nest_odd_shapes",
      [("EmpT", 21), ("EmpT._model._impl.0", 10), ("ImpT", 14), ("ImpT._model._impl.0", 16),
       ("LetT", 22), ("LetT._model._impl.0", 22), ("FunP", 15), ("FunP._model._impl.0", 14),
       ("Deep3", 31), ("Deep3._model._impl.0", 26), ("EvT", 29), ("EvT._model._impl.0", 26)], [])
    -- **No `Eq` in the input at all**, which used to be a refusal and is now a
    -- splice: 15 declarations plus Lean's own `Eq`. The file is still named
    -- for what it does *not* declare.
  , ("decline_no_eq", [("Tree", 16), ("Tree._model._impl.0", 14)], [])
  , ("nest_through_mutual", [("A", 29), ("A._model._impl.0", 20)], [])
  , ("nest_mutual_both", [("A", 28), ("A._model._impl.0", 34)], [])
  , ("nest_through_nested", [("Tree", 15), ("Tree._model._impl.0", 14), ("T", 23), ("T._model._impl.0", 20)], [])
  , ("nest_cycle_group",
      [("Tree", 15), ("Tree._model._impl.0", 14), ("U", 23), ("U._model._impl.0", 20),
       ("V", 30), ("V._model._impl.0", 34)], [])
  , ("nest_mutual_cycle",
      [("Tree", 15), ("Tree._model._impl.0", 14), ("P", 37), ("P._model._impl.0", 32),
       ("R", 21), ("R._model._impl.0", 20)], [])
    -- **`C`/`D` is a plain mutual block** — the pair of containers `X` cycles
    -- through — so the *second* construction (`src/InductiveModels/Mutual.lean`) models
    -- it, and it heads this row because the export declares it first. Two
    -- members and four constructors: the tag, the carrier, two type formers,
    -- four constructors, two recursors and four ι theorems is 14.
  , ("nest_family_edges",
      [("C", 14), ("A1", 34), ("A1._model._impl.0", 40), ("X", 23),
       ("X._model._impl.0", 20)], [])
  , ("nest_mutual_index", [("MA", 32), ("MA._model._impl.0", 38)], [])
    -- **`nest_fam_arg` is the head-normalization sweep and has moved to `expectedPrim`**,
    -- because the redex it exists for reaches layer 3 as well and that is
    -- where it now has to be measured. The row there asserts everything this
    -- one did — the nested and mutual counts, in the same order — and the
    -- composition's third step on top.
    -- ── the second construction: a plain mutual block ──────────────────────
    --
    -- **`src/InductiveModels/Mutual.lean`, and its coverage is its own.** A plain mutual
    -- block is not the nested construction at zero mimics — that is the
    -- identity — so none of the rows above says anything about it. Before
    -- metadata, the count is `2 + 2r + 2c` for `r` members and `c` constructors:
    -- the tag, the carrier,
    -- one type former and one recursor per member, one definition and one ι
    -- theorem per constructor. Each eligible projection adds its definition
    -- and reduction theorem, each metadata role adds one theorem, and the first
    -- such model may also carry tight-pair/PUnit support records. Plus Lean's `Eq`
    -- where the input has none.
    --
    -- **Three members everywhere**, because two cannot distinguish an ordering,
    -- and unequal constructor counts within a block, because equal ones let a
    -- generator that flattened the members wrongly still land every minor at
    -- the right arity.
  , ("mutual_shapes", [("A", 30), ("PA", 55), ("UA", 54)], [])
    -- The indices. `T0`/`T1`/`T2` is the shape; `MA`/`MB`/`MC` have index
    -- telescopes of **different lengths**, which is what the tag exists for;
    -- `DA`/`DB` differ in the index *type* at the same sort; `SA`/`SB`/`SC` is
    -- the `Prop` family indexed by `Type 1`, the only shape in the tree where
    -- the tag's own sort is not `Sort 1`; `VA`/`VB` has an index type that
    -- mentions a parameter.
  , ("mutual_index", [("T0", 32), ("MA", 20), ("DA", 14), ("SA", 18), ("VA", 12)], [])
    -- `Prop`, where a block of several members has **no motive universe** and
    -- the auxiliary inductive may still have one of its own. Read off each
    -- recursor and never off the sort.
  , ("mutual_prop", [("Even", 12), ("M0", 16), ("Sa", 22)], [])
    -- A member that recurses into nothing: only one member recursive, a member
    -- with **no constructors**, and the K-rule shape. It is isolated because a
    -- replay implementation that recomputes `isRec` per member disagrees with
    -- Lean's block-level flag on both the input and generated output.
  , ("mutual_nonrec", [("OA", 28), ("EA", 14), ("Ka", 12)], [])
    -- The sweep: a `let` in a field's type, implicit binders and a
    -- `Sort`-valued field, a **dependent** index telescope, an index at a
    -- parameter (so the tag's sort is `max 1 (u+1)` and not a numeral), and a
    -- parameter that is a function type.
  , ("mutual_odd_shapes", [("LA", 62), ("IA", 58), ("WA", 35), ("QA", 35), ("FA", 39)], [])
    -- `KB._model.self` is intentionally a legacy-looking squatter. Under the
    -- declaration-local contract it is irrelevant, so both mutual blocks
    -- model; this preserves the regression test that a legacy name is ignored.
  , ("mutual_keying", [("KA", 43), ("GA", 35)], [])
    -- ── the two composed constructions ────────────────────────────────────
    --
    -- **The axis only the composition reaches.** Lean's nested specialisation
    -- writes a block whose members' sorts agree without being the same term —
    -- five of Mathlib's 41 declined on it — and no fixture over what
    -- `inductive` *declares* could find it, because it is a shape the
    -- elaborator forbids and the kernel writes. `PS` is it; `PT` and `PF` are
    -- the two guesses that did not reproduce it and `Q` is the control.
    -- Put `==` back where `isLevelDefEq` is and `PS._model._impl.0` declines alone.
  , ("compose_sorts",
      [("PT", 23), ("PT._model._impl.0", 14), ("PF", 15), ("PF._model._impl.0", 14),
       ("PS", 15), ("PS._model._impl.0", 14), ("Q", 14), ("Q._model._impl.0", 14)], [])
  ]

/-- **The simple-model construction's rows.**

`prim_shapes` is one positive occupant per route variant — the counts pin the
shape of each model (`self + ctors + rec + iotas`, its exact projection and
metadata roles, plus spliced basis declarations on the first model that needs
them). **No model splices a
`funext` or a `Quot.sound` any more**: `PU` cost both while its carrier was
the `False`-Π singleton. The derived lift's structure eta is definitional;
only equality between two opaque lifted inhabitants uses a recursor and proof
irrelevance in the internal uniqueness helper.
The role histogram distinguishes those support declarations from the
unit-like, structure-eta, rule-K, and projection declarations now emitted.
`prim_declines` pins former refusal boundaries as positive routing regressions;
`P` inside it is the ordinary indexed control. `Eq` is
**exempt** in all four, because all four declare it — its own row in the
report and not a decline, which is why the expected list
below reads `exempt ++ declined` and why one extra check per row says nothing
but a basis primitive reaches the first of the two.

`prim_graph` is **arm G** — the recursive subsingleton by the graph of its own
recursion, the arm that took `Acc` out of the basis. Its base counts are the twelve
declarations of the construction (`self`, `ctor_0`, `ind`, the six graph
declarations, `rec_0`, `rec_graph`, `iota_0_0`) plus whatever that shape
splices, and **the split between the shapes is the axiom table**: `G1` has no
binder on its recursive field, so it reaches no `funext`; `G4`, the next shape
with a binder, pays the quotient, `Quot.sound` and a derived `funext`; `Ac`,
`G2` and `G3` need only their own `funext`. Projection pairs are counted on top
of this support split. A version that asked for `funext` per *arm* rather than
per *shape* remains red here.
`prim_graph_pre` is the same arm on an input that declares ordinary `PSigma`,
`Nonempty` and `Classical.choice` itself. `PSigma'` is the pair support the arm
splices; both source inductives model beside it, demonstrating that neither
ordinary `PSigma` nor `Nonempty` is a basis primitive.
In `prim_graph` `Nonempty` is *spliced* rather than declared, and it is
modelled there too — that row checks the splice-and-model invariant, and it is
the fixture that would go red if layer 3 went back to being unable to model
what it introduces. It appears exactly once despite two shapes needing it,
which is the re-modelling guard.
`Inf` in `prim_declines` was a refusal until the graph arm landed, and
`Inf.below` beside it until the index axis closed — as were every other
`.below` declaration Lean mints for these shapes, `prim_idx`'s `Rxh` and `Rvx`
(`Inf.below` and `Acc.below` written deliberately) and `prim_graph`'s whole
`G*.below` column. Their index is `T.mk a`, which is not one of the
constructor's own data fields but **is a proof**, and two proofs of one
proposition are one term to the kernel: the inversion is statable at an
arbitrary index with no transport at all by proof irrelevance.
Data-valued non-pivots take an explicit packed transport. `BadC` reaches the
one-index case; `Rgd` beside it in `prim_idx` puts a proof-valued non-pivot in
front of the data one, and their `.below` declarations add the kernel-generated
proof index.
Arm F models its whole row of the same axis — a pivot anywhere in the
telescope, an expression over a data or a proof field beside it — so `MixI`
and `SvIx` in `prim_declines` moved from its declines to its models in the
commit that added `prim_idx`. `prim_idx` is the grid that records the two arms'
shared limit.
`BoxF` is no longer the level-incompleteness decline.  Its field
`((α → β) → β)` keeps an `imax` inside the outer domain after a shallow
codomain box, but recursive boxing transforms the whole Π tree.  Every atomic
leaf gains a never-`Prop` `PSigma'` codomain, every `imax` therefore normalizes
to `max`, and the forward and inverse maps are definitionally inverse.  The
seven declarations recorded below include its intrinsic projection and eta;
no level-normalizer relaxation or axiom is involved. -/
def expectedPrim : List Row :=
  [ -- A non-indexed tuple spine with one real child and a later field whose
    -- written owner mention β-reduces away.  The payload is non-recursive, so
    -- `Dead.step` consumes exactly one predecessor and the ordinary tuple
    -- route emits its six public declarations.
    ("nonindexed_vanishing", [("N", 15), ("Dead", 6)],
      [("Eq", "prim model: a basis primitive")])
  -- The two small-elimination seams under the derived exact-sort lift. `MI` forces the pair
    -- motive at two distinct result indices; `MR.step` forces a recursive
    -- carrier through `down` in the constructor and through `down`/`up` in the
    -- pair's element projection; `MRI` crosses both at a changing child fibre.
    -- Each has six public declarations; the first model in each raw export also
    -- pays for the `Eq` and tight-pair/PUnit support records.
  , ("maybe_zero_indexed", [("MI", 15)], [])
  , ("maybe_zero_recursive", [("MRI", 15), ("MR", 6)], [])
  -- Lifted arm F at its minimum: one proof field and one constant result
  -- index. The latter forces the packed equation; the existing one-field
  -- direct-carrier route is index-free. At positive `u`, forgetting the
  -- exact-sort lift boundary is a kernel type error; at `u = 0`, the same declaration
  -- checks the genuinely propositional end.
  , ("degenerate_graph", [("DG", 15)], [])
  , ("prim_shapes",
      [("Tri", 17), ("TagS4", 10), ("TagS3", 8), ("Weave", 10), ("Opt", 6),
       ("IdxP", 6), ("Le3", 8), ("Le3.below", 8), ("PM", 6), ("Emp", 2),
       ("Conj3", 10), ("PU", 6), ("Sv", 5), ("PE", 2), ("MNm", 8), ("IdxS", 5),
       ("Dec", 6), ("Conj", 8), ("TagS2", 8), ("TagS", 6), ("PT", 8),
       ("Tor", 8), ("Hq", 5), ("Boxed", 9), ("PI", 7), ("Sub", 9),
       ("UL", 7), ("Lst", 6), ("TrL", 7), ("Big", 7), ("PF", 7)],
      [ ("Eq", "prim model: a basis primitive")])
  -- **`Branch` and `Binder` are on the other side of the boundary now**, and
  -- this row is where that is recorded: they are the two shapes this file was
  -- built to refuse — a branching constructor and a recursive occurrence under
  -- a binder — and arm W models both. `Branch` is 213
  -- declarations because it is the first W target in the file and so the one
  -- that carries the W core; `Binder` behind it is its own dozen.
  --
  -- `_wcore.Acc` is 13 at every one of these rows now: the fragment carries
  -- `Nonempty` and `Classical.choice` itself since the untagged core widened it, so the
  -- graph arm splices neither wherever the core has already gone in.
  , ("prim_declines",
      [("P", 15), ("Idx", 5), ("Inf", 16), ("Nonempty", 4), ("Branch", 213),
       ("_wcore.Subtype", 9), ("_wcore.List", 6), ("_wcore.Sigma", 9),
       ("_wcore.Option", 6), ("_wcore.Exists", 4), ("_wcore.And", 8),
       ("_wcore.False", 2), ("_wcore.Decidable", 6), ("_wcore.PUnit", 6),
       ("_wcore.True", 6), ("_wcore.Or", 6), ("Iff", 8), ("_wcore.Acc", 13),
       ("_wcore.WellFounded", 6), ("_wcore.Bool", 6), ("_wcore.HEq", 5),
       ("_wcore.PProd", 9), ("MixI", 4), ("Inf.below", 18), ("Binder", 12),
       ("BoxF", 7), ("SvIx", 4)],
      [ ("Eq", "prim model: a basis primitive")])
  -- **The index axis**, as the explicit grid documented by
  -- `test/fixtures/inductive-models/prim_idx.lean`.
  -- Arm F's row models — `Fg` the all-ground control, `Fdup` one data field at
  -- two index positions, `Fdep` a non-pivot whose type mentions a pivot,
  -- `Fall3` every index a pivot and therefore no equation at all, `Fxh` an
  -- index expression over a proof field — and **arm G's row models too now**,
  -- because at a non-pivot whose own type is a `Prop` the two index vectors
  -- are two proofs of one proposition and the kernel identifies them.
  --
  -- **The base counts here are the arms, not the cells.** `Rv` is the first
  -- arm-G model in the file and carries the splice (`PSigma'`,
  -- `Nonempty`, `Classical.choice`, the quotient and a derived `funext`);
  -- `Inf` behind it is arm G's twelve declarations with nothing left to
  -- splice; `N` is 9 for the `Type` route's own basis. Every arm-F cell is 4 —
  -- the type former, constructor, recursor and recursor-local ι theorem —
  -- including `Fall3`, whose carrier
  -- packs nothing and whose recursor builds no `Eq.rec`. The **13**s are the
  -- twelve plus the `funext` `Graph.unique`'s congruence needs when a
  -- recursive field carries binders, exactly as in `prim_graph`. Projection
  -- pairs and metadata theorems are then added exactly where the exported
  -- kernel roles demand them. **Mixedness costs nothing** beyond those roles —
  -- that is the point of the arm, and these counts are where it is measured.
  --
  -- `Rxh` and `Rvx` are `Inf.below` and `Acc.below` written deliberately, and
  -- `Inf.below`, `Rv.below`, `Rxh.below` and `Rvx.below` are the same shape
  -- arriving by accident — which is the fixture saying the boundary is where
  -- it says it is, now from the green side.
  --
  -- `Rgd` is a proof non-pivot followed by a data non-pivot; `Rgd.below` adds
  -- the dependent proof index generated by the kernel. Both exercise the
  -- graph inversion's packed transport. `Fmid` and `FChain` remain the
  -- positive arm-F controls for one and several dependent pivot transports;
  -- `arm_f_zip` isolates the wider zipper cases.
  , ("prim_idx",
      [("N", 15), ("Rv", 17), ("Nonempty", 4), ("Rvx", 13), ("Inf", 14),
       ("Rxh", 18), ("Rxh.below", 22), ("FChain", 4), ("Rgd", 16),
       ("Rgd.below", 20), ("Fam", 6), ("Inf.below", 18),
       ("Fg", 5), ("Rv.below", 13), ("Fall3", 4), ("Fxh", 6), ("Fmid", 4),
       ("Fdep", 4),
       ("Rvx.below", 13), ("Fdup", 4)],
      [ ("Eq", "prim model: a basis primitive")])
  , ("arm_f_zip",
      [("FTwo", 11), ("FProof", 4), ("FChain", 4), ("FEndpoint", 4)],
      [ ("Nat", "prim model: a basis primitive")
      , ("Eq", "prim model: a basis primitive")])
  , ("prim_graph",
      [("G1", 23), ("Nonempty", 4), ("G4", 15), ("G4.below", 13), ("Ac", 13),
       ("N", 8), ("BadC", 14), ("BadC.below", 18), ("Ac.below", 13),
       ("G3", 13), ("G3.below", 13),
       ("G1.below", 18), ("G2", 13), ("G5", 13), ("G5.below", 13),
       ("G2.below", 13)],
      [ ("Eq", "prim model: a basis primitive")])
  , ("prim_graph_pre", [("Nonempty", 4), ("Ac", 20), ("Ac.below", 13),
      ("PSigma", 11)],
      [ ("Eq", "prim model: a basis primitive")])
  -- **The W arm's foundation.** `w_core.ndjson` is the transitive closure of
  -- the core's six roots — the export `lean4export` emits for
  -- `--#export WT.W WT.sup WT.Wrec WT.Wrec_iota instDecidableEqNat
  -- WT.decEqAll`, 20 inductive blocks and 3 axioms — and the W arm's plan is
  -- to splice it and model what it splices.
  --
  -- **The last two roots are why this row is worth re-reading rather than
  -- re-running.** `instDecidableEqNat` is the `DecidableEq Nat` the tagged
  -- instantiation needs and brought 11 declarations and **no** inductive;
  -- `WT.decEqAll` is the untagged one's `DecidableEq A` and took the
  -- export from 163 records to 208, of which exactly **one** is an inductive,
  -- `Nonempty`. That one is why this row is a row: had nobody checked, the arm
  -- would be emitting an unmodelled inductive. This row is what says the plan
  -- is sound — **every inductive the core reaches models**, except the two
  -- that are the basis exemption.
  --
  -- `Acc` is the interesting entry three times over. It is 12 declarations
  -- because it is arm G's graph route and this input has both the `Nonempty`
  -- and the `Classical.choice` it would otherwise splice; it is **the only
  -- model in the fragment that spends `Classical.choice`** at the tagged
  -- instantiation; and it is **last in the list rather than in the middle**,
  -- because those two are declared *after* it here — `Acc` arrives through
  -- `WellFounded.fix` and `Nonempty` only through `Classical.propDecidable`.
  -- This is the late-primitive class rather than a name that
  -- is lost, and [`InductiveModels.lateSpliceNames`] is what holds the model back
  -- until the input has caught up. Without that it is a decline, and this row
  -- is where the difference shows.
  --
  -- `Subtype`, `Sigma`, `And`, `Iff`, `WellFounded`, and `PProd` expose
  -- intrinsic projection roles. Their larger
  -- counts include the exact model definition and literal reduction theorem
  -- for each primitive projection. Non-propositional structure-like carriers
  -- additionally receive one eta theorem; unit-like and K-like declarations
  -- receive their own one-theorem metadata roles.
  , ("w_core",
      [("Iff", 8), ("Nonempty", 4), ("Subtype", 16), ("List", 6), ("Sigma", 9),
       ("Option", 6), ("Exists", 4), ("And", 8), ("False", 2), ("Decidable", 6),
       ("True", 6), ("Or", 6), ("Acc", 12), ("WellFounded", 6), ("Bool", 6),
       ("HEq", 5), ("PProd", 9)],
      [ ("Eq", "prim model: a basis primitive")
      , ("PUnit", "prim model: a basis primitive")
      , ("Nat", "prim model: a basis primitive")])
  -- **Arm C**, at one and at many recursive slots, and
  -- the three rows below the models are the arm's boundaries.
  -- Every `X._model._impl.skel` beside an `X` is the spliced index erasure being
  -- modelled in turn, so a row here going missing
  -- is arm C emitting a skeleton it did not model — the thing `Iso.requires`
  -- exists to make impossible.
  --
  -- `Mx`, `Sm3` and `Br` are the **multi-slot** occupants and `Inf2`, `Cf` and
  -- `Bif` the **infinitary** ones, and between them they are the reason this
  -- row grew the W fragment. Arm C runs at `erasureBare`: a constructor may
  -- have any number of recursive fields and each may sit under binders of its
  -- own, the erasure replaces each occurrence and keeps those binders, and the
  -- spliced skeleton that comes out **branches and is infinitary** — so it is
  -- arm W that models it, and the first skeleton to be reached carries the
  -- splice. That is `Bif._model._impl.skel` at 215 here, and the eighteen `_wcore`
  -- rows after it are the fragment being modelled in turn (`Iso.requires`'
  -- rule). Every other `_model._impl.skel` is its own dozen, because by then the
  -- fragment is in.
  --
  -- **`Bif._model._impl.skel`'s 215 is an ordering fact, not a fact about `Bif`**, in
  -- exactly the sense the arm W row below records for `Tree`: the fixture's
  -- declaration order decides which skeleton pays for the splice.
  --
  -- **`Inf2`, `Cf`, and `Bif` model successfully.** `Cf` is the infinitary
  -- erasure shape. The source's
  -- header carries the six mutations behind them and says which occupant each
  -- is red at; two of the six are red at exactly one, `Cf` and `Bif`.
  --
  -- **The erasure guard has no occupant left in this file** and the header
  -- says why: every shape it still refuses arrives from a specialisation and
  -- cannot be written in a `prelude` source. `nest_fam_arg`'s `OK` and `Key`
  -- are the positive layer-3 occupants for discarding a βζ-dead mention, and
  -- the row below asserts their auxiliary models and erased skeletons.
  , ("prim_carve",
      [("N", 15), ("P", 6), ("Bif", 8), ("Bif._model._impl.skel", 215),
       ("_wcore.Subtype", 9), ("_wcore.List", 6), ("_wcore.Sigma", 9),
       ("_wcore.Option", 6), ("_wcore.Exists", 4), ("_wcore.And", 8),
       ("_wcore.False", 2), ("_wcore.Decidable", 6), ("_wcore.PUnit", 6),
       ("_wcore.True", 6), ("_wcore.Or", 6), ("Iff", 8), ("_wcore.Acc", 13),
       ("_wcore.WellFounded", 6), ("_wcore.Bool", 6),
       ("_wcore.HEq", 5), ("_wcore.PProd", 9), ("Nonempty", 4),
       ("Cf", 8), ("Cf._model._impl.skel", 12), ("Inf2", 8), ("Inf2._model._impl.skel", 12),
       ("Vec", 8), ("Vec._model._impl.skel", 6), ("Bl", 10),
       ("Bl._model._impl.skel", 8), ("IBox", 16), ("IBox._model._impl.skel", 7),
       ("Vc", 8), ("Vc._model._impl.skel", 6),
       ("Mx", 8), ("Mx._model._impl.skel", 12),
       ("Two2", 8), ("Two2._model._impl.skel", 6), ("Fn", 8), ("Fn._model._impl.skel", 6),
       ("Sm3", 8), ("Sm3._model._impl.skel", 12), ("Br", 8), ("Br._model._impl.skel", 12),
       ("NoBase", 10), ("NoBase._model._impl.skel", 8),
       ("Tri3", 8), ("Tri3._model._impl.skel", 6)],
      [ ("Eq", "prim model: a basis primitive")])
  -- Arm W's two recursive-boxing seams. `WData` stores a non-recursive
  -- `((α → β) → β)` in the label tower; `WBind` stores the same type
  -- as an infinitary child's binder in the branch tower. The former is first
  -- and therefore carries the W fragment, while the latter is the arm's own
  -- twelve declarations. Both remain on the tagged W instantiation.
  , ("w_imax",
      [("WData", 224), ("_wcore.Subtype", 9), ("_wcore.List", 6),
       ("_wcore.Sigma", 9), ("_wcore.Option", 6), ("_wcore.Exists", 4),
       ("_wcore.And", 8), ("_wcore.False", 2), ("_wcore.Decidable", 6),
       ("_wcore.PUnit", 6), ("_wcore.True", 6), ("_wcore.Or", 6),
       ("Iff", 8), ("_wcore.Acc", 13), ("_wcore.WellFounded", 6),
       ("_wcore.Bool", 6), ("_wcore.HEq", 5), ("_wcore.PProd", 9),
       ("Nonempty", 4), ("WBind", 12)],
      [("Eq", "prim model: a basis primitive")])
  -- **Arm W**, and this row is three claims at once.
  --
  -- The four models are the shapes the tuple tower cannot express: `Wt` is a
  -- six-constructor target, `Tree` the same branching at a
  -- parameter and a level parameter, `Br` an infinitary child whose binder is a
  -- parameter, and `Dep` a data tower whose second field depends on its first.
  --
  -- **`Tree` is 224 declarations because it is the first W target in the file**
  -- and therefore the one that carries `Nat`, `PSigma'`, `PUnit`, and the W
  -- core splice. Every later target carries only its own construction and
  -- exact public feature roles. So the number is a property of *ordering* and
  -- not of `Tree`, and if it
  -- moves, the fragment changed size — which is a thing to notice, since
  -- `InductiveModels.wCoreText` is not in Lake's trace.
  --
  -- **The eighteen rows between it and `Q` are the fragment being modelled in
  -- turn** — `Iso.requires`' rule, the same one arm C's skeleton is under. A
  -- row going missing here is arm W emitting an unmodelled inductive in front
  -- of a consumer. `Iff`, `Nonempty` and `Classical.choice` carry no prefix on
  -- purpose: they are among the twenty names the fragment shares with the
  -- input, because downstream consumers key axioms on their exact names and
  -- statements.
  --
  -- **`Bad`, `Wty` and `Utd` are the untagged instantiation.** Nothing in this row's counts says which
  -- instantiation a target took — `#print axioms` does, and that is the report
  -- the section carries: these three at `[propext, Classical.choice,
  -- Quot.sound]` against every other target's `[propext, Quot.sound]`.
  -- `Twin`, `Mixed`, `TwinInf`, and `Prefix` are the binary one-layer
  -- public-carrier tranche. `Triple` deliberately remains on the legacy W
  -- route: its row is present, while the assertion in `runOne` requires the
  -- one-layer private certificate to be absent.
  , ("prim_w",
      [("Tree", 224), ("_wcore.Subtype", 9), ("_wcore.List", 6), ("_wcore.Sigma", 9),
       ("_wcore.Option", 6), ("_wcore.Exists", 4), ("_wcore.And", 8),
       ("_wcore.False", 2), ("_wcore.Decidable", 6), ("_wcore.PUnit", 6),
       ("_wcore.True", 6), ("_wcore.Or", 6), ("Iff", 8), ("_wcore.Acc", 13),
       ("_wcore.WellFounded", 6), ("_wcore.Bool", 6),
       ("_wcore.HEq", 5), ("_wcore.PProd", 9), ("Nonempty", 4), ("Wty", 23),
       ("Triple", 16), ("P", 6), ("Q", 8), ("Wt", 20),
       ("Dep", 12), ("Bad", 12), ("TwinInf", 23), ("Br", 12), ("Twin", 22),
       ("Prefix", 26), ("Utd", 14), ("Mixed", 25)],
      [ ("Eq", "prim model: a basis primitive")])
  -- **The head-normalization sweep, run through all three layers.** `RB α β`'s second
  -- parameter is a family, so specialising it leaves the constructor field
  -- `β k` as the redex `(fun _ => B₀) k` in the block — and the block is
  -- exactly what the composition hands layer 3, so the redex arrives *here*
  -- too. `JT` and `PT` are `Lean.Json` and `Lean.PrefixTreeNode` at that
  -- shape, and their `_model._impl.aux` families were the two declarations the
  -- Mathlib run reported as **infinitary** until the guards in
  -- `src/InductiveModels/Simple.lean` started reading a field's head through
  -- [`InductiveModels.headNorm`], the same function used by layer 1's
  -- three readers. Nine `_model._impl.aux` rows here are that repair; `Zeta`'s is
  -- the one that needs ζ and not β alone.
  --
  -- The row asserts everything the old non-prim `nest_fam_arg` row did — the
  -- nested and mutual counts, in the same order — and the third step besides,
  -- so nothing moved to get here. **`OK` nests in the container's *first*
  -- argument** and was a model at layer 1 before and after the normalization fix, so
  -- the table lives in one file and a repair that passes the gap by breaking
  -- the shape beside it is caught; eleven of the twelve were red on the commit
  -- that closed the gap and the twelfth is `OK`, and the source's table says
  -- which mutation each one kills.
  --
  -- **`RB` is 215 because it is this file's first W target** and therefore the
  -- one that carries the fragment's splice: `RB.node` has two recursive
  -- fields, so the tuple tower declines it and arm W models it. The eighteen
  -- `_wcore` rows after it are the fragment being modelled in turn
  -- (`Iso.requires`' rule). Both numbers are facts about *ordering*.
  --
  -- **Two formerly declining instances of the same erasure boundary.**
  --
  -- * `OK` and `Key` are the **vanishing mention**: the family parameter is
  --   `fun _ => N`, so the field is `(fun x : T … => N) k`, whose reduct is
  --   `N` and which is therefore not recursive at all — but the written
  --   domain mentions `T` in the discarded binder. The internal skeleton
  --   normalises exactly this domain rather than replacing it, so both aux
  --   families and both skeletons model. Their public declarations retain the
  --   literal redex; `VanishingErasureTest` checks that distinction directly.
  -- `Flat` is the positive control: its nested specialization reaches arm C
  -- through a skeleton with no base constructor, which arm E models as the
  -- exact empty carrier.
  , ("nest_fam_arg",
      [("N", 15), ("Opt", 6), ("L", 6), ("Vec", 8), ("Vec._model._impl.skel", 6),
       ("RB", 215),
       ("_wcore.Subtype", 9), ("_wcore.List", 6), ("_wcore.Sigma", 9),
       ("_wcore.Option", 6), ("_wcore.Exists", 4), ("_wcore.And", 8),
       ("_wcore.False", 2), ("_wcore.Decidable", 6), ("_wcore.PUnit", 6),
       ("_wcore.True", 6), ("_wcore.Or", 6), ("Iff", 8), ("_wcore.Acc", 13),
       ("_wcore.WellFounded", 6), ("_wcore.Bool", 6),
       ("_wcore.HEq", 5), ("_wcore.PProd", 9), ("Nonempty", 4),
       ("RB2", 6), ("Ctr", 9),
       ("OK", 15), ("OK._model._impl.0", 14), ("OK._model._impl.0._model._impl.tag", 6),
       ("OK._model._impl.0._model._impl.aux", 10),
       ("OK._model._impl.0._model._impl.aux._model._impl.skel", 14),
       ("JT", 15), ("JT._model._impl.0", 14), ("JT._model._impl.0._model._impl.tag", 6),
       ("JT._model._impl.0._model._impl.aux", 12),
       ("JT._model._impl.0._model._impl.aux._model._impl.skel", 16),
       ("PT", 17), ("PT._model._impl.0", 16), ("PT._model._impl.0._model._impl.tag", 6),
       ("PT._model._impl.0._model._impl.aux", 10),
       ("PT._model._impl.0._model._impl.aux._model._impl.skel", 14),
       ("PTP", 17), ("PTP._model._impl.0", 16), ("PTP._model._impl.0._model._impl.tag", 6),
       ("PTP._model._impl.0._model._impl.aux", 10),
       ("PTP._model._impl.0._model._impl.aux._model._impl.skel", 14),
       ("Deep", 23), ("Deep._model._impl.0", 20), ("Deep._model._impl.0._model._impl.tag", 8),
       ("Deep._model._impl.0._model._impl.aux", 14),
       ("Deep._model._impl.0._model._impl.aux._model._impl.skel", 18),
       ("Idx", 23), ("Idx._model._impl.0", 20), ("Idx._model._impl.0._model._impl.tag", 8),
       ("Idx._model._impl.0._model._impl.aux", 14),
       ("Idx._model._impl.0._model._impl.aux._model._impl.skel", 18),
       ("Both", 15), ("Both._model._impl.0", 14), ("Both._model._impl.0._model._impl.tag", 6),
       ("Both._model._impl.0._model._impl.aux", 10),
       ("Both._model._impl.0._model._impl.aux._model._impl.skel", 14),
       ("Two", 15), ("Two._model._impl.0", 14), ("Two._model._impl.0._model._impl.tag", 6),
       ("Two._model._impl.0._model._impl.aux", 10),
       ("Two._model._impl.0._model._impl.aux._model._impl.skel", 14),
       ("Flat", 14), ("Flat._model._impl.0", 16), ("Flat._model._impl.0._model._impl.tag", 6),
       ("Flat._model._impl.0._model._impl.aux", 8),
       ("Flat._model._impl.0._model._impl.aux._model._impl.skel", 6),
       ("Key", 23), ("Key._model._impl.0", 20), ("Key._model._impl.0._model._impl.tag", 8),
       ("Key._model._impl.0._model._impl.aux", 14),
       ("Key._model._impl.0._model._impl.aux._model._impl.skel", 18),
       ("Zeta", 23), ("Zeta._model._impl.0", 20), ("Zeta._model._impl.0._model._impl.tag", 8),
       ("Zeta._model._impl.0._model._impl.aux", 14),
       ("Zeta._model._impl.0._model._impl.aux._model._impl.skel", 18),
       ("Ix", 15), ("Ix._model._impl.0", 14), ("Ix._model._impl.0._model._impl.tag", 6),
       ("Ix._model._impl.0._model._impl.aux", 12),
       ("Ix._model._impl.0._model._impl.aux._model._impl.skel", 16)],
      [("Eq", "prim model: a basis primitive")])
  -- **An ordinary `PSigma` occurs after unrelated owners in the raw export.**
  -- It is no longer support: earlier owners use the fixed `PSigma'` bundle,
  -- while the source `PSigma` remains at its dependency position and receives
  -- its own model. This row distinguishes ordinary source order from support
  -- scheduling across direct, mutual and nested model islands.
  --
  -- **The order in this row is the claim.** After support scheduling, `N`, `L`
  -- and `Pre` model at their dependency positions, followed by `MA` and its
  -- composed simple models, then `Nd` and its two composed layers. No generated
  -- job survives its owner island or depends on replaying a subsequent owner.
  --
  -- `Pre` is the direct-simple control. `N`'s splice line names the actual
  -- fixed basis, while the input-owned `PSigma` appears as the final modeled
  -- owner rather than as an exemption.
  , ("prim_late_basis",
      [("N", 15), ("L", 6), ("Pre", 6), ("MA", 22),
       ("MA._model._impl.tag", 8), ("MA._model._impl.aux", 16),
       ("MA._model._impl.aux._model._impl.skel", 14),
       ("Nd", 15), ("Nd._model._impl.0", 14),
       ("Nd._model._impl.0._model._impl.tag", 6), ("Nd._model._impl.0._model._impl.aux", 12),
       ("Nd._model._impl.0._model._impl.aux._model._impl.skel", 219),
       ("_wcore.Subtype", 9), ("_wcore.List", 6), ("_wcore.Sigma", 9),
       ("_wcore.Option", 6), ("_wcore.Exists", 4), ("_wcore.And", 8),
       ("_wcore.False", 2), ("_wcore.Decidable", 6), ("_wcore.PUnit", 6),
       ("_wcore.True", 6), ("_wcore.Or", 6), ("Iff", 8), ("_wcore.Acc", 13),
       ("_wcore.WellFounded", 6), ("_wcore.Bool", 6),
       ("_wcore.HEq", 5), ("_wcore.PProd", 9), ("Nonempty", 4), ("PSigma", 9)],
      [ ("Eq", "prim model: a basis primitive")])
  ]

structure TAcc where
  failures : Array String := #[]
  checks : Nat := 0

def check (a : TAcc) (ok : Bool) (msg : String) : TAcc :=
  { a with checks := a.checks + 1, failures := if ok then a.failures else a.failures.push msg }

/-- One fixture, all four axes. With `cross`, compare the generated declaration
array with the committed filtered export and verify idempotence structurally. -/
def runOne (root : String) (a : TAcc) (r : Row)
    (dir := "test/fixtures/inductive-models")
    (cross := false) (prim := false) : IO TAcc := do
  let (name, want, wantDeclined) := r
  let path := s!"{root}/{dir}/{name}.ndjson"
  let text ← IO.FS.readFile path
  let .ok x := InductiveModels.parse text | do
    return check a false s!"{name}: does not parse"
  let env ← importModules #[] {}
  let ctx : Core.Context :=
    { fileName := "<test>", fileMap := default, maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((decls, rep), _) ←
    Lean.Core.CoreM.toIO
      (Lean.Meta.MetaM.run' (runFilter x true (legacyGenerationConfig prim))) ctx { env }
  let mut a := a
  -- axis 1: the counts, in order
  let got := rep.generated.toList.map fun (n, k) => (n.toString, k)
  a := check a (got == want) s!"{name}: models are {got}, expected {want}"
  if name == "prim_graph_pre" then
    let nonemptyIndex := x.decls.findIdx? (·.names.contains `Nonempty)
    let psigmaIndex := x.decls.findIdx? (·.names.contains `PSigma)
    a := check a
      (nonemptyIndex.any fun nonempty =>
        psigmaIndex.any fun psigma => nonempty < psigma &&
          rep.generated.any (·.1 == `Nonempty) && rep.generated.any (·.1 == `PSigma))
      "prim_graph_pre: Nonempty and the later ordinary PSigma did not both model"
  if name == "w_core" then
    a := check a
      (rep.generated.any (·.1 == `False) && !rep.declined.any fun entry => entry.1 == `False)
      "w_core: derived False did not model after fixed Nat support"
  if name == "prim_w" then
    let emittedNames := decls.flatMap (·.names.toArray)
    let privateRoot := `Triple._model._impl
    let certificate := #[Name.str privateRoot "self", Name.str privateRoot "ctor_0",
      Name.str privateRoot "rec", Name.str privateRoot "rec_iota_0",
      Name.str privateRoot "roll", Name.str privateRoot "unroll",
      Name.str privateRoot "unroll_roll", Name.str privateRoot "roll_unroll"]
    a := check a
      (rep.generated.any (·.1 == `Triple) && emittedNames.contains `Triple._model &&
        certificate.all fun name => !emittedNames.contains name)
      "prim_w: Triple did not generate on the legacy route without a one-layer certificate"
  if name == "prim_carve" then
    -- `IBox` is the indexed-fibre occupant in this mixed route fixture.  Its
    -- count grew from the eight public/implementation records to sixteen only
    -- because the indexed adapter adds this complete eight-record structural
    -- certificate; pin the names as well as the census so an unrelated record
    -- increase cannot bless a partial or legacy family.
    let emittedNames := decls.flatMap (·.names.toArray)
    let privateRoot := `IBox._model._impl
    let certificate := #[Name.str privateRoot "self", Name.str privateRoot "ctor_0",
      Name.str privateRoot "rec", Name.str privateRoot "rec_iota_0",
      Name.str privateRoot "roll", Name.str privateRoot "unroll",
      Name.str privateRoot "unroll_roll", Name.str privateRoot "roll_unroll"]
    a := check a
      (rep.generated.find? (·.1 == `IBox) == some (`IBox, 16) &&
        certificate.all emittedNames.contains &&
        !rep.declined.any (·.1 == `IBox))
      "prim_carve: IBox did not generate with the complete indexed-fibre certificate"
  -- **Exempt then declined.** The basis primitives are their own row in the
  -- report now and this list covers both, so a row that
  -- names `Eq` still pins it; the extra claim below is that nothing but a
  -- basis primitive ever lands in the exempt row.
  let gotD := (rep.exempt ++ rep.declined).toList.map fun (n, w) => (n.toString, w)
  a := check a (rep.exempt.all fun (n, _) => InductiveModels.inductiveBasis.contains n)
    s!"{name}: the exempt row holds a non-basis name: {rep.exempt.map (·.1)}"
  -- By **prefix**: which shape stopped the generator is the claim, and a
  -- kernel diagnostic quoted inside the message is not.
  let declinesMatch :=
    gotD.length == wantDeclined.length &&
    (gotD.zip wantDeclined).all fun ((gn, gw), (wn, ww)) => gn == wn && ww.isPrefixOf gw
  a := check a declinesMatch s!"{name}: declines are {gotD}, expected {wantDeclined}"
  -- axis 3: exact serialized statements against the exported owner records
  a := check a rep.stmtErrors.isEmpty s!"{name}: {rep.stmtErrors}"
  -- A fixture whose only declarations are refusals has nothing to compare;
  -- one that generated a model must have compared something.
  a := check a (rep.generated.isEmpty || rep.stmtChecked > 0)
    s!"{name}: a model was generated and no statement was compared"
  a := check a (rep.generated.isEmpty == (rep.maxLivePendingModels == 0))
    s!"{name}: pending-model retention does not match generation: \
      peak {rep.maxLivePendingModels}, generated {rep.generated.size}"
  a := check a (rep.generated.isEmpty == (rep.maxLiveIslandRecords == 0))
    s!"{name}: island-record retention does not match generation: \
      peak {rep.maxLiveIslandRecords}, generated {rep.generated.size}"
  -- Independent source replay audit: the input's exported recursors agree with
  -- those Lean reconstructs from the source inductive record.
  a := check a rep.recMismatch.isEmpty
    s!"{name}: the export's recursors differ from Lean's own: {rep.recMismatch}"
  -- The compact graph retains no declaration values.  It must nevertheless
  -- select exactly the same final order (or error) as the full export pass.
  -- Source scheduling hoists `prim_graph_pre`'s exact quotient support before
  -- the owner which derives `funext`.  Island-local ordering must preserve that
  -- boundary: `Quot.lift`, then the derived `funext`, then its source owner.
  -- The compact sequence is consequently already an ordinary-order fixed
  -- point; the full-export oracle below independently checks the same order.
  let compact := Order.summaries { x with decls }
  let compactFixed := Order.summariesAreOrdered compact
  let compactOrder := Order.summaryRecordOrder compact
  let fullOrder := Order.recordOrder { x with decls }
  let sameOrder := match compactOrder, fullOrder with
    | .ok compact, .ok full => compact == full
    | .error compact, .error full => compact == full
    | _, _ => false
  a := check a sameOrder s!"{name}: compact ordering differs from the full-export oracle"
  if name == "prim_graph_pre" then
    let indexOf := fun target => compact.findIdx? fun summary => summary.introduced.contains target
    let positionIn := fun order target => do
      let source ← indexOf target
      order.findIdx? (· == source)
    let quotientBoundary := match compactOrder with
      | .ok order =>
        match indexOf `Ac._model._impl.funext, indexOf `Ac, indexOf `Quot.lift,
            positionIn order `Ac._model._impl.funext, positionIn order `Ac,
            positionIn order `Quot.lift with
        | some rawFunext, some rawOwner, some rawLift,
            some finalFunext, some finalOwner, some finalLift =>
          rawLift < rawFunext && rawFunext < rawOwner &&
            finalLift < finalFunext && finalFunext < finalOwner
        | _, _, _, _, _, _ => false
      | .error _ => false
    a := check a (compactFixed && quotientBoundary)
      "prim_graph_pre: scheduled quotient support does not precede derived funext and its owner"
  -- axis 4: the round trip
  let out := ({ x with decls }).render
  match InductiveModels.parse out with
  | .error e => a := check a false s!"{name}: the output does not parse: {e}"
  | .ok y =>
    a := check a (y.decls == decls) s!"{name}: the output does not read back as it was written"
    a := check a (y.decls.size == decls.size) s!"{name}: declaration count changed on the round trip"
  -- Compare the committed filtered export with what this run produced.
  if cross then
    let fpath := s!"{root}/test/fixtures/inductive-models/filtered/{name}.ndjson"
    let ftext ← IO.FS.readFile fpath
    match InductiveModels.parse ftext with
    | .error e => a := check a false s!"{name}: filtered fixture does not parse: {e}"
    | .ok f =>
      match Order.reorder { x with decls } with
      | .error error =>
        a := check a false s!"{name}: generated export does not order: {repr error}"
      | .ok ordered =>
        a := check a (f.decls == ordered.decls)
          s!"{name}: committed filtered export differs from the public ordering pipeline; \
             regenerate it with scripts/export-fixture.sh"
      -- The filter is the identity on its own output.
      let ((d3, r3), _) ←
        Lean.Core.CoreM.toIO
          (Lean.Meta.MetaM.run' (runFilter f false (legacyGenerationConfig prim))) ctx { env }
      a := check a r3.generated.isEmpty
        s!"{name}: the filter generated a model on its own output: \
           {r3.generated.toList.map fun (n, k) => (n.toString, k)}"
      -- **Both constructions' name guards, because the output carries both.**
      -- A filtered nested declaration leaves a `T._model._impl.0 …` block behind and
      -- the composition models *that* too, so re-filtering
      -- declines twice per nested declaration: once at `mutual model name taken
      -- (T._model._impl.0._model._impl.tag)` for the block, once at `nested model name
      -- taken (T._model._impl.0)` for the declaration. Either prefix is the guard
      -- doing its job; anything else is not.
      a := check a (r3.declined.all fun (_, w) =>
          "nested model name taken".isPrefixOf w || "mutual model name taken".isPrefixOf w)
        s!"{name}: filtered fixture declines for a reason other than the name guard: \
           {r3.declined.toList.map fun (n, w) => (n.toString, w)}"
      -- Every declaration this run modelled, plus every one it declined, is a
      -- declaration the filtered copy declines — so the name guard covers the
      -- whole of what was spliced and not a prefix of it.
      a := check a (r3.declined.size == rep.generated.size + rep.declined.size)
        s!"{name}: filtered fixture declines {r3.declined.size}, expected \
           {rep.generated.size + rep.declined.size}"
      a := check a (d3 == f.decls) s!"{name}: the filter is not the identity on its output"
  -- axis 4b: the identity on a file with nothing to splice
  let plainPath := s!"{root}/test/fixtures/inductive-models/filtered/nat_char_equations.ndjson"
  if ← System.FilePath.pathExists plainPath then
    let t ← IO.FS.readFile plainPath
    let .ok p := InductiveModels.parse t | return check a false "nat_char_equations does not parse"
    let ((d2, r2), _) ←
      Lean.Core.CoreM.toIO
        (Lean.Meta.MetaM.run' (runFilter p false (legacyGenerationConfig false))) ctx { env }
    a := check a r2.generated.isEmpty "nat_char_equations should have no model"
    a := check a (d2 == p.decls) "nat_char_equations is not passed through unchanged"
  return a

/-- **What a replayed export is visible as**, captured as two checks rather
than prose alone.

Both are facts about *Lean* and not about this tool. The visibility hazard and
the conclusion that the kernel-level API is unusable both disappear if
`Environment.find?` gains a fallback to the kernel constant map. This is here
so that day is a test failure with a name on it.

1. **`T.rec_1` is in the kernel map and not in `Environment.find?`.**
   `Declaration.getNames` says of itself that it omits *"auxiliary recursors
   computed by the kernel for nested inductive types"*, and that is the loop
   `addDeclCore` registers async constants from — so the constant every model
   in this repository is about is one `MetaM` cannot name. `Tree.rec` is the
   atom beside it: it **is** registered, so this is not "nothing is visible".
2. **`ofKernelEnv` after a kernel replay shows nothing.** That is the whole of
   why this tool uses `Environment.addDeclCore` despite its collision panic.

`tools/EnvProbe.lean` runs the same two probes at larger scale. -/
def runWSpliceProbe (root : String) (a : TAcc) : IO TAcc := do
  let path := s!"{root}/test/fixtures/inductive-models/prim_carve.ndjson"
  let text ← IO.FS.readFile path
  let .ok x := InductiveModels.parse text | return check a false "prim_carve does not parse"
  let env0 ← importModules #[] {}
  let mut env := env0
  for d in x.decls do
    if let some dcl := toDeclaration env d then
      if let .ok e := env.addDeclCore 0 dcl none false then env := e
  let reserved : Std.HashSet Name :=
    x.decls.foldl (fun s d => d.names.foldl (·.insert ·) s) {}
  -- **The compiled-in fragment against the one on disk.**
  -- `InductiveModels.wCoreText` is an `include_str`, and `include_str` is *not* in
  -- Lake's trace for `InductiveModels.Model`: re-exporting the w_core fixture and
  -- running `lake build` reports success and leaves the binary carrying the
  -- previous fragment. Measured — a re-export that added 11 declarations still
  -- spliced the old 149, and neither `touch` nor an mtime forces it, because
  -- Lake hashes content and the content is `Model.lean`'s. Every other check in
  -- this function runs against `wCoreText`, so without this one they all pass
  -- on a stale tool and say nothing about the fragment that was committed.
  let onDisk ← IO.FS.readFile s!"{root}/test/fixtures/inductive-models/w_core.ndjson"
  let a := check a (onDisk == InductiveModels.wCoreText)
    s!"the compiled-in W core fragment is {InductiveModels.wCoreText.length} bytes and \
       the w_core fixture is {onDisk.length} — the fragment was re-exported and \
       the binary was not rebuilt, which `lake build` will not tell you"
  let nFrag := match InductiveModels.parse InductiveModels.wCoreText (analyse := false) with
    | .ok x => x.decls.size
    | .error _ => 0
  let act : MetaM (Array (Bool × String)) := do
    let mut cs : Array (Bool × String) := #[]
    match ← InductiveModels.ensureWCore reserved with
    | .error e =>
      return #[(false, s!"the W core splice declined on prim_carve: {e.label}")]
    | .ok ds =>
      cs := cs.push (ds.size > 100,
        s!"the W core splice added {ds.size} records, where the fragment parses to \
           {nFrag} and prim_carve supplies only its own Eq")
      -- **The fifth and sixth roots arrived and are visible.** The other four
      -- are the construction; these two are the `DecidableEq K` each
      -- instantiation needs and that the other four's closure cannot reach,
      -- because all four take the instance as a parameter —
      -- `instDecidableEqNat` at `K := Nat` and `WT.decEqAll` at `K := A`
      -- because those names are parameters rather than dependencies.
      for k in [InductiveModels.wCoreDecEqNat, InductiveModels.wCoreDecEqAll] do
        cs := cs.push (((← getEnv).find? k).isSome,
          s!"{k} is missing after the splice — one of the two instantiations has \
             no decidable equality and every W target on it would have to prove one")
      for k in [InductiveModels.wCoreSelf, InductiveModels.wCoreSup, InductiveModels.wCoreRec, InductiveModels.wCoreIota] do
        cs := cs.push (((← getEnv).find? k).isSome,
          s!"{k} is not visible to Environment.find? after the splice")
      -- **Once per run.** The sentinel is what makes the splice a splice and
      -- not 160 kernel checks per W target.
      match ← InductiveModels.ensureWCore reserved with
      | .error _ => cs := cs.push (false, "the second W core splice declined")
      | .ok ds2 => cs := cs.push (ds2.isEmpty,
          s!"the W core spliced a second time and added {ds2.size} records")
      -- **The exclusion list, from the side that would hurt.** A `_wcore`
      -- copy of either axiom is a *non-standard* axiom downstream, and a `propext`
      -- under Lean's name whose statement is at `_wcore.Iff` and `_wcore.Eq`
      -- is worse than that: consumers key the standard axiom by its name and
      -- would attach the wrong statement. Both are pinned, because the
      -- rename is one list and either mistake is one entry in it.
      for n in [InductiveModels.wCoreRoot ++ `propext, InductiveModels.wCoreRoot ++ `Quot.sound,
                InductiveModels.wCoreRoot ++ `Eq, InductiveModels.wCoreRoot ++ `Iff,
                InductiveModels.wCoreRoot ++ `Nat, InductiveModels.wCoreRoot ++ `Quot,
                InductiveModels.wCoreRoot ++ `Classical.choice,
                InductiveModels.wCoreRoot ++ `Nonempty] do
        cs := cs.push (((← getEnv).find? n).isNone,
          s!"{n} exists — a shared name was renamed even though the construction \
             requires the eight roots to retain their standard names")
      for n in [`propext, `Quot.sound, `Eq, `Iff, `Nat, `Quot,
                `Classical.choice, `Nonempty] do
        cs := cs.push (((← getEnv).find? n).isSome, s!"{n} is missing after the splice")
      -- The statements of the two axioms the whole exclusion list is about.
      -- `propext`'s must be at Lean's `Eq` and `Iff`, and `Classical.choice`'s
      -- at Lean's `Nonempty` — consumers key the clause on the name, so a
      -- trusted name carrying a `_wcore` statement is worse than a decline.
      if let some ci := (← getEnv).find? `propext then
        let us := ci.type.getUsedConstants
        cs := cs.push (us.contains `Eq && us.contains `Iff,
          s!"propext's statement mentions {us} — it must be Lean's, at Lean's Eq and Iff")
      if let some ci := (← getEnv).find? `Classical.choice then
        let us := ci.type.getUsedConstants
        cs := cs.push (us.contains `Nonempty,
          s!"Classical.choice's statement mentions {us} — it must be Lean's, at \
             Lean's Nonempty")
    return cs
  let (cs, _) ← Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' act)
    { fileName := "<test>", fileMap := default } { env }
  return cs.foldl (fun a (ok, msg) => check a ok msg) a

def runEnvProbe (root : String) (a : TAcc) : IO TAcc := do
  let path := s!"{root}/test/fixtures/inductive-models/nested_iota.ndjson"
  let text ← IO.FS.readFile path
  let .ok x := InductiveModels.parse text | return check a false "nested_iota does not parse"
  let env0 ← importModules #[] {}
  let mut env := env0
  for d in x.decls do
    if let some dcl := toDeclaration env d then
      if let .ok e := env.addDeclCore 0 dcl none false then env := e
  let kenv := env.toKernelEnv
  let mut a := a
  a := check a ((kenv.find? `Tree.rec_1).isSome && (env.find? `Tree.rec_1).isNone)
    "Tree.rec_1 is no longer in the kernel map and absent from Environment.find? — \
     the replay visibility invariant has changed"
  a := check a ((env.find? `Tree.rec).isSome)
    "Tree.rec is not visible to Environment.find? either, so the visibility control measures nothing"
  -- The kernel replay, and what `ofKernelEnv` lets `MetaM` see of it.
  let mut kenv2 := env0.toKernelEnv
  for d in x.decls do
    if let some dcl := toDeclaration (Environment.ofKernelEnv kenv2) d then
      if let .ok e := kenv2.addDeclWithoutChecking dcl then kenv2 := e
  let envB := Environment.ofKernelEnv kenv2
  a := check a ((kenv2.find? `Tree).isSome && (envB.find? `Tree).isNone)
    "Environment.ofKernelEnv now exposes a kernel-replayed constant to Environment.find? — \
     the obstacle to using the kernel-level replay API is gone"
  return a

/-- Every constant an export record introduces *or* refers to. A leaked alias
root is a name that appears here and in no declaration of the output, so this
is what the probe below searches. -/
def edeclNames : InductiveModels.EDecl → Array Name
  | .ax n _ t _ => #[n] ++ t.getUsedConstants
  | .defn n _ t v _ _ all => #[n] ++ all.toArray ++ t.getUsedConstants ++ v.getUsedConstants
  | .thm n _ t v all => #[n] ++ all.toArray ++ t.getUsedConstants ++ v.getUsedConstants
  | .opaq n _ t v _ all => #[n] ++ all.toArray ++ t.getUsedConstants ++ v.getUsedConstants
  | .quot n _ t _ => #[n] ++ t.getUsedConstants
  | .induct ts cs rs =>
    (ts.toArray.flatMap fun t =>
       #[t.name] ++ t.all.toArray ++ t.ctors.toArray ++ t.type.getUsedConstants) ++
    (cs.toArray.flatMap fun c => #[c.name, c.induct] ++ c.type.getUsedConstants) ++
    (rs.toArray.flatMap fun r =>
       #[r.name] ++ r.all.toArray ++ r.type.getUsedConstants ++
       r.rules.toArray.flatMap fun u => #[u.ctor] ++ u.rhs.getUsedConstants)

/-- **The normalized-name collision, closed.**

An export is many modules flattened into one file, so it holds both
`_private.M.0.X` and a public `X`. We model both, Lean's async constant map
keys on `privateToUserName`, and the second model's carrier is added to the
kernel and lost to the environment. `runCollisionProbe` above pins that Lean
behaves that way and that a differently-normalizing root escapes it; this pins
that `lean-inductive-models` *takes* the escape.

**The input is built here rather than checked in as a fixture, because no
`.lean` source can produce the pair.** A private `X` and a public `X` in one
module is an error; the collision only exists in an export, which is many
modules. So the probe parses a fixture and adds a second copy of one inductive
under a private name that normalizes back onto the original — which is exactly
the shape the export has.  The copy is made with an explicit whole-name
`AliasMap` and `EDecl.renameAliases`, the same exact substitution machinery
used to serialize a collision retry.

Source replay now moves ordinary declarations before they reach Lean's
normalized async map. An inductive block is different: its type former,
constructors, recursors, and rule roles are minted by one atomic kernel
operation. Until that whole role family has a dual exact/replay certificate,
the collision is rejected before the first source declaration is replayed.
This probe pins that deterministic fail-closed boundary; it must never regress
to the nonfatal PANIC followed by partially invisible environment state. -/
def runAliasProbe (root : String) (a : TAcc) : IO TAcc := do
  let path := s!"{root}/test/fixtures/inductive-models/prim_shapes.ndjson"
  let text ← IO.FS.readFile path
  let .ok x := InductiveModels.parse text | return check a false "prim_shapes does not parse"
  let tgt : Name := `Sv
  let priv : Name := (`_private.M).mkNum 0 |>.str "Sv"
  let mut a := a
  unless privateToUserName priv == tgt do
    return check a false "the manufactured private name does not normalize onto Sv"
  let some i := x.decls.findIdx? (·.names.contains tgt)
    | return check a false "prim_shapes no longer declares Sv"
  let aliases := x.decls[i]!.names.foldl (init := Naming.AliasMap.empty) fun aliases name =>
    aliases.insert name (name.replacePrefix tgt priv)
  let dup := x.decls[i]!.renameAliases aliases
  let decls := x.decls.extract 0 (i + 1) ++ #[dup] ++ x.decls.extract (i + 1) x.decls.size
  let env ← importModules #[] {}
  let ctx : Core.Context :=
    { fileName := "<test>", fileMap := default, maxHeartbeats := 0, maxRecDepth := 8192 }
  let rejected ← try
    discard <| Lean.Core.CoreM.toIO
      (Lean.Meta.MetaM.run'
        (runFilter { x with decls } true (legacyGenerationConfig true))) ctx { env }
    pure false
  catch error =>
    pure <| (toString error).contains "collision moves inductive role"
  return check a rejected
    "alias: a normalized inductive-role collision did not fail closed before replay"

/-- `def n : Nat → Nat := fun x => x`, under whatever name is asked for. The
collision probe needs two declarations that differ in nothing but their name. -/
private def probeIdDecl (n : Name) : Declaration :=
  let nat : Expr := .const `Nat []
  .defnDecl { name := n, levelParams := [], type := .forallE `x nat nat .default,
              value := .lam `x nat (.bvar 0) .default,
              hints := .abbrev, safety := .safe }

private def probeNatDecl : Declaration :=
  let nat : Expr := .const `Nat []
  .inductDecl [] 0
    [{ name := `Nat, type := .sort (.succ .zero),
       ctors := [{ name := `Nat.zero, type := nat },
                 { name := `Nat.succ, type := .forallE `n nat nat .default }] }] false

/-- **The normalized-name collision, measured rather than inherited**, including
the three things about it that are easy to
get wrong. Every claim here is a fact about *Lean* that this tool's
`nameTaken` decline rests on, so each is a test rather than a paragraph.

1. **`Environment.find?`'s `base` fast path is dead for anything this tool
   adds.** `find?` reads `env.base.constants.map₁` first and only then the
   async map, which reads as though a constant could be visible without the
   async map being involved. It cannot: `mkEmptyEnvironment` and
   `finalizeImport` both hand out a constant map already switched to **stage
   2**, so `SMap.insert` puts every locally-added constant in `map₂` and the
   `map₁` probe never fires. `map₁` is the *imported* half and this tool
   imports nothing. So "in the async map or invisible" is the whole of the
   available space, and it is not an artefact of which field an earlier
   experiment happened to write.

2. **The loss is the second arrival, in either order**, and it is a *name*
   property, not an API one: `AsyncConsts.add` keys its trie on
   `privateToUserName`, `panic!`s on a duplicate, and returns the collection
   **unchanged**. Adding the public name first loses the private one and vice
   versa, so no ordering discipline avoids it — which is why the guard in
   `InductiveModels.addChecked` tests membership *after* the add.

3. **A name that normalizes differently is added and found.** This is the
   escape, and it is inside this tool rather than inside Lean: generate the
   model under a root whose normalized form cannot collide and rename to the
   contract name on the way out. It costs no contract change and no weakening
   of the kernel check — the declaration the kernel accepts and the
   declaration emitted differ by an injective renaming of constants this run
   introduced. Model generation uses this retry for normalized-name collisions;
   this probe pins the environment property it relies on.

What is **not** an escape, all of it read off the pinned toolchain's
`Lean/Environment.lean` rather than guessed: `addConstAsync` (`:1018`) and
`replayConsts` (`:2440`) both insert through the same `AsyncConsts.add`, and
`replayConsts` additionally cannot replay an inductive at all (`panic! "must
be definition/theorem"`); `ofKernelEnv` is pinned above as strictly worse; and
`Kernel.Environment`'s constructor is `private mk ::`, so the constant map
cannot be rebuilt into stage 1 from outside that module.

**And Lean's own commented-out `!isPrivateName` guard would not have fixed
this.** `addDeclCore` (`:711`) adds to `asyncConstsMap.private`
*unconditionally* and only the `.public` insertion sits behind the guard, so
the private view collides whatever the guard does. A single colliding add
prints the panic **twice**, once per view. The public-view guard therefore does
not explain this collision. -/
def runCollisionProbe (a : TAcc) : IO TAcc := do
  let env0 ← importModules #[] {}
  let mut a := a
  -- (1) the base fast path
  a := check a (!env0.constants.stage₁)
    "the fresh environment's constant map is in SMap stage 1 — locally added constants would \
     now land in `map₁` and `Environment.find?`'s base probe would see them without the async \
     map; the normalized-name collision may no longer be structural"
  let mut env := env0
  let some env1 := (env.addDeclCore 0 probeNatDecl none true).toOption
    | return check a false "the collision probe cannot install Nat"
  env := env1
  a := check a (env.constants.map₁.isEmpty)
    "a locally added constant reached `base.constants.map₁`, which is supposed to be the \
     imported half only — `Environment.find?`'s base probe is live and the collision needs re-measuring"
  -- (2) the collision, both orders. `X.foo` and `_private.M.0.X.foo` normalize alike.
  let publ : Name := `X.foo
  let priv : Name := (`_private.M).mkNum 0 |>.str "X" |>.str "foo"
  a := check a (privateToUserName priv == publ)
    "privateToUserName no longer strips the private prefix, so this probe measures nothing"
  let secondIsLost := fun (first second : Name) => Id.run do
    let some e1 := (env.addDeclCore 0 (probeIdDecl first) none true).toOption | return false
    let some e2 := (e1.addDeclCore 0 (probeIdDecl second) none true).toOption | return false
    -- the kernel took it; the environment lost it; and the first one survives
    return e2.constants.contains second && (e2.find? second).isNone && (e2.find? first).isSome
  a := check a (secondIsLost priv publ)
    "the public name added after the private one is now visible to `Environment.find?` — \
     the normalized-name collision is gone and the `name taken` declines can be retired"
  a := check a (secondIsLost publ priv)
    "the private name added after the public one is now visible to `Environment.find?` — \
     the collision has become order-dependent, so `InductiveModels.addChecked`'s check-after-add \
     could be replaced by an ordering rule"
  -- (3) the escape: a root that normalizes differently is added and found.
  let al : Name := (`_private.M).mkNum 0 |>.str "X" |>.str "_mg1" |>.str "foo"
  a := check a (privateToUserName al != publ)
    "the alias root no longer normalizes away from the contract name, so it is not an escape"
  let aliasWorks := Id.run do
    let some e1 := (env.addDeclCore 0 (probeIdDecl publ) none true).toOption | return false
    let some e2 := (e1.addDeclCore 0 (probeIdDecl al) none true).toOption | return false
    return (e2.find? al).isSome && (e2.find? publ).isSome
  a := check a aliasWorks
    "a second declaration under a differently-normalizing root is no longer visible either — \
     the generate-under-an-alias escape for the normalized-name declines has closed"
  return a

/-- **The two streams and the four exit statuses**, against the built binary.

Axes 1–4 call `runFilter` directly and so cannot see the process boundary at
all — and the boundary is where reasons can be lost: a consumer that passes
`--quiet` to keep stdout export-clean receives no decline report. The stream
split is documented in `src/Main.lean`.

So this runs the binary and **captures stdout and stderr separately**, which is
the only way to observe the split. `infinitary` is the input that distinguishes
them: it has models *and* declines, so the report is non-empty while the export
is a whole file, and a report leaking into stdout would be a byte difference
against `-o FILE` rather than a wording difference.

It needs `.lake/build/bin/lean-inductive-models`, and reports a **failure** rather
than a skip when it is absent: the suite claims the CLI contract and cannot
check it from an unbuilt binary. `lake build` first. -/
def runCli (root : String) (a : TAcc) : IO TAcc := do
  let bin := s!"{root}/.lake/build/bin/lean-inductive-models"
  unless ← System.FilePath.pathExists bin do
    return check a false s!"{bin} is not built (`lake build`): the CLI contract is unchecked"
  let input := s!"{root}/test/fixtures/inductive-models/infinitary.ndjson"
  let mg := fun (args : List String) => IO.Process.output { cmd := bin, args := args.toArray }
  let mut a := a
  -- `-o -` is stdout, first class.  This older process-boundary test isolates
  -- the nested/mutual stream and its three known splice reports; MainCliTest
  -- separately exercises the all-branches default.
  let r ← mg [input, "-o", "-", "--no-simple", "--no-basic"]
  a := check a (r.exitCode == 0) s!"CLI: `-o -` exited {r.exitCode}"
  -- The report is on stderr, all of it, and none of it is on stdout.
  a := check a ((r.stderr.splitOn "FTree: model of 17 declarations").length == 2)
    s!"CLI: stderr does not carry the models: {r.stderr}"
  -- **A splice is reported.** `infinitary` declares no `funext`, so its report
  -- has to say which declarations were not the input's — permissive splicing
  -- still has to be observable.
  a := check a ((r.stderr.splitOn "prelude spliced").length == 4)
    s!"CLI: stderr does not carry the three splice lines: {r.stderr}"
  a := check a ((r.stderr.splitOn "HTree: prelude spliced — Quot, Quot.mk, Quot.lift, \
      Quot.ind, Quot.sound, HTree._model._impl.funext").length == 2)
    s!"CLI: the splice line does not name what was spliced: {r.stderr}"
  a := check a ((r.stdout.splitOn "prelude spliced").length == 1)
    "CLI: a report line reached stdout"
  -- …and stdout is the export, byte for byte what `-o FILE` writes.
  IO.FS.createDirAll s!"{root}/_tmp"
  let tmp := s!"{root}/_tmp/cli-test.ndjson"
  let f ← mg [input, "-o", tmp, "--quiet", "--no-simple", "--no-basic"]
  a := check a (f.exitCode == 0) s!"CLI: `-o FILE --quiet` exited {f.exitCode}"
  a := check a f.stderr.isEmpty s!"CLI: `--quiet` still wrote to stderr: {f.stderr}"
  if ← System.FilePath.pathExists tmp then
    let onDisk ← IO.FS.readFile tmp
    a := check a (onDisk == r.stdout) "CLI: `-o -` and `-o FILE` do not agree byte for byte"
    IO.FS.removeFile tmp
  else
    a := check a false "CLI: `-o FILE` wrote no file"
  -- **The Lean Kernel Arena exit statuses a consumer keys on**: accepted,
  -- rejected, declined, and tool failure are respectively 0, 1, 2, and 3.
  -- Malformed command lines, malformed serialization, and failed file IO are
  -- all failures of this tool to submit a candidate to the kernel, not kernel
  -- rejection or a model-generation decline.
  a := check a (r.exitCode == 0) "CLI: a decline is not exit 0"
  let u ← mg ["--no-such-flag"]
  a := check a (u.exitCode == 3) s!"CLI: an unknown flag exited {u.exitCode}, expected 3"
  let m ← mg [s!"{root}/test/scripts/export-inductive-models.sh", "-o", "-"]
  a := check a (m.exitCode == 3) s!"CLI: an unparsable input exited {m.exitCode}, expected 3"
  a := check a m.stdout.isEmpty "CLI: an unparsable input still wrote to stdout"
  let n ← mg [s!"{root}/test/fixtures/inductive-models/no-such-file.ndjson", "-o", "-"]
  a := check a (n.exitCode == 3) s!"CLI: a missing input exited {n.exitCode}, expected 3"
  return a

/-! ## The composition: model generation, then universe monomorphization

This is the only place the two passes meet inside one process, and it is here
because the two properties it pins are invisible to everything else in either
suite. **One is about the marker**: it encodes `|σ|`, so if the nine families of
a model do not agree on their level-parameter arity, one model comes out under
two markers and a consumer that derives the family from the type's name finds
part of it. **The other is about demand**: nothing in the file *references* a
model, so left to the backward sweep every model group takes `--default` and
`T`'s second and third copies have no model at all. No kernel sees either — the
fixture's output replays with **0 rejected** in both states.

`poly_nested_used` is the fixture because it is the one where the composition
can be measured at all: `PTree.{u}` is *used* at universes 0, 1 and 2, so thirty
of its thirty-six groups come out at three copies. On a file where every group
lands at exactly one instantiation, "the model came out at the instantiation its
declaration did" and "everything defaulted and the defaults agreed" are the same
observation, and a previous seat's claim that the composition worked was vacuous
for precisely that reason. `copies per group` is the check that says so, and it
is the first one below. -/
def runMonoCompose (root : String) (a : TAcc) : IO TAcc := do
  let text ← IO.FS.readFile s!"{root}/test/fixtures/inductive-models/poly_nested_used.ndjson"
  let .ok x := InductiveModels.parse text | return check a false "poly_nested_used does not parse"
  let env ← importModules #[] {}
  let ctx : Core.Context :=
    { fileName := "<test>", fileMap := default, maxHeartbeats := 0, maxRecDepth := 8192 }
  let ((decls, _), _) ←
    Lean.Core.CoreM.toIO
      (Lean.Meta.MetaM.run' (runFilter x false (legacyGenerationConfig false))) ctx { env }
  let modelled : Export := { x with decls }
  let mut a := a
  for (tag, opts) in [("A", ({ check := true } : Mono.Opts)),
                      ("B", { monoRecursors := true })] do
    let ((y, rep), _) ←
      Lean.Core.CoreM.toIO (Lean.Meta.MetaM.run' (Mono.monomorphize modelled opts)) ctx { env }
    a := check a rep.refused.isNone s!"compose[{tag}]: refused: {rep.refused}"
    a := check a (rep.rejected == 0) s!"compose[{tag}]: the kernel rejected {rep.rejected}"
    -- **Not vacuous, and this is the row that says so.** Three universes, so
    -- `PTree`'s group is at three copies — and so, now, are all 30 groups in
    -- the composed output. The six at one copy are `Eq` and `List`
    -- (carried), `N`, and the three `atK` that do the using. A composition
    -- measured on a file whose every group lands at one instantiation is
    -- measuring the defaults agreeing with themselves.
    --
    -- It was `#[(1, 35), (3, 1)]`: one three-copy row, the type, while the model
    -- incorrectly defaulted to a single copy beside it.
    a := check a (rep.hist == #[(1, 6), (3, 30)])
      s!"compose[{tag}]: copies per group {rep.hist}, expected #[(1, 6), (3, 30)]"
    -- Exact-role counting keys the 21 public declaration-local model roles
    -- plus one structurally proved model-of-model helper bridge. Other `_impl`
    -- helpers are copied by actual dependency demand, not by nominal `_model`
    -- ancestry, hence 22 keyed groups although the histogram has 30 triples.
    a := check a (rep.modelGroups == 22)
      s!"compose[{tag}]: {rep.modelGroups} model groups keyed, expected 22"
    a := check a (rep.modelDeclined == 0)
      s!"compose[{tag}]: the keying declined {rep.modelDeclined} model groups"
    -- **One model per copy of `PTree`, and the same model under each.** Every
    -- name is split at the `_at` marker; a name whose remainder has a `_model`
    -- component is a model's, and it is filed under the marker it carries.
    -- `T._model._impl.funext` is excluded: a spliced prelude theorem is
    -- polymorphic in universes that are nobody's motive, nothing
    -- derives its name, and it is not one of the nine families.
    --
    -- Two things are then checked, and the second is what reaches the *second*
    -- layer of the composed naming. The marker set the model's names use must
    -- be exactly the marker set `PTree` itself uses — three, not one, and not
    -- four. And the **suffixes** filed under each marker must be the same set:
    -- `PTree._model._impl.0._model` is a suffix like any other, so a copy that
    -- got the outer model and not the inner one fails here by name.
    -- Naming inversion removes the trailing `._elim.⟨w⟩` first.
    -- Mode B folds the *motive's* universe into it, and that numeral is a
    -- property of the copy, so the suffix sets would differ by construction if
    -- it stayed on — `PTree._model.1.rec._elim.1` under one marker against
    -- `._elim.3` under another is the same family member.
    let split (n : Name) : String × List String :=
      let ps0 := n.componentsRev.reverse.map toString
      let ps := match ps0.reverse with
        | w :: "_elim" :: r => if w.toNat?.isSome then r.reverse else ps0
        | _ => ps0
      match ps with
      | "_at" :: k :: r =>
        match k.toNat? with
        | some i => (".".intercalate ("_at" :: k :: r.take i), r.drop i)
        | none => ("", ps)
      | _ => ("", ps)
    let mut per : Std.HashMap String (Array String) := {}
    let mut ptreeMarks : Array String := #[]
    for d in y.decls do
      for n in d.names do
        let (mk, rest) := split n
        if rest == ["PTree"] then
          unless ptreeMarks.contains mk do ptreeMarks := ptreeMarks.push mk
        let some i := rest.findIdx? (· == "_model") | continue
        if rest.drop (i + 1) == ["funext"] then continue
        let seen := per.getD mk #[]
        let suffix := ".".intercalate rest
        unless seen.contains suffix do per := per.insert mk (seen.push suffix)
    a := check a (ptreeMarks.size == 3)
      s!"compose[{tag}]: PTree is at {ptreeMarks.size} markers, expected 3: {ptreeMarks}"
    for mk in ptreeMarks do
      a := check a (per.contains mk) s!"compose[{tag}]: no model under {mk}"
    a := check a (per.size == ptreeMarks.size)
      s!"compose[{tag}]: models under {per.size} markers, PTree at {ptreeMarks.size}: \
        {per.toArray.map (·.1)}"
    let ref := (per.getD (ptreeMarks.getD 0 "") #[]).qsort (· < ·)
    a := check a (ref.size == 44)
      s!"compose[{tag}]: {ref.size} model names under one marker, expected 44"
    for (mk, ns) in per.toArray do
      let ns := ns.qsort (· < ·)
      a := check a (ns == ref)
        s!"compose[{tag}]: the model under {mk} differs: \
          {ns.filter (!ref.contains ·)} / {ref.filter (!ns.contains ·)}"
  return a

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let root := args.head?.getD "."
  let mut a : TAcc := {}
  for r in expectedShared do
    a ← runOne root a r (cross := true)
  for r in expectedOwn do
    a ← runOne root a r
  for r in expectedPrim do
    a ← runOne root a r (prim := true)
  a ← runEnvProbe root a
  a ← runWSpliceProbe root a
  a ← runCollisionProbe a
  a ← runAliasProbe root a
  a ← runMonoCompose root a
  a ← runCli root a
  IO.println s!"{a.checks} checks, {a.failures.size} failed"
  for f in a.failures do IO.println s!"  FAIL {f}"
  return if a.failures.isEmpty then 0 else 1
