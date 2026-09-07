import InductiveModels.Driver.Types
import InductiveModels.Driver.GeneratedInfo
import InductiveModels.Driver.Unitlike
import InductiveModels.Driver.StructureRecursor
import InductiveModels.Driver.NestedField
import InductiveModels.Driver.Projections
import InductiveModels.Driver.StructureModels
import InductiveModels.Driver.Records
import InductiveModels.Driver.Island
import InductiveModels.Driver.Serialise
import InductiveModels.Driver.Readiness
import InductiveModels.Driver.Tower
import InductiveModels.Driver.Census
import InductiveModels.Driver.Filter

/-!
# The filter

`.ndjson` in, `.ndjson` out. Generation replays source declarations into its
analysis environment without checking their values; the independent
`--type-check-input` gate checks only input declarations, while
`--type-check-generated` checks each exact generated island once in an owner-free
environment as it is produced. Turning either gate off skips kernel checking
for that declaration class.

Beside each supported inductive the output carries that declaration's complete
public model family. Each island is appended immediately before its owner and
all other source declarations retain input order. Input declarations
themselves retain their exact exported records.

There are **three** constructions and they are separate files.
`src/InductiveModels/Model.lean` specialises a nested declaration into a mutual block
and proves the export's recursors over it; `src/InductiveModels/Mutual.lean` packs a
plain mutual block into an implementation tag and one auxiliary inductive;
`src/InductiveModels/Simple.lean`
models a single inductive from the primitive basis. None is a degenerate case
of another, and this driver is the only thing that composes them.

## Why output is re-interned

Declaration records refer to numeric name, level, and expression arena IDs.
Actual generated output feeds each callback declaration into one persistent
standard writer, reusing its global interning maps while releasing the `EDecl`
after the callback. The no-generation path keeps
[`InductiveModels.Export.writeTo`] for byte-stable whole-export writing.

## The free oracle

Lean's kernel builds the nested construction itself: given `Tree`'s
`inductDecl` it generates **both** `Tree.rec` and `Tree.rec_1`, at the shapes
the export declares. The optional internal recursor audit compares those
installed recursors with the export while replaying the file. The public
`--check` instead verifies the literal exported model interface.
-/

/-!
## Module layout

This file is a facade: it only re-exports the fourteen modules below, so
`import InductiveModels.Driver` continues to name the whole filter.

* [`InductiveModels.Driver.Types`] — the run report and the retention
  witnesses (the floor)
* [`InductiveModels.Driver.GeneratedInfo`] — a generated declaration's exact
  public statement
* [`InductiveModels.Driver.Unitlike`] — the unit-like equality theorem
* [`InductiveModels.Driver.StructureRecursor`] — the recursor prefix a
  structure-like proof runs on
* [`InductiveModels.Driver.NestedField`] — the nested rung's definitional
  field selector and projection eligibility
* [`InductiveModels.Driver.Projections`] — modeled primitive projections and
  their iota rules
* [`InductiveModels.Driver.StructureModels`] — structure eta, and the roof
  over the three structure-like additions
* [`InductiveModels.Driver.Records`] — Lean declarations read back as export
  records
* [`InductiveModels.Driver.Island`] — island assembly, the kernel gate, the
  close, and the `IslandObserver` seam
* [`InductiveModels.Driver.Serialise`] — one completed `Iso` as exact records
* [`InductiveModels.Driver.Readiness`] — the export's recursor metadata against
  what Lean actually built
* [`InductiveModels.Driver.Tower`] — `genPrim`, `primCompose`, `genMutual`:
  where the three constructions meet
* [`InductiveModels.Driver.Census`] — what the source export says about itself
* [`InductiveModels.Driver.Filter`] — the declaration-wise fold and the six
  public routes over it

Every import below is written where it is needed and nowhere else, so the
graph is exactly its edges — no part imports a part it only reaches through
another:

    GeneratedInfo        StructureRecursor
       ├──────────┐              │
    Unitlike   NestedField       │
       │          └──── Projections
       └───── StructureModels ───┘
                     │
    Types            │            Records
       └─────────────┴───────────────┤
                  Island             │
                     │             Census      Readiness
                 Serialise           │             │
                     │               │             │
                   Tower ────────────┴─── Filter ──┘

`Types`, `GeneratedInfo`, `StructureRecursor`, `Records` and `Readiness` import
no other part of the driver; `Filter` is the only leaf, and it is the only part
that reaches every other one.

Names which were file-private while the driver was one file and are now shared
between these parts are module-visible rather than private.  They remain
internal to `InductiveModels`: no name changed namespace, and the driver's
public API is unchanged.
-/
