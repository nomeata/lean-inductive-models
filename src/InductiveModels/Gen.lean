import InductiveModels.Gen.Monad
import InductiveModels.Gen.MetaKit
import InductiveModels.Gen.ExportShape
import InductiveModels.Gen.Prelude
import InductiveModels.Gen.Iso
import InductiveModels.Gen.WCore

/-!
# The shared generator core

The parts every one of the three constructions is built on: the monad and its
declines, the `MetaM` helpers, the pure export-shape readers, the spliced
prelude, the result record, and the W core.

**No rung is in here.** The three constructions are
`InductiveModels.Simple.*`, `InductiveModels.Mutual` and the nested one, and
each of them imports this and not the others' internals. A module that only
needs part of this should import that part directly; this facade exists so
that the core has one name.
-/
