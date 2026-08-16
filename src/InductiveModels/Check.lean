import InductiveModels.Check.Violation
import InductiveModels.Check.Kit
import InductiveModels.Check.Correspondence
import InductiveModels.Check.Family
import InductiveModels.Check.Reference
import InductiveModels.Check.Certificates
import InductiveModels.Check.Rules
import InductiveModels.Check.Index
import InductiveModels.Check.Compact
import InductiveModels.Check.Statements

/-!
# Structural checks for exported inductive models

This module is the format-only foundation of the model checker.  It discovers
public model families solely from the declarations in an original inductive
record.  If that record declares type former `T`, constructor `C`, recursor `R`
and rule `j`, their public names are respectively `T._model`, `C._model`,
`R._model` and `R._model.iota_j`, constructed by [`InductiveModels.Naming`].  A
recursor whose literal `k` flag is true additionally owns `R._model.ruleK`.  No
name is split at `_model`, so private names and originals which themselves
contain an `_model` component retain their exact identity.

Declaration records remain atomic for ordering.  A record which introduces at
least one exact public name belongs to the corresponding family in its entirety;
ordinary dependency edges order any non-contract implementation helpers on
which it depends.

The implemented invariants are:

* every declaration record in the model family precedes the inductive record
  containing its owner; and
* the complete owner inductive record does not refer to any name introduced by
  its model family;
* there is exactly one public type-former, constructor and recursor declaration,
  and one theorem for every exported recursor rule; and
* all declaration types, including the exact equality propositions synthesized
  for each ordinary rule and K reduction, are syntactically equal after the one public
  constant substitution and positional alignment of declaration universes.

The second walk covers both names held directly in export records and names in
expressions.  In expressions it treats both `Expr.const` and the `typeName`
field of `Expr.proj` as references. Literal comparisons never ask for
definitional equality; the few kernel-visible sort observations use only the
bounded export-syntax normalizer from `InductiveModels.Format`.
-/

/-!
## Module layout

This file is a facade: it only re-exports the ten modules below, so
`import InductiveModels.Check` continues to name the whole checker.

* [`InductiveModels.Check.Violation`] — the diagnostic vocabulary (the floor)
* [`InductiveModels.Check.Kit`] — the binder telescope and record tables
* [`InductiveModels.Check.Correspondence`] — the public constant substitution
* [`InductiveModels.Check.Family`] — reconstructed statements and the family record
* [`InductiveModels.Check.Reference`] — owner-reference traversal and certificate
* [`InductiveModels.Check.Certificates`] — declaration views and one-layer boundaries
* [`InductiveModels.Check.Rules`] — the per-slot structural checks
* [`InductiveModels.Check.Index`] — syntax tables, discovery, whole-export check
* [`InductiveModels.Check.Compact`] — name-only compact certificates
* [`InductiveModels.Check.Statements`] — the generation-time statement oracle

The graph is a chain with two side entries:

      Violation      Kit   Correspondence      Reference
          │            └────────┬────────┘         │
          │                  Family               │
          └────────────────┬────┘                  │
                     Certificates                  │
                           │                       │
                         Rules ────────────────────┘
                           │
                         Index
                        ╱     ╲
                  Compact     Statements

`Violation`, `Kit`, `Correspondence` and `Reference` are the roots; only
`Compact` and `Statements` are leaves, and neither depends on the other.

The checker's independence from the generator is a correctness property, not a
convention: `test/scripts/check-checker-imports.sh` pins this closure exactly,
so every module above reaches only `Format`, `Naming`, `Plan`, `Projection` and
`EqKit`.

Names which were file-private while the checker was one file and are now shared
between these parts are module-visible rather than private.  They remain
internal to `InductiveModels.Check`: no name changed namespace, and the
checker's public API is unchanged.
-/
