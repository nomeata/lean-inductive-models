import InductiveModels.Format.Types
import InductiveModels.Format.Alias
import InductiveModels.Format.Export
import InductiveModels.Format.Exact
import InductiveModels.Format.Parse
import InductiveModels.Format.Write
/-!
# The Lean 4 export format, read and written

`lean4export` 3.1.0's `.ndjson`: one JSON object per line, each either a
*record* interning a name (`in`), a level (`il`) or an expression (`ie`), or a
**declaration** naming earlier records by index.

The parser here is the whole of the tool's trust boundary and it does **no
checking**: an export is read into `Lean.Name` / `Lean.Level` / `Lean.Expr`
verbatim. Input validation is deliberately separate from parsing, and nothing
below runs a typechecker.

Two properties the rest of the tool depends on:

* **References must name an explicitly defined arena entry.** Arena IDs may be
  sparse, out of order, or overwritten, but an absent ID is never an implicit
  anonymous name, zero level, or bound variable. [`Writer`] emits a fresh dense
  arena when transforming an export.
* **The writer's key order is alphabetical and it emits no whitespace.** This
  is the canonical `lean4export` spelling, so canonical dense fixtures retain
  their bytes on a no-op run. Sparse, overwritten, metadata-bearing, or
  differently formatted valid input is normalized when it is written again.
-/

/-!
## Module layout

This file is a facade: it only re-exports the six modules below, so
`import InductiveModels.Format` continues to name the whole format library.

* [`InductiveModels.Format.Types`] — the export record types (the floor)
* [`InductiveModels.Format.Alias`] — collision-safe source replay aliases
* [`InductiveModels.Format.Export`] — `Export` and its primitive projections
* [`InductiveModels.Format.Exact`] — exact export-syntax normalization
* [`InductiveModels.Format.Parse`] — the reader
* [`InductiveModels.Format.Write`] — the writer

`Types` is imported by everything; `Alias`, `Exact` and `Write` are leaves.
`Write` imports `Parse` only to sit above it in the module order.
-/
