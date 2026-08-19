/- **A declaration may name a universe parameter that nothing inside it
   mentions**, and the export must still introduce that parameter as a level.

   `levelParams` is part of a declaration's kernel identity, not a summary of
   the levels its type and value happen to use: the kernel accepts
   `def levelComp4.{u} : Sort 1 := Sort 0`, whose one universe parameter occurs
   in neither expression. `lean4export` emits the parameter regardless — its
   `dumpUparams` dumps every name *and* the `Level.param` of every name before
   the record that lists them — so a stream always introduces the level
   parameters its declarations name. A writer that emitted only the levels
   reachable from expressions drops that line and leaves the declaration naming
   a parameter the stream never declares; a consumer which interns
   `Level.param` at parse time (nanoda does) then has nothing to intern.

   `018_levelComp4` of the Lean Kernel Arena's `good/tutorial` set is exactly
   the `def` below, and is where this was found.

   **Lean's elaborator cannot write this file.** `unused universe parameter 'w'`
   is an elaboration error (`Lean/Elab/DeclUtil.lean`), so the four
   declarations are added through `addDecl`: the kernel, which is what an export
   is a transcript of, has no such rule. That is the point of the fixture — the
   shape is unreachable from surface Lean and reachable from the kernel, so
   only a hand-built declaration finds it.

   All four ordinary declaration kinds that can carry a level parameter are
   here. `quot`'s four declarations are fixed by `init_quot` and have no
   unused-parameter form, and an inductive block cannot exhibit the missing
   line at all — every constructor ends in the type applied to the block's own
   parameters, so a block always mentions them. The writer's remaining
   level-parameter lists are pinned per declaration kind in `arenaformat`. -/
import Lean

open Lean

inductive UnusedP : Prop where
  | mk : UnusedP

--#export UnusedP unusedAxiom unusedDef unusedTheorem unusedOpaque

/- The four kernel declarations whose one universe parameter no expression of
   theirs mentions. `unusedDef` is `018_levelComp4` of the arena set. -/
run_cmd Elab.Command.liftCoreM do
  addDecl <| .axiomDecl
    { name := `unusedAxiom, levelParams := [`w], type := .sort (.succ .zero), isUnsafe := false }
  addDecl <| .defnDecl
    { name := `unusedDef, levelParams := [`w], type := .sort (.succ .zero), value := .sort .zero,
      hints := .opaque, safety := .safe }
  addDecl <| .thmDecl
    { name := `unusedTheorem, levelParams := [`w], type := .const `UnusedP [],
      value := .const `UnusedP.mk [] }
  addDecl <| .opaqueDecl
    { name := `unusedOpaque, levelParams := [`w], type := .sort (.succ .zero),
      value := .sort .zero, isUnsafe := false }
