/-
# The whole demonstration, in one file

This is the minimal standalone reproducer for the claim that **meta-level code
can change what Lean's kernel accepts**.  It is an ordinary Lean executable.
It uses no `sorry`, no `native_decide`, no `@[implemented_by]`, no
`unsafe`, and no compiler or elaborator extension point.  It calls
`Lean.loadDynlib`, which is a plain `IO` action available to any Lean program,
and after that call `Environment.addDeclCore` — the kernel — gives a different
answer to the same question.

## The declaration

`Witness.{u,v}` is *stated* to be `Sort (max 1 u v)`, and its value is

    PUnit.{max 1 (imax (imax u v) v) (max 1 u v)}

whose type is `Sort (max 1 (imax (imax u v) v) (max 1 u v))`.  The two levels
are equal at every assignment of `u` and `v` — the `imax` is dominated by the
`max 1 u v` sitting next to it — so the declaration is semantically fine.  Lean
rejects it anyway, because its level definitional equality is normal-form
comparison and a `max` does not absorb an `imax` it dominates.  That refusal is
`MODELGEN.md` §8.6, and it is the one that makes `modelgen` decline the `BoxF`
carrier.

Note the declaration is built by hand rather than written as source: Lean's
*elaborator* compares levels with `Lean.Level.isEquiv`, which is implemented in
Lean and is a different function from the kernel's C++ `lean::is_equivalent`.
The library loaded here rewrites the kernel's call sites only.  So the
elaborator is unchanged, and going through `addDeclCore` directly is what makes
this a statement about the kernel.

## Running it

    lake build
    ./.lake/build/bin/leveldemo ../levelhack.so

Expected output: `REJECTED` before the `loadDynlib`, `ACCEPTED` after it, with
the same `Environment` and the same `Declaration`.

## The point

Nothing here is a bug in Lean.  A Lean program that can run `IO` can load
native code, and native code in the same address space can rewrite the kernel.
"Checked by Lean's kernel" is a claim about a process, not about a proof term,
and a process that has done this is no longer making it.
-/
import Lean
open Lean

/-- `u` and `v`, as raw level parameters.  The `Level` constructors are used
directly rather than the `mkLevel*'` smart constructors, because the smart
constructors would simplify the very shape under test. -/
def lu : Level := .param `u
def lv : Level := .param `v
def one : Level := .succ .zero

/-- `max 1 u v`. -/
def small : Level := .max (.max one lu) lv

/-- `max 1 (imax (imax u v) v) (max 1 u v)` — equal to `small` at every
assignment, and not equal to it under Lean's normaliser. -/
def big : Level := .max (.max one (.imax (.imax lu lv) lv)) small

def witness : Declaration :=
  .defnDecl { name := `Witness, levelParams := [`u, `v],
              type := .sort small, value := .const ``PUnit [big],
              hints := .abbrev, safety := .safe }

/-- Ask the kernel, with checking on. -/
def ask (env : Environment) : IO String := do
  match env.addDeclCore 0 witness none true with
  | .ok _ => return "ACCEPTED"
  | .error e =>
    let msg ← (e.toMessageData {}).format
    return s!"REJECTED — {msg.pretty.replace "\n" " "}"

def main (args : List String) : IO UInt32 := do
  let some (so : String) := args[0]?
    | do IO.eprintln "usage: leveldemo PATH/TO/levelhack.so"; return 1
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init }] {}

  IO.println "declaration:  Witness.{u,v} : Sort (max 1 u v) :="
  IO.println "                PUnit.{max 1 (imax (imax u v) v) (max 1 u v)}"
  IO.println ""
  IO.println s!"before loadDynlib:  {← ask env}"
  Lean.loadDynlib so
  IO.println s!"after  loadDynlib:  {← ask env}"
  IO.println ""
  IO.println "Same environment, same declaration, same kernel entry point."
  return 0
