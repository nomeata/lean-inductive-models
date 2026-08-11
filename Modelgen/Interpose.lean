import Lean

/-!
# `--interpose-levels`: running the corpus against a kernel that is not stock

This module is the Lean half of `modelgen/interpose/`.  The other half is a
shared object of C that, when loaded, rewrites the call sites of
`lean::is_equivalent` and `lean::is_geq` inside this process so that Lean's
kernel gets a *complete* universe-level procedure instead of its own
normal-form comparison.  Read `modelgen/interpose/interpose.c`'s header for the
mechanism; read `MODELGEN.md` §8.6 for why anyone would want it.

## What this module owes the rest of the tool

Three things, and they are all about not lying afterwards.

* **The load is opt-in and loud.**  Nothing here runs unless
  `--interpose-levels PATH` is given.  The shared object prints a banner naming
  every call site it rewrote, and a census at exit splitting level comparisons
  into *accepted by the stock kernel*, *accepted only under interposition*, and
  *rejected by both*.

* **The load is verified by a behaviour change, not by a return code.**
  [`Modelgen.Interpose.enable`] asks the kernel about [`levelWitness`] twice:
  once before the load, where it must be **rejected**, and once after, where it
  must be **accepted**.  Either half failing is a hard error.  A `loadDynlib`
  that succeeded and changed nothing is exactly the failure this repository has
  paid for nine times — a check reporting success having done nothing
  (`DECISIONS.md` 2026-08-08, "SKIP is not PASS") — so it is made impossible to
  reach silently.

* **The claim changes.**  With this flag on, "checked by Lean's kernel" is
  false for anything that only passed because of an escape.  The census is what
  tells the two populations apart; `escapes = 0` means the run was, for level
  comparisons, a stock-kernel run after all.

## What it does not touch

this project's own `kernel/` — the Rust trusted computing base — is not involved
in any of this and is not modified.  The kernel being rewritten is *Lean's*
C++ one, inside this process, for the duration of this process.
-/

namespace Modelgen.Interpose

open Lean

/-- `max 1 u v`. -/
private def small : Level := .max (.max (.succ .zero) (.param `u)) (.param `v)

/-- `max 1 (imax (imax u v) v) (max 1 u v)`.  Equal to [`small`] at every
assignment of `u` and `v`; not equal to it under Lean's normaliser, which is
`MODELGEN.md` §8.6's whole subject.  Raw `Level` constructors, not the
`mkLevel*'` smart ones, which would simplify the shape under test away. -/
private def big : Level := .max (.max (.succ .zero) (.imax (.imax (.param `u) (.param `v)) (.param `v))) small

/-- The declaration whose kernel verdict flips.  Its value is the sort `Sort
big`, whose type is `Sort (big+1)`; it is declared at `Sort (small+1)`.  Stock
Lean rejects — `big` and `small` are equal at every assignment and its
normaliser does not see it — and a complete level procedure accepts.

Two deliberate choices.  It is **not** the `BoxF` carrier, so that a failure
here is a failure of the interposition and of nothing else.  And it mentions
**no constant at all**, because `modelgen` runs against `importModules #[] {}`;
an earlier version used `PUnit` and the verdict failed to flip for the boring
reason that `PUnit` was not in scope — caught, as intended, by
[`enable`]'s refusal rather than by anyone reading a log. -/
def levelWitness : Declaration :=
  .defnDecl { name := `Modelgen.Interpose.levelWitness.probe, levelParams := [`u, `v],
              type := .sort (.succ small), value := .sort big,
              hints := .abbrev, safety := .safe }

/-- The kernel's verdict on [`levelWitness`]: `none` for accepted, `some msg`
for rejected.

**`IO`, and that is not decoration.** `Environment.addDeclCore` looks pure —
same environment, same declaration — and here it is not: the whole point is
that its answer changes when native code is loaded underneath it.  Written as a
`Bool`-valued pure function, Lean's compiler is entitled to evaluate the two
calls in [`enable`] once, and it did: the take-verification reported "no flip"
on a run where the flip demonstrably happened.  The `IO` is what stops the two
questions from being the same question. -/
def kernelVerdict (env : Environment) : IO (Option String) :=
  match env.addDeclCore 0 levelWitness none true with
  | .ok _ => return none
  | .error e => return some (← (e.toMessageData {}).format).pretty

def kernelAcceptsWitness (env : Environment) : IO Bool :=
  return (← kernelVerdict env).isNone

/-- Does the **elaborator** — not the kernel — call `big` and `small` equal?

This is a separate question with a separate answer, and the separation is the
main finding of this whole exercise.  `Lean.Meta.isLevelDefEq` is compiled Lean;
`lean::is_equivalent` is C++; they are different functions with different
incompleteness.  `modelgen`'s planner asks *this* one — `Modelgen/Simple.lean`'s
`plan`, which tries `max (max 1 ℓ⃗) w =?= w` as its pad candidate — so a
kernel-only interposition changes nothing the planner decides, which was
measured across the whole corpus before this check existed. -/
def metaAcceptsWitness (env : Environment) : IO Bool := do
  let ctx : Core.Context :=
    { fileName := "<interpose-probe>", fileMap := default, maxHeartbeats := 0 }
  let (b, _) ← (Meta.MetaM.run' (Meta.isLevelDefEq big small)).toIO ctx { env }
  return b

/-- Load the interposition and prove it took.  Throws unless **both** the
kernel's verdict on [`levelWitness`] and the elaborator's verdict on the same
level pair go from reject to accept. -/
def enable (env : Environment) (so : System.FilePath) : IO Unit := do
  let some before ← kernelVerdict env
    | throw <| IO.userError <|
        "--interpose-levels: this kernel already accepts the §8.6 witness before " ++
        "anything was loaded. Either it is not the Lean this was written against, " ++
        "or an interposition is already active. Refusing to report a flip that did " ++
        "not happen."
  if ← metaAcceptsWitness env then
    throw <| IO.userError <|
      "--interpose-levels: the elaborator already calls the §8.6 pair equal " ++
      "before anything was loaded. Refusing to report a flip that did not happen."
  Lean.loadDynlib so
  if let some after ← kernelVerdict env then
    throw <| IO.userError <|
      s!"--interpose-levels: loaded {so}, and the kernel's verdict on the §8.6 " ++
      "witness did not change. The interposition did not take. Refusing to " ++
      "continue: a run under a flag that did nothing is worse than no run.\n" ++
      s!"  before: {before}\n  after:  {after}"
  unless ← metaAcceptsWitness env do
    throw <| IO.userError <|
      s!"--interpose-levels: loaded {so}, the kernel flipped, and " ++
      "Lean.Meta.isLevelDefEq did not. Only half the interposition took, and " ++
      "the half that decides whether modelgen's planner even builds the model " ++
      "is the half that did not. Refusing to continue."
  IO.eprintln <|
    "[modelgen] --interpose-levels: kernel verdict on the §8.6 witness flipped " ++
    "reject -> accept.\n" ++
    "[modelgen] This run's kernel is NOT stock. Read the [levelhack] census at " ++
    "exit before\n" ++
    "[modelgen] describing anything below as 'checked by Lean's kernel'.\n" ++
    "[modelgen] Exactly 1 of the escapes in that census is this probe; the rest " ++
    "are the run's own."

end Modelgen.Interpose
