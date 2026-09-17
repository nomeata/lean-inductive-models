/- **An owner whose gates are decided by the checker that judges the result.**

   Every conversion question this tool asks is a question about the *kernel's*
   conversion, and the kernel is what judges the emitted island, so every gate
   asks it directly ([`InductiveModels.kernelDefEq`]). `Sg` is the minimal
   occupant of the one gate where that is not a preference but the only
   answerable form of the question.

   `Sg._model.proj_1`'s codomain is `add_assoc`'s type with `toAdd` replaced by
   `proj_0` at the major; the constructor's own binder carries the same type
   with the field itself. The two convert exactly when `proj_0` *selects* its
   field on the modeled constructor, which is a δι question and not a
   syntactic one — and the terms it is asked of are the source's own, here an
   ordinary `Π`-nest over `HAdd.hAdd` applications at carrier `G`.

   Asking `Meta.isDefEq` instead used to kill the run outright.
   `Lean.Meta.isDefEqOffset` recognizes a `Nat` offset by *constant name* —
   `Nat.succ`, `Nat.add`, `Add.add`, `HAdd.hAdd`, `OfNat.ofNat` — and confirms
   the instance argument against `instAddNat` and `@instHAdd Nat instAddNat`;
   it asks that *before* its own `Nat`-typed guard, so a `G`-valued `+` pays
   the lookup too. Every environment this tool computes in is the input stream
   plus what generation splices, with no prelude underneath, so the lookup
   found nothing and `Unknown constant` reached the CLI as exit 3 — on an input
   that is in scope and perfectly well formed. The kernel asks for no constant
   that is not in the terms it is given.

   This is an **algebraic hierarchy at its usual shape** and nothing more:
   `Add` and `HAdd` are one-field classes, `instHAdd` is the ordinary bridge,
   and `Sg` is a two-field structure whose `Prop` field's type mentions the
   first field — the tight `PSigma'` tower, spine and block. What matters is
   that the source binds the recognized names, and any algebraic hierarchy
   does. `Nat` itself is nowhere in this export, and the model never needs it. -/

--#export Sg

universe u

structure Sg (G : Type u) extends Add G where
  add_assoc : ∀ a b c : G, a + b + c = a + (b + c)
