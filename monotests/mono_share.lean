/- **The memo's key is shared across declarations, so it has to be canonical.**

   `monomorph` memoises the rewrite of a subterm on `(e, σ restricted to the
   parameters e mentions)`, and the memo lives for the whole emission — so the
   *same* `Expr` is looked up while emitting *different* declarations. The
   export is an arena: two declarations that write the same type share one node.

   `fwd` and `rev` below have **the same type expression** — `Sort u → Sort v →
   N`, one node, interned once — and **opposite `levelParams` orders**. So:

   * a key that names parameters by their **position in the declaring
     declaration's own list** makes `fwd`'s `{u↦0, v↦1}` and `rev`'s
     `{v↦0, u↦1}` both read `pos0↦0, pos1↦1`. One key, two different right
     answers, and the memo returns the first — `rev` comes out with `fwd`'s
     type. Nothing about the naming or the counts would look wrong; the kernel
     replay is what catches it, which is why this fixture exists at all.
   * a key that names them **globally, by name**, gives `fwd` `{u↦0, v↦1}` and
     `rev` `{u↦1, v↦0}`. Two keys, and both copies are right.

   The other half of the property is a *hit*: `fwd.{0,1}` and `fwd.{0,2}` agree
   on `u` and differ on `v`, so the subterm `Sort u` — whose carrier is `{u}` —
   must key the same under both. That one is not observable in the output, by
   construction; `MONO_STATS=1`'s entry count is where it is measured, and
   `MONOMORPH.md` §9.8 has the number.

   Two declarations would not distinguish this: it takes a shared node, two
   orders, and two instantiations that agree positionally. -/
prelude

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

--#export fwd rev useFwd useRev useFwdAgain

def fwd.{w, x} (_a : Sort w) (_b : Sort x) : N := N.z

def rev.{x, w} (_a : Sort w) (_b : Sort x) : N := N.z

/-- `fwd` at `w↦0, x↦1`. -/
def useFwd : N := fwd.{0, 1} (Eq N.z N.z) N

/-- `rev` at `x↦0, w↦1` — the same numerals in the same *positions*, and a
different substitution. -/
def useRev : N := rev.{0, 1} N (Eq N.z N.z)

/-- `fwd` again, agreeing with `useFwd` on `w` and differing on `x`: the hit. -/
def useFwdAgain : N := fwd.{0, 2} (Eq N.z N.z) (Type 0)
