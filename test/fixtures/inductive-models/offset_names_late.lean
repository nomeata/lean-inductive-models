/- **The same owner, with the input's own `Nat` record behind it.**

   `offset_names.lean` is this shape with no `Nat` in the export at all. The
   two are the same state at the point the projection gate is decided — the
   construction environment holds what the stream has delivered so far, and a
   record further down the stream has not been delivered — so the same gate is
   asked the same question, of the kernel ([`InductiveModels.kernelDefEq`]),
   and neither run needs `Nat` to answer it.

   What this file adds is the half that only exists once `Nat` is in the
   export: `Cnt` is an ordinary two-constructor owner in front of everything,
   so generation writes its own `Nat` and `Eq` at the first point one is
   needed, and the input's own `Nat` record — which arrives four records later,
   because `Use` is the first root that mentions it — is dropped against the
   declaration that was written
   ([`InductiveModels.canonicalBasisRecordMatches`]). Both are reported as the
   basis exemption.

   `Sg` stands between the two, and it is why the pair is not a duplicate: it
   is modelled with `Nat` already installed and `instAddNat` still absent.
   Under the old elaborator gate that was a *different* failure from
   `offset_names.lean`'s, at a different constant, which is the evidence that
   installing a basis member was never the repair — the gate was asking the
   wrong checker. -/

--#export Cnt Sg Use

universe u

inductive Cnt : Type where
  | zero : Cnt
  | succ : Cnt → Cnt

structure Sg (G : Type u) extends Add G where
  add_assoc : ∀ a b c : G, a + b + c = a + (b + c)

inductive Use : Nat → Prop where
  | mk (x : Nat) (h : x = x) : Use x
