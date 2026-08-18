/- **A field domain that is the owner only after an ι step, and whose major
   premise is the field before it.**

   `Owner.node`'s second field is written `Eq.rec Owner h`. Its `whnf` is
   `Owner`, so this is an ordinary bare recursive field and Lean's positivity
   check — which reduces a field domain before testing it — accepts the
   declaration, gives `Owner` a recursor with the induction hypothesis and
   builds the ι rule that applies it. Nothing here is nested, indexed, forged
   or unsafe; the fixture is what a kernel-valid export of this shape looks
   like.

   What makes it a fixture is *where* the reduct comes from. The step that
   exposes `Owner` is the K-reduction of `Eq.rec`, and its major premise is
   `h` — the constructor's **own earlier field**. A shape walk that reads the
   constructor telescope as the raw `Π`-nest it is exported as therefore hands
   `whnf` a domain in which `h` is still a loose de Bruijn variable, and
   `Lean.Meta.whnfEasyCases` answers that with `PANIC ... loose bvar in
   expression` rather than with a verdict. Three walks did exactly that —
   `InductiveModels.erasureBareFailure?`, `InductiveModels.recSlotOf` and
   `InductiveModels.bareRecSlotOf` — and each is reached on this declaration:
   the first from `analysePrim` and from the indexed-fibre adapter's
   eligibility test, the last two from the never-zero recursive route.

   `(fun _ : T => N) k` and `let _u := T; N` — `nonindexed_vanishing` and
   `dead_owner_mention` — are the βζ spellings of a mention the field's own
   reduction *discards*; `InductiveModels.headNorm` settles those without
   asking the kernel anything. This is the opposite one: the reduction is an ι
   step, no amount of β or ζ performs it, and the only way to ask for it is to
   open the telescope with real local declarations first.

   `P` is a two-element type so that `Eq P.one P.one` is a proposition with
   something to be about; `Eq` is declared here because the fixture is a
   `prelude`. -/
prelude
--#export Eq P Owner

universe u

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive P : Type where
  | one : P
  | two : P

inductive Owner : Type where
  | tip : Owner
  | node (h : Eq P.one P.one)
      (child : @Eq.rec P P.one (fun _ _ => Type) Owner P.one h) : Owner
