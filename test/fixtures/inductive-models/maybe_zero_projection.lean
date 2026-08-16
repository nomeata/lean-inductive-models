/- **The one-constructor owners at a maybe-zero sort whose payload the model
   must retain, and which no route retains it for.**

   The maybe-zero (`.bare`) route is the Church encoding under the derived
   exact-sort lift.  That carrier is the lift of a *proposition*, so it is a
   subsingleton at every positive instantiation of `u`, and its recursor's
   motive is `Prop`-valued.  For the recursor and its ι rule that is a model
   and not a collapse — the argument in `InductiveModels.Simple`'s header — and
   for a multi-constructor owner it is the whole story, because nothing asks
   for a field back.

   A **one constructor** owner does ask.  Intrinsic projections are demanded of
   every one-constructor owner and of nothing else: `nc == 1` is the entire
   shape gate (`Driver.lean:810-817`, and `Format/Exact.lean:326-328` says in
   as many words that the kernel "does not require the owner to be
   non-recursive or unindexed").  A subsingleton carrier cannot satisfy
   `proj (mk a) = a` and `proj (mk b) = b` at once, which is exactly what
   `Simple/Tight.lean:9-15` records, and it is why the **direct** routes exist:
   `.identity` when the field's sort is the carrier's, `.propLift` when the
   field is exactly a proposition, and the right-nested `PSigma'` tower for two
   or more.

   Those routes are gated on `nonrecursiveOneConstructor && ni == 0`
   (`Simple/Site.lean:469-471`).  **The projection contract is not.**  The two
   excluded conjuncts are this file:

   * `MZSelf` — recursion alone, and the minimum of the whole family.  The one
     projected field *is* the carrier, at `Sort u`, and the Church recursor
     eliminates only into `Prop`.
   * `MZData` — the same with a data field in front of the child.
   * `MZIdx` — no recursion; an **index**, and a data field.  The route that
     was supposed to cover this is arm F, whose guard carries `large`
     (`Site.lean:322-323`).  `Site.lean:359-374` argues that a data field which
     is not a conclusion index is unreachable there, "because the kernel mints
     that recursor only when every non-proof field is literally recoverable as
     a conclusion index".  That premise is correct and the conclusion drawn
     from it is not: the kernel does not refuse such a declaration, it mints a
     **small** recursor for it — so `large` is false, arm F never fires, and
     the shape falls through to Church.  `MZIdx.rec`'s motive really is
     `Prop`-valued; read the export.
   * `MZIdx2` — the same at two data fields, which is the tight tower's own
     shape with an index in front of it.

   `MZOne` and `MZProof` are the controls on either side: the first is the
   direct `.identity` route (`ni == 0`, not recursive), the second is arm F
   proper (every field a proof, so the kernel does mint the large eliminator).
   Both model.

   The four in the middle do not.  The generator emits the projection anyway
   and Lean's kernel refuses it:

       [MZSelf._model.proj_0]: (kernel) application type mismatch

   The run aborts at the first refusal, so only one of the four is named per
   run; the family is the four, not the one that happens to be printed. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u

inductive Eq : {a : Sort u} → a → a → Prop where
  | refl (x : a) : Eq x x

inductive Nt : Type where
  | z : Nt
  | s : Nt → Nt

inductive MZOne (a : Sort u) : Sort u where
  | mk : a → MZOne a

inductive MZProof (p : Prop) (n : Nt) : Nt → Sort u where
  | mk : p → MZProof p n n

inductive MZSelf : Sort u where
  | mk : MZSelf → MZSelf

inductive MZData (a : Sort u) : Sort u where
  | mk : a → MZData a → MZData a

inductive MZIdx (a : Sort u) (n : Nt) : Nt → Sort u where
  | mk : a → MZIdx a n n

inductive MZIdx2 (a : Sort u) (b : Sort u) (n : Nt) : Nt → Sort u where
  | mk : a → b → MZIdx2 a b n n
