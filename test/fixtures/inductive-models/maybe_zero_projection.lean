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

   Those routes are gated on `nonrecursiveOneConstructor && ni == 0`.
   **The projection contract is not.**  The two excluded conjuncts are this
   file, and the index one is closed:

   * `MZSelf` — recursion alone, and the minimum of the whole family.  The one
     projected field *is* the carrier, at `Sort u`, and the Church recursor
     eliminates only into `Prop`.
   * `MZData` — the same with a data field in front of the child.
   * `MZIdx` — no recursion; an **index**, and a data field.  **Green now, on
     arm S.**  The route that was supposed to cover it is arm F, whose guard
     carries `large`; `Site.lean` argued that a data field which is not a
     conclusion index is unreachable there, "because the kernel mints that
     recursor only when every non-proof field is literally recoverable as a
     conclusion index".  That premise is correct and the conclusion drawn from
     it was not: the kernel does not refuse such a declaration, it mints a
     **small** recursor for it, so `large` is false and the shape fell through
     to Church.  `MZIdx.rec`'s motive really is `Prop`-valued; read the export.
     What arm F cannot do here is *store* the field — its carrier is a Church
     conjunction of proofs, and it recovers data only by substituting at a
     pivot — so the shape is not arm F's after all.  Arm S is arm F's packed
     Henry-Ford equation over the direct routes' exact-sort storage:
     `T p⃗ ι⃗ := Σ'(t : Store p⃗), pack ι⃗_ctor(proj⃗ t) = pack ι⃗`, with `Store`
     the tight `PSigma'` tower as a **definition**.  The projection is the
     tower's own, so it selects definitionally and its rule is `Eq.refl`.
   * `MZIdx2` — the same at two data fields, which is the tight tower's own
     shape with an index in front of it.  **Green, on the same arm and the
     same tower.**

   `MZOne` and `MZProof` are the controls on either side: the first is the
   direct `.identity` route (`ni == 0`, not recursive), the second is arm F
   proper (every field a proof, so the kernel does mint the large eliminator).
   Both model, and both are untouched by arm S — arm F is tried first, and
   `ni == 0` never reaches arm S at all.

   **`MZSelf` and `MZData` are still red, deliberately.**  They are Direct's
   `isRec` corner: the projected field of `MZSelf` *is* the carrier at
   `Sort u`, `MZData` has a data field in front of that child, and the Church
   recursor eliminates only into `Prop`.  Nothing here stores a recursive
   field — the tight tower would have to hold an inhabitant of the type being
   declared — so neither the direct routes nor arm S reaches them, and whether
   a maybe-zero *recursive* one-constructor owner should be asked for a
   projection at all is a contract question rather than a construction one.
   The generator emits the projection anyway and Lean's kernel refuses it:

       [MZData._model.proj_0]: (kernel) application type mismatch

   The run aborts at the first refusal, so only one of the two is named per
   run; the family is the two, not the one that happens to be printed. -/
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
