/- **The one-constructor owners at a maybe-zero sort whose payload the model
   must retain, and the four different answers to "retain it how".**

   The maybe-zero (`.bare`) route is the Church encoding under the derived
   exact-sort lift.  That carrier is the lift of a *proposition*, so it is a
   subsingleton at every positive instantiation of `u`, and its recursor's
   motive is `Prop`-valued.  For the recursor and its ι rule that is a model
   and not a collapse — the argument in `InductiveModels.Simple`'s header — and
   for a multi-constructor owner it is the whole story, because nothing asks
   for a field back.

   A **one constructor** owner does ask.  Intrinsic projections are demanded of
   every one-constructor owner and of nothing else: `nc == 1` is the entire
   shape gate (`Driver.lean`'s `addProjectionModels`, and `Format/Exact.lean`
   says in as many words that the kernel "does not require the owner to be
   non-recursive or unindexed").  A subsingleton carrier cannot satisfy
   `proj (mk a) = a` and `proj (mk b) = b` at once, which is exactly what
   `Simple/Tight.lean` records, and it is why the **direct** routes exist:
   `.identity` when the field's sort is the carrier's, `.propLift` when the
   field is exactly a proposition, and the right-nested `PSigma'` tower for two
   or more.

   Those routes were gated on `nonrecursiveOneConstructor && ni == 0`.
   **The projection contract is not.**  Both excluded conjuncts are this file,
   and both are now closed — by two different constructions, because they are
   two different questions:

   * `MZIdx` — no recursion; an **index**, and a data field.  **Green on the
     direct routes' indexed case.**  The route that was supposed to cover it is
     arm F, whose guard carries `large`; `Site.lean` argued that a data field
     which is not a conclusion index is unreachable there, "because the kernel
     mints that recursor only when every non-proof field is literally
     recoverable as a conclusion index".  That premise is correct and the
     conclusion drawn from it was not: the kernel does not refuse such a
     declaration, it mints a **small** recursor for it, so `large` is false and
     the shape fell through to Church.  `MZIdx.rec`'s motive really is
     `Prop`-valued; read the export.  What arm F cannot do here is *store* the
     field — its carrier is a Church conjunction of proofs, and it recovers
     data only by substituting at a pivot — so the shape is not arm F's after
     all.  Storing it is what the direct routes already do, and the index is
     discharged by arm F's packed Henry-Ford equation over that same storage:
     `T p⃗ ι⃗ := Σ'(t : Store p⃗), pack ι⃗_ctor(proj⃗ t) = pack ι⃗`, with `Store`
     the tight `PSigma'` tower as a **definition**.  The projection is the
     tower's own, so it selects definitionally and its rule is `Eq.refl`.
   * `MZIdx2` — the same at two data fields, which is the tight tower's own
     shape with an index in front of it.  **Green, on the same route and the
     same tower.**
   * `MZSelf` — recursion alone, and the minimum of the whole family.  The one
     projected field *is* the carrier, at `Sort u`.  **Arm E.**
   * `MZData` — the same with a data field in front of the child.  **Arm E.**

   `MZOne` and `MZProof` are the controls on either side: the first is the
   direct `.identity` route (`ni == 0`, not recursive), the second is arm F
   proper (every field a proof, so the kernel does mint the large eliminator).
   Both model, and both are untouched by either closure.  The indexed case's
   guard carries `!armFNonRec`, so every shape whose data the index vector
   *does* carry stays arm F's; `ni == 0` selects one of the two unindexed
   cases; and arm E is reached only past both.

   **`MZSelf` and `MZData` are not a storage problem; they are empty.**  The
   reading that kept them red asked where a *recursive* field could be stored —
   the tight tower would have to hold an inhabitant of the type being declared,
   which a definition cannot mention — and concluded that nothing retains the
   field, leaving open whether such an owner should be asked for a projection
   at all.  The question does not arise.  Each of these constructors has a
   **bare** recursive field, so applying it already needs an inhabitant of the
   carrier: `MZSelf` and `MZData a` are uninhabited at every instantiation of
   `u`.  That is exactly the class arm E models, by
   `emptyAt w = PSigma'.{0,w} (∀ p : Prop, p) (fun _ => PUnit.{w})` — the
   derived exact-sort lift of Church `⊥`.

   **And the *non*-recursive field is stored after all.**  What makes a
   `PSigma'` uninhabited is one uninhabited component, so
   `Σ'(x : a), emptyAt u` is empty because of its tail while holding `MZData`'s
   data field in front of it, and that tail is a constant — it does not mention
   the carrier, so the carrier is still a definition.  `MZSelf` has no such
   field and its carrier is the bare `emptyAt u`; `MZData`'s is a one-component
   tower, its field 0 is the tower's own `PSigma'.fst`, and its ι rule is
   `Eq.refl`.  Neither owner's *recursive* field is stored, and by positivity
   no codomain can ever name one.

   **The universe question is the one the lift already answers.**  `∀ p : Sort u, p`
   is empty too, but it lives at `Sort (imax (u+1) u)` and so misses the
   declared sort; the lift instead puts an empty *proposition* at
   `Sort (max 0 w) = Sort w` for a **bare** `w` exactly as for a never-zero
   one.  So arm E was never sort-specific, and its guard no longer says it is:
   it reads `route matches .type | .bare`, `ni == 0`, `isRec`, and
   `bareRecSlotOf` at every constructor.  Nothing about the class is about
   linearity, a base constructor, or a `Type`-valued carrier.

   Everything the contract asks for then follows from emptiness, with no
   axiom:

   * the carrier ends at `emptyAt u`, with the constructor's non-recursive
     fields stored in front of it;
   * `mk` is `⟨f⃗, drop t⟩` for its own bare recursive field `t`, whose descent
     `drop` already carries that emptiness — so it manufactures nothing;
   * `rec` eliminates its major premise.  This is a genuine change of model —
     Church handled the recursor adequately and this replaces it — and it is
     adequate for the same interface and more: both owners' kernel recursors
     are **small** (`MZSelf`'s field is not a proof and is not a conclusion
     index, so the subsingleton rule declines it, and `MZData`'s data field
     likewise), and `emptyAtElim` serves at every result universe, so arm E
     would deliver a large eliminator too if the kernel had minted one, which
     the Church fold could not.  Arm E's `large` guard is therefore an
     invariant of the never-zero route and not a precondition of the arm;
   * every ι rule is on the literal contract with the constructor's own binder
     on the right, exactly as everywhere else — `Eq.refl` for a stored field,
     whose projection is the tower's own and reduces by π, and an elimination
     of the descended major for the recursor's and the recursive field's.

   The carrier level and the descent travel from the arm to the common
   projection driver as `Iso.emptyCarriers`, which is a stated property of the
   emitted model and not a name, a count or a fixture:
   `Driver.addProjectionModels` reads it, and where it is present the recursive
   fields' selector and rule are eliminations through that descent and there is
   no other route to fall back to. -/
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
