/- **The family the exact-sort pad models at a maybe-zero sort**, and the one
   level relation all of it turns on.

   A nonrecursive one-constructor owner at a maybe-`Prop` sort is the
   field-preserving direct routes': the Church encoding behind them remembers
   only inhabitation, and every one-constructor owner is asked for its fields
   back (`Driver.addProjectionModels`' `nc == 1` gate is the whole shape gate).
   Those routes store the fields in a right-nested `PSigma'`
   ([`InductiveModels.tightTowerTy`]) which — ending at its last field — lands
   at `Sort (max ℓ⃗)`.

   **`max ℓ⃗` is not the carrier's sort in general, and that is one relation and
   not several.** Lean admits the declaration by `is_geq(w, ℓᵢ)` at each field;
   what the model needs is that bound *as a conversion*, `max ℓ⃗ w ≡ w`, which
   `is_geq` does not give and which a tower with no `w` in it cannot state.
   Every occupant below is that relation and nothing else: `PadOne` at one
   field, `PadMany` at several of the same level, `PadMix` at several of
   different levels, `PadDep` at fields whose types depend on each other, and
   `PadIdx`/`PadIdx2` with the conclusion's index telescope on top. They were
   three separate `incomplete` declines — the one-field route's, the tight
   tower's and the indexed case's — and they are one debt.

   **The pad is [`InductiveModels.unitAt`] `w` and it already existed.** The
   tower ends at the derived exact-sort lift of `⊤`,
   `PSigma'.{0,w} ⊤ (fun _ => PUnit.{w})`, which sits at `Sort (max 0 w)` —
   that is `Sort w` for a **bare, maybe-zero** `w` exactly as for a never-zero
   one, which is the same fact that lets the empty arm's `emptyAt w` be the exact
   carrier of an empty type at every route's sort. The tower then lands at
   `Sort (max ℓ⃗ w)`, and `max u (max u v)` *is* `max u v` in normal form. This
   is the never-zero tuple tower's own pad ([`InductiveModels.padsAt`]) at the
   one sort nothing had taken it to; no new construction was needed.

   Nothing is weakened to admit any of this. The pad's inhabitant is
   *definitionally* canonical — tight-pair and `PUnit` structure eta, proof
   irrelevance on `⊤` — so `mk (proj⃗ t) ≡ t` still holds, the recursor drops
   the pad by ι alone, and every projection and ι rule is still `Eq.refl`. The
   level question is asked with **stock** `isLevelDefEq`, never the complete
   procedure, because the carrier is a term the kernel must accept against
   `Sort w` and the kernel decides that by normal form; so no widening is
   reachable from here and none is counted.

   `PadNone` is the control the ordering rests on: its two fields already reach
   `max u v`, so the plan is *no pad* and its carrier is the bare two-component
   tower it always was. `IdOne` and `PropOne` are the two exact one-field
   answers, which still run first and are still the field itself and the bare
   lift — a pad would have modelled them too, and wrapping them in a pair
   nothing needs is what taking them first avoids.

   The shapes beyond the pad are `prim_shape_declines`' `PadImax` and
   `PadImaxIdx`, which are out of scope rather than incomplete. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v w

inductive Eq : {a : Sort u} → a → a → Prop where
  | refl (x : a) : Eq x x

inductive Nt : Type where
  | z : Nt
  | s : Nt → Nt

-- The two exact one-field answers, unchanged and taken before the tower.
inductive IdOne (a : Sort u) : Sort u where
  | mk : a → IdOne a

inductive PropOne (p : Prop) (a : Sort u) : Sort u where
  | mk : p → PropOne p a

-- No pad: the fields' own levels already reach the carrier's sort.
inductive PadNone (a : Sort u) (b : Sort v) : Sort (max u v) where
  | mk : a → b → PadNone a b

-- One field, several fields, several levels, dependent fields.
inductive PadOne (a : Sort u) (b : Sort v) : Sort (max u v) where
  | mk : a → PadOne a b

inductive PadMany (a : Sort u) (b : Sort v) : Sort (max u v) where
  | mk : a → a → PadMany a b

inductive PadMix (a : Sort u) (b : Sort v) (c : Sort w) : Sort (max u (max v w)) where
  | mk : a → b → PadMix a b c

inductive PadDep (a : Sort u) (f : a → Sort v) (c : Sort w) : Sort (max u (max v w)) where
  | mk : (x : a) → f x → PadDep a f c

-- The same storage with the conclusion's index telescope on top.
inductive PadIdx (a : Sort u) (b : Sort v) (n : Nt) : Nt → Sort (max u v) where
  | mk : a → PadIdx a b n n

inductive PadIdx2 (a : Sort u) (b : Sort v) (n : Nt) : Nt → Sort (max u v) where
  | mk : a → a → PadIdx2 a b n n
