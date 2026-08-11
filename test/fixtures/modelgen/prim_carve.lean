/- **Arm C**: an indexed family at a never-zero sort, modelled by carving it
   out of its own **index erasure** using a skeleton-plus-`good` construction,
   standing on a spliced inductive rather than on a W-type.

   Every occupant here declined before the arm landed, all with the one
   reason "an indexed family at a never-zero sort". Each is chosen for a
   discrimination the others do not make.

   * `Vc` — the base case: one index, linear recursion, and the index *moves*
     (`N.s n`) so the child's index and the result's differ.

   * `Two2` — **two constructors at the same index**. `Vc`'s two are separated
     by their index (`N.z` versus `N.s n`), so a model that lost the
     constructor tag entirely could still pass `Vc`'s pins; `Two2.l n` and
     `Two2.r n _` both live at `n`, so the recursor has to tell them apart on
     its own.

   * `Bl` — an index **telescope of length two**, packed into one `PSigma`.
     Two indices are not enough on their own: `bin` moves the first and leaves
     the second, `wide` moves the second and leaves the first, so a treatment
     that swapped the two, or applied one where the other belongs, is a type
     error in one of the two constructors rather than invisible in both.

   * `Fn` — an indexed family with **no recursion at all**, so `good` has no
     conjunction and the whole carve is one index equation. The arm's
     zero-recursive-field branch is otherwise unreached.

   * `Vec` — **parameterised**. Everything above is parameter-free, and a
     parameter is threaded through the skeleton's own type, its constructors,
     `good`, the carrier and the recursor; nothing without one would notice a
     parameter dropped in any of those five places.

   * `Tri3` — **three non-recursive fields**, with the recursive field's index
     read off the *first* and the conclusion's off the *third*. Two fields
     cannot distinguish an order that is preserved from one that is reversed,
     and a constructor whose child index and result index come from the same
     field cannot distinguish reading one for the other.

   Three occupants for the **multi-slot** carve — a constructor with more than
   one recursive field. Arm C runs at `erasureBare` rather than at
   `erasureLinear`: [`Modelgen.eraseCtorTy`] and [`Modelgen.spineSwap`] replace
   a recursive field's whole domain and do it once per such field, so the
   erasure of a branching family is as bare as a linear one — and the spliced
   skeleton that comes out branches, which is **arm W's** to model. That is why
   these three could not land before arm W did.

   * `Br` — the base case: **two recursive fields at different indices**,
     interleaved with the two non-recursive fields that carry those indices.
     Different child indices make most slot confusions a type error, which is
     what makes it the cheap target; it declined before this tranche with
     `erasure linear: no` and models now.

   * `Mx` — two recursive fields **interleaved with non-recursive ones and
     under a parameter**, at positions 1 and 4 of a five-field telescope. A
     carve that used a slot's *ordinal* where its telescope *position* belongs
     writes the child into a `N` field and is a type error here; with the
     recursive fields at the front of the telescope it would not be one.

   * `Sm3` — **three recursive fields at the same index and the same type**,
     which is the arm's own "skip is not pass" pin and the reason the count is
     three rather than two. Four mutations were run against these three
     occupants and the two axes below are the two that `Br` and `Mx` do not
     cover on their own.

     *Permutation.* All three of `tri`'s children have model type
     `Sm3._model n`, so a carve that permutes them builds a **well-typed
     constructor** — the skeleton constructor takes the three first components
     in the wrong order and the carve proof supplies the three `good` clauses
     in the matching wrong order, and the kernel accepts `ctor_1`. At `Br` and
     at `Mx` the same mutation dies at `ctor_1`, because their children sit at
     *different* indices and the swap is a type mismatch; only where the
     children are interchangeable does the constructor survive it. It is caught
     one declaration later, at `rec_0`: the recursor's minor concludes at
     the motive applied to the declaration-local constructor model, so that
     constructor's own value has
     to reduce to the skeleton term the index transport's motive was written
     against, and a permuted one does not. Measured: `Br` and `Mx` red at
     `ctor_1`, `Sm3` red at `rec_0`, and every single-slot occupant above
     untouched.

     *Association.* The carve's tail is a right-nested chain `B₀ ∧ (B₁ ∧ B₂)`,
     built by `chainMkOf` and taken apart by `chainSplit`, and those two have
     to invert each other. **With two conjuncts there is only one association**,
     so a chain built left and split right is invisible — measured, and `Br`
     and `Mx` both still model under it. `Sm3` is red at `ctor_1`. This is the
     one axis on which two recursive fields are no better than one.

     Two further mutations, for the record, and both loud at every multi-slot
     occupant: a **dropped** slot is rejected at `_model.good`, where the
     minor's induction-hypothesis count stops matching the skeleton recursor's
     own; **reversed** induction-hypothesis binders in the recursor are
     rejected at `rec_0`.

   Three occupants for the **infinitary** carve — a recursive occurrence under
   a binder. The erasure keeps the binders and replaces only the occurrence
   under them (`∀ z⃗, T p⃗ e⃗` becomes `∀ z⃗, S p⃗`), and each of the three
   consumers — `good`'s clause, the constructor's component, the recursor's
   induction hypothesis — wraps what it built in the same `z⃗`
   ([`Modelgen.withRecSlot`]). The spliced skeleton is then **arm W's**, which
   is why these could not land before arm W did, and `Inf2` was this file's
   third negative until they did.

   * `Inf2` — the base case: one binder at a ground type, and the child's index
     is a *field* rather than the binder. It was the occupant of the erasure
     guard's infinitary refusal and is now a model.

   * `Cf` — **`PFunctor.Approx.CofixA` transcribed**, which is the declaration
     this arm was extended for: two **parameters**, the second a family, the
     branch type `B a` reading the constructor's own earlier field, and a
     nullary base constructor. It is the one occupant with a parameter, and
     that is exactly what it pins. [`Modelgen.eraseCtorTy`] is raw de Bruijn
     surgery and every binder of the field it crosses pushes the parameters one
     index further out; a treatment that erased the occurrence at the *field's*
     depth rather than at the depth under its own binders writes
     `Cf._model._impl.skel B A` and the kernel refuses it. Measured: `Cf` red at
     `_model._impl.skel` under that mutation and `Inf2` and `Bif` **both models**,
     because a parameter-free declaration's `skel` has no bound variable for
     the shift to move.

   * `Bif` — a **bare** recursive field and an **infinitary** one in the same
     constructor, and the infinitary one has **two** binders, of different
     types, whose *second* is the child's index. Two binders is what makes an
     order visible and two types is what makes a reversal a type error, and
     with one binder each `Inf2` and `Cf` cannot see it: measured, a mutation
     that hands the consumers the branch's binders in reverse is red at `Bif`'s
     `_model.good` **alone** and every other occupant in this file models under
     it. It is `Utd`'s role in `prim_w.lean` arriving at arm C.

   Four further mutations, for the record, and all four loud at every
   infinitary occupant: erasing the occurrence *with* its binders (the
   whole-domain replacement the bare case does) is rejected at `_model.good`,
   as is the same omission in [`Modelgen.spineSwap`]; appending the branch's
   binders after the induction hypothesis's own arguments rather than before is
   rejected at the recursor model; and taking the constructor's field without
   applying it to the branch is rejected at the constructor model.

   **The erasure guard now has no occupant in this file, and that is not an
   oversight.** What is left of it — a mention βζ discards, a binder only βζ
   reveals, a binder type naming the declaration, an occurrence that is not an
   application of the declaration — is unwritable in a `prelude` source: the
   first three arrive only from a *specialisation* the elaborator performed,
   and the fourth is a nested occurrence, which never reaches `primIso` because
   layer 1 compiles it away first. `nest_fam_arg.lean`'s `OK` and `Key` are the
   live occupants of the same guard, at layer 3, and they are where it is
   exercised.

   * `IBox` and `NoBase` — two indexed families whose erasure is bare and
     **still does not model**, so the skeleton is spliced, the prim pass
     cannot model it, and the whole emission is **withdrawn**. A family whose
     skeleton does not model produces no emission, so that
     nothing unmodelled ever reaches a consumer. Without them that rule would
     be a comment. They withdraw for *different* inner reasons, which is what
     pins that the decline carries the skeleton's own reason rather than only
     the fact of failure: `IBox`'s erasure is `prim_declines`' `BoxF`, whose
     field keeps an `imax` even boxed, and `NoBase`'s erasure is linearly
     recursive with **no base constructor**.

   `NoBase` is worth a second sentence, because arm C is how the shape came to
   light. `NoBase._model._impl.skel` is `S | mk : N → S → S` — an *uninhabited*
   linearly recursive inductive, which Lean accepts and the tuple tower does
   not model: its spine's zero fibre is a chain of no fields and the plan
   gives it no pad. That is a gap in the **Type route** and not in arm C. It is
   recorded rather than fixed. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive N : Type where
  | z : N
  | s : N → N

inductive Vc : N → Type where
  | nil : Vc N.z
  | cons : (n : N) → Vc n → Vc (N.s n)

inductive Two2 : N → Type where
  | l : (n : N) → Two2 n
  | r : (n : N) → Two2 (N.s n) → Two2 n

inductive Bl : N → N → Type where
  | tip : Bl N.z N.z
  | bin : (a b : N) → Bl a b → Bl (N.s a) b
  | wide : (a b : N) → Bl a b → Bl a (N.s b)

inductive Fn : N → Type where
  | fz : (n : N) → Fn (N.s n)
  | fs : (n : N) → Fn (N.s (N.s n))

inductive Vec (α : Type) : N → Type where
  | vnil : Vec α N.z
  | vcons : α → (n : N) → Vec α n → Vec α (N.s n)

inductive Tri3 : N → Type where
  | base : Tri3 N.z
  | mk : (a : N) → (b : N) → (c : N) → Tri3 a → Tri3 (N.s c)

inductive Br : N → Type where
  | leaf : Br N.z
  | node : (m n : N) → Br m → Br n → Br (N.s N.z)

inductive Mx (α : Type) : N → Type where
  | mx0 : Mx α N.z
  | mx2 : (a : N) → Mx α a → α → (b : N) → Mx α b → Mx α (N.s b)

inductive Sm3 : N → Type where
  | tip : Sm3 N.z
  | tri : (n : N) → Sm3 n → Sm3 n → Sm3 n → Sm3 (N.s n)

inductive Inf2 : N → Type where
  | ileaf : Inf2 N.z
  | inode : (n : N) → (N → Inf2 n) → Inf2 (N.s n)

inductive P : Type where
  | one : P
  | two : P

inductive Cf (A : Type u) (B : A → Type u) : N → Type u where
  | c0 : Cf A B N.z
  | c1 : (n : N) → (a : A) → (B a → Cf A B n) → Cf A B (N.s n)

inductive Bif : N → Type where
  | b0 : Bif N.z
  | b2 : (a : N) → Bif a → ((x : P) → (y : N) → Bif y) → Bif (N.s a)

inductive IBox (α : Sort u) (β : Sort v) : N → Sort (max 1 u v) where
  | mk : ((α → β) → β) → IBox α β N.z

inductive NoBase : N → Type where
  | mk : (n : N) → NoBase n → NoBase (N.s n)
