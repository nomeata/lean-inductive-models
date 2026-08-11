/- **The index axis of the one-constructor `Prop`**
   (`src/Modelgen/Simple.lean`), presented as an explicit grid.

   # What the axis is

   The kernel grants a `Sort v` motive to a one-constructor `Prop` exactly when
   every constructor field is either a **proof** or a piece of **data that is
   literally one of the conclusion's index arguments** — by identity, not by
   occurrence, as the kernel checks exercised below demonstrate. That rule is
   not a technicality: a model of a
   `Prop` can extract its proof fields by small elimination and has *no way
   whatever* to extract data, so **the index vector is the only place data can
   come back from**, and the kernel's rule is what guarantees it is there.

   So each index position is one of two things, and the whole axis is which:

   * a **pivot** — literally one of the constructor's data fields. The model
     substitutes the recursor's own index argument for it.
   * anything else — an arbitrary term over the parameters, the data fields and
     the *proof* fields. Nothing can be recovered from such a position, so arm
     F discharges it by a **Henry-Ford equation at the non-pivot subsequence**
     and arm G, where the position is at a `Prop`, by nothing at all: see
     below, it is where the two rows end in different places.

   The two arms meet at mixed pivot/non-pivot vectors: arm F supplies equations
   for the non-pivots, while arm G can omit proof-valued non-pivots. The grid
   makes those intermediate cases explicit.

   |            | ground | pivot | expr over data | expr over proof |
   |------------|--------|-------|----------------|-----------------|
   | non-rec, F | `Fg`   | `Fall3`, `Fdup`, `Fdep` | `Fdup`, `Fdep` | `Fxh` |
   | rec, G     | `BadC` (`prim_graph`), `Rgd` | `Rv`, `Rvx` | — | `Rxh`, `Rvx`, `Rgd` |

   **Both rows model but for the ground column of arm G's**, and the reason
   the two rows end in different places is the third splitting of the axis and
   the last: a non-pivot index position is either at a **data** type or at a
   `Prop`. Arm F must equate either way — it packs a `PSigma` and builds an
   `Eq.rec`, and at a proof position that equation is inhabited by `rfl` and
   costs nothing but is still written. **Arm G need not equate at a proof
   position at all.** Its `GraphInv ι⃗ t val` concludes `val = step f⃗ g⃗` at
   the constructor's own index vector `ι⃗_ctor`, and where `ι⃗_ctor[j]` and
   `ι⃗[j]` are both proofs of one proposition the kernel identifies them by
   proof irrelevance: the statement is already the one wanted, and there is
   nothing to transport. It propagates through the telescope, too — a later
   index type mentioning `j` is defeq at the two — so a whole *suffix* of
   proof positions is free.

   The recursive proof-index class is represented by `Acc.below`: its index 1
   is `Acc r a`, and every `.below` Lean generates beside a recursive `Prop`
   has that shape. Thus `Inf.below`, `Rv.below`, `Rxh.below`, `Rvx.below`, and
   `prim_graph`'s `G*.below` column exercise the same boundary. `Rxh` and `Rvx`
   isolate the two mixed cases deliberately.

   What is left is a non-pivot at a **data** position, where the transport
   really needs a transport that is not built: `BadC`
   in `prim_graph`, and `Rgd` here.

   # Why every cell needs a leading non-pivot

   Lean's front end **promotes** a leading index that is a bare constructor
   field into a *parameter*, at which point the shape is not indexed at all:
   `inductive A : N → Prop | mk (x : N) : A x` arrives as `np=1, ni=0`. A pivot
   is therefore only reachable behind a position that cannot be promoted — a
   constant, or a term. Every cell below is written that way; `MixI` in
   `prim_declines.lean` independently pins the same promotion behavior.

   # The occupants and the mutations, red at one apiece

   * `Fg` — the **control**: one ground index, no pivot at all. Arm F exactly
     as it was before the split, and green under every mutation below, which
     is what says the new cells and not the old path are what they measure.
   * `Fdup` — **one** data field at **two** index positions. Only *one* of them
     can be the pivot; the other is an ordinary non-pivot and the equation
     carries it. (Which one is free: taking the first rather than the last is
     green, and that is measured, not assumed.)
   * `Fdep` — a non-pivot index whose **type mentions a pivot** (`Fam n` at the
     pivot `n`), with a second non-pivot before it. The packed subsequence is
     built at an opened telescope and instantiated at the caller's indices, and
     this is the cell where that instantiation is not the identity and where
     the non-pivot positions are not a prefix.
   * `Fall3` — **every** index a pivot, at three, mapped on by a 3-cycle. There
     is then nothing left to equate: the carrier is a bare Church conjunction,
     no `PSigma` is packed and no `Eq.rec` is built. Three and not two, because
     with two pivots a wrong field↦index map is a transposition.
   * `Fxh` — a non-pivot index that is an expression over a **proof** field
     (`k h`), and no data fields at all: `Inf.below`'s shape without the
     recursion. **Green under every mutation in the sweep, and that is the
     finding rather than a gap** — see below.
   * `Fmid` — a pivot whose type moves with a preceding non-pivot; arm F
     transports a function over that pivot along the packed equation.
   * `Rv` — arm G's control, `Acc`'s own shape, every index a pivot; `Rxh` and
     `Rvx` its two mixed cells, a proof non-pivot beside no pivot and beside
     one.
   * `Rgd` — arm G's **refusal**, and a sharper one than `BadC`: a **proof**
     non-pivot at index 0 standing in front of a **data** non-pivot at index
     1. It declines naming index **1**, which is what says the arm asks its
     question of every non-pivot and not of the first one it meets. `BadC`
     alone cannot say that — its first non-pivot is already the data one.

   | mutation | red |
   |---|---|
   | **A** the data fields' pivot assignments rotated among themselves | `Fall3` |
   | **B** *every* occurrence of a data field marked a pivot, not just the chosen one | `Fdup` |
   | **F** the packed type not instantiated at the caller's index vector | `Fdep` |
   | **E** the unpacked components written back at the identity positions | `Fdep` |
   | **N** the non-pivot positions taken as a prefix rather than as the complement | `Fdep` |
   | **M** the dependent pivot cast to the constructor endpoint and back instead of transported as a function | `Fmid` |
   | **H** the rebuilt carrier handed every field rather than the bound ones | `Fdep`, `Fdup` |
   | **C** the whole index vector packed rather than the non-pivot subsequence | every cell with a pivot; `Fg` and `Fxh` green |
   | **D** the non-pivot subsequence reversed | nothing here; `prim_shapes`'s `Hq` and the W core's `HEq`, whose packs are dependent |
   | **P** arm G's guard dropped, every non-pivot taken as free | `BadC`, `BadC.below` — they decline at `GraphInv`'s own test instead |
   | **Q** arm G's guard asked of the *first* non-pivot rather than of every one | `Rgd`, `Rgd.below`; `BadC` green |
   | **R** either half of arm G's change reverted — the guard back to every non-pivot, or `GraphInv`'s index test back to syntactic | `Rxh`, `Rvx` and every `.below` here and in `prim_graph`; every arm-F cell green |

   **`GraphInv`'s index test is a backstop and is measured as one.** Dropping
   it alone (mutation **T**) is green everywhere, because behind the guard it
   cannot fire: at a pivot the two index terms are the same term and at a
   proof position they are defeq. Under **P** it is what catches `BadC`, and
   under **Q** it is what catches `Rgd` — and with **both** it and the guard
   gone, `BadC` reaches the kernel and is rejected at
   `BadC._model.graph_inv_ty` with an application type mismatch. That is the
   measurement that says the test is worth its lines: it is the difference
   between a named decline and a kernel diagnostic when the guard is widened.

   **C and D cascade.** A decline moves a splice, so both take out the whole W
   core fragment in `prim_declines`, `prim_carve` and `prim_w`; the columns
   above are read off `prim_idx`, `prim_shapes` and `prim_graph`, where nothing
   is spliced downstream. The isolated fixture rows avoid that cascade.

   # Four cells were built and dropped, and one finding is why

   `Fxd` (a non-pivot expression over a data field beside its pivot), `Fall`
   (two pivots rather than three), and `Fperm` (expr, expr, pivot, pivot, expr,
   pivot, with three data fields on a 3-cycle) are each red only under mutations
   that `Fdup`, `Fdep`, or `Fall3` are also red under. No mutation in the sweep
   separates them, so by this file's rule they measured nothing the survivors
   do not, and they are gone.

   `Fp` — an index that is **literally a proof field** — was dropped for a
   sharper reason, and it is worth keeping the sentence. The mutation built for
   it was the pivot test written as "is a *variable*" rather than "is *data*",
   which marks such a position a pivot and drops it from the equation. It is
   **green**, at every occupant, and so is every other mutation at `Fxh`. The
   reason is one fact: a pivot and an extraction at a proof position are two
   proofs of one proposition, so the kernel cannot tell them apart, and no
   threading bug on the proof half of this axis can produce a term that fails
   to typecheck. **The proof column of the grid is free.** `Fxh` stays as the
   witness that it is inhabited and works; `Fp` would have been a second
   witness of the same nothing.

   # Arm F's dependent pivot transport

   `Fmid : (α : Type) → α → α → Prop` with `mk (x : N) : Fmid N x N.z` is a
   pivot whose *own type* is the ground index before it. The model reads a data
   field off the recursor's index argument, and there that argument's type is
   index 0 — an arbitrary `Type`, which only the packed equation says is `N`.
   The recursor therefore transports a **function over the pivot**: at the
   constructor endpoint it accepts `x : N` and applies the minor; at the caller
   endpoint it accepts `x : α` and is applied to the caller's field literally.
   Casting the field to `N` and back would be only propositionally equal to the
   caller's term and would leave the recursor motive at the wrong syntactic
   index. The function transport makes both endpoints exact and keeps ι `rfl`.

   # Arm G's refusal, and it is one column and not a row

   `Rgd` and `prim_graph`'s `BadC` decline at the generalisation arm F has and
   arm G does not: `GraphInv ι⃗ t val` concludes `val = step f⃗ g⃗`, whose
   right-hand side lands at the constructor's index expressions, and with a
   **data** non-pivot among them the two sides sit at genuinely different
   indices, so the equation needs a transport along the very packed equation
   arm F carries. Proof irrelevance is why it is not owed for the proof column.
   It is not built, and these
   two are what go green when it is.

   `Inf` and `N` beside them are the controls that say the arms are not
   swallowing the file: `Inf` is arm G's degenerate positive and `N` an
   ordinary `Type`-route model. -/
prelude

universe u

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive N : Type where
  | z : N
  | s : N → N

inductive Fam : N → Type where
  | c (n : N) : Fam n

inductive Inf : Prop where
  | mk : Inf → Inf

-- ── arm F: the non-recursive row ──

inductive Fg : N → Prop where
  | mk : Fg N.z

inductive Fdup (o : N → N) : N → N → N → Prop where
  | mk (a : N) : Fdup o (o a) a a

inductive Fdep (o : N → N) : N → (n : N) → Fam n → Prop where
  | mk (k : N) : Fdep o (o k) k (Fam.c k)

inductive Fall3 : N → N → N → Prop where
  | mk (a b c : N) : Fall3 c a b

inductive Fxh (q : Prop) (k : q → N) : N → Prop where
  | mk (h : q) : Fxh q k (k h)

inductive Fmid : (α : Type) → α → α → Prop where
  | mk (x : N) : Fmid N x N.z

-- ── arm G: the recursive row ──

inductive Rv (r : N → N → Prop) : N → Prop where
  | mk (x : N) (h : (y : N) → r y x → Rv r y) : Rv r x

inductive Rxh (mo : Inf → Prop) : Inf → Prop where
  | mk (a : Inf) (b : Rxh mo a) (m : mo a) : Rxh mo (Inf.mk a)

inductive Rvx (r : N → N → Prop) (mo : (a : N) → Rv r a → Prop) :
    (a : N) → Rv r a → Prop where
  | intro (x : N) (h : (y : N) → r y x → Rv r y)
          (b : (y : N) → (a : r y x) → Rvx r mo y (h y a))
          (m : (y : N) → (a : r y x) → mo y (h y a)) : Rvx r mo x (Rv.mk x h)

inductive Rgd : Inf → N → Prop where
  | mk (a : Inf) (h : Rgd a N.z) : Rgd (Inf.mk a) N.z
