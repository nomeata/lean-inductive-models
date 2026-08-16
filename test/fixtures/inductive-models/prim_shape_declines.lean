/- **Shapes that reach no generation arm**, and the two different things that
   can mean.

   `prim_declines.lean` is the *former* refusal boundaries, kept as positives
   for the routes that replaced them. This file is the complement: four owners
   the simple construction still does not model, each of which **aborted the
   run** until the route dispatcher learned to classify them. An abort is the
   wrong answer for all four — the output contract says an unsupported owner
   passes through unchanged and is reported, and exit `2` says so — and for a
   thirty-minute stream it is the difference between a decline row and a run
   that stops in the middle.

   The four split two-and-two across the distinction the report line carries,
   and pinning *which* verdict each one gets is the point of the file:

   * **out of scope** — the construction looked at the shape and decided
     against it. `Foreign` and `Foreign0` are the two: a field mentioning the
     owner other than as `∀ z⃗, T p⃗ e⃗` is a *nested* occurrence, and nesting
     is layer 1's business. Both write that occurrence as
     `idf (T … → Type) (fun _ => N) child`, which is dead — its reduct is `N`
     — but only after **δ**, and the route analysis reduces β and ζ and
     unfolds no constant on purpose ([`InductiveModels.headNorm`]). What
     survives that normalization is an occurrence under a foreign type former,
     which every arm of every route would have to replace and none can:
     the tuple tower takes a spine predecessor, arm C its index erasure, arm W
     a branch of `B'`, the Church routes the encoding's own `C`.

     `Foreign` is the indexed case, which used to abort inside
     `analysePrim`; `Foreign0` is the non-indexed one, which used to reach arm
     W and abort inside it. They are two owners rather than one because the
     two aborts were in different places, and a fix that moved only the first
     would leave the second reading green.

     Both are kernel-accepted with `numNested = 0`: Lean's own positivity
     check unfolds `idf` and finds no occurrence at all, so neither is routed
     to `Plan.plan` and both arrive here.

   * **incomplete** — the arm that owns the shape ought to reach it and does
     not. `PadOne` and `PadMany` are the two. A nonrecursive one-constructor
     owner at a **maybe-zero** sort is the field-preserving arm's, decided
     before any arm runs, and the Church fallback behind it would record only
     inhabitation and lose the field. That arm retains a field at exactly the
     carrier's sort (`prim_shapes`' `PI`) or a field that is exactly a
     proposition (`PF`), and a field at `Sort u` under a carrier at
     `Sort (max u v)` is neither — one field (`PadOne`) or several
     (`PadMany`), the same missing piece either way. The never-zero tuple
     tower closes precisely this level gap with a pad
     ([`InductiveModels.unitAt`]); this arm has none. Nothing about the shape
     is out of bounds, so the verdict says so, and says which arm to finish.

   `N` is the control: an ordinary owner in the same file that models, so a
   run which declined everything could not pass this row.

   The **fifth** hole the audit named — arm W's `labelFactored` guard refusing
   a shape at a never-zero non-indexed sort — has no occupant here, and not
   for want of trying. It needs a recursive field one of whose *binder types*
   depends on an earlier recursive field, and the kernel rejects an owner
   mention in a binder type as a non-positive occurrence whatever hides it
   (β-redex, `let`, or a definition), while a dependence without a mention
   would need a constant of type `T → Sort` that does not exist while `T` is
   being declared. The dispatcher classifies it anyway; see
   `InductiveModels.primIsoWithInterface`. -/
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

/-- The identity, as an ordinary definition. It is what puts the owner under a
foreign type former: `idf (T → Type) (fun _ => N) child` mentions `T`, reduces
to `N`, and needs δ to get there. -/
def idf (α : Sort u) (a : α) : α := a

--#export Eq N idf Foreign Foreign0 PadOne PadMany

inductive Foreign : N → Type where
  | base : Foreign N.z
  | step (n : N) (child : Foreign n)
      (tag : idf (Foreign n → Type) (fun _ => N) child) : Foreign (N.s n)

inductive Foreign0 : Type where
  | base : Foreign0
  | step (child : Foreign0) (tag : idf (Foreign0 → Type) (fun _ => N) child) : Foreign0

inductive PadOne (α : Sort u) (β : Sort v) : Sort (max u v) where
  | mk : α → PadOne α β

inductive PadMany (α : Sort u) (β : Sort v) : Sort (max u v) where
  | mk : α → α → PadMany α β
