/- **The dependent-field family on the empty-carrier route, and every refusal
   it currently produces.**

   The intrinsic projection ι contract is literal: `T._model.proj_j` at the
   modeled constructor *is* constructor field `j`, with no transport. For a
   field whose type names an earlier field the left-hand side's type is that
   field type with each earlier field replaced by its own modeled projection,
   so the equation is a proposition only if each of those projections
   **selects** — reduces to — its field on the modeled constructor.

   Arm E's property is that every constructor has a **bare** recursive field,
   so no constructor can ever be applied and the carrier is `emptyAt w`, the
   derived exact-sort lift of Church `⊥`. `mk` returns its own recursive field,
   which already inhabits that carrier, and a projection out of it is an
   *elimination* of the major: total at every codomain, and reducing to no
   field because the carrier stores none. So `proj_0 (mk f⃗)` δβ-reduces to a
   bare field — a variable — and stops, and a later field's codomain is not the
   field's own type.

   `w_dependent_field.lean` is the same question one construction earlier, and
   arm W now answers it out of its data tower. This file pins the whole shape
   family on arm E **before** anything answers it here, so that what the answer
   has to survive is on record rather than reconstructed afterwards. Every
   owner but `EMulti` declines today.

   * `EDep` — the minimum: field 1 names field 0.
   * `EChain` — a **two-step** dependency, `Tag a v` naming fields 0 and 1
     while field 1 names field 0. A single layer does not exercise the nesting.
   * `EMid` — **several bare recursive fields**, with the dependent field
     *between* two of them, so the constructor's field index and any storage
     position would disagree.
   * `ENon` — a **non-bare** recursive field (`N → ENon`) beside a bare one.
     No field type can name either, by the positivity fact
     `nested_value_dependency.lean` writes out.
   * `EBare` — the **maybe-zero** route at the same dependency. Arm E serves
     `Sort u` on the same terms, so whatever answers this must too.
   * `EMulti` — **two constructors**, each with a bare recursive field. It
     models, and must keep modelling: intrinsic projections are asked of a
     one-constructor owner and of nothing else, so nothing is asked back here.
   * `EOpaque` — a field at an **opaque `imax` level**, `Sort (imax u v)`,
     under a carrier at `Type (max 1 u v)`. This is the level algebra's own
     gap — a `max` does not absorb an `imax`, and no recursive box can inspect
     an opaque atomic type far enough to normalize its level — so it is the
     one owner here whose refusal is not about the empty carrier at all.

   Every owner hides its result former behind a reducible definition — the same
   idiom `HiddenIndexed` uses in `indexed_fibre_boundary.lean` — so
   `InductiveModels.phase1DirectTypeOneLayerEligible` refuses it and the legacy
   arm is what builds the model.
-/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

--#export Eq HiddenType HiddenSort HiddenIm HiddenBig EDep EChain EMid ENon EBare EMulti EOpaque

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

inductive Vec : N → Type where
  | vnil : Vec N.z
  | vcons : (n : N) → Vec n → Vec (N.s n)

/-- A family indexed by a `Vec`, so that one constructor field can name two
earlier ones at once. -/
inductive Tag : (n : N) → Vec n → Type where
  | tag : (n : N) → (v : Vec n) → Tag n v

/-- A `Sort u`-valued family indexed by a `Sort u` element, so the maybe-zero
owner below has a dependent field at all. -/
inductive Fib (a : Sort u) : a → Sort u where
  | mk : (x : a) → Fib a x

/-- Reducible result formers, hidden in the serialized owner types. -/
def HiddenType := Type
def HiddenSort := Sort u
def HiddenIm := Sort (imax u v)
def HiddenBig := Type (max 1 u v)

/-- Every constructor has a bare recursive field, so the carrier is empty; and
field 1's type names field 0. -/
inductive EDep : HiddenType where
  | mk : (a : N) → Vec a → EDep → EDep

/-- A two-step dependency: field 2 names fields 0 and 1, and field 1 names
field 0. -/
inductive EChain : HiddenType where
  | mk : (a : N) → (v : Vec a) → Tag a v → EChain → EChain

/-- Several bare recursive fields, with the dependent field between two of
them. -/
inductive EMid : HiddenType where
  | mk : (a : N) → EMid → Vec a → EMid → EMid

/-- A non-bare recursive field beside a bare one; neither is stored and no
field type can name either. -/
inductive ENon : HiddenType where
  | mk : (a : N) → (N → ENon) → Vec a → ENon → ENon

/-- The same dependency at a maybe-zero sort. -/
inductive EBare (a : HiddenSort.{u}) : HiddenSort.{u} where
  | mk : (x : a) → Fib a x → EBare a → EBare a

/-- Two constructors, each with a bare recursive field: nothing is asked back
and nothing is stored. -/
inductive EMulti : HiddenType where
  | mk : (a : N) → Vec a → EMulti → EMulti
  | wrap : EMulti → EMulti → EMulti

/-- The residual decline: field 0 is opaque at `Sort (imax u v)`, so no tower
over it reaches the carrier's sort, and field 2 names fields 0 and 1. -/
inductive EOpaque (α : HiddenIm.{u, v}) : HiddenBig.{u, v} where
  | mk : (x : α) → (f : α → N) → Vec (f x) → EOpaque α → EOpaque α
