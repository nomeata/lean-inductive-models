/- **Dependent ordinary fields on the empty-carrier route**, and the one
   occupant left that keeps `InductiveModels.Decline.projectionCodomain` a live
   verdict rather than dead code.

   The intrinsic projection ι contract is literal: `T._model.proj_j` at the
   modeled constructor *is* constructor field `j`, with no transport. For a
   field whose type names an earlier field the left-hand side's type is that
   field type with each earlier field replaced by its own modeled projection,
   so the equation is a proposition only if each of those projections
   **selects** — reduces to — its field on the modeled constructor.

   Arm E's property is that every constructor has a **bare** recursive field,
   so no constructor can ever be applied and the carrier is empty. That used to
   be read as "stores nothing, so cannot select", and it is not: what makes the
   carrier empty is a single empty *component*, and a right-nested `PSigma'`
   tower ending at `InductiveModels.emptyAt` `w` is empty for that reason while
   holding every non-recursive field in front of it. The tail is a constant —
   it does not mention the carrier — so the carrier is still a definition,
   which is exactly what self-reference blocked when the recursive field itself
   was the candidate to store. `mk` is then `⟨f⃗, drop t⟩`, where `t` is its own
   bare recursive field and `drop` is the `snd` chain: it manufactures nothing
   it was not handed. The stored fields' projections are the tower's own, so
   they select by π and their ι rules are `Eq.refl`; the recursor and the
   recursive fields' projections still eliminate, through the same `drop`, at
   every result universe.

   `w_dependent_field.lean` is the same closure one construction earlier: arm W
   selects its stored fields through `_wcore.WT.root` and the data tower.

   Seven owners, one per thing the storage has to survive.

   * `EDep` — the original occupant, and the minimum: field 1 names field 0.
   * `EChain` — a **two-step** dependency, `Tag a v` naming fields 0 and 1
     while field 1 names field 0. A single layer does not exercise the nesting.
   * `EMid` — **several bare recursive fields**, with the dependent field
     *between* two of them, so the constructor's field index and the tower's
     component position disagree.
   * `ENon` — a **non-bare** recursive field (`N → ENon`) beside a bare one.
     Both are excluded from the tower — a component whose type mentions the
     carrier cannot be stored in a definition — and by positivity no field type
     can name either, so nothing is lost.
   * `EBare` — the **maybe-zero** route at the same dependency. Arm E serves
     `Sort u` on the same terms, and so does the tower: every component is a
     field of an inductive at `Sort u`, hence at a level the kernel's own
     acceptance of the input says `Sort u` absorbs.
   * `EMulti` — **two constructors**, each with a bare recursive field. Nothing
     is stored, because intrinsic projections are asked of a one-constructor
     owner and of nothing else, so there is no reader for a stored field and no
     single telescope to store; the carrier is the bare `emptyAt` and the owner
     models exactly as it did.
   * `EOpaque` — **the residual decline**, and the only one. Its first field is
     an opaque parameter at `Sort (imax u v)`, and no tower over it lands at
     the carrier's `Type (max 1 u v)`: level conversion is normal-form equality
     and a `max` does not absorb an `imax`, which is what the recursive box
     exists to fix — and no box can inspect an opaque atomic type far enough to
     remove it. So this owner stores nothing, its projections are eliminations
     again, and field 2's codomain `Vec (proj_1 … (proj_0 …))` is not the
     field's own `Vec (f x)`. It declines.

     **This is a limit of Lean's conversion, not of the storage idea.**
     `imax u v ≤ max 1 u v` is true, and the kernel established it in admitting
     this declaration: its `is_geq` splits the `imax` on the right and proves
     the stronger `max`-shaped bound. That does not help, because the tower has
     to *be* at `Sort (max 1 u v)` and the kernel decides that by normal-form
     equality, in which a true inequality is not a conversion
     (`InductiveModels.wTowerLevel` says which test is asked and why it is the
     stock one). It is the same wall the tuple route and arm W hard-fail on;
     arm E does not hard-fail only because it has a total alternative the other
     two do not: emptiness alone is already a model.

     The verdict is `InductiveModels.Decline.projectionCodomain` and not a
     shape verdict because arm E models this owner completely — carrier,
     constructors, recursor and ι rules all exist and check. Only the intrinsic
     projection *rules* have no well-formed statement.

     **The class needs a binder whose sort literally spells `imax` after
     `whnf`.** Ordinary Lean elaboration does not produce one; it takes a source
     that writes `Sort (imax u v)` by hand, as `HiddenIm` does here. That is a
     fact about the class and not a defence of the decline: generality is the
     bar and rarity justifies nothing.

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
