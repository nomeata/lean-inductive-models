/- **Dependent ordinary fields on the legacy W route.**

   The intrinsic projection ι contract is literal: `T._model.proj_j` applied to
   the modeled constructor equals constructor field `j` itself, with no
   transport. For a *dependent* field — one whose type names an earlier field —
   the left-hand side's type is the field type with each earlier field replaced
   by its own modeled projection, so the equation is a proposition **only if
   each of those projections selects its field definitionally**. Where it does
   not, the two sides live in different types and there is nothing to state.

   **Arm W selects its stored fields definitionally, and this file is the
   family that says so rather than one specimen.** The tagged W scheme puts a
   constructor's non-recursive fields in a `PSigma'` data tower `D p⃗ t` and its
   recursive positions in the branch tower, and the label `⟨t, d⟩` of a node is
   `_wcore.WT.root` of that node — which reduces on `WT.sup` by βιπ alone
   (`root (sup a f) ≡ a`, and `kids (sup a f) ≡ f` is what does *not* hold).
   So every non-recursive field is reachable from the major by `root`, the
   label's two `PSigma'` projections, one `Nat.rec` cascade on the tag and the
   data tower's own projections, none of which is `WT.Wrec`. Positivity leaves
   no spelling in which a field's type reads a *recursive* field's value
   (`nested_value_dependency.lean` writes out every attempt and the kernel
   refuses each), so the fields a later field can depend on are exactly the
   ones the data tower stores.

   Every owner below hides its result former behind `HiddenType`, so the
   serialized owner type does not end in a literal sort. That is the idiom
   `HiddenIndexed` uses in `indexed_fibre_boundary.lean`, and it is what kept
   these owners off the withdrawn direct one-layer adapter — the one that used
   to supply reflexive selectors of its own — while it existed. Arm W supplies
   them itself, for every owner of this shape now that the adapter is gone.
   Each is infinitary in at least one recursive position, so the tuple tower
   declines them and arm W models them.

   The five owners are the five spellings of the same question:

   * `WDep` — **the untagged instantiation.** The child's binder type `Vec a`
     reads the label's own data, so `InductiveModels.tagFactored` is false and
     the arm runs the core at `K := A` with `WT.decEqAll`. Field 1's codomain
     is `Vec (WDep._model.proj_0 self)`.
   * `WTag` — **the tagged instantiation, same dependency.** The child binder
     is `N`, which names no field, so the arm runs the core at `K := Nat` with
     `instDecidableEqNat`. Untagged-ness is therefore *not* what the dependent
     field needs repaired: both columns need the same selector.
   * `WMid` — **the depended-upon field and the dependent field are separated
     by a recursive one.** Fields 0 and 2 are stored in the data tower at
     positions 0 and 1 while the driver asks for them at telescope positions 0
     and 2, and field 1 is a child. This is the owner that distinguishes "the
     tower's index" from "the constructor's index"; a selector that confused
     them would return field 2's value for field 0 here and nowhere else.
   * `WChain` — **a two-step dependency.** Field 2's type `Tag a v` names both
     field 0 and field 1, and field 1's type names field 0, so field 2's
     codomain is `Tag (proj_0 self) (proj_1 self)` and the selector for field 2
     is written at a motive that already mentions the selectors for 0 and 1.
     One layer of dependency does not exercise that nesting.
   * `WPlain` — **the control**, and it must keep modelling: the same reducible
     result former, the same legacy W arm, the same three projected fields —
     and no field type that names an earlier one.

   Before arm W supplied the selectors this file is why: generation emitted
   `WDep._model.proj_1.iota` at `Eq (Vec (WDep._model.proj_0 (WDep.mk._model …)))`
   with the constructor's own `Vec a` binder on the right, and Lean's kernel
   rejected the declaration with an application type mismatch. Nothing in the
   suite read that verdict; then the owners declined with
   `InductiveModels.Decline.projectionCodomain`; now they model.

   **The recursive fields keep their `WT.Wrec` selector and that is not a
   gap.** `kids (sup a f)` is `WT.kids_sup`, a theorem carrying a cast, so a
   child position has no definitional selector — and by the positivity fact
   above nothing can ever depend on one, so no ι rule needs it to have one.
   `WMid.mk`'s fields 1 and 3 and `WChain.mk`'s field 3 are those positions,
   and their rules are still `WT.Wrec_iota` at this declaration's own `F`.
-/
prelude

universe u

--#export Eq HiddenType WDep WTag WMid WChain WPlain

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

/-- Reducible result former, hidden in the serialized owner type. -/
def HiddenType := Type

/-- Dependent ordinary field, untagged arm: `Vec a` names the data field `a`
and the child's binder reads it too. -/
inductive WDep : HiddenType where
  | mk : (a : N) → Vec a → (Vec a → WDep) → WDep

/-- The same dependent field on the *tagged* arm: the child's binder is `N`,
so the branch type is a function of the tag alone. -/
inductive WTag : HiddenType where
  | mk : (a : N) → Vec a → (N → WTag) → WTag

/-- The dependent field sits after a child, so the data tower's position and
the constructor's field index disagree. -/
inductive WMid : HiddenType where
  | mk : (a : N) → (Vec N.z → WMid) → Vec a → (N → WMid) → WMid

/-- A two-step dependency: field 2 names fields 0 and 1, and field 1 names
field 0. -/
inductive WChain : HiddenType where
  | mk : (a : N) → (v : Vec a) → Tag a v → (N → WChain) → WChain

/-- The control: same route, same three projected fields, no dependent one. -/
inductive WPlain : HiddenType where
  | mk : (a : N) → Vec N.z → (Vec N.z → WPlain) → WPlain
