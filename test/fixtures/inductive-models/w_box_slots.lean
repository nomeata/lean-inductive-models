/- Tree-arm owners whose boxed components are **slots** — boxed, and named by
   nothing after them — beside boxed components something later names.

   A slot's round trip is the box's lemma, not a conversion
   (`docs/maintainers/DagSafety.md`), so each of these exercises one place the
   tree arm's recursor, eta lemma or ι rules go through `boxFix`, the box's
   `rt` or its `cast`:

   * `WSlotDep` stores a boxed slot `g` beside a boxed field `h` that the next
     field's type names, and a recursive field whose binder names the stored
     `a` — the untagged instantiation, where a child's type names the label;
   * `WSlotBind` has a recursive field with a boxed slot binder *before* an
     unboxed one, and a constructor with a data slot and a binder slot at once;
   * `WSlotOne` has one constructor, so its model owes a selector for each
     stored field, boxed or not. -/
prelude

set_option bootstrap.inductiveCheckResultingUniverse false

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive WSlotDep (α : Sort u) (β : Sort v) (P : α → Sort v)
    (Q : ((α → β) → β) → Sort v) : Type (max u v) where
  | leaf : WSlotDep α β P Q
  | node (a : α) (g : (α → β) → β) (h : (α → β) → β) (q : Q h)
      (k : P a → WSlotDep α β P Q) (l : WSlotDep α β P Q) : WSlotDep α β P Q

inductive WSlotBind (α : Sort u) (β : Sort v) : Type (max u v) where
  | leaf : ((α → β) → β) → WSlotBind α β
  | lim : (((α → β) → β) → α → WSlotBind α β) → WSlotBind α β
  | both : ((α → β) → β) → (((α → β) → β) → WSlotBind α β) → WSlotBind α β →
      WSlotBind α β

inductive WSlotOne (α : Sort u) (β : Sort v) : Type (max u v) where
  | mk : ((α → β) → β) → α → (((α → β) → β) → WSlotOne α β) → WSlotOne α β

--#export Eq WSlotDep WSlotBind WSlotOne
