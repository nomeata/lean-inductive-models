/- **A constructor field at a mimic under a binder, with a `funext` to prove it
   with.** Lean accepts the shape and the block types the field `∀ x⃗, Bₘ ι⃗`, so
   the declaration-local constructor model builds `fun x⃗ => pack (f x⃗)` and
   the round trips, the
   recursor's minor and the ι rules all have to transport along
   `(fun x⃗ => pack (unpack (f x⃗))) = f` — which is function extensionality.
   `infinitary.lean` is the same three declarations *without* one, and
   `modelgen` derives one there and splices it in; this
   file is them **with** one, and is the control that says an input's own
   `funext` beats a derived one — nothing is spliced here and the five counts
   below are unchanged from before the splice existed.

   `funext` here is Lean's own development, written out: `init_quot`, the
   `Quot.sound` axiom that `Init/Core.lean` declares, and `congrArg` on the
   extensional application of a `Quot`. It is a theorem and not an axiom,
   exactly as in Lean — which is also what `modelgen` emits when it has to
   derive one, and this file is where the two can be read side by side.

   The three declarations are the three *places* a binder can sit relative to
   the nesting, and they reach three different proofs:

   * `HTree.node : (N → List HTree) → HTree` — the **root**'s field, so the
     funext lands in `recValue`'s minor and in every ι rule of `HTree.rec`.
     `pack` and `unpack` need only a lambda.
   * `RTree.mk : Rose RTree → RTree`, `Rose.node : (N → Rose α) → Rose α` — the
     container's **own recursive** field. Here `pack` and `unpack` need nothing
     at all, because the induction hypothesis already *is* the function they
     want; it is the two round trips that transport, `unpack₀ (pack₀ (Rose.node
     f))` reducing to `Rose.node (fun n => unpack₀ (pack₀ (f n)))`.
   * `OTree.mk : Outer OTree → OTree`, `Outer.mk : (N → Inner α) → Outer α` — a
     container's field at **another** mimic. `Outer` is not recursive, so there
     is no hypothesis to lean on and the round trips carry `funext (fun n =>
     unpackPack₁ (f n))` outright.

   Two more, because one binder at one position cannot distinguish anything:

   * `H2.node : (N → N → List H2) → H2` — a **two-binder** telescope, so an
     implementation that closed only the innermost `funext` is caught.
   * `H3.node : List H3 → (N → List H3) → H3` — two moving positions, **one
     under a binder and one not**, in one constructor. The congruence fold
     moves them one at a time and the two steps are built differently (a
     `congrPack_0` declaration for the bare one, an inline congruence of a
     whole function for the other), so a fold that mixed them up passes
     `HTree` and fails here. -/
prelude

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

init_quot

axiom Quot.sound : {α : Sort u} → {r : α → α → Prop} → {a b : α} → r a b →
  Eq (Quot.mk r a) (Quot.mk r b)

theorem congrArg {α : Sort u} {β : Sort v} {a b : α} (f : α → β) (h : Eq a b) :
    Eq (f a) (f b) :=
  Eq.rec (motive := fun x _ => Eq (f a) (f x)) (Eq.refl (f a)) h

theorem funext {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}
    (h : (x : α) → Eq (f x) (g x)) : Eq f g :=
  congrArg
    (fun (q : Quot (fun (a b : (x : α) → β x) => (x : α) → Eq (a x) (b x))) (x : α) =>
      Quot.lift (fun (a : (x : α) → β x) => a x)
        (fun a b (hab : (x : α) → Eq (a x) (b x)) => hab x) q)
    (Quot.sound h)

inductive N : Type where
  | z : N
  | s : N → N

inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

inductive Rose (α : Type) : Type where
  | leaf : α → Rose α
  | node : (N → Rose α) → Rose α

inductive Inner (α : Type) : Type where
  | mk : α → Inner α

inductive Outer (α : Type) : Type where
  | mk : (N → Inner α) → Outer α

--#export Eq funext N List Rose Inner Outer HTree RTree OTree H2 H3

inductive HTree : Type where
  | leaf : HTree
  | node : (N → List HTree) → HTree

inductive RTree : Type where
  | mk : Rose RTree → RTree

inductive OTree : Type where
  | mk : Outer OTree → OTree

inductive H2 : Type where
  | leaf : H2
  | node : (N → N → List H2) → H2

inductive H3 : Type where
  | leaf : H3
  | node : List H3 → (N → List H3) → H3
