/- **A field at a mimic under a binder, crossed with every other axis.**
   `funext_binder.lean` is the shape on its own — a monomorphic, one-member
   declaration nesting through an unindexed container. Nothing there says the
   binder survives the *declaration's* indices, a mutual block, or a cycle of
   mimics, and the cycle in particular does **not** come for free: `pack` and
   the retraction for a cyclic group go through
   [`InductiveModels.packFamMinor`]/[`InductiveModels.retractFamilyValue`], which are a second
   copy of the one-at-a-time path and were measured refusing `CycB` before they
   were taught the same telescope.

   * `DTel.mk : ((n : N) → Vec N n → List DTel) → DTel` — a **dependent**
     binder telescope, two binders deep and the second's type mentioning the
     first. The pointwise transport is per *telescope*, so a treatment that
     handled a single non-dependent binder passes `funext_binder`'s `H2` and
     fails here.
   * `IdxB.mk : (N → Vec IdxB (N.s N.z)) → IdxB` — the binder and an **indexed
     container** at once, so the index vector has to be read under the binder
     and threaded into `pack`, `unpack` and the retraction there.
   * `MutB`/`MutC` — the binder inside a **mutual** block, where the packed
     position sits in one member and the carrier family has two.
   * `CycB.mk : Tr CycB → CycB` with `Tr.node : (N → List (Tr α)) → Tr α` — the
     binder inside a **cycle** of mimics. `Tr CycB` and `List (Tr CycB)` are
     mutually recursive, so the two are one simultaneous recursion over
     `Tr.rec`/`Tr.rec_1`, and the binder sits inside that recursion's minor. -/
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

inductive Box (α : Type) : Type where
  | mk : α → Box α

inductive Vec (α : Type) : N → Type where
  | vnil : Vec α N.z
  | vcons : α → (n : N) → Vec α n → Vec α (N.s n)

inductive Tr (α : Type) : Type where
  | leaf : α → Tr α
  | node : (N → List (Tr α)) → Tr α

--#export Eq funext N List Box Vec Tr DTel IdxB MutB MutC CycB

inductive DTel : Type where
  | mk : ((n : N) → Vec N n → List DTel) → DTel

inductive IdxB : Type where
  | mk : (N → Vec IdxB (N.s N.z)) → IdxB

mutual
inductive MutB : Type where
  | mk : (N → List MutC) → MutB
inductive MutC : Type where
  | mk : Box MutB → MutC
end

inductive CycB : Type where
  | mk : Tr CycB → CycB
