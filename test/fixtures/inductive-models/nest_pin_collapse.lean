/- **A nested container whose own recursion collapses at the occurrence.**

   `J α β | node (x : Pair α (J α β)) (y : Pair β (J α β))` is itself a nested
   inductive, and its recursion has **three** members: `J α β`, `Pair α (J α
   β)` and `Pair β (J α β)`, over `J.rec`, `J.rec_1` and `J.rec_2`. A block
   nesting through `J C C` instantiates both parameters alike, the last two
   members become one expression, and the kernel's auxiliary construction for
   the block mints **one** `Pair` mimic for them (con-leche's
   `nested_pin_collide` is this shape; it calls the members *pins*). So the
   group of mimics is two and the family it is a recursion over is three.

   `pack` for the `Pair` mimic can only be one of the two components, `J.rec_1`;
   `J.node`'s ι rule leaves its `y` at the other, `J.rec_2`. The two are equal
   but not definitionally, so the model proves them equal once per collapsed
   mimic (`packCoh`) and transports along it where the other one turns up:
   the retraction, the section and the ι rules. These are the shapes that
   reach each part of that:

   * `C1` — the shape itself, a class of two.
   * `C3` — a class of **three**, so the coherence is a conjunction of two
     equations and the one a position needs has to be selected.
   * `CK` — collapsed members whose *own* fields sit at different collapsed
     members: `K`'s `Q α (K α β)` has its `Pair` at `Pair α (K α β)` and `Q β
     (K α β)` at `Pair β (K α β)`, so proving `Q`'s two components equal needs
     `Pair`'s two equal first — the coherence is one simultaneous induction,
     not one per class.
   * `CB` — the collapsed position **under a binder**, `(N → Pair β (JB α
     β))`, so the coherence reaches the ι rules through `funext`.
   * `CI` — the collapse at an **indexed** container, `IPair α β : N → Type`.
   * `CP` — the root nesting **into** the collapsed mimic: `Pair CP (J CP CP)`
     is the root's own occurrence as well as both of `J`'s `Pair` members. -/
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

inductive Pair (α β : Type) : Type where
  | mk : α → β → Pair α β

inductive Q (α β : Type) : Type where
  | mk : Pair α β → Q α β

inductive IPair (α β : Type) : N → Type where
  | mk : α → β → IPair α β N.z

inductive J (α β : Type) : Type where
  | leaf : J α β
  | node : Pair α (J α β) → Pair β (J α β) → J α β

inductive J3 (α β γ : Type) : Type where
  | leaf : J3 α β γ
  | node : Pair α (J3 α β γ) → Pair β (J3 α β γ) → Pair γ (J3 α β γ) → J3 α β γ

inductive K (α β : Type) : Type where
  | leaf : K α β
  | node : Q α (K α β) → Q β (K α β) → K α β

inductive JB (α β : Type) : Type where
  | leaf : JB α β
  | node : Pair α (JB α β) → (N → Pair β (JB α β)) → JB α β

inductive JI (α β : Type) : Type where
  | leaf : JI α β
  | node : IPair α (JI α β) N.z → IPair β (JI α β) N.z → JI α β

--#export Eq funext N Pair Q IPair J J3 K JB JI C1 C3 CK CB CI CP

inductive C1 : Type where
  | mk : J C1 C1 → C1

inductive C3 : Type where
  | mk : J3 C3 C3 C3 → C3

inductive CK : Type where
  | mk : K CK CK → CK

inductive CB : Type where
  | mk : JB CB CB → CB

inductive CI : Type where
  | mk : JI CI CI → CI

inductive CP : Type where
  | base : CP
  | mk : Pair CP (J CP CP) → CP
