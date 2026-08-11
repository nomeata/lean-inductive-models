/- **Shapes Lean accepts that no other fixture has a reason to write.** This
   file exists because the gap list is claimed to be empty, and a claim like
   that is only worth what was swept for it. Each of these was found by asking
   "what else does Lean's `inductive` allow here?" rather than by a failure
   arriving, and two of them were refusals when they were first written.

   * `EmpT.mk : Emp EmpT → EmpT`, `Emp α` having **no constructors**. The
     mimic's recursor has no minors and the block has one uninhabited member.
   * `ImpT.mk : Imp ImpT → ImpT`, where `Imp.mk : {x : α} → α → Imp α` has an
     **implicit** binder. Binder info is not the field telescope's business and
     this says so.
   * `LetT.mk : Let LetT → LetT`, where `Let.mk : (n : N) → (let m := n; Vec' α
     m) → Let α` puts a **`let` in a constructor field's type**. Lean accepts
     it; the member the field sits at is then not the head of the expression as
     written, and every "which member is this field at" test in the generator
     reads through `Gen.zetaHead` for that reason. **Measured refusing** before
     it did — first at `unpack_1`, then at `iota_1_0` when the index vector was
     still read off the un-reduced type.
   * `FunP f` — a declaration **parameter that is a function type**, so the
     container is applied to a parameter that is not a type former.
   * `Deep3.mk : List (List (N → List Deep3)) → Deep3` — **depth three**, with
     the binder at the deepest level rather than the outermost, so the mimic
     that carries the funext is discovered third.
   * `EvT`/`EvU` — a **mutual** block with a **parameter** and an **index**
     whose members nest through an **indexed container** and through `List`,
     one of them **under a binder**. Every axis this tool has, at once.
     **Measured refusing** before the cyclic-group path learned the binder
     telescope, and the fixture that says the axes compose rather than merely
     coexist. -/
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

inductive Emp (α : Type) : Type where

inductive Imp (α : Type) : Type where
  | mk : {x : α} → α → Imp α

inductive Vec' (α : Type) : N → Type where
  | nil : Vec' α N.z
  | cons : α → (n : N) → Vec' α n → Vec' α (N.s n)

inductive Let (α : Type) : Type where
  | mk : (n : N) → (let m := n; Vec' α m) → Let α

--#export Eq funext N List Emp Imp Vec' Let EmpT ImpT LetT FunP Deep3 EvT EvU

inductive EmpT : Type where
  | mk : Emp EmpT → EmpT

inductive ImpT : Type where
  | mk : Imp ImpT → ImpT

inductive LetT : Type where
  | mk : Let LetT → LetT

inductive FunP (f : N → N) : Type where
  | mk : List (FunP f) → FunP f

inductive Deep3 : Type where
  | mk : List (List (N → List Deep3)) → Deep3

mutual
inductive EvT (p : N) : N → Type where
  | leaf : EvT p N.z
  | node : (N → Vec' (EvU p N.z) (N.s N.z)) → EvT p (N.s N.z)
inductive EvU (p : N) : N → Type where
  | leaf : EvU p N.z
  | node : List (EvT p (N.s N.z)) → EvU p (N.s N.z)
end
