/- **The nested occurrence is inside a lambda in a container argument**, which
   was §5.1's one gap and is closed. `Lean.Json` and `Lean.PrefixTreeNode` are
   this shape and were the only two of Mathlib's 41 nested declarations
   `modelgen` refused (§6.3).

   `RB α β`'s second parameter is a **family**, so specialising it leaves the
   constructor field `β k` as the redex `(fun _ => B₀) k` in the block. Three
   readers used to answer that expression with the lambda they saw at its head
   — which member, which occurrence, which index vector — and `Plan.spec` never
   entered a lambda that sat in an application's head. Every declaration below
   is one of those two mistakes, and each one is red under a different mutation
   of the repair; the header of `Modelgen.Gen.occIdx?` is the diagnosis.

   `OK` is the discriminating control that was here before the fix and is still
   the first line of it: the **same container** with the recursion in the
   argument the others do *not* use, so a repair that makes the gap pass by
   breaking the shape beside it is caught.

   | witness | the shape | what it is the only one of |
   | --- | --- | --- |
   | `OK.mk : RB OK (fun _ => N) → OK` | a family parameter, the recursion in the **first** argument — `dependent_fields.lean`'s `Ctr KTree (fun _ => N)` at this container | the control. A model before the fix and after it, so the family parameter was never the obstruction |
   | `JT.obj : RB N (fun _ => JT) → JT` | `Lean.Json`'s `obj (kvPairs : RBNode String (fun _ => Json))` with `String` shrunk to `N` | the Mathlib reproduction. `RB.node`'s minor binds `motive₂ a`, **`motive₁ a_1`**, `motive₂ a_2` — a root hypothesis **between** two of the container's, which two positions could not have shown |
   | `PT.node : N → RB N (fun _ => PT) → PT` | `Lean.PrefixTreeNode` with its parameters dropped | the second Mathlib decline, so the first is not about `JT`'s constructor arrangement |
   | `PTP.node : Opt β → RB α (fun _ => PTP α β) → PTP α β` | `Lean.PrefixTreeNode` **as it is declared**, parameters and all | the lambda body mentions the block's own **parameter telescope**, which `mimicFor` has to lower and rebuild |
   | `Deep.obj : RB N (fun _ => L Deep) → Deep` | the occurrence inside the lambda is itself under a **container** | the mimic that only exists if `Plan.spec` enters an application's **head**. A repair confined to the readers leaves `L Deep` unspecialised, and `unpack` then hands the root's constructor an `L Deep` where its field is the mimic |
   | `Idx.obj : RB N (fun k => Vec Idx k) → Idx` | the lambda's binder is **used**, and what it indexes is a container | the lambda that is not constant, and a mimic whose index vector is read off the **reduct** |
   | `Both.obj : RB Both (fun _ => Both) → Both` | the occurrence in the family's **key and value at once** | two *root* hypotheses in one minor (`k : α` and `β k`), so a repair that assumes at most one loses the vector again |
   | `Two.obj : RB2 N (fun _ _ => Two) → Two` | a **two**-argument family, so the redex is `(fun _ _ => B₀) k l` | a repair that peels one argument and stops |
   | `Flat.obj : Ctr N (fun _ => Flat) → Flat` | a container with **no recursive field**, so the redex's hypothesis is the *only* entry in the vector | the arm that is not `unpack`: before the fix this one failed at `Flat._model.iota_1_0`, not at `unpack_0` |
   | `Key.obj : RB (RB N (fun _ => Key)) (fun _ => N) → Key` | the nesting is in the family's **key**, and its value is the constant family | the field `β k` **mentions** the moved field `k` and its reduct does not, which the dependent-field guard has to see through |
   | `Zeta.obj : RB N (fun _ => let X := L Zeta; X) → Zeta` | a `let` **inside** the lambda | β alone is not enough: `headNorm` has to ζ-reduce what β uncovers |
   | `Ix.obj : RB N (fun _ => Ix N.z) → Ix N.z` | an **indexed declaration**, the redex reducing to it at a concrete index | the index vector must come from the reduct: reading it off the redex gives `k` where the type says `N.z`, and the ι rule says so |

   `nest_odd_shapes.lean` is the sweep over what `inductive` *declares*; this
   one is the sweep over how a container is **applied**, which is the axis that
   sweep could not see. Three shapes beside these were tried and Lean refuses
   them too, so they are §5.2 and have no fixture: `Ctr N (fun x => Vec T x)`
   is "nested inductive datatypes parameters cannot contain local variables",
   and so is any lambda whose body indexes the occurrence by the lambda's own
   binder through a second container.
-/
prelude

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

inductive Opt (α : Type) : Type where
  | none : Opt α
  | some : α → Opt α

inductive L (α : Type) : Type where
  | nil : L α
  | cons : α → L α → L α

inductive Vec (α : Type) : N → Type where
  | nil : Vec α N.z
  | cons : {n : N} → α → Vec α n → Vec α (N.s n)

inductive RB (α : Type) (β : α → Type) : Type where
  | leaf : RB α β
  | node : RB α β → (k : α) → β k → RB α β → RB α β

inductive RB2 (α : Type) (β : α → α → Type) : Type where
  | leaf : RB2 α β
  | node : (k : α) → (l : α) → β k l → RB2 α β → RB2 α β

inductive Ctr (α : Type) (P : α → Type) : Type where
  | mk : (x : α) → P x → Ctr α P

--#export Eq N Opt L Vec RB RB2 Ctr OK JT PT PTP Deep Idx Both Two Flat Key Zeta Ix

inductive OK : Type where
  | mk : RB OK (fun _ => N) → OK

inductive JT : Type where
  | null : JT
  | obj : RB N (fun _ => JT) → JT

inductive PT : Type where
  | node : N → RB N (fun _ => PT) → PT

inductive PTP (α : Type) (β : Type) : Type where
  | node : Opt β → RB α (fun _ => PTP α β) → PTP α β

inductive Deep : Type where
  | obj : RB N (fun _ => L Deep) → Deep

inductive Idx : Type where
  | obj : RB N (fun k => Vec Idx k) → Idx

inductive Both : Type where
  | obj : RB Both (fun _ => Both) → Both

inductive Two : Type where
  | obj : RB2 N (fun _ _ => Two) → Two

inductive Flat : Type where
  | obj : Ctr N (fun _ => Flat) → Flat

inductive Key : Type where
  | obj : RB (RB N (fun _ => Key)) (fun _ => N) → Key

inductive Zeta : Type where
  | obj : RB N (fun _ => let X := L Zeta; X) → Zeta

inductive Ix : N → Type where
  | obj : RB N (fun _ => Ix N.z) → Ix N.z
  | s : {n : N} → Ix n → Ix (N.s n)
