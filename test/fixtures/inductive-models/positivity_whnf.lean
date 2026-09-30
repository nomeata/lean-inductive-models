/- **A recursive occurrence one definition away, read as the kernel reads it.**

   Lean's positivity check weak-head-normalises a field type before it looks
   at it, and again under every `Π` it peels: a binder type must not mention
   the owner, and what is left at the bottom must be an application of it.
   So `node (f : Fn R)` with `def Fn α := Nat → α` is an ordinary, safe,
   kernel-accepted recursive field whose occurrence is `∀ z : Nat, R` — the
   exported recursor binds an induction hypothesis `(z : Nat) → motive (f z)`
   for it — even though nothing in the field *as written* is a `Π` or an
   application of `R`. The export says `numNested = 0` and `isReflexive =
   false`; the second is syntactic and wrong about the kernel's reading, the
   first is right.

   The construction reads every field through
   `InductiveModels.positivityForm`, which is that same walk, so each owner
   below reaches its arm with the literal `∀ z⃗, T p⃗ e⃗` the arm peels, while
   every public statement is still spelled from the export byte for byte.
   These used to be an internal error ("mentions it other than as
   `∀ z⃗, R p⃗ e⃗`"); con-leche's `ind_pos_whnf_fn` is `R`.

   * `R` — con-leche's shape: one unfolding exposes the `Π`.
   * `R2` — two unfoldings, with a `Π` between them (`Fn2 α := Bool → Fn α`),
     so the walk must reduce again under the binder it just peeled.
   * `R3` — the `Π` written, the next one behind a definition.
   * `V` — an indexed family, the occurrence `V n` behind `FnI V n`.
   * `P` — a proposition.
   * `Tr` — a parameterised owner whose parameter is also the binder domain.
-/

def Fn (α : Type) : Type := Nat → α
def Fn2 (α : Type) : Type := Bool → Fn α

--#export R R2 R3 V P Tr

inductive R where
  | leaf
  | node (f : Fn R)

inductive R2 where
  | leaf
  | node (f : Fn2 R2)

inductive R3 where
  | leaf
  | node (f : Bool → Fn R3)

def FnI (α : Nat → Type) (n : Nat) : Type := Nat → α n
inductive V : Nat → Type where
  | nil : V 0
  | cons (n : Nat) (f : FnI V n) : V (n + 1)

def FnP (α : Prop) : Prop := Nat → α
inductive P : Prop where
  | base
  | step (h : FnP P)

def FnA (β : Type) (α : Type) : Type := β → α
inductive Tr (β : Type) where
  | leaf
  | node (x : β) (f : FnA β (Tr β))
