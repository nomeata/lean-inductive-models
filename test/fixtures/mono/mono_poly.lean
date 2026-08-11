/- **The pass's own axis: one declaration, several instantiations.**

   Every claim `monomorph` makes is invisible on a file where each polymorphic
   declaration is used at exactly one instantiation — there, "one copy per
   instantiation" and "rename" are the same function. So:

   * `Wrap.{u}` is used at **three** distinct universes (`0`, `1`, `2`), which
     needs three copies. Two would not distinguish an ordering.
   * `Pair.{u,v}` is used at `(0,1)` and at `(1,0)` — the **same two atoms in
     both orders** — so a pass that sorted, set-ified or otherwise lost the
     order of an instantiation produces one copy where two are needed, and a
     pass that read the arguments right-to-left swaps the two carriers.
   * `unused.{u}` is mentioned by nothing, and is the default's witness.
   * `chain.{u}` uses `Wrap.{u+1}`, and only `chain.{3}` is used, so `Wrap`
     is demanded at `4` — a universe nothing in the file writes down
     rather than at `σ`: the sweep has to *evaluate* the argument, not copy it. -/
prelude

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive Wrap (α : Sort u) : Sort (max 1 u) where
  | mk : α → Wrap α

inductive Pair (α : Sort u) (β : Sort v) : Sort (max 1 u v) where
  | mk : α → β → Pair α β

inductive N : Type where
  | z : N
  | s : N → N

--#export atProp atType atType1 bothOrders unused chain useChain

def atProp : Wrap.{0} (Eq N.z N.z) → Wrap.{0} (Eq N.z N.z) := fun w => w
def atType : Wrap.{1} N → Wrap.{1} N := fun w => w
def atType1 : Wrap.{2} (Type 0) → Wrap.{2} (Type 0) := fun w => w

def bothOrders : Pair.{0,1} (Eq N.z N.z) N → Pair.{1,0} N (Eq N.z N.z) → N :=
  fun _ _ => N.z

def unused (α : Sort u) : Sort (max 1 u) := Wrap α

def chain : Type u := Wrap.{u+1} (Sort u)

def useChain : chain.{3} → chain.{3} := fun x => x
