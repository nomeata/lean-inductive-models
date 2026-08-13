/- **A nested polymorphic declaration, actually used at three instantiations.**

   `test/fixtures/lean-inductive-models/poly_nested.ndjson` declares `PTree.{u}` and `QTree.{u,v}`
   and *uses* neither, so every group in it monomorphizes to exactly one copy
   (`copies per group: [(1, 42)]`). On that file "the model came out at the
   instantiation its declaration did" and "everything defaulted and the defaults
   agreed" are the same observation, and the composition of `lean-inductive-models` with
   `monomorph` cannot be measured.

   Here `PTree.{u}` is used at **three** distinct universes. Three rather than
   two: two copies cannot distinguish a per-instantiation model from a model
   emitted once per *something else that happens to come in pairs*.

   What this file is for is the question `lean-inductive-models`'s model raises and
   `poly_nested` cannot ask: the model's declarations — `PTree._model._impl.0`, its
   `pack_i`/`unpack_i`, its `rec_k` and `iota_k_j` — are **referenced by
   nothing**. A consumer finds them by the naming convention, not by a use site. So
   `monomorph`'s backward sweep sees no demand on the model's groups and takes
   the default, while `PTree` itself gets one copy per use. Whether that is what
   happens is the measurement captured by this fixture. -/
prelude

universe u w

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive List (α : Type w) : Type w where
  | nil : List α
  | cons : α → List α → List α

inductive N : Type where
  | z : N
  | s : N → N

inductive PTree (α : Type u) : Type u where
  | leaf : α → PTree α
  | node : List (PTree α) → PTree α

--#export Eq List PTree atZero atOne atTwo

def atZero : PTree.{0} N → PTree.{0} N := fun t => t
def atOne : PTree.{1} (Type 0) → PTree.{1} (Type 0) := fun t => t
def atTwo : PTree.{2} (Type 1) → PTree.{2} (Type 1) := fun t => t
