/- **A mutual `def` block's members are not contiguous in an export.**

   `lean4export` dumps each declaration where its own dependencies are ready,
   and a `mutual partial def` block becomes one `opaque` per member with no
   shared companion — so the members can land arbitrarily far apart with other
   declarations, including ones a *later* member uses, in between. This fixture
   captures that shape in five records.

   The export this produces has, in order:

     opaque early     the first member, `all = [early, late]`
     def    useEarly  a user of the first member, between the two
     inductive Box    declared here, because only `late` needs it
     opaque late      the second member, same `all`, and it mentions `Box`

   A grouping that makes the block one node opens it at `early` and so carries
   `late` in front of `Box` — and then reports the forward reference it created.
   Members that were *adjacent* would not distinguish the two groupings, which
   is why `useEarly` and `Box` are both between them.

   The two members are also demanded at **different** instantiations —
   `early.{0}` by `useEarly`, `late.{1}` by `useLate` — so a grouping that makes
   them share one instantiation set emits two copies of each where one is
   wanted. The counts in `MonoTest.lean` are what says which happened. -/
prelude

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

/-- `partial def` packs a mutual block's inhabitants through `PProd`. -/
structure PProd (α : Sort u) (β : Sort v) where
  fst : α
  snd : β

class Inhabited (α : Sort u) where
  default : α

export Inhabited (default)

instance : Inhabited N := ⟨N.z⟩
instance : Inhabited Type := ⟨N⟩
instance (α : Sort u) (β : Sort v) [Inhabited β] : Inhabited (α → β) := ⟨fun _ => default⟩
instance (α : Sort u) (β : Sort v) [Inhabited α] [Inhabited β] : Inhabited (PProd α β) :=
  ⟨PProd.mk default default⟩

/-- Only `late` mentions this, so the export declares it *between* the two
members of the block below. -/
structure Box (α : Type u) : Type u where
  val : α

instance (α : Type u) [Inhabited α] : Inhabited (Box α) := ⟨Box.mk default⟩

mutual
partial def early (α : Type u) [Inhabited α] (a : α) : α := (late α a).val
partial def late (α : Type u) [Inhabited α] (a : α) : Box α := Box.mk (early α a)
end

--#export useEarly useLate

def useEarly (n : N) : N := early N n
noncomputable def useLate (a : Type) : Box.{1} Type := late.{1} Type a
