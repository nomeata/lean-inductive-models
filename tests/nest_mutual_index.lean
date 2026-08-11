/- **A mutual block that nests, whose members carry indices.** The two axes
   were closed separately and nothing crossed them: `nest_mutual_both.lean` is
   a mutual block with no indices anywhere and `indexed_decl.lean` is an
   indexed declaration that is not mutual. A treatment that read the *first*
   member's index count for every member, or that assumed one shared index
   telescope, passes both of those and fails here.

   `MA : N → Type` and `MB : N → N → Type` have index telescopes of **different
   lengths**, so the block's recursors have a different index arity per member
   and the two mimics have none — three distinct arities in one motive vector.
   Each member carries a *recursive* field whose index differs from its
   result's — `MA.up : (n : N) → MA n → MA (N.s n)`, `MB.wide : MB a b →
   MB (N.s a) b` — and `MB.wide` moves the first index only, so an index order
   read backwards is visible. Both members nest, at two different containers,
   which is what `nest_mutual_both.lean` established a per-member carrier
   family for. -/
prelude

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α

inductive Box (α : Type) : Type where
  | mk : α → Box α

--#export Eq N List Box MA MB

mutual
inductive MA : N → Type where
  | leaf : MA N.z
  | up : (n : N) → MA n → MA (N.s n)
  | node : List (MB N.z (N.s N.z)) → MA (N.s (N.s N.z))
inductive MB : N → N → Type where
  | leaf : MB N.z N.z
  | wide : (a b : N) → MB a b → MB (N.s a) b
  | node : Box (MA (N.s N.z)) → MB N.z (N.s N.z)
end
