/- **The axis only composed model generation reaches: a block whose members' sorts
   agree without being the same term.**

   The mutual construction declares its carrier at one sort `u`, read off the first
   member, having checked that every member agrees. For a `mutual` block of the
   *input* that check is free: Lean's elaborator makes the members agree on the
   nose, and a source block whose members disagree does not compile at all.

   **Lean's own nested specialisation is not under that discipline.** A mimic's
   sort is the *container's* level expression instantiated at the occurrence,
   and the two agree without being the same term — so the comparison has to be
   `isLevelDefEq` and not `==`. **Five of Mathlib's 41 declined on exactly this**
   (`Lean.PrefixTreeNode`, `Lean.PersistentHashMap.Node`, `Lean.Doc.Block`,
   `Lean.Doc.Part`, `IO.AsyncList`) and no fixture in the tree could have found
   it, because it is a shape Lean's *elaborator* forbids and Lean's *kernel*
   writes.

   **`PS` is the one that reproduces it, and the other three say why it took
   three tries.** What matters is not the container's *level* but its
   **spelling**: substituting `v := max u v` into `(max u v)+1` collapses back
   to `(max u v)+1`, and into `max (u+1) (v+1)` does not — it gives
   `max (u+1) ((max u v)+1)`, which is `Lean.PrefixTreeNode`'s block to the
   character. Lean's own `RBNode` carries the second spelling.

   | | container | its result sort, as written | mimic's sort |
   | --- | --- | --- | --- |
   | `PT` | `Cont α (PT α β)`, two ordinary parameters | `Type (max u v)` | collapses |
   | `PF` | `RB α (fun _ => PF α β)`, a **family** parameter | `Type (max u v)` | collapses |
   | `PS` | `RB2 α (fun _ => PS α β)`, the same family | `Sort (max (u+1) (v+1))` | **`max (u+1) ((max u v)+1)`** |
   | `Q` | `Box (Q α β)`, one parameter | `Type u` | equal on the nose |

   So `PT` and `PF` are not decoration: they are the two guesses that did *not*
   reproduce it, kept so that the next person does not spend the same three
   builds, and they are also the control that says a repair which simply
   stopped checking would be indistinguishable. Under a mutation that puts `==`
   back, **`PS._model._impl.0` declines and the other three still model** — which is
   what makes this file pin the repair rather than merely exercise it. -/
prelude

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

/-- Two parameters at two levels, landing at their `max`. -/
inductive Cont (α : Type u) (β : Type v) : Type (max u v) where
  | leaf : Cont α β
  | node : α → β → Cont α β → Cont α β

/-- One parameter, landing where it does. The control's container. -/
inductive Box (α : Type u) : Type u where
  | mk : α → Box α

/-- **A container whose second parameter is a family**, which is what
    `Lean.PrefixTreeNode` nests through and what makes the mimic's sort come
    out unnormalised. -/
inductive RB (α : Type u) (β : α → Type v) : Type (max u v) where
  | leaf : RB α β
  | node : RB α β → (k : α) → β k → RB α β → RB α β

/-- The same container with its result sort **spelled** `max (u+1) (v+1)`
    rather than `(max u v)+1`. The two are one level; Lean's own `RBNode`
    carries the first spelling, and it is the spelling that survives
    instantiation uncollapsed. -/
inductive RB2 (α : Type u) (β : α → Type v) : Sort (max (u+1) (v+1)) where
  | leaf : RB2 α β
  | node : RB2 α β → (k : α) → β k → RB2 α β → RB2 α β

--#export Eq N Cont Box RB RB2 PT PF PS Q ptMk pfMk psMk qMk

/-- Through a container with two ordinary parameters. -/
inductive PT (α : Type u) (β : Type v) : Type (max u v) where
  | mk : Cont α (PT α β) → PT α β

/-- **The shape.** `PrefixTreeNode` as Lean declares it, at two level
    parameters: the specialised block is `PF._model._impl.0 : Sort ((max u v)+1)`
    beside the mimic of `RB α (fun _ => PF α β)` at
    `Sort (max (u+1) ((max u v)+1))`. -/
inductive PF (α : Type u) (β : Type v) : Type (max u v) where
  | mk : RB α (fun _ => PF α β) → PF α β

/-- **The shape**, at the spelling Lean's own `RBNode` carries. -/
inductive PS (α : Type u) (β : Type v) : Type (max u v) where
  | mk : RB2 α (fun _ => PS α β) → PS α β

/-- The control: `Box (Q α β)` is at `Q`'s own sort, term for term. -/
inductive Q (α : Type u) (β : Type v) : Type (max u v) where
  | mk : Box (Q α β) → Q α β

def ptMk (α : Type u) (β : Type v) (c : Cont α (PT α β)) : PT α β := PT.mk c
def pfMk (α : Type u) (β : Type v) (c : RB α (fun _ => PF α β)) : PF α β := PF.mk c
def psMk (α : Type u) (β : Type v) (c : RB2 α (fun _ => PS α β)) : PS α β := PS.mk c
def qMk (α : Type u) (β : Type v) (b : Box (Q α β)) : Q α β := Q.mk b
