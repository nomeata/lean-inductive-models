/- Focused arm-F index-zipper cases.

   Each declaration has a large eliminator and at least one data pivot whose
   declared index type changes with an earlier index.  Together they force the
   model to recover constructor fields from left to right:

   * `FTwo` has two moving data pivots.
   * `FProof` binds a proof after its moving pivot.
   * `FChain` makes one pivot type depend on a three-entry index prefix.
   * `FEndpoint` repeats the recovered pivot at a later non-pivot endpoint.

   `prim_idx.lean` supplies the one-pivot `Fmid` control in the broader pivot /
   non-pivot grid. -/

--#export FTwo FProof FChain FEndpoint

inductive FTwo : (α : Type) → α → α → α → Prop where
  | mk (x y : Nat) : FTwo Nat Nat.zero x y

inductive FProof : (α : Type) → α → α → Prop where
  | mk (x : Nat) (h : x = x) : FProof Nat Nat.zero x

inductive FChain : (α : Type) → (β : α → Type) → (a : α) → β a → Prop where
  | mk (x : Nat) : FChain Nat (fun _ => Nat) Nat.zero x

inductive FEndpoint : (α : Type) → α → α → Prop where
  | mk (x : Nat) : FEndpoint Nat x x
