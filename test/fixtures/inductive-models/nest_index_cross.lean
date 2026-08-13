/- **An indexed container, crossed with every other axis.** `indexed_container.
   lean` is the axis on its own — a monomorphic, one-member declaration nesting
   through an indexed container. Nothing there says the container's index
   telescope survives the *declaration's* own indices, a mutual block, or a
   cycle of mimics, and a treatment that threaded one telescope where two meet
   passes that file and fails this one.

   * `CTree` — the **declaration's** indices and the **container's** at once.
     `CTree.node : CTree N.z → Vec (CTree (N.s N.z)) (N.s N.z) → CTree (N.s
     (N.s N.z))` is `indexed_decl.lean`'s `I3` with the container indexed too:
     the recursive field's index, the occurrence's parameter's, the mimic's own
     and the result's are **four** values and all differ, so reading any one
     where another belongs is a type error.
   * `PA`/`PB` — a **mutual** block whose members carry indices *and* nest
     through an indexed container, each at a different one. Four block members
     with three distinct index arities, two carriers, and two indexed mimics.
   * `XT` — a **cycle** of mimics both of which are indexed. `ITr` is itself a
     nested inductive over `Vec`, so `XT.mk : ITr XT N.z → XT` makes the mimics
     `ITr XT` and `Vec (ITr XT N.z)` mutually recursive: `pack₀` and `pack₁`
     are one simultaneous recursion over `ITr.rec`/`ITr.rec_1`, and *that*
     family's recursors carry index telescopes of their own. -/
prelude

universe u v

inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a

inductive N : Type where
  | z : N
  | s : N → N

inductive Vec (α : Type) : N → Type where
  | vnil : Vec α N.z
  | vcons : α → (n : N) → Vec α n → Vec α (N.s n)

inductive Box (α : Type) : Type where
  | mk : α → Box α

inductive ITr (α : Type) : N → Type where
  | mk : α → ITr α N.z
  | node : Vec (ITr α N.z) (N.s N.z) → ITr α (N.s N.z)

--#export Eq N Vec Box ITr CTree PA PB XT

inductive CTree : N → Type where
  | leaf : CTree N.z
  | node : CTree N.z → Vec (CTree (N.s N.z)) (N.s N.z) → CTree (N.s (N.s N.z))

mutual
inductive PA : N → Type where
  | leaf : PA N.z
  | node : Vec (PB N.z) (N.s N.z) → PA (N.s N.z)
inductive PB : N → Type where
  | leaf : PB N.z
  | node : Vec (PA (N.s N.z)) N.z → PB N.z
end

inductive XT : Type where
  | mk : ITr XT N.z → XT
