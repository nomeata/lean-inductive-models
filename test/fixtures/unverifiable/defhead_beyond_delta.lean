/- **Type formers the statement checker cannot restate.**

   Lean's kernel reads an inductive's parameters, indices and sort by
   weak-head normalising its type, and its normalisation includes ι and
   projection reduction: `XP` has one index, reached through `(…, …).1`, and
   `XM` one reached through `pick`, a definition by `match`. The structural
   checker restates every owner's telescope with the export's deliberately
   bounded normaliser (δβζ), so it could verify no model of either. The run
   stops before any construction with exit 3 and says so. It is not a decline:
   a decline would call the input valid on the kernel's word alone, and this
   shape is where a since-fixed kernel bug lived (the Kernel Arena's
   `bad/bugs/proj-of-stuck-prop`, `proj-of-subst-prop` and `rec-of-subst-prop`
   prove `False` through Lean v4.33.0's kernel; leanprover/lean4#14807 fixed it
   in v4.34.0). Both declarations here are kernel-valid.
   `test/MainCliTest.lean` pins the exit and the message.
-/

inductive XP : (((Nat → Type), (0 : Nat)) : (Type 1) × Nat).1 where
  | mk : Nat → XP 0

def pick : Bool → Type 1
  | true => Nat → Type
  | false => Type

inductive XM : pick true where
  | mk : Nat → XM 0

--#export XP XM
