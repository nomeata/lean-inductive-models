/- **A type former the kernel reaches by structure η, and the statement
   checker does not.**

   Lean's kernel reduces a recursor of a structure (outside `Prop`) on *any*
   major premise, by η-expanding it to the constructor applied to its
   projections. `XE`'s type applies `PUnit.rec` to the parameter `u`, a
   variable, so the kernel reads one index, `Nat`. The structural checker's
   reading takes ι steps only on a literal constructor application, never η,
   so to it `XE`'s type is stuck: it can verify no model, and the run stops
   with exit 3. `test/MainCliTest.lean` pins the exit and the message.
-/

inductive XE (u : PUnit.{1}) :
    @PUnit.rec (fun _ => Type 1) (Nat → Type) u where
  | mk : Nat → XE u 0

--#export XE
