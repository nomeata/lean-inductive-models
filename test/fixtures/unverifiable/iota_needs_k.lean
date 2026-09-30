/- **A type former the kernel reaches by K, and the statement checker does not.**

   `Eq.rec` is a K-like recursor: Lean's kernel reduces it on *any* major
   premise whose type is `a = a`, by replacing the major with `Eq.refl a`.
   `XK`'s type applies it to the parameter `h`, a variable, so the kernel
   reads one index, `Nat`. The structural checker's reading takes ι steps only
   on a literal constructor application, never K, so to it `XK`'s type is
   stuck: it can verify no model, and the run stops with exit 3.
   `test/MainCliTest.lean` pins the exit and the message.
-/

inductive XK (h : (0 : Nat) = 0) :
    @Eq.rec Nat 0 (fun _ _ => Type 1) (Nat → Type) 0 h where
  | mk : Nat → XK h 0

--#export XK
