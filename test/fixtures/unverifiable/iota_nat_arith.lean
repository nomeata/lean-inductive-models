/- **A type former whose two readings differ: `Nat` arithmetic.**

   Lean's kernel evaluates `Nat.add` on two literals natively, to a literal:
   the major premise `1 + 1` of `fins`'s recursor becomes `2`, read as
   `Nat.succ 1`, and the field it hands on is the literal `1`. The statement
   checker's reading has no such extension; it unfolds `Nat.add` and takes its
   ι steps on the literals, which reaches a `Nat.succ` of an unevaluated sum —
   the same number, but not the same expression. `XA`'s index domain is
   therefore `Fin (1 + 1)` to the kernel and `Fin (… + 1)` over that sum to the
   checker, and a checker that compared every model statement against its own
   reading would compare against the wrong telescope. The driver requires the two readings
   to be the same expression, so the run stops with exit 3 and says so.
   `test/MainCliTest.lean` pins the exit and the message.
-/

def fins : Nat → Type 1
  | 0 => Type
  | n + 1 => Fin (n + 1) → Type

inductive XA : fins (1 + 1) where
  | mk : XA ⟨0, Nat.zero_lt_succ _⟩

--#export XA
