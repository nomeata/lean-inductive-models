/-
# The characteristic equations of Lean's `Nat` operations, as `rfl`

`NAT-REPRESENTATION.md` §10.1 recorded one thing as unsettled and load-bearing:
*"whether `mini` can derive `Nat.add`'s two defining equations today"*. The
uniqueness bridge — *any function satisfying the primitive-recursion equations
equals the efficient implementation* — has to be instantiated at
`f := ⟦Nat.add⟧`, and that instantiation needs

```
Nat.add n 0       = n
Nat.add n (m+1)   = Nat.succ (Nat.add n m)
```

**by δ + ι**, from the export's own definition. Lean does not define `Nat.add`
by a bare recursor application: the structural recursion is compiled to a
`Nat.brecOn` / `Nat.below` / `Nat.add.match_1` nest whose step case projects the
induction hypothesis out of a `PProd` with `Expr.proj`. This fixture is that
question stated as an export.

**It is not `prelude`.** Every other source in this directory is, because
`lean4export` would otherwise emit thousands of declarations. This one has to
be different: the whole question is about *Lean's own* `Nat.add`, so a
hand-rolled restatement would measure the elaborator's output on a different
declaration and prove nothing about the file we care about. The `--#export`
filter keeps the result to the transitive closure of the theorems below: 44
declaration entries, 1059 lines.

## What the fixture holds

| group | theorems | shape it exercises |
| --- | --- | --- |
| control | `recAddZero`, `recAddSucc` | `recAdd` is written **directly on `Nat.rec`** — no `brecOn`, no `below`, no projection |
| `add` | `natAddZero`, `natAddSucc` | Lean's `Nat.add`, recursion on the **second** argument |
| `sub` | `natSubZero`, `natSubSucc` | `Nat.sub`, second argument |
| `mul` | `natMulZero`, `natMulSucc` | `Nat.mul`, second argument |
| `pow` | `natPowZero`, `natPowSucc` | `Nat.pow`, second argument, motive `fun _ => Nat` rather than `fun _ => Nat → Nat` |
| `beq` | `natBeqZZ`, `natBeqZS`, `natBeqSZ`, `natBeqSS` | `Nat.beq`, recursion on the **first** argument |
| `ble` | `natBleZ`, `natBleSZ`, `natBleSS` | `Nat.ble`, first argument |

The control is the point of comparison: it is the *same mathematical equations*
about the *same recursion*, differing only in whether the definition went
through the `brecOn` nest. `recAdd` certifies; nothing that went through the
nest does.

**`Nat.div` and `Nat.mod` are deliberately absent.** They have no
primitive-recursion characterisation to state: `Nat.div x y` is
`dite (0 < y) (fun hy => Nat.div.go x y (x+1) x _) (fun _ => 0)`, a fuel-driven
inner loop, and Lean's own characterisation (`Init/Data/Nat/Div/Basic.lean:39`,
`Nat.div_eq : x / y = if 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0`) is proved
`by`, not by `rfl`. `Nat.div n 0 = 0` and `Nat.mod n 0 = n` were both tried as
`rfl` at `v4.29.1` and both fail to elaborate — the `dite` is stuck on the
variable `y`, so there is nothing for δ + ι to do.

`gcd`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight` are out of scope twice
over: they are well-founded rather than structural, and `init-prelude` does not
name them.
-/
import Init.Prelude

--#export recAdd recAddZero recAddSucc
--#export natAddZero natAddSucc natSubZero natSubSucc
--#export natMulZero natMulSucc natPowZero natPowSucc
--#export natBeqZZ natBeqZS natBeqSZ natBeqSS
--#export natBleZ natBleSZ natBleSS

/-- The control: primitive recursion written straight onto `Nat.rec`. -/
noncomputable def recAdd (n m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) n (fun _ ih => Nat.succ ih) m

theorem recAddZero (n : Nat) : Eq (recAdd n Nat.zero) n := Eq.refl _
theorem recAddSucc (n m : Nat) : Eq (recAdd n (Nat.succ m)) (Nat.succ (recAdd n m)) := Eq.refl _

/-- `Nat.add`, recursion on the second argument. -/
theorem natAddZero (n : Nat) : Eq (Nat.add n Nat.zero) n := Eq.refl _
theorem natAddSucc (n m : Nat) : Eq (Nat.add n (Nat.succ m)) (Nat.succ (Nat.add n m)) := Eq.refl _

theorem natSubZero (n : Nat) : Eq (Nat.sub n Nat.zero) n := Eq.refl _
theorem natSubSucc (n m : Nat) : Eq (Nat.sub n (Nat.succ m)) (Nat.pred (Nat.sub n m)) := Eq.refl _

theorem natMulZero (n : Nat) : Eq (Nat.mul n Nat.zero) Nat.zero := Eq.refl _
theorem natMulSucc (n m : Nat) : Eq (Nat.mul n (Nat.succ m)) (Nat.add (Nat.mul n m) n) := Eq.refl _

theorem natPowZero (m : Nat) : Eq (Nat.pow m Nat.zero) (Nat.succ Nat.zero) := Eq.refl _
theorem natPowSucc (m n : Nat) : Eq (Nat.pow m (Nat.succ n)) (Nat.mul (Nat.pow m n) m) := Eq.refl _

/-- `Nat.beq` and `Nat.ble` recurse on the **first** argument. -/
theorem natBeqZZ : Eq (Nat.beq Nat.zero Nat.zero) true := Eq.refl _
theorem natBeqZS (m : Nat) : Eq (Nat.beq Nat.zero (Nat.succ m)) false := Eq.refl _
theorem natBeqSZ (n : Nat) : Eq (Nat.beq (Nat.succ n) Nat.zero) false := Eq.refl _
theorem natBeqSS (n m : Nat) : Eq (Nat.beq (Nat.succ n) (Nat.succ m)) (Nat.beq n m) := Eq.refl _

theorem natBleZ (m : Nat) : Eq (Nat.ble Nat.zero m) true := Eq.refl _
theorem natBleSZ (n : Nat) : Eq (Nat.ble (Nat.succ n) Nat.zero) false := Eq.refl _
theorem natBleSS (n m : Nat) : Eq (Nat.ble (Nat.succ n) (Nat.succ m)) (Nat.ble n m) := Eq.refl _
