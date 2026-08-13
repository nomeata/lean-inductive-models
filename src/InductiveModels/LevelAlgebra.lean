import Lean

/-
# `InductiveModels.LevelAlgebra` — a complete decision procedure for Lean's
universe-level algebra, in Lean.

## Why the planner wants this and the elaborator will not do

`Lean.Meta.isLevelDefEq` compares levels by normalising and testing the
normal forms structurally. That is sound but **incomplete**: a `max` does not
absorb an `imax` it dominates, so

    max 1 (imax (imax u v) v) (max 1 u v)   and   max 1 u v

are equal at every assignment and Lean says no. `InductiveModels.primIso`'s
**planner** asks exactly this question when it decides whether a pad or a box
closes a field's level gap, so the incompleteness shows up there as a
*decline* — a model not attempted, rather than a model built wrong.

## How the planner uses the procedure

The procedure is used to **widen** Lean's answer, never to narrow it:

    isLevelDefEqComplete u v  :=  laEquiv u v == .true  ||  isLevelDefEq u v

so the planner accepts whenever *either* the complete procedure or the
elaborator says yes. Three consequences, and they are the reason the change
is safe to make in a planner:

* **The change is monotone.** No pair that was accepted before is rejected
  now, so a coverage measurement can only see declines *close*, never open.
  A coverage regression would therefore be a bug in the port and not a
  judgement call.
* **`unknown` needs no special handling.** A cap hit (too many variables, too
  many nested case splits, arena exhaustion) is not `.true`, so it falls
  through to the elaborator under the "no opinion, fall back" contract.
* **Level metavariables are safe.** `laEquiv` has no way to *assign* one, and
  `isLevelDefEq` does; a level containing an `.mvar` converts to `none` here
  and is decided entirely by the elaborator, as before.

Permissiveness in the planner costs wasted work and cannot cost soundness:
every declaration the generator produces goes through `addChecked`, which is
`addDeclCore … doCheck := true`, and the tool's standing contract is that a
proof the generator builds and the kernel rejects is a **decline**, never an
emission.

## Fuzzing

`tools/LevelFuzz.lean` tests the procedure against a bounded semantic oracle over
six million generated pairs. The caps below bound pathological inputs so the
procedure returns `unknown` instead of hanging.
-/

namespace InductiveModels.LevelAlgebra

open Lean

/-- At most this many distinct level variables in one comparison. -/
def maxVars : Nat := 16

/-- At most `2 ^ maxSplits` leaves in the case split. Ten distinct variables
in `imax` second position in one comparison does not occur in practice; the
cap exists so that a pathological input degrades to `unknown` instead of
hanging. -/
def maxSplits : Nat := 10

/-- The private AST: Lean's level algebra with variables numbered, and with
no metavariables and no cached data. Working over this rather than over
`Lean.Level` keeps the smart constructors (`mkLevelMax'` and friends, which
simplify) from interfering with the algorithm's invariants. -/
inductive LA where
  | zero
  | succ (a : LA)
  | max  (a b : LA)
  | imax (a b : LA)
  | var  (i : Nat)
  deriving Inhabited, Repr, BEq

/-- The verdict. `unknown` means a cap was hit: **no opinion**, never a
guess, and a caller must fall back. This is what keeps the procedure from
ever being *less* sound than the thing it extends. -/
inductive Verdict where
  | false_
  | true_
  | unknown
  deriving Inhabited, Repr, BEq

/-! ## Step 1: push `imax` down until its second argument is a variable -/

/-- `imaxSmart a b` with `b` already simplified — so `b` is `zero`, `succ`,
`max`, `var`, or an `imax` whose own second argument is a `var`. The four
rewrites are semantics-preserving; each is checked at every case of "is the
second argument zero". Terminating on the size of `b`: the `max` case
recurses into `b`'s children and the `imax` case into `b`'s second child. -/
def imaxSmart : LA → LA → LA
  | _, .zero     => .zero                                    -- imax a 0 = 0
  | a, .succ b   => .max a (.succ b)                 -- imax a (succ b) = max
  | a, .max c d  => .max (imaxSmart a c) (imaxSmart a d)     -- distributes
  | a, .imax c d => imaxSmart (.max a c) d           -- imax a (imax c d) = …
  | a, .var i    => .imax a (.var i)                         -- irreducible
termination_by _ b => b

/-- Apply `imaxSmart` bottom-up, so that every surviving `imax` has a bare
variable as its second argument. -/
def simp : LA → LA
  | .zero     => .zero
  | .var i    => .var i
  | .succ a   => .succ (simp a)
  | .max a b  => .max (simp a) (simp b)
  | .imax a b => imaxSmart (simp a) (simp b)

/-- The first variable occurring as the second argument of an `imax`, if any.
Assumes `simp` has run, so an `imax`'s second argument is a `var`. -/
def imaxVar : LA → Option Nat
  | .zero | .var _ => none
  | .succ a        => imaxVar a
  | .max a b       => imaxVar a <|> imaxVar b
  | .imax a b      => imaxVar a <|> (match b with
                                     | .var i => some i
                                     | _      => imaxVar b)

/-- Replace variable `x` by `0` (`succ? = false`) or by `succ x`
(`succ? = true`). The latter is the reparametrisation `ρ(x) = 1 + ρ'(x)`,
which is a bijection onto the assignments with `ρ(x) ≥ 1`. -/
def subst (x : Nat) (succ? : Bool) : LA → LA
  | .zero     => .zero
  | .var i    => if i == x then (if succ? then .succ (.var x) else .zero)
                 else .var i
  | .succ a   => .succ (subst x succ? a)
  | .max a b  => .max (subst x succ? a) (subst x succ? b)
  | .imax a b => .imax (subst x succ? a) (subst x succ? b)

/-! ## Step 3: canonical form of an `imax`-free level

At the leaves no `imax` remains, so the level is a `max` of `x + k` terms and
a constant. The canonical form is `(k, off)` meaning
`max(k, maxᵥ (ρ(v) + off v))`, with `k` dropped to `0` when some present
variable's offset covers it. -/

/-- `k` is the constant; `off[i]` is `some o` when variable `i` occurs at
maximal offset `o`. -/
structure NF where
  k   : Nat
  off : Array (Option Nat)
  deriving Inhabited, BEq

/-- Accumulate into a normal form. Fails (`none`) if an `imax` survives,
which cannot happen after `simp` plus a complete case split. -/
def nfAcc (nvars : Nat) : LA → Nat → NF → Option NF
  | .zero,     shift, o => some { o with k := Nat.max o.k shift }
  | .succ a,   shift, o => nfAcc nvars a (shift + 1) o
  | .max a b,  shift, o => do nfAcc nvars b shift (← nfAcc nvars a shift o)
  | .var i,    shift, o =>
    if i < nvars then
      let cur := o.off[i]!.getD 0
      some { o with off := o.off.set! i (some (Nat.max cur shift)) }
    else none
  | .imax _ _, _,     _ => none

/-- The canonical form, or `none` if an `imax` survived. -/
def toNF (nvars : Nat) (n : LA) : Option NF := do
  let o ← nfAcc nvars n 0 { k := 0, off := Array.replicate nvars none }
  -- the constant is redundant when some present variable's offset covers it
  if o.off.any (fun | some d => d ≥ o.k | none => false) then
    return { o with k := 0 }
  return o

/-- The minimum over `ρ` of the level denoted, attained at `ρ = 0`. -/
def NF.min (a : NF) : Nat :=
  a.off.foldl (fun m acc => match acc with | some d => Nat.max m d | none => m) a.k

/-- `u ≥ v` at every assignment: `u`'s minimum covers `v`'s constant, and
every variable of `v` occurs in `u` at an offset at least as large. -/
def NF.geq (u v : NF) : Bool := Id.run do
  if u.min < v.k then return false
  for i in [0 : v.off.size] do
    match v.off[i]!, u.off[i]! with
    | none,   _        => continue
    | some _, none     => return false
    | some d, some du  => if du < d then return false
  return true

/-! ## The recursion -/

/-- The case split. `fuel` counts down from `maxSplits`: each surviving
`imax` variable costs one level, and either substitution makes every
`imax _ x` reduce away by `simp` while introducing no new variable in second
position, so the number of `imax` variables strictly decreases. -/
def go (nvars : Nat) (geq : Bool) : LA → LA → Nat → Verdict
  | _, _, 0 => .unknown
  | u₀, v₀, fuel + 1 =>
    let u := simp u₀
    let v := simp v₀
    match imaxVar u <|> imaxVar v with
    | none =>
      match toNF nvars u, toNF nvars v with
      | some nu, some nv =>
        if geq then (if nu.geq nv then .true_ else .false_)
        else (if nu == nv then .true_ else .false_)
      | _, _ => .unknown
    | some x =>
      -- `false_` and `unknown` both propagate
      match go nvars geq (subst x false u) (subst x false v) fuel with
      | .true_ => go nvars geq (subst x true u) (subst x true v) fuel
      | r      => r

/-! ## Conversion from `Lean.Level` -/

/-- Number the `.param`s of a level, appending to `acc`. `none` if the level
contains an `.mvar` (the elaborator may assign one; we may not) or if it
exceeds `maxVars` distinct parameters. -/
private def collect : Level → Array Name → Option (Array Name)
  | .zero,       acc => some acc
  | .succ a,     acc => collect a acc
  | .max a b,    acc => do collect b (← collect a acc)
  | .imax a b,   acc => do collect b (← collect a acc)
  | .mvar _,     _   => none
  | .param n,    acc =>
    if acc.contains n then some acc
    else if acc.size ≥ maxVars then none
    else some (acc.push n)

private def build (vars : Array Name) : Level → Option LA
  | .zero     => some .zero
  | .succ a   => do return .succ (← build vars a)
  | .max a b  => do return .max (← build vars a) (← build vars b)
  | .imax a b => do return .imax (← build vars a) (← build vars b)
  | .mvar _   => none
  | .param n  => do return .var (← vars.idxOf? n)

/-- Convert a pair of `Lean.Level`s to the private AST over a shared variable
numbering, or `none` if either mentions a metavariable or the pair has more
than `maxVars` distinct parameters. -/
def ofLevels (u v : Level) : Option (Nat × LA × LA) := do
  let vars ← collect v (← collect u #[])
  return (vars.size, ← build vars u, ← build vars v)

/-! ## The entry points -/

/-- Decides `∀ ρ, ⟦u⟧ = ⟦v⟧` over the private AST. -/
def laEquiv (nvars : Nat) (u v : LA) : Verdict := go nvars false u v maxSplits

/-- Decides `∀ ρ, ⟦u⟧ ≥ ⟦v⟧` over the private AST. -/
def laGeq (nvars : Nat) (u v : LA) : Verdict := go nvars true u v maxSplits

/-- `∀ ρ, ⟦u⟧ = ⟦v⟧` for `Lean.Level`s: `.unknown` when the pair is out of
range (a metavariable, or a cap hit). -/
def levelEquiv (u v : Level) : Verdict :=
  match ofLevels u v with
  | none              => .unknown
  | some (nv, lu, lv) => laEquiv nv lu lv

/-- `∀ ρ, ⟦u⟧ ≥ ⟦v⟧` for `Lean.Level`s. -/
def levelGeq (u v : Level) : Verdict :=
  match ofLevels u v with
  | none              => .unknown
  | some (nv, lu, lv) => laGeq nv lu lv

/-! ## The control and the census

The widening has a runtime control so an A/B measurement remains a property
of one binary rather than two builds. The baseline is the identical binary
with widening disabled.

The census answers the prior question, which is whether the widening ever
fires at all. An **escape** is a pair the complete procedure accepts and
`Lean.Meta.isLevelDefEq` rejects — the only pairs at which this change can
possibly alter behaviour. Zero escapes on representative exports means the
change is a measured null there, and that is a result, not a failure. -/

/-- The control: `LEAN_INDUCTIVE_MODELS_PLANNER_STOCK_LEVELS=1` restores the elaborator's
answer exactly, widening disabled. -/
initialize stockLevels : Bool ←
  return (← IO.getEnv "LEAN_INDUCTIVE_MODELS_PLANNER_STOCK_LEVELS") == some "1"

/-- `LEAN_INDUCTIVE_MODELS_PLANNER_LEVEL_TRACE=1` prints every escaping pair. An escape is
rare enough that naming each one is the right granularity. -/
initialize traceLevels : Bool ←
  return (← IO.getEnv "LEAN_INDUCTIVE_MODELS_PLANNER_LEVEL_TRACE") == some "1"

/-- Calls, and escapes: pairs where the complete procedure said yes and the
elaborator said no. -/
initialize levelCalls : IO.Ref Nat ← IO.mkRef 0
initialize levelEscapes : IO.Ref Nat ← IO.mkRef 0

/-- **The planner's level equality.** Accepts whenever *either* the complete
procedure or the elaborator does, so it is a strict widening of
`Lean.Meta.isLevelDefEq` — see the header for why that is the right shape
here. `.unknown` and `.false_` both fall through to the elaborator, which
also preserves its ability to assign level metavariables. -/
def isLevelDefEqComplete (u v : Level) : MetaM Bool := do
  levelCalls.modify (· + 1)
  let stock ← Lean.Meta.isLevelDefEq u v
  if stock || stockLevels then return stock
  if levelEquiv u v == .true_ then
    levelEscapes.modify (· + 1)
    if traceLevels then
      IO.eprintln s!"levels: escape  {u}  ≡  {v}"
    return true
  return false

/-! ## The semantic oracle

Evaluate under an explicit assignment. Used by the fuzz, and by nothing
else. -/
def laEval (rho : Array Nat) : LA → Nat
  | .zero     => 0
  | .succ a   => laEval rho a + 1
  | .max a b  => Nat.max (laEval rho a) (laEval rho b)
  | .imax a b => let vb := laEval rho b
                 if vb == 0 then 0 else Nat.max (laEval rho a) vb
  | .var i    => rho[i]!

end InductiveModels.LevelAlgebra
