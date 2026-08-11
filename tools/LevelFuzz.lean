import Modelgen.LevelAlgebra

/-!
# `LevelFuzz` — semantic fuzzing for the level algebra

Every generated pair is evaluated at every assignment in a bounded box and
the decision procedure's verdict is scored against that oracle. A discovered
counterexample is conclusive, so the `FALSE_ACCEPTS` count is exact; a
"missed" equality remains only an upper bound because a bounded oracle cannot
prove semantic equality.

The fixed seed and FNV-1a digest make runs deterministic and easy to compare
across changes to the Lean implementation.

Usage: `lake exe levelfuzz <pairs> <depth> <vars> <wide>`, or with no
arguments the full six-million-pair sweep.
-/

open Modelgen.LevelAlgebra

namespace LevelFuzz

/-- A fixed-seed xorshift64 generator. Returns the high 32 bits. -/
structure Rng where
  s : UInt64
  deriving Inhabited

def Rng.init : Rng := { s := 0x9E3779B97F4A7C15 }

@[inline] def Rng.next (g : Rng) : UInt32 × Rng :=
  let s := g.s
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  let s := s ^^^ (s <<< 17)
  ((s >>> 32).toUInt32, { s })

/-- Generate a level expression, sequencing recursive calls left to right. -/
def gen (nvars : Nat) : Nat → Rng → LA × Rng
  | 0, g =>
    let (r, g) := g.next
    let r := r.toNat % (nvars + 1)
    if r == 0 then (.zero, g) else (.var (r - 1), g)
  | depth + 1, g =>
    let (r, g) := g.next
    match r.toNat % 6 with
    | 0 => (.zero, g)
    | 1 => let (v, g) := g.next; (.var (v.toNat % nvars), g)
    | 2 => let (a, g) := gen nvars depth g; (.succ a, g)
    | 3 => let (a, g) := gen nvars depth g
           let (b, g) := gen nvars depth g
           (.max a b, g)
    | _ => let (a, g) := gen nvars depth g
           let (b, g) := gen nvars depth g
           (.imax a b, g)

/-- FNV-1a over verdict bytes. -/
@[inline] def digest (d : UInt64) (b : UInt8) : UInt64 :=
  ((d ^^^ b.toUInt64) * 1099511628211)

@[inline] def code : Verdict → UInt8
  | .false_ => 0
  | .true_  => 1
  | .unknown => 2

/-- Score one pair against the oracle over the box `[0, wide]^nvars`, and
separately over `[0,4]^nvars` as a narrow independent oracle. Returns
`(eq4, eq, ge)`. -/
def oracle (nvars wide : Nat) (a b : LA) : Bool × Bool × Bool := Id.run do
  let mut rho : Array Nat := Array.replicate nvars 0
  let mut eq4 := true
  let mut eq := true
  let mut ge := true
  repeat
    let x := laEval rho a
    let y := laEval rho b
    let narrow := rho.all (· ≤ 4)
    if x != y then
      eq := false
      if narrow then eq4 := false
    if x < y then ge := false
    -- odometer over the box
    let mut k := 0
    let mut carried := true
    while k < nvars do
      if rho[k]! < wide then
        rho := rho.set! k (rho[k]! + 1); carried := false; break
      else
        rho := rho.set! k 0; k := k + 1
    if carried then break
  return (eq4, eq, ge)

/-- `Lean.Level.isNeverZero`, transliterated onto the private AST.

This is not part of the port. It is here because the planner's **route
selector** ([`Modelgen.classifyRoute`]) asks "is this carrier level never zero?" with
this structural test, and routes to `.bare` when it says no — whose declines
are the route classifier's `type` and `maybeZero` cases. That is a level question decided
structurally, so it is a candidate for exactly the incompleteness this whole
change is about, and a swap that fixed the four `isLevelDefEq` calls while
leaving a second incomplete level test in the same planner would be the
partial swap the brief warns against.

`laGeq nvars a (succ zero)` decides the same question completely, so the two
can simply be fuzzed against each other. The fuzz reports disagreements. -/
def isNeverZero : LA → Bool
  | .zero    => false
  | .var _   => false
  | .succ _  => true
  | .max a b => isNeverZero a || isNeverZero b
  | .imax _ b => isNeverZero b

structure Tally where
  sem4      : Nat := 0
  semw      : Nat := 0
  narrowBad : Nat := 0
  eqMiss    : Nat := 0
  eqFalseAcc : Nat := 0
  eqUnknown : Nat := 0
  geSemw    : Nat := 0
  geMiss    : Nat := 0
  geFalseAcc : Nat := 0
  geUnknown : Nat := 0
  /-- `Level.isNeverZero` said no where the complete procedure proves `≥ 1`:
  a route the planner takes structurally and would not take completely. -/
  nzMissed  : Nat := 0
  /-- `Level.isNeverZero` said yes where the level really can be zero. This
  one would be a soundness bug in Lean and is expected to stay at 0. -/
  nzWrong   : Nat := 0
  dig       : UInt64 := 1469598103934665603
  deriving Inhabited

def run (n depth nvars wide : Nat) : Tally := Id.run do
  let mut g := Rng.init
  let mut t : Tally := {}
  for _ in [0 : n] do
    let (a, g') := gen nvars depth g
    let (b, g'') := gen nvars depth g'
    g := g''
    let (eq4, eq, ge) := oracle nvars wide a b
    let mineEq := laEquiv nvars a b
    let mineGe := laGeq nvars a b
    t := { t with dig := digest (digest t.dig (code mineEq)) (code mineGe) }
    if eq4 then t := { t with sem4 := t.sem4 + 1 }
    if eq then t := { t with semw := t.semw + 1 }
    if eq4 && !eq then t := { t with narrowBad := t.narrowBad + 1 }
    match mineEq with
    | .unknown => t := { t with eqUnknown := t.eqUnknown + 1 }
    | .false_  => if eq then t := { t with eqMiss := t.eqMiss + 1 }
    | .true_   => if !eq then t := { t with eqFalseAcc := t.eqFalseAcc + 1 }
    -- the route selector's structural never-zero test, against the complete one
    let nzStruct := isNeverZero a
    let nzComplete := laGeq nvars a (.succ .zero) == .true_
    if nzComplete && !nzStruct then t := { t with nzMissed := t.nzMissed + 1 }
    if nzStruct && !nzComplete then t := { t with nzWrong := t.nzWrong + 1 }
    if ge then t := { t with geSemw := t.geSemw + 1 }
    match mineGe with
    | .unknown => t := { t with geUnknown := t.geUnknown + 1 }
    | .false_  => if ge then t := { t with geMiss := t.geMiss + 1 }
    | .true_   => if !ge then t := { t with geFalseAcc := t.geFalseAcc + 1 }
  return t

/-- Zero-padded 16-digit lowercase hex, to match `%016llx`. -/
def hex16 (x : UInt64) : String :=
  let ds := (Nat.toDigits 16 x.toNat).asString
  "".pushn '0' (16 - ds.length) ++ ds

def report (n depth nvars wide : Nat) (t : Tally) : String :=
  s!"lean pairs={n} depth={depth} vars={nvars} wide={wide}\n" ++
  s!"lean eq: sem(0..4)={t.sem4} sem(wide)={t.semw} narrow_wrong={t.narrowBad}\n" ++
  s!"lean eq: missed={t.eqMiss} FALSE_ACCEPTS={t.eqFalseAcc} unknown={t.eqUnknown}\n" ++
  s!"lean ge: sem(wide)={t.geSemw} missed={t.geMiss} FALSE_ACCEPTS={t.geFalseAcc} unknown={t.geUnknown}\n" ++
  s!"lean nz: isNeverZero missed={t.nzMissed} wrong={t.nzWrong}\n" ++
  s!"lean digest={hex16 t.dig}"

/-- The wide oracle's box edge, chosen so the point count stays around a
couple of thousand per pair whatever the variable count is. -/
def wideFor : Nat → Nat
  | 3 => 12    -- 2197 points
  | 4 => 6     -- 2401
  | 5 => 4     -- 3125
  | 6 => 3     -- 4096
  | _ => 12

end LevelFuzz

def main (args : List String) : IO Unit := do
  match args with
  | [n, d, v, w] =>
    let n := n.toNat!; let d := d.toNat!; let v := v.toNat!; let w := w.toNat!
    IO.println (LevelFuzz.report n d v w (LevelFuzz.run n d v w))
  | _ =>
    -- Depths 3..8 over 3..6 variables, 6,000,000 pairs in total, spread
    -- evenly over the 24 configurations.
    let per := 6000000 / 24
    let mut faEq := 0
    let mut faGe := 0
    let mut unk := 0
    let mut tot := 0
    let mut nzM := 0
    let mut nzW := 0
    for d in [3:9] do
      for v in [3:7] do
        let w := LevelFuzz.wideFor v
        let t := LevelFuzz.run per d v w
        IO.println (LevelFuzz.report per d v w t)
        faEq := faEq + t.eqFalseAcc
        faGe := faGe + t.geFalseAcc
        unk := unk + t.eqUnknown + t.geUnknown
        nzM := nzM + t.nzMissed
        nzW := nzW + t.nzWrong
        tot := tot + per
    IO.println s!"\nTOTAL pairs={tot} eq FALSE_ACCEPTS={faEq} ge FALSE_ACCEPTS={faGe} unknown={unk}"
    IO.println s!"TOTAL isNeverZero: missed={nzM} wrong={nzW}"
