/- **Type formers computed by ι or projection reduction.**

   Lean's kernel reads an inductive's parameters, indices and sort by
   weak-head normalising its type, and its normalisation includes ι and
   projection reduction. The construction reads every owner through
   `InductiveModels.kernelFormer` (the kernel's own whnf), and the statement
   checker through `ExactNormalizationEnv.readKernelFormer`: δ, β and ζ, and
   ι and projection steps on *literal constructor applications* only, with
   recursor rules exactly as the export states them. Every owner here reaches
   its sort that way, so each is modelled and verified; before, each stopped
   the run with exit 3. The driver requires both readings to be the same
   expression on every owner it models.

   * `XP` — one index, through a projection of a pair literal `(…, …).1`.
   * `XM` — one index, through `pick`, a definition by `match`
     (`pick.match_1` unfolds to `Bool.casesOn`, and that to `Bool.rec`).
   * `XC` — the same through `Bool.casesOn` written directly.
   * `XN` — nested ι: `pick`'s major premise is `negate false`, itself a
     `match` that has to reduce to `true` first.
   * `XL` — ι on a `Nat` literal: `byNat 2` is structural recursion
     (`Nat.rec` through `brecOn`, with `PProd` projections), and the kernel
     reads the literal `2` as `Nat.succ 1`.
   * `XI` — a parameter written, two indices computed by ι.
   * `XT`, `XPr` — the sort itself computed by ι: `Type` through `pick`,
     `Prop` through `prp`.
   * `XR` — a structure at a sort computed by ι: projections and η.
   * `MA`/`MB` — a mutual block whose members' telescopes are computed by ι.

   What still stops is in `test/fixtures/unverifiable/`: an ι step that needs
   K, or structure η, on a major premise that is a variable.
-/

inductive XP : (((Nat → Type), (0 : Nat)) : (Type 1) × Nat).1 where
  | mk : Nat → XP 0

def pick : Bool → Type 1
  | true => Nat → Type
  | false => Type

inductive XM : pick true where
  | mk : Nat → XM 0

inductive XC : Bool.casesOn (motive := fun _ => Type 1) true Type (Nat → Type) where
  | mk : Nat → XC 0

def negate : Bool → Bool
  | true => false
  | false => true

inductive XN : pick (negate false) where
  | mk : Nat → XN 0

def byNat : Nat → Type 1
  | 0 => Type
  | n + 1 => Nat → byNat n

inductive XL : byNat 2 where
  | mk : XL 0 1

def idx : Bool → Type 1
  | true => Nat → Bool → Type
  | false => Type

inductive XI (α : Type) : idx true where
  | mk : α → XI α 0 true

def prp : Bool → Type
  | true => Prop
  | false => Nat → Prop

inductive XT : pick false where
  | a : XT
  | b : Nat → XT

inductive XPr : prp true where
  | mk : XPr

inductive XR : pick false where
  | mk : Nat → Bool → XR

mutual
  inductive MA : pick true where
    | nil : MA 0
    | cons : MB → MA 1
  inductive MB : pick false where
    | wrap : MA 0 → MB
end

--#export XP XM XC XN XL XI XT XPr XR MA MB
