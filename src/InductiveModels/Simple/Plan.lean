import InductiveModels.Simple.Church

open Lean Meta

namespace InductiveModels

/-! ## The model -/

/-- One constructor's storage plan, settled by level arithmetic before
anything is spliced: which fields are boxed, and the pad level, `none` where
the chain reaches `Sort w` on its own. The pad level is `1` when that already
closes the gap and `w` otherwise. -/
structure CPlan where
  boxed : Array Bool
  pad? : Option Level
  deriving Inhabited

/-- The pads of every constructor at the given parameter scope, `none` where
the plan needs none. A `dsingOk` level gets the [`InductiveModels.dsingAt`] pad; any
other level — a bare parameter in the gap, `PULift`'s shape — gets the
[`InductiveModels.unitAt`] lift, which exists at every level.

**Both are marked `canonical`**, and that is the measured fact rather than a
symmetry: each family's canonical element is a literal constructor
application, so the kernel converts an opaque element onto it and neither pad
costs a transport. What the lift does *not* give is a conversion between two
opaque elements; nothing here asks for one. -/
def padsAt (plans : Array CPlan) :
    GenM (Array (Option Pad)) := do
  plans.mapM fun plan => do
    let some ℓ := plan.pad? | return none
    if dsingOk ℓ then
      let (t, c) ← dsingAt ℓ
      return some { ty := t, lv := ℓ, canon := c, canonical := true }
    return some { ty := unitAt ℓ, lv := ℓ, canon := unitAtCanon ℓ, canonical := true }

/-- The constructors, analysed at a parameter scope. -/
def pctorsAt (exportCtors : Array (Name × Expr)) (plans : Array CPlan)
    (pads : Array (Option Pad)) (ps : Array Expr) : GenM (Array PCtor) := do
  (Array.range exportCtors.size).mapM fun j => do
    let (_, cty) := exportCtors[j]!
    let tele ← instForall cty ps
    let nf := numForalls tele
    let boxed := plans[j]!.boxed
    let (chain, _) ← chainTy pads[j]! boxed nf tele
    return { tele, nf, pad? := pads[j]!, boxed, chain }

/-- Which route the carrier's sort admits: `Sort 0` is the Church encoding, a
never-zero sort the `Nat`-tagged sum, and a **maybe-zero** sort — `Prop` at
some instantiations, `Type` at others, `PUnit`'s and `PEmpty`'s shape — the
same Church encoding under a [`InductiveModels.puliftT`]. -/
inductive PrimRoute | type | prop | bare

/-- A field-preserving model for the one-field corner of the bare route.
`identity` applies when the field already inhabits the carrier's exact sort;
`propLift` lifts an exactly proposition-valued field to that sort. -/
inductive DirectFieldRoute | identity | propLift

/-- The complete field-preserving direct routes. The one-field cases share
[`InductiveModels.directFieldModel`]; `tight` is the multi-field `PSigma'`
tower; `indexed` is that same storage with the conclusion's index telescope
discharged by one packed equation over it.

`indexed` is not a fourth construction. It stores the constructor's fields in
the very tower `tight` stores them in — [`InductiveModels.tightTowerTy`], which
at one field *is* that field's type and therefore *is* `field .identity`'s
carrier — and then says which fibre of the family that storage sits in. What
distinguishes the cases is the index telescope, not the storage, which is why
they are one route with three shapes rather than separate arms. -/
inductive DirectRoute
  | field (route : DirectFieldRoute)
  | tight
  | indexed

end InductiveModels
