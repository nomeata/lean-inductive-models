import Lean

/-!
# `Eq`, `Eq.refl` and `Eq.rec` as name-and-`Expr` plumbing

[`InductiveModels.EqInfo`] is the one record every construction in this package
carries so that it can write an equation, a reflexivity proof and a transport
without hard-coding `` `Eq ``: the input's own three constants where it has
them, and Lean's spliced in where it does not (see
[`InductiveModels.ensureEq`]).

**This module deliberately depends on nothing but `Lean`.** `EqInfo` is a triple
of `Name`s and four builders over `Expr`; the only environment it ever reads is
the one handed to [`InductiveModels.EqInfo.check`], and it reads that one to
decide whether the three constants have Lean's shape. Nothing here is in a
generator monad and nothing here installs a declaration.

That isolation is the point rather than a coincidence.
`src/InductiveModels/Projection.lean`, and through it the independent structural
checker `src/InductiveModels/Check.lean`, need exactly this much of the
equality interface and none of the generator behind it — the checker's verdict
is supposed to be reachable without the construction it checks, and an import
of the nested generator would quietly make that false.
`test/scripts/check-checker-imports.sh` holds the separation down.
-/

open Lean

namespace InductiveModels

/-- `Eq`, `Eq.refl` and `Eq.rec` at the arities the round trips need. The
input's own where it has them, and Lean's spliced in where it does not — see
[`InductiveModels.ensureEq`]. -/
structure EqInfo where
  eqN : Name
  reflN : Name
  recN : Name
  deriving Inhabited

/-- Read the three constants and check the recursor is Lean's shape:
`Eq.rec α a motive base b h`, two parameters and one index. The error says
*which* of them is wrong, because a reason that names where a value stopped
rather than why is the defect class this repository has paid for most. -/
def EqInfo.check (env : Environment) : Except String EqInfo := do
  let eq := `Eq
  let some (.inductInfo iv) := env.constants.find? eq | throw "it is not an inductive type"
  unless iv.numParams == 2 && iv.numIndices == 1 && iv.ctors.length == 1 do
    throw s!"it has {iv.numParams} parameters, {iv.numIndices} indices and \
      {iv.ctors.length} constructors, where Lean's has 2, 1 and 1"
  let rc := Name.str eq "rec"
  let some (.recInfo rv) := env.constants.find? rc | throw "Eq.rec is not a recursor"
  unless rv.numParams == 2 && rv.numMotives == 1 && rv.numMinors == 1 && rv.numIndices == 1 do
    throw s!"Eq.rec has {rv.numParams} parameters, {rv.numMotives} motives, {rv.numMinors} \
      minors and {rv.numIndices} indices, where Lean's has 2, 1, 1 and 1"
  let rf := Name.str eq "refl"
  unless env.constants.contains rf do throw "Eq.refl is not declared"
  return { eqN := eq, reflN := rf, recN := rc }

/-- `Eq.{u} α a b`. -/
def EqInfo.mk' (e : EqInfo) (u : Level) (α a b : Expr) : Expr :=
  mkAppN (.const e.eqN [u]) #[α, a, b]

/-- `Eq.refl.{u} α a`. -/
def EqInfo.refl' (e : EqInfo) (u : Level) (α a : Expr) : Expr :=
  mkAppN (.const e.reflN [u]) #[α, a]

/-- `Eq.rec.{v,u} α a motive base b h`. The motive sits at `Prop` wherever an
*equation* is transported and at the eliminator's own universe wherever a
*value* is; each caller passes `v` explicitly for that reason. -/
def EqInfo.recAt (e : EqInfo) (v u : Level) (α a motive base b h : Expr) : Expr :=
  mkAppN (.const e.recN [v, u]) #[α, a, motive, base, b, h]

end InductiveModels
