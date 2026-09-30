/- **Owners whose parameters, indices or sort sit behind a definition.**

   Lean's kernel does not read an inductive's type as written. `add_inductive`
   whnf's the type, peels a `Π`, and whnf's again until a `Sort` is left: the
   binders it peeled are the parameters and then the indices, and the sort is
   the block's. So `inductive SF : MyFam` with `def MyFam := Nat → Type` is an
   indexed family with one index, and its recursor, `numIndices` and every
   constructor say so, while the type as written has no binder at all.

   The construction reads every owner through `InductiveModels.kernelFormer`
   (the kernel's own whnf, step by step) and the statement checker through
   `ExactNormalizationEnv.kernelFormer?` (the export's bounded normaliser, the
   same steps); `T._model` still restates the declared type. `SF` used to stop
   with "SF._model's public type does not open as 1 written binders", in the
   projection builder and again in the statement checker.

   The kernel's nested-inductive pre-pass reads the *first* member's
   parameters syntactically (`get_params`), so no accepted block hides those;
   a later member's parameters, and every index and sort, may be hidden.

   Single member, by route:
   * `SF` — the reported shape: one constructor, one index behind `MyFam`;
     it takes the indexed fibre one-layer adapter exactly as `Nat → Type`
     would. `PI` adds a written parameter, `NF` two indices through two
     definitions (`MyFam2 := Nat → MyFam`), `PW` one index written and one
     hidden, `DF` a dependent index telescope, `LB` a β-redex head, `IRF` an
     irreducible definition (added through `addDecl`, since the elaborator
     does not unfold it).
   * `IF` — recursive and indexed (carve arm); `EF`/`ET` empty; `UF` a
     one-constructor indexed family with no fields.
   * `Ev`/`SP` — propositions behind `MyPred`; `SP` has a proof projection.
   * `STy`, `SS`, `CS`, `IRS` — structures at a sort behind one, two, and an
     irreducible definition: projections and η. `LTy` is a list-like at
     `MyType`. `PS` is a proposition behind `MyProp` whose proof field is
     projectable and whose data field is not. `UIP` is unit-like at an
     irreducible `Prop`.

   Nested: `NT` at `MyType`, `NI` indexed behind `MyFam`, `NB` nested through
   a container `Box` whose own index is behind `MyFam`.

   Mutual: `MA`/`MB` single-constructor members indexed behind `MyFam`;
   `PMA`/`PMB`, where `PMB`'s parameter is behind `PT := Type → Type`; and
   `QA`/`QB`, where `QB`'s parameter and index are behind `PIT`.

   A type former that reaches its sort only by ι or a projection is not here:
   the statement checker cannot restate it, and the run stops;
   `test/fixtures/unverifiable/defhead_beyond_delta.lean` pins that.
-/
import Lean

open Lean

def MyFam : Type 1 := Nat → Type
def MyType : Type 1 := Type
def MyType2 : Type 1 := MyType
def MyProp : Type := Prop
def MyPred : Type := Nat → Prop
def MyFam2 : Type 1 := Nat → MyFam
@[irreducible] def IrrFam : Type 1 := Nat → Type
@[irreducible] def IrrType : Type 1 := Type
@[irreducible] def IrrProp : Type := Prop
def PT : Type 1 := Type → Type
def PIT : Type 1 := Type → Nat → Type
def DepFam : Type 1 := (n : Nat) → n = n → Type

inductive SF : MyFam where
  | mk : Nat → SF 0

inductive IF : MyFam where
  | z : IF 0
  | s : IF n → IF (n + 1)

inductive PI (α : Type) : MyFam where
  | mk : α → PI α 0

inductive NF : MyFam2 where
  | mk : Nat → NF 0 1

inductive PW : Nat → MyFam where
  | mk : Nat → PW 1 2

inductive DF : DepFam where
  | mk : Bool → DF 0 rfl

inductive LB : (fun x => x) (Nat → Type) where
  | mk : Nat → LB 3

inductive STy : MyType where
  | mk : Nat → Bool → STy

inductive LTy : MyType where
  | nil
  | cons : Nat → LTy → LTy

inductive EF : MyFam

inductive ET : MyType

inductive UF : MyFam where
  | u : UF 0

inductive Ev : MyPred where
  | z : Ev 0
  | ss : Ev n → Ev (n + 2)

inductive SP : MyPred where
  | mk : True → SP 0

inductive PS : MyProp where
  | mk : Nat → True → PS

inductive NT : MyType where
  | mk : List NT → NT

inductive NI : MyFam where
  | leaf : NI 0
  | mk : List (NI 0) → NI 1

inductive Box (α : Type) : MyFam where
  | mk : α → Box α 0

inductive NB where
  | leaf
  | mk : Box NB 0 → NB

mutual
inductive MA : MyFam where
  | mk : Nat → MA 0
inductive MB : MyFam where
  | mk : MA 0 → MB 1
end

structure SS (α : Type) : MyType where
  x : α
  y : Nat

structure CS : MyType2 where
  x : Nat

run_cmd Elab.Command.liftCoreM do
  let nat := Expr.const ``Nat []
  -- an index behind an irreducible definition
  let irf := Expr.const `IRF []
  addDecl <| .inductDecl [] 0 [
    { name := `IRF, type := .const `IrrFam [],
      ctors := [{ name := `IRF.mk, type := .forallE `n nat (.app irf (mkNatLit 0)) .default }] }] false
  -- a structure at an irreducible sort
  let irs := Expr.const `IRS []
  let irsMk := Expr.forallE `n nat (.forallE `b (.const ``Bool []) irs .default) .default
  addDecl <| .inductDecl [] 0 [
    { name := `IRS, type := .const `IrrType [],
      ctors := [{ name := `IRS.mk, type := irsMk }] }] false
  -- unit-like at an irreducible `Prop`
  addDecl <| .inductDecl [] 0 [
    { name := `UIP, type := .const `IrrProp [],
      ctors := [{ name := `UIP.u, type := .const `UIP [] }] }] false
  -- a mutual block whose second member's parameter is behind `PT`
  let ty := Expr.sort 1
  let pma := Expr.const `PMA []
  let pmb := Expr.const `PMB []
  let pmaLeaf := Expr.forallE `α ty (.app pma (.bvar 0)) .default
  let pmaNode := Expr.forallE `α ty (.forallE `b (.app pmb (.bvar 0)) (.app pma (.bvar 1)) .default) .default
  let pmbNode := Expr.forallE `α ty (.forallE `a (.app pma (.bvar 0)) (.app pmb (.bvar 1)) .default) .default
  addDecl <| .inductDecl [] 1 [
    { name := `PMA, type := .forallE `α ty ty .default,
      ctors := [{ name := `PMA.leaf, type := pmaLeaf }, { name := `PMA.node, type := pmaNode }] },
    { name := `PMB, type := .const `PT [],
      ctors := [{ name := `PMB.node, type := pmbNode }] }] false
  -- an indexed mutual block whose second member's parameter and index are
  -- behind `PIT`
  let qa := Expr.const `QA []
  let qb := Expr.const `QB []
  let succ := fun (e : Expr) => mkApp (.const ``Nat.succ []) e
  let qaNil := Expr.forallE `α ty (mkApp2 qa (.bvar 0) (mkNatLit 0)) .default
  let qaCons := Expr.forallE `α ty (.forallE `n nat (.forallE `a (.bvar 1)
    (.forallE `t (mkApp2 qb (.bvar 2) (.bvar 1)) (mkApp2 qa (.bvar 3) (succ (.bvar 2))) .default)
    .default) .default) .default
  let qbCons := Expr.forallE `α ty (.forallE `n nat
    (.forallE `t (mkApp2 qa (.bvar 1) (.bvar 0)) (mkApp2 qb (.bvar 2) (succ (.bvar 1))) .default)
    .default) .default
  addDecl <| .inductDecl [] 1 [
    { name := `QA, type := .forallE `α ty (.forallE `n nat ty .default) .default,
      ctors := [{ name := `QA.nil, type := qaNil }, { name := `QA.cons, type := qaCons }] },
    { name := `QB, type := .const `PIT [],
      ctors := [{ name := `QB.cons, type := qbCons }] }] false

--#export SF IF PI NF PW DF LB STy LTy EF ET UF Ev SP PS NT NI NB MA SS CS IRF IRS UIP PMA QA
