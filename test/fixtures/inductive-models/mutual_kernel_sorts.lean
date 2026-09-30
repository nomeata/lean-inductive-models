/- **Mutual blocks whose sorts the kernel reads differently from their syntax.**

   Three questions about a member's sort, each of which the construction once
   answered from the written term rather than the way Lean's kernel answers it.

   * **A sort behind a definition.** The kernel whnf's an inductive's type while
     it reads the parameter and index telescope and the result, so a member may
     be declared at `MyType` or at `MyFam`, definitions that unfold to a sort or
     to an index telescope ending in one. `DA`/`DB` is recursive, unindexed and
     never-`Prop`, so it takes the mutual one-layer adapter; `FA`/`FB` is
     indexed behind its definition, so it takes the tag-and-family encoding.
     `IrrType` is irreducible: the kernel unfolds it all the same.

   * **`Sort (max 0 0)` is not `Prop` to the kernel's projection rule.**
     `infer_proj` asks whether a type's type is *literally* `Sort 0`, so the
     field `b : PB` of the `Prop` owner `PA` is not a proof, and `PA` has no
     intrinsic projection. The elaborator would call `PB` a proposition.

   * **A kernel projection the recursor cannot reach.** `NC`/`ND` sit at a bare
     `Sort u`, so the block is mutual at a maybe-zero sort and its recursors
     eliminate only into `Prop` — while `infer_proj`, seeing a sort that is not
     literally `Prop`, grants `NC` a projection onto `ND`. No construction here
     selects data from such a carrier, and the block declines, out of scope.

   The last three blocks are added through `addDecl`, the kernel an export is
   a transcript of: the elaborator cannot even state `x : IA` at an
   irreducible sort, refuses a maybe-zero resulting universe, and a raw
   `Sort (max 0 0)` is simplest to write as a term. `IA` is exported directly
   for the first reason. -/
import Lean

open Lean

def MyType : Type 1 := Type

mutual
inductive DA : MyType where
  | leaf : DA
  | node : DB → DA
inductive DB : MyType where
  | node : DA → DB
end

def MyFam : Type 1 := Nat → Type

mutual
inductive FA : MyFam where
  | zero : FA 0
  | succ : FB n → FA (n + 1)
inductive FB : MyFam where
  | zero : FB 0
  | succ : FA n → FB (n + 1)
end

@[irreducible] def IrrType : Type 1 := Type

run_cmd Elab.Command.liftCoreM do
  let ia := Expr.const `IA []
  let ib := Expr.const `IB []
  addDecl <| .inductDecl [] 0 [
    { name := `IA, type := .const `IrrType [],
      ctors := [{ name := `IA.leaf, type := ia }, { name := `IA.node, type := .forallE `b ib ia .default }] },
    { name := `IB, type := .const `IrrType [],
      ctors := [{ name := `IB.node, type := .forallE `a ia ib .default }] }] false
  let pa := Expr.const `PA []
  let pb := Expr.const `PB []
  addDecl <| .inductDecl [] 0 [
    { name := `PA, type := .sort .zero,
      ctors := [{ name := `PA.mk, type := .forallE `b pb pa .default }] },
    { name := `PB, type := .sort (.max .zero .zero),
      ctors := [{ name := `PB.mk, type := .forallE `a pa pb .default },
        { name := `PB.triv, type := pb }] }] false
  let u := Level.param `u
  let nc := Expr.const `NC [u]
  let nd := Expr.const `ND [u]
  addDecl <| .inductDecl [`u] 0 [
    { name := `NC, type := .sort u,
      ctors := [{ name := `NC.mk, type := .forallE `d nd nc .default }] },
    { name := `ND, type := .sort u,
      ctors := [{ name := `ND.nil, type := nd }, { name := `ND.cons, type := .forallE `c nc nd .default }] }] false

theorem DA.self (x : DA) : x = x := rfl
theorem FA.self (x : FA 0) : x = x := rfl
theorem PB.self (x : PB) : x = x := rfl
theorem NC.self.{u} (x : NC.{u}) : x = x := rfl

--#export DA.self FA.self IA PB.self NC.self
