import Lean
import Modelgen.Format

/-!
# Specialising a nested inductive into a mutual block

`inductive Tree | leaf | node : List Tree → Tree` becomes the ordinary mutual
block

```text
Tree            : Type          Tree._nested.1      : Type
  leaf : Tree                     nil  : Tree._nested.1
  node : Tree._nested.1 → Tree    cons : Tree → Tree._nested.1 → Tree._nested.1
```

with one **mimic** per distinct nested occurrence. This module is purely
syntactic: it rewrites constructor types and never asks a checker anything.

Two invariants are particularly important:

* An occurrence is stored **at the block's own parameter telescope depth** —
  its only loose bound variables are the block's parameters. Every use
  instantiates it with the parameter `fvar`s in scope, so no shift is ever
  written at a use site.
* Mimics are discovered **breadth first**, because that is the order Lean
  numbers the motives of the nested recursors in: `DTree.node : List (List
  DTree) → DTree` yields `List (List DTree)` from the declaration and `List
  DTree` from *that copy's* `cons`, and the export's `rec_1` / `rec_2` are in
  exactly that order.

The declared block may itself be **mutual**, and then every member is
specialised into the same block: `mutual inductive A | mk : List B → A …;
inductive B | mk : Box A → B … end` becomes the four-member block `A`, `B`,
`List B`, `Box A`. A nested container may be mutual too: discovering `C α`
adds every member of `C`'s mutual block at `α` immediately, in `all` order.
The sweep is over the declared members and then breadth first over those mimic
families, which is Lean's own motive order — measured against
`test/fixtures/modelgen/nest_mutual_both.ndjson` and the mutual-container
closure in `test/fixtures/modelgen/hard_nested_mutual_index.ndjson`.
-/

open Lean

namespace Modelgen

/-- The last component of a name, as a string. -/
def lastStr : Name → String
  | .str _ s => s
  | n => toString n

/-- One specialised copy of a container — Lean 3 called it the *mimic*. -/
structure Mimic where
  /-- The fresh block member, e.g. `Tree._nested.1`. -/
  name : Name
  /-- The container applied to the parameters the occurrence uses, at the
  block's parameter telescope depth. -/
  occ : Expr
  /-- `(the copy's constructor, the real constructor at those parameters)`. -/
  ctors : Array (Name × Expr)
  deriving Inhabited

/-- One member of the specialised block. -/
structure PType where
  name : Name
  type : Expr
  ctors : Array (Name × Expr)
  deriving Inhabited

/-- The specialised block, and everything needed to restore it. -/
structure Plan where
  /-- Members `0 … numAll−1` are the declared block's own, in the export's `all`
  order; members `numAll …` are the mimics, in discovery order. **That is Lean's
  own motive order**, measured on
  `test/fixtures/modelgen/nest_mutual_both.ndjson`:
  `A`, `B`, `List B`, `Box A`. -/
  types : Array PType
  /-- How many of `types` are the export's own members. `1` unless the
  declaration is a mutual block. -/
  numAll : Nat
  mimics : Array Mimic
  /-- The block's parameter binder types, outermost first. -/
  paramTys : Array Expr
  deriving Inhabited

/-- Does `e` mention any of `ns` as a constant head? -/
def mentionsAny (ns : Array Name) (e : Expr) : Bool :=
  Option.isSome <| e.find? fun s => match s with
    | .const n _ => ns.contains n
    | _ => false

/-- Does `e` mention `n`? -/
def mentions (n : Name) (e : Expr) : Bool := mentionsAny #[n] e

private structure SpState where
  members : Array Name
  mimics : Array Mimic

private structure SpCtx where
  env : Environment
  numParams : Nat
  us : List Level
  root : Name
  paramTys : Array Expr

private abbrev SpM := ReaderT SpCtx (StateT SpState (Except String))

/-- Peel `n` `∀` binders, collecting their types. -/
def peelParams (ty : Expr) (n : Nat) : Except String (Array Expr) := do
  let mut out := #[]
  let mut cur := ty
  for _ in [0:n] do
    match cur with
    | .forallE _ t b _ => out := out.push t; cur := b
    | _ => throw "inductive type has fewer binders than parameters"
  return out

/-- Wrap `body` in the block's parameter telescope. -/
def wrapParams (ps : Array Expr) (body : Expr) : Expr :=
  ps.foldr (fun t b => .forallE `p t b .default) body

/-- Peel `args.size` binders and substitute, leaving the residual type. -/
private def atParams (ty : Expr) (args : Array Expr) : Except String Expr := do
  let mut cur := ty
  for a in args do
    match cur with
    | .forallE _ _ b _ => cur := b.instantiate1 a
    | _ => throw "container type has too few parameters"
  return cur

/-- `some p` when `c` is an inductive **outside** the block applied to at least
its `p` parameters. Nesting happens in a container's parameters and nowhere
else, so the occurrence is the container at its parameters and any indices ride
outside it. -/
private def containerArity (c : Name) (nargs : Nat) : SpM (Option Nat) := do
  let ctx ← read
  let st ← get
  if st.members.contains c then return none
  let some (.inductInfo v) := ctx.env.constants.find? c | return none
  if nargs ≥ v.numParams then return some v.numParams else return none

/-- The mimic for `occ`, created if this is the first sighting. `occ` arrives at
depth `d`; the record keeps it at the parameter telescope's depth. -/
private def mimicFor (occ : Expr) (c : Name) (ls : List Level) (d : Nat) : SpM Name := do
  let ctx ← read
  let k := d - ctx.numParams
  for i in [0:k] do
    if occ.hasLooseBVar i then
      throw s!"a nested occurrence in {ctx.root} depends on a constructor field"
  let occ := occ.lowerLooseBVars k k
  let st ← get
  if let some m := st.mimics.find? (fun m => m.occ == occ) then return m.name
  let some (.inductInfo v) := ctx.env.constants.find? c | throw s!"unknown container {c}"
  let occArgs := occ.getAppArgs
  -- Lean closes a nested occurrence over the container's whole mutual block.
  -- Seeing `C α` where `C` and `D` are mutual therefore introduces the
  -- motives for both `C α` and `D α`, in the block's `all` order, before
  -- discovery continues. Adding only the member syntactically present delays
  -- the companion until one of the container constructors happens to expose
  -- it; every motive and minor after that point then has the wrong position.
  --
  -- Mutual members share their parameter telescope, so the occurrence's
  -- parameter arguments and levels instantiate each companion directly. A
  -- companion may already have been discovered through another field; retain
  -- it rather than minting a second copy.
  let mut answer? : Option Name := none
  for family in v.all do
    let some (.inductInfo fv) := ctx.env.constants.find? family
      | throw s!"unknown mutual container member {family}"
    unless fv.numParams == v.numParams do
      throw s!"mutual container members {c} and {family} have different parameter counts"
    let familyOcc := mkAppN (.const family ls) occArgs
    let cur ← get
    let name ← match cur.mimics.find? (fun m => m.occ == familyOcc) with
      | some m => pure m.name
      | none => do
        let idx := cur.mimics.size + 1
        let name := Name.num (Name.str ctx.root "_nested") idx
        if ctx.env.constants.contains name then throw s!"{name} is already declared"
        let cs := fv.ctors.toArray.map fun cn =>
          (Name.str name (lastStr cn), mkAppN (.const cn ls) occArgs)
        set (σ := SpState)
          { members := cur.members.push name, mimics := cur.mimics.push ⟨name, familyOcc, cs⟩ }
        pure name
    if family == c then answer? := some name
  let some answer := answer? | throw s!"{c} is absent from its own mutual block"
  return answer

/-- Specialise one expression at binder depth `d`, which counts *all* binders
opened so far, of which the outermost `numParams` are the block's. -/
private partial def spec (e : Expr) (d : Nat) : SpM Expr := do
  match e with
  | .app .. | .const .. =>
    let h := e.getAppFn
    let args := e.getAppArgs
    if let .const c ls := h then
      if let some np ← containerArity c args.size then
        let occ := mkAppN h (args.extract 0 np)
        let st ← get
        if mentionsAny st.members occ then
          let ctx ← read
          if d < ctx.numParams then
            throw s!"a nested occurrence in {ctx.root} sits inside a parameter"
          let name ← mimicFor occ c ls d
          let ps := (List.range ctx.numParams).toArray.map fun l => Expr.bvar (d - 1 - l)
          let head := mkAppN (.const name ctx.us) ps
          let rest ← (args.extract np args.size).mapM (spec · d)
          return mkAppN head rest
    let args ← args.mapM (spec · d)
    -- **The head too, when it is not a constant.** A container's parameter may
    -- be a *family* — `RBNode α β`'s `β : α → Type` — and then instantiating it
    -- leaves the constructor field as the redex `(fun x => …) k`, whose lambda
    -- body is where the nesting is. `getAppFn` hands back the lambda, so a
    -- sweep over the arguments alone never enters it and an occurrence in
    -- there — `RB N (fun _ => L Deep)`, `RB N (fun k => Vec Idx k)`, both in
    -- `test/fixtures/modelgen/nest_fam_arg.lean` — gets no mimic at all.
    -- Nothing else reaches here with a compound head: a
    -- `bvar`/`fvar`/`sort` head falls through the catch-all unchanged.
    let h ← if h.isConst then pure h else spec h d
    return mkAppN h args
  | .lam n t b bi => return .lam n (← spec t d) (← spec b (d + 1)) bi
  | .forallE n t b bi => return .forallE n (← spec t d) (← spec b (d + 1)) bi
  | .letE n t v b nd => return .letE n (← spec t d) (← spec v d) (← spec b (d + 1)) nd
  | .proj tn i s => return .proj tn i (← spec s d)
  | _ => return e

/-- The mimic's own declaration: the container's type and constructors at the
occurrence's parameters, specialised in turn. -/
private def mimicDecl (m : Mimic) : SpM (Expr × Array (Name × Expr)) := do
  let ctx ← read
  let .const cn cls := m.occ.getAppFn | throw "the occurrence is not headed by a constant"
  let some ci := ctx.env.constants.find? cn | throw s!"unknown container {cn}"
  let occArgs := m.occ.getAppArgs
  -- An *indexed* container whose index types mention a member would otherwise
  -- keep an unspecialised occurrence in a position nothing later rewrites, so
  -- the mimic's own type is specialised too.
  let ty ← atParams (ci.type.instantiateLevelParams ci.levelParams cls) occArgs
  let ty ← spec ty ctx.numParams
  let ty := wrapParams ctx.paramTys ty
  let mut out : Array (Name × Expr) := #[]
  for (mc, real) in m.ctors do
    let .const rc _ := real.getAppFn | throw s!"{mc} has no real constructor"
    let some rci := ctx.env.constants.find? rc | throw s!"unknown constructor {rc}"
    let cty ← atParams (rci.type.instantiateLevelParams rci.levelParams cls) occArgs
    let cty ← spec cty ctx.numParams
    out := out.push (mc, wrapParams ctx.paramTys cty)
  return (ty, out)

/-- **Is this declaration nested, and if so how is it specialised?**

`none` means no constructor mentions the type under a foreign inductive.
`throw` means the declaration *is* nested and this module cannot express it. -/
def plan (env : Environment) (lparams : List Name) (numParams : Nat)
    (types : Array PType) : Except String (Option Plan) := do
  let some root := types[0]? | return none
  let paramTys ← peelParams root.type numParams
  let ctx : SpCtx := {
    env, numParams, root := root.name
    us := lparams.map .param, paramTys }
  let st : SpState := { members := types.map (·.name), mimics := #[] }
  let go : SpM (Array PType) := do
    let mut out : Array PType := #[]
    for t in types do
      let mut cs : Array (Name × Expr) := #[]
      for (cn, cty) in t.ctors do
        cs := cs.push (cn, ← spec cty 0)
      out := out.push { t with ctors := cs }
    -- Indexing rather than iterating: the vector grows inside the loop, and
    -- that growth is the depth-2 case (`DTree`) working.
    let mut k := 0
    repeat
      let st ← get
      if k ≥ st.mimics.size then break
      let m := st.mimics[k]!
      let (ty, cs) ← mimicDecl m
      out := out.push { name := m.name, type := ty, ctors := cs }
      k := k + 1
    return out
  let (out, st') ← (go ctx).run st
  if st'.mimics.isEmpty then return none
  return some { types := out, numAll := types.size, mimics := st'.mimics, paramTys }

end Modelgen
