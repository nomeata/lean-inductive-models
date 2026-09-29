/- **Constructor fields whose types are small as DAGs and astronomically large
   as trees**, on ordinary non-mutual inductives — the owners the Simple route
   models.

   This is the shape the Lean Kernel Arena's `navier-stokes-euler` export
   exposed: `EulerMeanVariationalInverse.StrongMeanEvolution` is a structure
   with nine parameters and thirteen fields whose constructor type is 1,481
   expression nodes with maximal sharing and 188,635,673 as a tree. A
   traversal that forgets sharing even once — a rebuild, a fold, a size, a
   hash, a comparison without a memo — pays for the tree, and there it was
   tens of gigabytes.

   The towers here are deeper than any real declaration: depth 60, so every
   tower is about 2^60 nodes as a tree and a few hundred as a DAG. Nothing
   that expands one can finish, so these owners are a gate on *every*
   traversal of their declarations, not a benchmark.

   * `tt k A` — a **type** tower over `A : Type`: `tt 0 A = A`,
     `tt (k+1) A = KT (tt k A) (tt k A)`, `KT = fun (P Q : Type) => P`.
     Defeq to `A`, so a field `d : tt 60 α` is an ordinary data field of type
     `α`.
   * `vt k T a` — a **term** tower in `T`: `vt 0 T a = a`,
     `vt (k+1) T a = KV (vt k T a) (vt k T a)`, `KV = fun (p q : T) => p`.
     Defeq to `a`.

   Every tower is **open**: it is built over a parameter or an earlier field,
   so it has loose bound variables inside the constructor's telescope, and a
   walk cannot stop at the first closed subterm.

   The owners, one per shape the Simple route distinguishes:

   * `TowerFields` — structure-like, two parameters, five fields: a type
     tower as a data field's type, a term tower in a `Prop` field over a
     parameter, one over an earlier field, and a type tower as a function
     field's domain. This is the `StrongMeanEvolution` shape.
   * `TowerSum` — two constructors, each carrying a tower.
   * `TowerList` — recursive, a tower field beside the recursive one.
   * `TowerIdx` — indexed, with the tower in the **index** of the
     constructor's result type.
   * `TowerProp` — a proposition whose one field carries a tower.
   * `TowerProd` — a data field whose type is the **`Prod`** tower `pt 60 α`
     (`pt (k+1) α = pt k α × pt k α`), the shape of the instance towers in
     `StrongMeanEvolution`: an inductive former applied to itself, which no
     reduction makes smaller. Its projection `TowerProd.pair` is exported
     too, as the `structure` command would write it — a definition whose
     value is `Expr.proj` — with the tower in its type. (The `structure`
     command itself does not finish elaborating a depth-60 tower.)
   * `TowerArrow`, `TowerArrowProp` — a field whose type is the **arrow**
     tower `at 60 α` (`at (k+1) α = at k α → at k α`), in `Type` and in
     `Prop`. A `Π` is not a redex, so nothing that reduces the field type makes
     it smaller; every walk that descends into both a binder's domain and its
     body — type inference, sort computation, boxing — meets the whole tower.

   **Lean's elaborator cannot write these.** Surface syntax would have to
   spell the tree. The declarations are built with sharing in `MetaM` and
   added with `addDecl`; the kernel accepts them (Lean's kernel caches every
   traversal it makes) and generates the recursors, and lean4export writes the
   DAG with one table entry per distinct subterm. -/
import Lean

open Lean Meta

--#export Eq Nat TowerFields TowerSum TowerList TowerIdx TowerProp TowerArrow TowerArrowProp TowerProd TowerProd.pair

namespace DagTowers

def depth : Nat := 60

/-- `fun (P Q : T) => P`. -/
def kFirst (T : Expr) : Expr :=
  .lam `P T (.lam `Q T (.bvar 1) .default) .default

/-- `K (t k) (t k)`, iterated, with both arguments the *same* object. -/
def tower (K base : Expr) : Nat → Expr
  | 0 => base
  | k + 1 => let t := tower K base k; mkApp2 K t t

/-- The type tower over `A : Type`. -/
def tt (A : Expr) : Expr := tower (kFirst (.sort 1)) A depth

/-- The term tower in `T` over `a : T`. -/
def vt (T a : Expr) : Expr := tower (kFirst T) a depth

/-- The `Prod` tower over `A : Type`: `pt 0 A = A`, `pt (k+1) A = pt k A × pt k A`. -/
def prods (A : Expr) : Nat → Expr
  | 0 => A
  | k + 1 => let t := prods A k; mkApp2 (.const ``Prod [0, 0]) t t

/-- The arrow tower over `A`: `at 0 A = A`, `at (k+1) A = at k A → at k A`.
Not a redex anywhere: a `Π` whose domain and body are the same object. -/
def arrows (A : Expr) : Nat → Expr
  | 0 => A
  | k + 1 => let t := arrows A k; .forallE `x t t .default

def nat : Expr := .const ``Nat []
def natZero : Expr := .const ``Nat.zero []
def eqAt (T a b : Expr) : Expr := mkApp3 (.const ``Eq [1]) T a b
def eqProp (a b : Expr) : Expr := mkApp3 (.const ``Eq [1]) (.sort 0) a b

def addBlock (types : List InductiveType) (numParams : Nat) : MetaM Unit :=
  addDecl <| .inductDecl [] numParams types false

run_meta do
  -- TowerFields (α : Type) (a : α) : Type
  let tyFields ← withLocalDeclD `α (.sort 1) fun α => withLocalDeclD `a α fun a => do
    mkForallFVars #[α, a] (.sort 1)
  let mkFields ← withLocalDeclD `α (.sort 1) fun α => withLocalDeclD `a α fun a => do
    withLocalDeclD `x nat fun x =>
    withLocalDeclD `d (tt α) fun d =>
    withLocalDeclD `h (eqAt α (vt α a) a) fun h =>
    withLocalDeclD `e (eqAt nat (vt nat x) natZero) fun e => do
    withLocalDeclD `f (← mkArrow (tt α) nat) fun f =>
      mkForallFVars #[α, a, x, d, h, e, f] (mkApp2 (.const `TowerFields []) α a)
  addBlock [{ name := `TowerFields, type := tyFields,
              ctors := [{ name := `TowerFields.mk, type := mkFields }] }] 2

  -- TowerSum (α : Type) : Type
  let tySum ← withLocalDeclD `α (.sort 1) fun α => mkForallFVars #[α] (.sort 1)
  let inl ← withLocalDeclD `α (.sort 1) fun α =>
    withLocalDeclD `x nat fun x =>
    withLocalDeclD `e (eqAt nat (vt nat x) natZero) fun e =>
      mkForallFVars #[α, x, e] (mkApp (.const `TowerSum []) α)
  let inr ← withLocalDeclD `α (.sort 1) fun α =>
    withLocalDeclD `d (tt α) fun d =>
      mkForallFVars #[α, d] (mkApp (.const `TowerSum []) α)
  addBlock [{ name := `TowerSum, type := tySum,
              ctors := [{ name := `TowerSum.inl, type := inl },
                        { name := `TowerSum.inr, type := inr }] }] 1

  -- TowerList : Type
  let list : Expr := .const `TowerList []
  let cons ← withLocalDeclD `x nat fun x =>
    withLocalDeclD `e (eqAt nat (vt nat x) natZero) fun e =>
    withLocalDeclD `tl list fun tl =>
      mkForallFVars #[x, e, tl] list
  addBlock [{ name := `TowerList, type := .sort 1,
              ctors := [{ name := `TowerList.nil, type := list },
                        { name := `TowerList.cons, type := cons }] }] 0

  -- TowerIdx : Nat → Type
  let idx : Expr := .const `TowerIdx []
  let idxMk ← withLocalDeclD `x nat fun x =>
    withLocalDeclD `e (eqAt nat (vt nat x) natZero) fun e =>
      mkForallFVars #[x, e] (mkApp idx (vt nat x))
  let tyIdx ← mkArrow nat (.sort 1)
  addBlock [{ name := `TowerIdx, type := tyIdx,
              ctors := [{ name := `TowerIdx.mk, type := idxMk }] }] 0

  -- TowerProp (p : Prop) : Prop
  let tyProp ← withLocalDeclD `p (.sort 0) fun p => mkForallFVars #[p] (.sort 0)
  let propMk ← withLocalDeclD `p (.sort 0) fun p =>
    withLocalDeclD `h (eqProp (vt (.sort 0) p) p) fun h =>
      mkForallFVars #[p, h] (mkApp (.const `TowerProp []) p)
  addBlock [{ name := `TowerProp, type := tyProp,
              ctors := [{ name := `TowerProp.mk, type := propMk }] }] 1

run_meta do
  -- TowerArrow (α : Type) : Type
  let tyArrow ← withLocalDeclD `α (.sort 1) fun α => mkForallFVars #[α] (.sort 1)
  let arrowMk ← withLocalDeclD `α (.sort 1) fun α =>
    withLocalDeclD `f (arrows α depth) fun f =>
      mkForallFVars #[α, f] (mkApp (.const `TowerArrow []) α)
  addBlock [{ name := `TowerArrow, type := tyArrow,
              ctors := [{ name := `TowerArrow.mk, type := arrowMk }] }] 1

  -- TowerArrowProp : Prop
  let arrowPropMk ← withLocalDeclD `h (arrows (eqAt nat natZero natZero) depth) fun h =>
    mkForallFVars #[h] (.const `TowerArrowProp [])
  addBlock [{ name := `TowerArrowProp, type := .sort 0,
              ctors := [{ name := `TowerArrowProp.mk, type := arrowPropMk }] }] 0

run_meta do
  -- TowerProd (α : Type) : Type
  let tyP ← withLocalDeclD `α (.sort 1) fun α => mkForallFVars #[α] (.sort 1)
  let prodMk ← withLocalDeclD `α (.sort 1) fun α =>
    withLocalDeclD `p (prods α depth) fun p =>
    withLocalDeclD `n nat fun n =>
      mkForallFVars #[α, p, n] (mkApp (.const `TowerProd []) α)
  addBlock [{ name := `TowerProd, type := tyP,
              ctors := [{ name := `TowerProd.mk, type := prodMk }] }] 1
  -- TowerProd.pair (α : Type) (self : TowerProd α) : pt 60 α := self.1
  let pairTy ← withLocalDeclD `α (.sort 1) fun α =>
    withLocalDeclD `self (mkApp (.const `TowerProd []) α) fun self =>
      mkForallFVars #[α, self] (prods α depth)
  let pairVal ← withLocalDeclD `α (.sort 1) fun α =>
    withLocalDeclD `self (mkApp (.const `TowerProd []) α) fun self =>
      mkLambdaFVars #[α, self] (.proj `TowerProd 0 self)
  let pair : DefinitionVal :=
    { name := `TowerProd.pair, levelParams := [], type := pairTy, value := pairVal,
      hints := .abbrev, safety := .safe }
  addDecl (.defnDecl pair)

end DagTowers
