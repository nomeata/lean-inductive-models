import InductiveModels.Simple.Tuple

open Lean Meta

namespace InductiveModels

/-! ## The carve arm's index erasure

The skeleton the carve arm splices is the declaration with its indices dropped: the
carrier loses its index telescope and every recursive field and every
constructor's conclusion loses its index arguments. Nothing else moves except
that a field whose only owner mention βζ-disappears is stored at its reduct;
[`InductiveModels.erasureFieldDomain`] is that one internal exception. Public types
remain literal. This is the whole reason this arm has no currying glue where
the tree route has one lemma per constructor.

Both functions below are **raw `Expr` surgery on de Bruijn indices and not a
telescope walk**, and that is forced rather than stylistic: opening a telescope
means `withLocalDecl` at a type mentioning `T._model.skel`, which `MetaM` would
have to `inferType`, and the constant does not exist yet — it is the one being
declared. Asking for it costs an `Unknown constant` and exit 3. -/

/-- `∀ p⃗, Sort w` from the declaration's `∀ p⃗ ι⃗, Sort w`. -/
partial def eraseSelfTy (np : Nat) (w : Level) (e : Expr) : Expr :=
  if np == 0 then .sort w else
  match e with
  | .forallE x d b bi => .forallE x d (eraseSelfTy (np - 1) w b) bi
  | _ => .sort w

/-- One constructor's type with its indices erased. After `np` parameters and
`i` field binders the parameter `p_k` sits at de Bruijn index `np-1-k+i`, which
is what `skelAt` rebuilds `T._model.skel p⃗` from.

A field is recursive exactly when it mentions `tname`, and `erasureBare` has
already established that the occurrence is a bare `T p⃗ e⃗` **under a possibly
empty binder telescope of its own** — so replacing the occurrence and keeping
the binders is right, and a field this would corrupt has been declined.
**Once per such field and no cap on how many**: a branching constructor erases
exactly as a linear one does, which is why the carve arm is gated on bareness alone.

`eraseOcc` is where the infinitary field is carried. `∀ z⃗, T p⃗ e⃗` erases to
`∀ z⃗, S p⃗` — the binder types are kept from the field's head-normal form.
They may mention the parameters and the constructor's earlier non-recursive
fields, neither of which moves, and each binder crossed pushes the parameters
one index further out, which is what its `d` counts. At zero binders it is the
whole-domain replacement this function has always done, byte for byte. -/
partial def eraseCtorTy (tname skelN : Name) (us : List Level) (np : Nat) (e : Expr) : Expr :=
  let skelAt := fun (d : Nat) => mkAppN (.const skelN us)
    ((Array.range np).map fun k => Expr.bvar (np - 1 - k + d))
  let rec eraseOcc (d : Nat) (t : Expr) : Expr :=
    match t with
    | .forallE x z b bi => .forallE x z (eraseOcc (d + 1) b) bi
    | _ => skelAt d
  let rec fields (i : Nat) (t : Expr) : Expr :=
    match t with
    | .forallE x dom b bi =>
      let dom := erasureFieldDomain tname dom
      .forallE x (if mentionsAny #[tname] dom then eraseOcc i dom else dom) (fields (i + 1) b) bi
    | _ => skelAt i
  let rec params (k : Nat) (t : Expr) : Expr :=
    if k == np then fields 0 t else
    match t with
    | .forallE x dom b bi => .forallE x dom (params (k + 1) b) bi
    | _ => fields 0 t
  params 0 e

/-- **A recursive slot, opened.** A recursive field's type is `∀ z⃗, T p⃗ e⃗`
with `z⃗` possibly empty; this opens the `z⃗` as local declarations and hands
the continuation them and the child's index arguments `e⃗`, which may mention
them. Everything the carve arm builds per slot — the `good` clause, the constructor's
component, the recursor's induction hypothesis — is a `mkLambdaFVars zs` or a
`mkForallFVars zs` around what the continuation returns, and at `zs = #[]` each
of them is the term the bare case built before this existed.

**Read through [`InductiveModels.headNorm`]**, exactly as `erasureBareWhy`,
[`InductiveModels.eraseCtorTy`], [`InductiveModels.spineSwap`] and [`InductiveModels.swapOcc`] read
it: the guard and every internal consumer must agree about how many binders a
field has and what its index vector is. A domain that arrives as a redex has
neither until it is reduced; only the internal skeleton sees that reduction,
while the public declaration remains literal.

Not a decline path in practice: every refusal it can make, `erasureBareWhy`
has already made before the arm was entered. It is stated rather than
`unreachable!` because the two walks are separate code. -/
partial def withRecSlot [Inhabited α] (tname : Name) (np ni : Nat) (dom : Expr)
    (k : Array Expr → Array Expr → GenM α) (zs : Array Expr := #[]) : GenM α := do
  match headNorm dom with
  | .forallE x z b bi =>
    withLocalDecl x bi z fun zv =>
      withRecSlot tname np ni (b.instantiate1 zv) k (zs.push zv)
  | h =>
    let some args ← ownerAppArgs? tname np ni h
      | badShape s!"a recursive field of {tname} is not a bare application at {np} \
          parameters and {ni} indices"
    k zs (args.extract np args.size)

end InductiveModels
