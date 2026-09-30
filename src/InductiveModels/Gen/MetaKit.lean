import Lean
import InductiveModels.Gen.Monad

/-!
# `MetaM` helpers at the generator's monad

Thin wrappers that lift `Meta` operations into `GenM`, plus the two head
normalisations every construction reads a field's type through. Nothing here
knows what is being generated.
-/

open Lean Meta

namespace InductiveModels
/-- `Meta.inferType`, at the generator's monad. -/
def ityp (e : Expr) : GenM Expr := inferType e

/-- The sort a type lives at. -/
def ilevel (e : Expr) : GenM Level := getLevel e

/-- Zeta-reduce the head of a type. Lean accepts a constructor field whose type
is a `let` — `(n : N) → (let m := n; Vec α m) → Let α` is one — and then the
member the field sits at is not the head of the expression as written. Only
`let` is unfolded and no definition is, so nothing else about the type moves. -/
partial def zetaHead : Expr → Expr
  | .letE _ _ v b _ => zetaHead (b.instantiate1 v)
  | e => e

/-- **A type's head, ζ- *and* β-reduced.** [`InductiveModels.zetaHead`] plus the redex
a container's **family** parameter leaves behind, iterated until neither moves.
Only `let` and β move and no constant is unfolded, so this answers "which
member / which occurrence / which index vector" and changes nothing about what
the type *is*. Every reader below goes through it; see the section on reading a
type's head, at [`InductiveModels.Gen.occIdx?`]. -/
partial def headNorm (e : Expr) : Expr :=
  match e with
  | .letE _ _ v b _ => headNorm (b.instantiate1 v)
  | .app .. => let e' := e.headBeta; if e' == e then e else headNorm e'
  | _ => e

/-- How many leading `∀` binders an expression has, **syntactically**. No
`whnf`: every telescope peeled here is one the export wrote as a literal
`Π`-nest, and unfolding a carrier to find another binder would be a different
question. -/
def numForalls : Expr → Nat
  | .forallE _ _ b _ => numForalls b + 1
  | _ => 0

/-- **Weak head normal form, asked of the kernel.** `Lean.Kernel.whnf` in the
current local context: the reduction the kernel itself performs, so a question
answered through it cannot disagree with the verdict on the emitted island. A
kernel exception is a construction fault, as for
[`InductiveModels.kernelDefEq`]. -/
def kernelWhnf (e : Expr) : MetaM Expr := do
  match Lean.Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok e => return e
  | .error exception =>
    throwError "kernel whnf failed on a construction term: \
      {← (exception.toMessageData {}).toString}\n  term: {e}"

/-- **An inductive's type as the kernel reads it** — the one place the generator
reads an owner's telescope and sort.

The kernel does not read an inductive's type as written. `add_inductive` whnf's
the type, peels a `Π`, and whnf's again, until what is left is a `Sort`; the
binders it peeled are the parameters and then the indices, and that sort is the
block's. So a member may be declared at a definition that unfolds to its sort
(`inductive U : MyType`, `def MyType := Type`), to part or all of its index
telescope (`inductive SF : MyFam`, `def MyFam := Nat → Type`), to a chain of
such definitions, or to an irreducible one — the kernel knows no reducibility —
and the exported `numIndices` and recursor are the ones for the *exposed*
telescope.

This returns that exposed form, `∀ p⃗ i⃗, Sort u` with every binder written
syntactically, by the kernel's own `whnf` at each step. Every construction reads
parameters, indices and sort off it; every **public** declaration still restates
the declared type, which is definitionally equal to it by δβζ. A type that is
already written that way is returned unchanged, without a reduction. The same
reading on the statement checker's side is
[`InductiveModels.ExactNormalizationEnv.readKernelFormer`], with the export's
own head normaliser: δ, β and ζ, and ι and projection steps on literal
constructor applications, with the export's recursor rules. The kernel's
`whnf` can do more — K, structure η, `Nat` literal arithmetic — so
`Driver/Filter.lean` requires the two readings to be the same expression on
every owner the tool models and stops the run before any construction
otherwise; every type that reaches here is one both sides open alike.

Parameters are read here too, although the kernel's nested-inductive pre-pass
requires the *first* member's parameters to be written: every later member of a
block, and every index, may hide behind a definition. -/
partial def kernelFormer (type : Expr) : MetaM Expr := do
  if written type then return type
  go type
where
  written : Expr → Bool
    | .forallE _ _ body _ => written body
    | .sort _ => true
    | _ => false
  go (type : Expr) : MetaM Expr := do
    match ← kernelWhnf type with
    | .forallE x dom body bi =>
      withLocalDecl x bi dom fun xv => do mkForallFVars #[xv] (← go (body.instantiate1 xv))
    | .sort u => return .sort u
    | _ => throwError "an inductive type does not land in a sort, even as the kernel reads it"

/-- The arity and sort of a former in [`InductiveModels.kernelFormer`]'s exposed
form, which always ends in a `Sort`; the last arm is unreachable on it. -/
def formerShape (exposed : Expr) : Nat × Level :=
  go 0 exposed
where
  go (n : Nat) : Expr → Nat × Level
    | .forallE _ _ body _ => go (n + 1) body
    | .sort u => (n, u)
    | _ => (n, .zero)

/-- **The kernel's `is_prop` of an inductive's sort**: its former, read by
[`InductiveModels.kernelFormer`], ends in *literally* `Sort 0`, which is the
question `infer_proj` asks and the one the statement checker's
`ExactNormalizationEnv.isPropositionFormer` answers. `Meta.isPropFormerType`
opens the telescope without unfolding, so `inductive SP : MyPred` with
`def MyPred := Nat → Prop` is not a proposition to it. -/
def kernelFormerIsProp (type : Expr) : MetaM Bool :=
  return (formerShape (← kernelFormer type)).2 == .zero

/-- **A constructor field's type**, with any leading `let` gone. Every place in
this module that asks which member a field sits at reads it through here. -/
def ftyp (e : Expr) : GenM Expr := return zetaHead (← inferType e)

def constInfo (n : Name) : GenM ConstantInfo := do
  let some ci := (← getEnv).constants.find? n | badShape s!"{n} is not declared"
  return ci

/-- The container's constructors. -/
def ctorsOf (c : Name) : GenM (Array Name) := do
  let .inductInfo iv ← constInfo c | badShape s!"{c} is not an inductive"
  return iv.ctors.toArray

/-- How many fields a constructor has. -/
def numFieldsOf (c : Name) : GenM Nat := do
  let .ctorInfo cv ← constInfo c | badShape s!"{c} is not a constructor"
  return cv.numFields

/-- Peel `args.size` `∀` binders, substituting as it goes. -/
def instForall (ty : Expr) (args : Array Expr) : GenM Expr := do
  let mut cur := ty
  for a in args do
    match cur with
    | .forallE _ _ b _ => cur := b.instantiate1 a
    | _ => badShape "too few binders to instantiate"
  return cur

/-- **Open a `Π`-nest's leading binders as local declarations**, at most `n` of
them, and hand the continuation those local declarations and whatever is left
of the nest.

A constructor is exported as a raw `Π`-nest, so a field domain read straight
off it names the parameters and the constructor's earlier fields as *loose* de
Bruijn variables. That is fine for a syntactic question — `mentionsAny` and
[`InductiveModels.headNorm`] never look at a variable's type — and it is not
fine for a question that reduces. Recognizing a field through a transparent
former, or through an ι step whose major premise is an earlier field, is
`whnf`'s business, and `whnf` answers a loose bound variable with
`Lean.Meta.whnfEasyCases`' panic rather than with a verdict. Walking the nest
through here is what makes each domain closed in the current local context, so
that the question can be asked at all.

`test/fixtures/inductive-models/recursor_field_domain.lean` is a kernel-valid
export of exactly that shape.

A nest with fewer than `n` binders is not an error here: the continuation is
handed the ones there were, and each caller says what a short telescope means
to it. -/
partial def withTeleFVars [Inhabited α] (n : Nat) (ty : Expr)
    (k : Array Expr → Expr → GenM α) (fvars : Array Expr := #[]) : GenM α := do
  if fvars.size == n then return ← k fvars ty
  let .forallE x dom body bi := ty | k fvars ty
  withLocalDecl x bi dom fun xv =>
    withTeleFVars n (body.instantiate1 xv) k (fvars.push xv)

/-- A constructor's type at the given levels with `qs` substituted for its
leading binders, leaving the field telescope. -/
def instCtor (cn : Name) (ls : List Level) (qs : Array Expr) : GenM Expr := do
  let ci ← constInfo cn
  instForall (ci.type.instantiateLevelParams ci.levelParams ls) qs

/-- Open a type's telescope, with the binder types. -/
def withFields (ty : Expr) (k : Array Expr → Array Expr → GenM α) : GenM α := do
  forallTelescope ty fun fs _ => do k fs (← fs.mapM ftyp)

/-- A constructor's field types, with its binders instantiated left-to-right
by another constructor's corresponding fields. This keeps dependencies on an
earlier field in the caller's local context instead of returning types that
mention the temporary free variables introduced by [`withFields`]. -/
def fieldTypesAt (ty : Expr) (fields : Array Expr) : GenM (Array Expr) := do
  let mut cur := ty
  let mut tys := #[]
  for field in fields do
    match cur with
    | .forallE _ dom body _ =>
      tys := tys.push dom
      cur := body.instantiate1 field
    | _ => badShape "the constructors have different field counts"
  if cur.isForall then badShape "the constructors have different field counts"
  return tys

/-- **The dependency the congruence fold cannot survive, and only that one.**

The fold replaces one *packed* position of a constructor application at a time,
so a field whose type mentions an earlier packed field is ill-typed at every
intermediate stage. A dependency on a field that does **not** move is never
touched by the fold, and Lean supports it — `node : (n : N) → Vec N n → List
DTree → DTree` and `node : List ETree → (n : N) → Vec N n → ETree` are both
`test/fixtures/inductive-models/dependent_fields.lean`, and both are models now.

A dependency *on* a packed field is out of reach for a different reason: Lean
does not support it either. `node : (l : List GTree) → Len l N.z → GTree` fails
Lean's own nested compilation with `unknown constant 'GTree'`, because the
auxiliary block replaces `List GTree` with a fresh member and `Len l` is then
about a constant absent at that point in the block.

**The mention has to survive β**, which is why the type goes through
[`InductiveModels.headNorm`] first.
A container whose parameter is a *family* leaves its field as the redex
`(fun x => …) k`, and `k` is the field before it; when the family is constant —
`RB (RB N (fun _ => Key)) (fun _ => N)`, where the nesting is in the **key** —
the
redex mentions `k` and its reduct does not, so the fold has nothing to survive.
This used to decline that shape as a dependent field, which was a wrong reason
as well as a wrong answer: Lean compiles it. -/
def noDepOnPacked (packed : Array Expr) (fs tys : Array Expr) : GenM Unit := do
  for i in [0:tys.size] do
    let ti := headNorm tys[i]!
    for j in [0:i] do
      if packed.contains fs[j]! && ti.containsFVarDag fs[j]!.fvarId! then
        badShape "a field type depends on an earlier packed field"

/-- Read `n` minor premise types off a recursor application. -/
def withMinorTypes (recApp : Expr) (n : Nat) (k : Array Expr → GenM α) : GenM α := do
  let ty ← ityp recApp
  forallBoundedTelescope ty (some n) fun mvars _ => do
    k (← mvars.mapM ityp)

end InductiveModels
