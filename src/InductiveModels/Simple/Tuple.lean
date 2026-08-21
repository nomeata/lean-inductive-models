import InductiveModels.Simple.Church

open Lean Meta

namespace InductiveModels

/-! ## Linear recursion at a never-zero sort: the tuple tower

A **linearly recursive** declaration is one whose every
constructor has at most one recursive field, with that field not under a
binder. Constructors then split into *base* (no recursive field) and *step*
(exactly one), and the carrier is a spine-indexed tower:

```text
V 0       := Σ'(tag : Nat), Base_tag           -- a Nat.rec tag tower
V (n+1)   := Σ'(tag : Nat), Step_tag (V n)     -- another, at the shorter spine
T         := Σ'(n : Nat), V n

base ctor c_j f⃗            := ⟨0,       ⟨bⱼ, chain f⃗⟩⟩
step ctor c_j pre r post   := ⟨r.1 + 1, ⟨sⱼ, chain (pre, r.2, post)⟩⟩
```

`n` counts recursive depth, so the representation is unique and no carve is
needed. The recursor is `PSigma'.rec'` on the outer pair, `Nat.rec` on the
spine, the existing tag towers inside each level, and `PSigma'.rec'` down each
chain — and **every ι rule is `Eq.refl`**, because at a step constructor the
recursive argument is rebuilt as `⟨n, r.2⟩`, which structure eta makes
definitionally `r`, and the induction hypothesis is the spine's own `Nat.rec`
at `r.1` applied to `r.2`, which is the recursor at `r` for the same reason.
No transport, no `funext`.

What it cannot do is a constructor with **two** recursive fields: the spine is
a single `Nat` and `⟨r.1 + 1, …⟩` has exactly one predecessor to take, so two
sub-terms at spines `n₁` and `n₂` cannot both sit in one fibre `V n` unless
the spine is generalised to a tree — which is the very inductive being built.
That is plan B's territory, and `Lean.ParserDescr` lives there. -/

/-! ### Reading a field's head, at layer 3

**`Expr.getAppFn` on `(fun x => T p⃗ e⃗) k` is a lambda**, so every "is the
recursive occurrence a bare `T p⃗ e⃗`" test in this file answers *no* on a
field whose type is a redex — and reports it as infinitary, which it is not:
there is no binder over the occurrence at all, only an application nobody
reduced.

That is Lean's own nested specialisation and not a hypothetical. A container
with a dependent value field — `Impl α β | inner : … → (k : α) → β k → …` —
specialised at `β := fun _ => T` carries the field as `(fun x => T) k`, and a
`let` in the family's body survives the same way. This same defect at layer 1
cost `Lean.Json` and `Lean.PrefixTreeNode` their
nested models until [`InductiveModels.Gen.occIdx?`] and its two siblings started
reading through [`InductiveModels.headNorm`]. Layer 3 is the same two declarations
one step further on: their `_model.aux` families are what the composition
hands *this* file, and the redex is still in them.

So the repair is the same function and deliberately not a second one — β and
ζ, iterated, no constant unfolded. It is applied where this file asks a
question whose answer is invariant under β and ζ:

* **is the occurrence bare** — [`InductiveModels.recSlotOf`] and `erasureBareWhy`;
* **what are its index arguments, and how many binders is it under** —
  [`InductiveModels.withRecSlot`], which is where the carve arm's `ctorIdxAt` used to inspect
  only the unreduced head;
* **what binders does a recursive field have** — [`InductiveModels.tagFactored`],
  which has none to peel until the redex is gone.

and at the indexed erasure's internal boundary:
[`InductiveModels.erasureFieldDomain`] head-normalises a field which syntactically
mentions the erased owner. If the occurrence disappears, the field was never
recursive; if binders appear, the skeleton keeps those binders and replaces
the occurrence beneath them. No public declaration type is normalised, and a
declaration whose constructor types are already βζ-normal therefore takes
exactly the path it took before, byte for byte. A genuinely nested occurrence
survives head normalisation under its foreign type former and is still routed
back to layer 1.

`PFunctor.Approx.CofixA`'s `(F.B a → CofixA n)` is a binder that is genuinely
*written*, so none of this touches it — it is the carve arm's infinitary erasure that
carries it, and `prim_carve`'s `Inf2`, `Cf` and `Bif` are its fixtures. -/

/-- **Does `B` factor through the constructor tag?** — the one question that
decides whether a declaration W can model is *certifiable*.

The untagged W construction uses a path step carrying the whole label, so `mk`
has to decide `x.1 = a` at the label type; that is
`Classical.propDecidable`, and it costs `[propext, Classical.choice,
Quot.sound]` on every constant. The tagged construction uses the same W with a
path step carrying only the **constructor tag**, so the test is `Fin k` equality and
the bill drops to `[propext, Quot.sound]` — the covered set, since
`Classical.choice` has been refuted as a term of the checker's language while
the other two are certified or covered.

The tagged construction needs the branch type to be a function of the tag
alone, which is exactly: **a recursive field's binder types may not mention the
constructor's own non-recursive fields.** They may mention the parameters,
which are fixed for the whole declaration. `DT | mk : (n : Nat) → (Fin n → DT)
→ DT` is the counterexample and `Lean.Expr.app : Expr → Expr → Expr` is the
common case, whose recursive fields have no binders at all and so pass
vacuously.

De Bruijn bookkeeping, since it is what the test actually is: inside a
recursive field's domain at field position `i`, having opened `j` of the
domain's own binders, indices `0 … j-1` are those binders, `j … j+i-1` are the
constructor's earlier fields, and above that the parameters. So a binder type
must have no loose bvar in `[j, j+i)`.

Non-throwing, and asked of every declaration the tree arm would take, so that the
census reports the certifiable and uncertifiable populations as two numbers
rather than one. -/
def tagFactored (tname : Name) (np : Nat) (exportCtors : Array (Name × Expr)) : Bool :=
  exportCtors.all fun (_, cty) => Id.run do
    let mut t := cty
    for _ in [0:np] do
      match t with
      | .forallE _ _ b _ => t := b
      | _ => return false
    let mut i := 0
    while t matches .forallE .. do
      let .forallE _ dom b _ := t | unreachable!
      if mentionsAny #[tname] dom then
        -- peel the field's own binder telescope and check each binder type.
        -- Through `headNorm`: a redex has no binders to peel until it is
        -- reduced, and the binders it hides are the ones this is asking about.
        let mut d := headNorm dom
        let mut j := 0
        while d matches .forallE .. do
          let .forallE _ z db _ := d | unreachable!
          for m in [0:i] do
            if z.hasLooseBVar (j + m) then return false
          d := db
          j := j + 1
      t := b
      i := i + 1
    return true

/-- **Does `B` factor through the whole label?** — the same question as
[`InductiveModels.tagFactored`], asked of the *untagged* instantiation of the same
core, and the guard the tree arm actually runs on.

The untagged form is the tagged construction at `K := A` and `tg := id`, so
there is one construction and two bills. At `K := A` the branch
type is `B' : A → Sort w` and `A` is the tag *paired with that constructor's
non-recursive fields*, so a recursive field's binders may mention those fields
freely — `Tel` reads them back out of the label's own data. What they still may
not mention is an earlier **recursive** field: the label carries no children,
so there is nowhere for `Tel` to read one from.

`tagFactored` implies this, and the difference between the two is exactly the
two columns the report prints. A declaration this admits and `tagFactored`
refuses is modelled at `[propext, Classical.choice, Quot.sound]`, because
`WT.decEqAll` is `Classical.propDecidable`; one it admits *and* `tagFactored`
admits keeps `instDecidableEqNat` and stays at `[propext, Quot.sound]`.

**This is an invariant, not a route condition.** It was a conjunct of `armTree`
until its refusal class was shown empty, and [`InductiveModels.mkPrimSite`]
now asserts it — a hard failure — where it used to test it. The argument is
written out there; in one line: everything reaching the assertion has passed
[`InductiveModels.erasureBareFailure?`], so every recursive field domain is
`∀ z⃗, T p⃗ e⃗` with no binder type mentioning `T`, and a binder can then name
an earlier *recursive* field only through a type former whose domain mentions
the type being declared — which no constant, parameter or surviving earlier
field can be. The uncontracted-redex spelling that would name one without a
former is a non-positive occurrence to Lean's kernel, because positivity tests
a Π domain syntactically. `VanishingErasureTest` pins both halves.

It stays a computed predicate rather than becoming `True` because it is also a
*report* column: the census prints it beside `tagFactored` at the shape
declines, where the telescope has not passed `erasureBare` and the answer can
still be no.

Non-throwing, for the same reason `tagFactored` is. -/
def labelFactored (tname : Name) (np : Nat) (exportCtors : Array (Name × Expr)) : Bool :=
  exportCtors.all fun (_, cty) => Id.run do
    let mut t := cty
    for _ in [0:np] do
      match t with
      | .forallE _ _ b _ => t := b
      | _ => return false
    -- Which of this constructor's own fields are recursive, by position. The
    -- test is the plain `mentionsAny`, exactly as [`InductiveModels.eraseCtorTy`] and
    -- `wShapeOf` ask it, and all three agree because the telescope reached them
    -- through [`InductiveModels.shapeCtorTy`]: on that array a βζ-dead mention is
    -- already gone, so the cheap syntactic test *is* the reduced one
    -- ([`InductiveModels.mkPrimSite`] asserts as much).
    let mut recAt : Array Bool := #[]
    let mut u := t
    while u matches .forallE .. do
      let .forallE _ dom b _ := u | unreachable!
      recAt := recAt.push (mentionsAny #[tname] dom)
      u := b
    let mut i := 0
    while t matches .forallE .. do
      let .forallE _ dom b _ := t | unreachable!
      if recAt[i]! then
        -- Same de Bruijn bookkeeping as `tagFactored`'s: with `j` of the
        -- domain's own binders opened, loose index `j + m` is the field at
        -- position `i - 1 - m`. Only the recursive ones are refused.
        let mut d := headNorm dom
        let mut j := 0
        while d matches .forallE .. do
          let .forallE _ z db _ := d | unreachable!
          for m in [0:i] do
            if recAt[i - 1 - m]! && z.hasLooseBVar (j + m) then return false
          d := db
          j := j + 1
      t := b
      i := i + 1
    return true

/-- The field domain used by an internal erasure or spine.

Usually this is the exported field domain byte for byte. A specialised redex
which syntactically mentions the owner is head-normalised at this internal
boundary. Thus `(fun _ : T i => N) k` becomes the genuinely non-recursive `N`,
while a redex reducing to `∀ z, T i` exposes the binder the erasure must retain.
A nested occurrence remains nested after the same reduction and is declined by
the routing guard. Public declaration types never pass through this function. -/
def erasureFieldDomain (tname : Name) (dom : Expr) : Expr :=
  if mentionsAny #[tname] dom then headNorm dom else dom

/-- Whether an internal erasure or spine field contains an occurrence which
must be replaced, after exposing its βζ head and discarding dead mentions. -/
def erasureRecursive (tname : Name) (dom : Expr) : Bool :=
  mentionsAny #[tname] (erasureFieldDomain tname dom)

/-- **A field domain with a βζ-*dead* owner mention discarded, and nothing
else touched.**

`(fun _ : T => N) k` and `let _u : Type := T; N` both mention `T` as written
and reduce to a domain that does not mention it at all; this returns that
reduct. Every other domain — including one whose reduct still mentions the
owner, such as the redex hiding `∀ z, T i` — is returned **byte for byte**,
because exposing a live occurrence is the internal erasure's business
([`InductiveModels.erasureFieldDomain`]) and not this normalisation's.

The distinction matters because this one *is* applied to the constructor
telescope every shape question is then asked of. Reducing only the domains
whose owner mention disappears is what makes the operation invisible: a
declaration with no dead mention gets the identical array back. -/
def shapeFieldDomain (tname : Name) (dom : Expr) : Expr :=
  if erasureRecursive tname dom then dom else erasureFieldDomain tname dom

/-- One constructor type with every βζ-dead owner mention discarded from a
**field** domain, its `np` parameter binders and its conclusion untouched.

**This is the whole of the normalisation, and it happens once.** The three
questions the tree arm splits its telescope by — [`InductiveModels.wShapeOf`],
[`InductiveModels.labelFactored`] and [`InductiveModels.eraseCtorTy`] — used to test
`mentionsAny` on the domain *as written*, so a field whose owner mention βζ
discards was a recursive *branch* to all three, and to
[`InductiveModels.analysePrim`]'s `isRec` and [`InductiveModels.classifyCtor`] besides.
Teaching each of them to reduce first is five tests that must then agree
forever. Normalising the telescope once, before any of them runs, is one.

Sound because it is a **βζ reduct**: the reduced domain and the written one
are definitionally equal with no unfolding and no proof, so a carrier built
from this array is a carrier the written constructor type typechecks against.
The written array is retained beside it ([`InductiveModels.PrimSite.sourceCtors`])
and is what every emitted statement is spelled from; nothing this returns ever
reaches the output. -/
def shapeCtorTy (tname : Name) (np : Nat) (cty : Expr) : Expr :=
  let rec fields (t : Expr) : Expr :=
    match t with
    | .forallE x dom b bi => .forallE x (shapeFieldDomain tname dom) (fields b) bi
    | _ => t
  let rec params (k : Nat) (t : Expr) : Expr :=
    if k == np then fields t else
    match t with
    | .forallE x dom b bi => .forallE x dom (params (k + 1) b) bi
    | _ => t
  params 0 cty

/-- [`InductiveModels.shapeCtorTy`] at a whole constructor array, names kept. -/
def shapeCtors (tname : Name) (np : Nat) (cs : Array (Name × Expr)) :
    Array (Name × Expr) :=
  cs.map fun (cn, cty) => (cn, shapeCtorTy tname np cty)

/-! ### The mention that only δ discards

[`InductiveModels.shapeFieldDomain`] answers "does this field carry a
recursive occurrence" with β and ζ, which is every reduction that can be
performed without an environment. A field can also mention the owner in a
position that only **unfolding a definition** discards: `idf (T → Type) (fun _
=> N) child`, with `idf` the identity, is a domain whose reduct is `N` and
whose owner mention is as dead as `(fun _ : T => N) k`'s. `T` occurs in it, and
after full reduction it does not occur anywhere.

**A field is recursive exactly when an owner occurrence survives full
reduction**, and the three functions below decide it that way — not by naming a
constant, and not by pattern-matching a shape.

Two facts make the walk cheap and make it sound.

*Cheap*: a subterm with no syntactic mention of the owner cannot acquire one by
reducing, because **no constant in the environment can mention `T`**. Every
constant a constructor field's type names was declared before `T` was, and `T`
is what is being declared. So reduction only ever *removes* mentions, the
syntactic test is an exact over-approximation, and the walk skips every subterm
the cheap test clears — which, in a declaration with no dead mention at all, is
the whole of it at the first question asked.

*Sound as a reduction*: the reduct and the written domain are definitionally
equal, exactly as the βζ case is. δ is not weaker for the kernel than β is; it
is only unavailable to a pure function. Nothing here reaches the output —
[`InductiveModels.PrimSite.sourceCtors`] keeps the export byte for byte and is
what every emitted statement is spelled from. -/

/-- **Reduction at the kernel's transparency.** The question being asked is the
kernel's — its positivity check is what decided this field is not recursive —
and the kernel unfolds every definition it is given. `Meta.whnf` at its default
setting does not: it stops at `@[irreducible]`, and at a theorem. Reading the
declaration less strongly than the kernel wrote it would put this analysis back
in the business of refusing a shape Lean accepts, so it reads at `.all`.

`@[irreducible] def idf` in front of a dead mention is the shape at issue, and
Lean does mint a recursor with no induction hypothesis for that field. It does
not reach here as one: an attribute lives in an environment extension and an
export carries kernel data, so an exported definition always arrives
semireducible. This is the transparency that stays right if that ever changes,
and it is what makes the reduction the same reduction the kernel performed. -/
def whnfKernel (e : Expr) : GenM Expr := withTransparency .all (whnf e)

/-- The expression with every **δ-dead** owner mention discarded, and every
surviving one left where it stands.

The walk is the reduction restricted to the subterms that mention the owner:
head-normalise, and if the mention is gone keep the reduct; otherwise descend
into the parts that still mention it and ask again. A subterm the syntactic
test clears is returned untouched and never reduced.

The result may still mention the owner — that is the case where the mention is
live, and [`InductiveModels.deltaFieldDomain`] discards the whole reduct
there rather than hand back a churned expression. -/
partial def deltaDeadReduct (tname : Name) (e : Expr) : GenM Expr := do
  unless mentionsAny #[tname] e do return e
  let e ← whnfKernel e
  unless mentionsAny #[tname] e do return e
  match e with
  | .app .. =>
    let f ← deltaDeadReduct tname e.getAppFn
    let as ← e.getAppArgs.mapM (deltaDeadReduct tname)
    return mkAppN f as
  | .forallE x d b bi =>
    let d ← deltaDeadReduct tname d
    withLocalDecl x bi d fun z => do
      mkForallFVars #[z] (← deltaDeadReduct tname (b.instantiate1 z))
  | .lam x d b bi =>
    let d ← deltaDeadReduct tname d
    withLocalDecl x bi d fun z => do
      mkLambdaFVars #[z] (← deltaDeadReduct tname (b.instantiate1 z))
  | .mdata _ b => deltaDeadReduct tname b
  | .proj s i b => return .proj s i (← deltaDeadReduct tname b)
  | _ => return e

/-- **A field domain with a δ-dead owner mention discarded, and nothing else
touched** — [`InductiveModels.shapeFieldDomain`] one reduction further on, and
all-or-nothing for the same reason: a domain whose occurrence survives is
returned **byte for byte**, so a declaration with no dead mention gets the
identical expression back and takes the path it took before.

The domain must be closed in the current local context; a raw constructor
`Π`-nest names the parameters and the earlier fields as loose bound variables,
and `whnf` answers those with a panic rather than a verdict. -/
def deltaFieldDomain (tname : Name) (dom : Expr) : GenM Expr := do
  unless mentionsAny #[tname] dom do return dom
  let reduced ← deltaDeadReduct tname dom
  return if mentionsAny #[tname] reduced then dom else reduced

/-- One constructor type with every δ-dead owner mention discarded from a
**field** domain, its `np` parameter binders and its conclusion untouched —
[`InductiveModels.shapeCtorTy`] at the reduction a pure function cannot do.

The telescope is *opened* so that each domain is closed and can be reduced, and
the answers are then written back into the raw `Π`-nest by de Bruijn surgery:
at field position `i` the abstraction array is the parameters followed by the
earlier fields, which is the nest's own index order. A constructor with nothing
to discard is returned unchanged, the same object it arrived as. -/
def deltaCtorTy (tname : Name) (np : Nat) (cty : Expr) : GenM Expr := do
  let replacements ← withTeleFVars np cty fun ps rest => do
    if ps.size < np then return (#[] : Array (Nat × Expr))
    withTeleFVars (numForalls rest) rest fun fs _ => do
      let mut replacements : Array (Nat × Expr) := #[]
      for i in [0:fs.size] do
        let dom ← ityp fs[i]!
        let reduced ← deltaFieldDomain tname dom
        unless reduced == dom do
          replacements := replacements.push (i, reduced.abstract (ps ++ fs.extract 0 i))
      return replacements
  if replacements.isEmpty then return cty
  let table : Std.HashMap Nat Expr := replacements.foldl (fun m (i, d) => m.insert i d) {}
  let rec fields (i : Nat) (t : Expr) : Expr :=
    match t with
    | .forallE x dom b bi => .forallE x (table.getD i dom) (fields (i + 1) b) bi
    | _ => t
  let rec params (k : Nat) (t : Expr) : Expr :=
    if k == np then fields 0 t else
    match t with
    | .forallE x dom b bi => .forallE x dom (params (k + 1) b) bi
    | _ => t
  return params 0 cty

/-- [`InductiveModels.deltaCtorTy`] at a whole constructor array, names kept. -/
def deltaCtors (tname : Name) (np : Nat) (cs : Array (Name × Expr)) :
    GenM (Array (Name × Expr)) :=
  cs.mapM fun (cn, cty) => return (cn, ← deltaCtorTy tname np cty)

/-- Explain why the index erasure cannot replace every recursive occurrence
by its bare skeleton owner.  This walk is monadic solely because a transparent
former around the owner must be recognized by definitional reduction; its
answer remains a diagnostic value and it emits no declaration.

Keeping the early exits in a named `GenM` computation also makes their scope
unambiguous: they return from this analysis, never from the surrounding model
construction.

**Opened, not peeled.** The telescope goes through
[`InductiveModels.withTeleFVars`] because the reduction below is asked of a
field domain, and a domain read off the raw `Π`-nest names the parameters and
the constructor's earlier fields as loose bound variables. -/
def erasureBareFailure? (tname : Name) (np ni : Nat)
    (exportCtors : Array (Name × Expr)) : GenM (Option String) := do
  for (cn, cty) in exportCtors do
    let why ← withTeleFVars np cty fun ps rest => do
      if ps.size < np then
        return some s!"{cn}'s telescope is shorter than {np} parameters"
      withTeleFVars (numForalls rest) rest fun fields _ => do
        for field in fields do
          let dom := erasureFieldDomain tname (← ityp field)
          unless mentionsAny #[tname] dom do continue
          -- Peel the field's own binders after βζ head normalization. The
          -- erasure retains those binder types, so an owner mention there would
          -- refer to the wrong carrier after the field itself is retyped.
          let inner ← withTeleFVars (numForalls dom) dom fun zs core => do
            for z in zs do
              if mentionsAny #[tname] (← ityp z) then
                return some s!"binder mention: a binder of {cn}'s recursive field mentions \
{tname}, and the erasure keeps binder types verbatim"
            -- A transparent former around `T p⃗ e⃗` is bare, and so is an ι
            -- step that exposes one. Reduction is confined to this route/index
            -- analysis; the public model retains `dom`.
            if (← ownerAppArgs? tname np ni core).isNone then
              return some s!"nested: {cn} has a recursive occurrence that is not an \
application of {tname}"
            return none
          if inner.isSome then return inner
        return none
    if why.isSome then return why
  return none

/-- Which field of a constructor is the recursive one, if any. Declines the
shapes the tower cannot express, each by name. -/
def recSlotOf (tname : Name) (np ni : Nat) (cn : Name) (nf : Nat) (tele : Expr)
    (tagged : Bool := true) (typeU : Bool := true) (labelled : Bool := true) :
    GenM (Option Nat) := do
  -- **The tree arm's bill, printed at the decline that names it**, and it is two
  -- questions because the arm runs the one core at two
  -- instantiations. `labelled` is [`InductiveModels.labelFactored`] and `tagged`
  -- is [`InductiveModels.tagFactored`], which decides what the model *costs* —
  -- yes and it is `[propext, Quot.sound]`, which is covered; no and it spends
  -- `Classical.choice` on top. Two populations, so the census counts two
  -- numbers.
  --
  -- Neither column can now read `no` at a declaration the tree arm would otherwise
  -- have taken: `labelled` is an invariant asserted at
  -- [`InductiveModels.mkPrimSite`] rather than a route condition. It is printed
  -- here because *this* decline is reached before `erasureBare` holds, where
  -- the answer is still informative about the telescope that was rejected.
  let bill := s!"; B factors through the tag: {if tagged then "yes" else "no"}\
; through the label: {if labelled then "yes" else "no"}\
; carrier is Type u: {if typeU then "yes" else "no"}"
  -- Opened rather than peeled, for [`InductiveModels.withTeleFVars`]' reason.
  withTeleFVars nf tele fun fields _ => do
    unless fields.size == nf do
      badShape "field telescope shorter than its field count"
    let mut slot : Option Nat := none
    for i in [0:nf] do
      let d := erasureFieldDomain tname (← ityp fields[i]!)
      if mentionsAny #[tname] d then
        if slot.isSome then
          badShape s!"{cn} has two recursive fields: the tuple tower's spine is one \
Nat and a constructor takes one predecessor, so a branching constructor needs the \
W/path construction (plan B){bill}"
        -- A βζ-dead mention was removed above.  Every domain which remains is a
        -- real binder or nesting if its head is not the owner itself.
        unless (← ownerAppArgs? tname np ni d).isSome do
          badShape s!"{cn} has a recursive field that is not a bare occurrence of \
{tname} — under a binder, or nested, neither of which the tuple tower reaches{bill}"
        slot := some i
    return slot

/-- **A constructor's first bare recursive field**, or `none` where it has
none. Bare means what it means everywhere else in this file: after βζ head
normalization the field's domain is an application of the owner itself, with no
binder over that occurrence.

This is [`InductiveModels.recSlotOf`]'s question with its two refusals dropped
rather than raised, and the two are separate functions because they answer for
two different constructions. The tower needs *the* recursive field — its spine
is one `Nat` and a step constructor takes exactly one predecessor — so a
constructor with two of them is a shape it cannot express, and saying so is the
dispatcher signal that selects W. The empty route needs only *a* recursive
field, because all it does with it is return it: a constructor whose every
inhabitant would have to supply an inhabitant of the carrier cannot be applied
at all, however many such fields it has.

**Bare is load-bearing and not an approximation.** A recursive occurrence under
a binder is a field `∀ z⃗, T p⃗`, which is inhabited whenever the binder's domain
is empty — `test/fixtures/inductive-models/empty_no_base.lean`'s `NbVac`
recurses under an empty domain and is therefore *inhabited*. Emptiness of a
binder domain is not a question this analysis can ask, so the shape class stops
at the occurrences that carry an inhabitant of the owner directly. Non-throwing,
because it is asked of every recursive declaration and its answer selects a
route rather than refusing one. -/
def bareRecSlotOf (tname : Name) (np ni : Nat) (nf : Nat) (tele : Expr) :
    GenM (Option Nat) := do
  -- Opened rather than peeled, for [`InductiveModels.withTeleFVars`]' reason.
  withTeleFVars nf tele fun fields _ => do
    unless fields.size == nf do
      badShape "field telescope shorter than its field count"
    for i in [0:nf] do
      let d := erasureFieldDomain tname (← ityp fields[i]!)
      if mentionsAny #[tname] d then
        if (← ownerAppArgs? tname np ni d).isSome then return some i
    return none

/-- A recursive field's domain with the **occurrence** replaced by `Vn` and the
binders it sits under kept verbatim: `T p⃗ e⃗` becomes `Vn` and `∀ z⃗, T p⃗ e⃗`
becomes `∀ z⃗, Vn`.

The domain is read through [`InductiveModels.headNorm`], so the same operation handles
a binder exposed only by βζ reduction. `Vn` is closed over the parameter scope
and never mentions `z⃗`, which is what
makes keeping the binders and replacing only the core well typed. The binder
types themselves are kept **as written** — they may mention the constructor's
earlier non-recursive fields, and `erasureBareWhy` has already refused a binder
type that mentions `tname`, which is the one shape that would not survive the
retyping of the field it names. -/
partial def swapOcc (Vn : Expr) (d : Expr) : GenM Expr := do
  match headNorm d with
  | .forallE x z b bi =>
    withLocalDecl x bi z fun zv => do mkForallFVars #[zv] (← swapOcc Vn (b.instantiate1 zv))
  | _ => return Vn

/-- The constructor's field telescope with its recursive field's type replaced
by the shorter spine's fibre `V n`. The recursive occurrence sits at `Sort w`
either way, so the storage plan computed on the export's telescope is the
plan for this one too.

The tuple tower only ever calls this at a **bare** occurrence, where
[`InductiveModels.swapOcc`] is the identity on binders and this is the whole-domain
replacement it always was; the carve arm calls it at an infinitary one too. -/
partial def spineSwap (tname : Name) (Vn : Expr) (nf : Nat) (tele : Expr) :
    GenM Expr := do
  if nf == 0 then return tele
  let .forallE x d b bi := tele | badShape "field telescope shorter than its field count"
  let d := erasureFieldDomain tname d
  let d' ← if mentionsAny #[tname] d then swapOcc Vn d else pure d
  withLocalDecl x bi d' fun xv => do
    mkForallFVars #[xv] (← spineSwap tname Vn (nf - 1) (b.instantiate1 xv))

/-- The same classification as [`InductiveModels.churchSwapAt`] makes, without the
rewrite — used where the *values* are built, since those are bound at the
model's restored telescope and not at the export's.

**Classified through [`InductiveModels.erasureFieldDomain`]**, exactly as
[`InductiveModels.recSlotOf`], [`InductiveModels.bareRecSlotOf`] and
[`InductiveModels.spineSwap`] are. Every caller now hands it a telescope
[`InductiveModels.shapeCtorTy`] has already normalised, so the reduction here
is a second line of defence rather than the only one; it stays because a
βζ-dead owner mention makes a plain data field look recursive, and a walk that
reads a field's *classification* must never depend on which of the two arrays
it was handed. The **binder** the walk introduces is still the domain as
written: only the classification reduces. -/
partial def classifyCtor (tname : Name) (nf : Nat) (tele : Expr)
    (acc : Array PField := #[]) : GenM (Array PField) := do
  if nf == 0 then return acc
  let .forallE x d b bi := tele | badShape "telescope shorter than its field count"
  let fld : PField ←
    if erasureRecursive tname d then
      forallTelescope d fun zs _ => pure { rec? := some zs.size }
    else pure { rec? := none }
  withLocalDecl x bi d fun xv =>
    classifyCtor tname (nf - 1) (b.instantiate1 xv) (acc.push fld)

/-- **One `Pair`-valued premise of the strong-induction fold.**

Walks constructor `j`'s *export* telescope, binding one variable per field —
a recursive field at `∀ z⃗, Pair e⃗` rather than at its own type — and ends at

    fun D k => k (c_j elems) (fun _h => minor elems ihs)

where, for each recursive slot, `elems` holds the carrier element read out of
that slot's pair and `ihs` the induction hypothesis read out beside it, both
pointwise under the field's own binders. The minor premise takes the fields in
declaration order and then the hypotheses, which is the order Lean's recursors
use.

The index expressions are taken from the export telescope as it is walked, not
read back off the built types: `Pair` is a λ, so `Pair e⃗` is a β-redex and
whether its arguments are still visible is a fact about whoever last touched
the expression. This is the bug that cost the first two attempts.

At a maybe-zero sort, `Self` itself cannot instantiate the pair's `D : Prop`.
`baseAt` is the Church proposition under the derived exact-sort lift; extracting a recursive
element instantiates at that proposition, maps the stored `Self` through
`down`, and maps the result back through `up`. With no lift, `baseAt = Self`
and these two boundary maps are identities. -/
partial def pairArm (tname : Name) (np ni : Nat) (us : List Level)
    (selfAt : Array Expr → Expr) (pairAt : Array Expr → GenM Expr)
    (baseAt : Array Expr → GenM Expr) (lift? : Option Level)
    (motive : Expr) (cN : Name) (minor : Expr) (ps : Array Expr)
    (nf : Nat) (tele : Expr) (elems ihs : Array Expr) : GenM Expr := do
  if nf == 0 then
    let some args ← ownerAppArgs? tname np ni tele
      | badShape s!"a constructor of {tname} does not present {ni} index arguments"
    let isj := args.extract np args.size
    let sfj := selfAt isj
    let built := mkAppN (.const cN us) (ps ++ elems)
    return ← withLocalDeclD `D (.sort .zero) fun D => do
      let armTy ← withLocalDeclD `e sfj fun e => do
        let qTy ← withLocalDeclD `h sfj fun h =>
          mkForallFVars #[h] (mkAppN motive (isj.push h))
        withLocalDeclD `q qTy fun q => mkForallFVars #[e, q] D
      withLocalDeclD `k armTy fun k => do
        let proof ← withLocalDeclD `h sfj fun h =>
          mkLambdaFVars #[h] (mkAppN minor (elems ++ ihs))
        mkLambdaFVars #[D, k] (mkAppN k #[built, proof])
  let .forallE x d b bi := tele | badShape "telescope shorter than its field count"
  if !(mentionsAny #[tname] d) then
    return ← withLocalDecl x bi d fun xv => do
      mkLambdaFVars #[xv] (← pairArm tname np ni us selfAt pairAt baseAt lift?
        motive cN minor ps (nf - 1) (b.instantiate1 xv) (elems.push xv) ihs)
  -- a recursive field `∀ z⃗, T p⃗ e⃗`: bind it at `∀ z⃗, Pair e⃗`
  let nb ← forallTelescope d fun zs _ => pure zs.size
  let dPair ← forallBoundedTelescope d (some nb) fun zs res => do
    let some a ← ownerAppArgs? tname np ni res
      | badShape s!"a recursive field of {tname} does not present {ni} index arguments"
    mkForallFVars zs (← pairAt (a.extract np a.size))
  withLocalDecl x bi dPair fun pv => do
    let (el, ih) ← forallBoundedTelescope d (some nb) fun zs res => do
      let some a ← ownerAppArgs? tname np ni res
        | badShape s!"a recursive field of {tname} does not present {ni} index arguments"
      let ris := a.extract np a.size
      let sf := selfAt ris
      let baseTy ← baseAt ris
      let app := mkAppN pv zs
      let mkArm := fun (k : Expr → Expr → GenM Expr) =>
        withLocalDeclD `e sf fun e => do
          let qTy ← withLocalDeclD `h sf fun h =>
            mkForallFVars #[h] (mkAppN motive (ris.push h))
          withLocalDeclD `q qTy fun q => do mkLambdaFVars #[e, q] (← k e q)
      let elArm ← mkArm fun e _ => pure <| match lift? with
        | none => e
        | some ℓ => puliftDown ℓ baseTy e
      let elBase := mkAppN app #[baseTy, elArm]
      let el := match lift? with
        | none => elBase
        | some ℓ => puliftUp ℓ baseTy elBase
      let ihArm ← mkArm fun _ q => pure (mkApp q el)
      let ih := mkAppN app #[mkAppN motive (ris.push el), ihArm]
      return (← mkLambdaFVars zs el, ← mkLambdaFVars zs ih)
    mkLambdaFVars #[pv] (← pairArm tname np ni us selfAt pairAt baseAt lift? motive cN minor ps
      (nf - 1) (b.instantiate1 el) (elems.push el) (ihs.push ih))

end InductiveModels
