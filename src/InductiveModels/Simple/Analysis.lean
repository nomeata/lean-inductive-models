import InductiveModels.Simple.Tuple
import InductiveModels.Simple.Plan

/-!
# The shape facts every primitive-model route shares

One analysis pass, run before any emission, so that the route dispatcher sees
plain data rather than closures over the declaration telescope.
-/

open Lean Meta

namespace InductiveModels

/-- **How many induction hypotheses the exported recursor's `j`-th minor
premise binds**, given that constructor's field count.

The minor premise for `C_j` is `∀ x⃗ ih⃗, M ι⃗_j (C_j p⃗ x⃗)`: one binder per
field, then one per *recursive* field. Its binder count less the field count is
therefore the export's own statement of how many of `C_j`'s fields carry a
recursive occurrence — read off the recursor's type, with nothing reduced and
no shape decided here.

`0` where the type is shorter than the walk expects; [`InductiveModels.analysePrim`]
has already refused a recursor whose motive, minor and index counts are not the
declaration's. -/
def minorIHCount (rv : RecursorVal) (j nf : Nat) : Nat := Id.run do
  let mut t := rv.type
  for _ in [0:rv.numParams + rv.numMotives + j] do
    match t with
    | .forallE _ _ b _ => t := b
    | _ => return 0
  match t with
  | .forallE _ dom _ _ => return numForalls dom - nf
  | _ => return 0

/-- The declaration facts shared by all primitive-model routes.  Keeping this
phase separate from emission gives the route dispatcher plain data rather than
closures over the declaration telescope. -/
structure PrimAnalysis where
  declaredMemberTy : Expr
  memberTy : Expr
  ni : Nat
  w : Level
  isRec : Bool
  rv : RecursorVal
  large : Bool
  v : Level
  recLs : List Level
  nonrecursiveOneConstructor : Bool
  route : PrimRoute
  erasureBare : Bool
  erasureLinear : Bool

set_option maxRecDepth 2048 in
/-- Analyse the installed declaration and its recursor before any support or
model declarations are installed. -/
def analysePrim (tname : Name) (lparams : List Name) (np : Nat) (memberTy : Expr)
    (exportCtors : Array (Name × Expr)) : GenM PrimAnalysis := do
  let us := lparams.map Level.param
  let nc := exportCtors.size
  let peel : Expr → Option (Nat × Level) := fun ty => Id.run do
    let mut cur := ty
    for _ in [0:np] do
      match cur with
      | .forallE _ _ b _ => cur := b
      | _ => return none
    let mut n := 0
    while cur matches .forallE .. do
      let .forallE _ _ b _ := cur | unreachable!
      cur := b
      n := n + 1
    match cur with
    | .sort w => return some (n, w)
    | _ => return none
  let declaredMemberTy := memberTy
  let (memberTy, ni, w) ←
    match peel memberTy with
    | some (n, w) => pure (memberTy, n, w)
    | none => do
      let exposed ← forallBoundedTelescope memberTy (some np) fun ps rest =>
        forallTelescopeReducing rest fun is res => do
          unless (← whnf res) matches .sort _ do
            badShape "the declaration does not land in a sort, even after unfolding \
              its result type"
          mkForallFVars (ps ++ is) (← whnf res)
      let some (n, w) := peel exposed
        | badShape "the declaration does not land in a sort"
      pure (exposed, n, w)
  let isRec := exportCtors.any fun (_, cty) => Id.run do
    let mut t := cty
    for _ in [0:np] do
      match t with
      | .forallE _ _ b _ => t := b
      | _ => return false
    let mut r := false
    while t matches .forallE .. do
      let .forallE _ dom b _ := t | unreachable!
      if mentionsAny #[tname] dom then r := true
      t := b
    return r

  let ern := Name.str tname "rec"
  let .recInfo rv ← constInfo ern | badShape s!"{ern} is not a recursor"
  unless rv.numMotives == 1 && rv.numMinors == nc && rv.numIndices == ni do
    badShape s!"{ern} does not have 1 motive, {nc} minors and {ni} indices"
  let large := rv.levelParams.length == lparams.length + 1
  unless (if large then rv.levelParams.tail! else rv.levelParams) == lparams do
    badShape s!"{ern} carries the level parameters {rv.levelParams}"
  let v := if large then Level.param rv.levelParams[0]! else Level.zero
  let recLs := if large then v :: us else us
  let nonrecursiveOneConstructor := nc == 1 && !isRec
  let wn := w.normalize
  let route : PrimRoute ←
    if wn.isZero then pure .prop
    else if wn.isNeverZero then pure .type
    else pure .bare

  let erasureBareWhy ← erasureBareFailure? tname np ni exportCtors
  let infinitaryWhy : Option String := Id.run do
    for (cn, cty) in exportCtors do
      let mut t := cty
      for _ in [0:np] do
        match t with
        | .forallE _ _ b _ => t := b
        | _ => pure ()
      while t matches .forallE .. do
        let .forallE _ dom b _ := t | unreachable!
        if erasureRecursive tname dom && (headNorm dom) matches .forallE .. then
          return some s!"infinitary: {cn} has a recursive occurrence under a binder"
        t := b
    return none
  let branchingWhy : Option String := Id.run do
    for (cn, cty) in exportCtors do
      let mut t := cty
      for _ in [0:np] do
        match t with
        | .forallE _ _ b _ => t := b
        | _ => pure ()
      let mut nrec := 0
      while t matches .forallE .. do
        let .forallE _ dom b _ := t | unreachable!
        if erasureRecursive tname dom then nrec := nrec + 1
        t := b
      if nrec > 1 then return some s!"branching: {cn} has {nrec} recursive fields"
    return none
  let erasureWhy : Option String :=
    (erasureBareWhy.orElse fun _ => infinitaryWhy).orElse fun _ => branchingWhy
  let erasureBare : Bool := erasureBareWhy.isNone
  let erasureLinear : Bool := erasureWhy.isNone

  -- **A recursive occurrence this construction cannot replace, decided once
  -- and for every route.**
  --
  -- Every arm below represents a recursive field by *replacing* its occurrence:
  -- the tuple tower with a spine predecessor, arm C with its index erasure, arm
  -- W with a branch of `B'`, the Church routes with the encoding's own `C`. All
  -- four need the occurrence to be `∀ z⃗, T p⃗ e⃗` after βζ head normalization,
  -- which is exactly what [`InductiveModels.erasureBareFailure?`] answers, so a
  -- field that mentions `T` any other way reaches no arm on any route.
  --
  -- That is **`README`'s routing boundary and not a missing case**: an
  -- occurrence remaining under a foreign type former is nesting, and nesting is
  -- layer 1's business — `Driver` sends a block Lean marked nested to
  -- `Plan.plan` and never here. A binder type naming the declaration is the
  -- other half: an internal erasure or spine keeps binder types verbatim, so
  -- retyping the field it names would leave the binder pointing at the wrong
  -- carrier. Neither is a gap in an arm.
  --
  -- This used to be raised as an internal tool error, and only on the indexed
  -- never-zero route. It aborted the whole stream at an owner the contract says
  -- should pass through unchanged and be reported.
  if let some why := erasureBareWhy then
    -- **The boundary is claimed only where the export itself agrees there is
    -- nothing recursive here to miss.**
    --
    -- The decline below says the occurrence is *nesting*. That is a statement
    -- about the declaration, and the declaration answers it: the exported
    -- recursor's minor premise for `C_j` binds one induction hypothesis per
    -- recursive field, so the export says how many of `C_j`'s fields carry an
    -- occurrence the elaborator's own reduction found. Where that number is the
    -- number this analysis reads, the fields it cannot read are ones the
    -- kernel does not treat as recursive either — a mention that δ discards,
    -- which is what `prim_shape_declines.lean`'s `Foreign` is — and the
    -- boundary is a boundary.
    --
    -- Where it is larger, the two disagree about the declaration's own shape:
    -- the export asserts a recursive occurrence at a field whose domain this
    -- analysis does not reduce to the owner. There is then no model of *that*
    -- recursor for any arm to build — every arm represents a recursive field
    -- by replacing an occurrence it can find — and "declined" would report a
    -- boundary the tool is not standing on. So it fails instead, and says
    -- which constructor and which two numbers.
    --
    -- This is asked here and nowhere else on purpose. A disagreement can only
    -- hide behind a decline: wherever a model *is* built, `R._model` carries
    -- the exported recursor's type verbatim and is kernel-checked as it is
    -- produced, so a construction that read the wrong fields as recursive is
    -- refused there already.
    for j in [0:nc] do
      let (cn, cty) := exportCtors[j]!
      let nf := numForalls cty - np
      let asserted := minorIHCount rv j nf
      let seen ← bareRecFieldCount tname np ni cty
      unless asserted == seen do
        badShape s!"{ern}'s minor premise for {cn} binds an induction hypothesis for \
{asserted} of its fields and this analysis reads {seen} of them as recursive, so the \
export asserts a recursive occurrence at a field whose domain does not reduce to \
{tname} here and no model of {ern} can be built ({why})"
    declineWith (.shapeUnsupported tname .outOfScope
      s!"a field mentions {tname} other than as `∀ z⃗, {tname} p⃗ e⃗` after βζ head \
normalization, and every arm of every route represents a recursive field by replacing \
exactly that occurrence ({why}); route: \
{match route with | .type => "never-zero" | .prop => "Prop" | .bare => "maybe-zero"}\
; indices: {ni}; erasure linear: {if erasureLinear then "yes" else "no"}\
; B factors through the tag: {if tagFactored tname np exportCtors then "yes" else "no"}\
; through the label: {if labelFactored tname np exportCtors then "yes" else "no"}\
; carrier is Type u: {if w.normalize.dec.isSome then "yes" else "no"}")

  return {
    declaredMemberTy, memberTy, ni, w, isRec, rv, large, v, recLs,
    nonrecursiveOneConstructor, route, erasureBare, erasureLinear
  }

end InductiveModels
