import InductiveModels.Simple.Analysis
import InductiveModels.Simple.Interface
import InductiveModels.Simple.WArm
import InductiveModels.Simple.Tight

/-!
# One primitive model's site: everything settled before the route is chosen

`primIsoWithInterface` used to be a single definition whose six arms all read
one seven-hundred-line `let` context. The context is this record and the arms
are separate definitions over it, which is what lets the arms be separate
modules — and separate translation units — without any of them being a copy
of another.

`PrimSite` is *only* what the arms read: names and their guards, the shape
analysis, the route booleans, and the closures arm W and the ι rules share.
`PrimOut` is the emission state every arm threads.
-/

open Lean Meta

namespace InductiveModels

/-- The complete context the route dispatcher settles before any arm runs. -/
structure PrimSite where
  tname : Name
  root : Name
  lparams : List Name
  np : Nat
  memberTy : Expr
  exportCtors : Array (Name × Expr)
  reserved : Std.HashSet Name
  sourceRecursor? : Option ERec
  interface? : Option PrimInterfaceNames
  us : List Level
  model : Name
  impl : Name
  selfN : Name
  ern : Name
  recN : Name
  ctorN : Nat → Name
  iotaN : Nat → Name
  indN : Name
  skelN : Name
  goodN : Name
  skelCtorN : Nat → Name
  nc : Nat
  taken : Name → GenM Unit
  declaredMemberTy : Expr
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
  gIsData : Array Bool
  gIdxPos : Array Nat
  gRecNb : Array (Option Nat)
  gNf : Nat
  gPivotTransports : Array (Nat × Nat)
  gNonPiv : Array Nat
  armG : Bool
  eqi : EqInfo
  ctorPairs : Array (Name × Name)
  tbl : Std.HashMap Name (Nat × Expr)
  installedRecTy : Expr
  exactSource? : Option (Expr → Expr)
  publicSource : Expr → Expr
  publicRecTy : Expr
  emptySlots : Array (Option Nat)
  armE : Bool
  directRoute? : Option DirectRoute
  armF : Bool
  armS : Bool
  armC : Bool
  wTagged : Bool
  wPlan : WCarrierPlan
  armW : Bool
  wW : Level
  wDN : Name
  wTelN : Name
  wBN : Name
  wAN : Name
  wTgN : Name
  wFN : Name
  andCMk : Expr → Expr → Expr → Expr → GenM Expr
  andCFst : Expr → Expr → Expr → GenM Expr
  andCSnd : Expr → Expr → Expr → GenM Expr
  wNatT : Expr
  uL : Level
  wKL : Level
  wShapeOf : Nat → GenM (Array Nat × Array Nat)
  wRecCount : Nat → GenM Nat
  wDAt : Array Expr → Expr
  wAAt : Array Expr → Expr
  wLabel : Array Expr → Expr → Expr → Expr
  wKTy : Array Expr → Expr
  wKeyOf : Array Expr → Nat → Expr → Expr
  wTelFn : Array Expr → Expr → GenM Expr
  wBAt : Array Expr → Expr → GenM Expr
  wBFn : Array Expr → Expr
  wTgAt : Array Expr → Expr
  wDecEq : Array Expr → Expr
  wSup : Array Expr → Expr → Expr → Expr
  wLowSelfAt : Array Expr → Expr
  wBranch : Array Expr → Expr → Expr → Expr → GenM Expr
  wDataTy : Array Expr → Nat → GenM Expr
  wNrProjs : Array Expr → Nat → Expr → GenM (Array Expr)
  wRecDom : Array Expr → Nat → Nat → Array Expr → GenM Expr
  wTelTy : Array Expr → Nat → Array Expr → Nat → GenM Expr
  wDispAt : Array Expr → Nat → Expr → Array Expr →
    (Nat → Array Expr → Array Expr → GenM Expr) → Expr → GenM Expr
  wDispLam : Array Expr → Nat → Expr → Array Expr →
    (Nat → Array Expr → Array Expr → GenM Expr) → GenM Expr
  wEtaAt : Array Expr → Nat → Expr → Array Expr → Expr → GenM Expr
  wCtorParts : Array Expr → Nat → Array Expr → GenM (Expr × Expr)
  wMkF : Array Expr → Expr → Array Expr → GenM Expr

/-- The emission state an arm threads: the declarations built so far, the
basis names spliced beside them, the skeleton the model still requires, and
the intrinsic projection overrides it publishes. -/
structure PrimOut where
  out : Array Declaration
  requires : Array Name
  spliced : Array Name
  projectionOverrides : Array (Name × Nat × Expr × Expr)

/-- Open the declaration's parameter telescope. Universe-polymorphic in the
continuation's result, which is why it is a definition over the site rather
than one more closure inside it. -/
def PrimSite.withParams (site : PrimSite) (k : Array Expr → GenM α) : GenM α :=
  forallBoundedTelescope site.memberTy (some site.np) fun ps _ => k ps

set_option maxRecDepth 2048 in
/-- Settle every fact the arms share, in the order the single definition
settled them: the name guards run before the shape analysis, and the shape
analysis before the route booleans that read it. -/
def mkPrimSite (tname : Name) (root : Name) (lparams : List Name) (np : Nat) (memberTy : Expr)
    (exportCtors : Array (Name × Expr)) (reserved : Std.HashSet Name)
    (sourceRecursor? : Option ERec := none)
    (interface? : Option PrimInterfaceNames := none) : GenM (PrimSite × PrimOut) := do
  let us := lparams.map Level.param
  -- **Where the model is built and where it is emitted can differ.** `root` is
  -- the former and `tname` the latter; they are the same name for every
  -- declaration but the handful whose model name is lost to a normalized-name
  -- collision, where [`InductiveModels.genPrim`] retries under an alias root and
  -- renames the export records back. So every *guard*
  -- below is about `tname`'s names — those are what reach the output and what
  -- must not collide with the input — while descendants of `tname` are built
  -- under `root`. An exact raw private constructor need not be a descendant of
  -- its public type name, and then its model name remains raw and exact.
  let interface := interface?.getD (PrimInterfaceNames.standard tname root exportCtors)
  unless interface.ctors.size == exportCtors.size && interface.iotas.size == exportCtors.size do
    badShape s!"{tname}'s implementation name bundle has the wrong constructor arity"
  let model := interface.model
  let impl := interface.impl
  let selfN := interface.self
  let ern := Name.str tname "rec"
  let recN := interface.recursor
  -- `primRuleK` asks for iota slot zero even for a constructorless
  -- declaration, where it immediately observes that K is disabled.  The
  -- historical name function was total; keep this refactoring boundary total
  -- as well so an ordinary declined attempt never emits a caught bounds panic
  -- (and its address-bearing native backtrace) on stderr.
  let ctorN := fun (j : Nat) => interface.ctors[j]?.getD
    (Naming.modelName (Naming.relocateSource tname root
      (exportCtors[j]?.map (·.1) |>.getD (Name.str tname s!"ctor_{j}"))))
  let iotaN := fun (j : Nat) => interface.iotas[j]?.getD
    (Naming.iotaName (Naming.relocateSource tname root ern) j)
  let indN := Name.str impl "ind"
  -- Arm G's **internal** names, guarded exactly like the interface's — but
  -- only when the arm is taken, so a file that declares
  -- `T._model._impl.graph` of its own costs nothing to a declaration this arm
  -- never sees.
  let graphNames : List Name :=
    [indN, Name.str impl "graph", Name.str impl "graph_mk",
     Name.str impl "graph_inv_ty", Name.str impl "graph_inv",
     Name.str impl "graph_unique", Name.str impl "graph_exists",
     Name.str impl "rec_graph"]
  -- Arm C's **internal** names. `skel` is the index erasure, spliced as an
  -- ordinary inductive so that the kernel mints its recursor and its ι is
  -- definitional (the construction uses the real type); `good` is
  -- the carving predicate. Guarded like arm G's, and only when the arm fires.
  let skelN := Name.str impl "skel"
  let goodN := Name.str impl "good"
  let skelCtorN := fun (j : Nat) => Name.str skelN s!"c_{j}"
  let nc := exportCtors.size

  if inductiveBasis.contains tname then declineWith .basisExempt

  -- The guard runs on the **emitted** name and, where the two differ, on the
  -- built one too: the first is the contract this run must not break and the
  -- second is a constant this run is about to add to the environment.
  let taken1 : Name → GenM Unit := fun n => do
    if reserved.contains n || (← getEnv).constants.contains n then declineWith (.nameTaken n)
  let taken : Name → GenM Unit := fun n => do
    let emitted :=
      if model.isPrefixOf n then n.replacePrefix model (Naming.modelName tname) else n
    taken1 emitted
    if root != tname && n != emitted then taken1 n
  taken selfN
  taken recN
  for j in [0:nc] do
    taken (ctorN j)
    taken (iotaN j)

  -- ── shape ──
  -- **A declaration may hide its index telescope behind a definition.** Lean
  -- stores an inductive's type as declared, so `inductive P (X) : Presieve X`
  -- comes back as `(X : C) → Presieve X` with the indices inside the `def`,
  -- and a syntactic peel finds no `Sort` at the end and no indices at all.
  -- Lean's own `numIndices` counts the *unfolded* ones — which is why the
  -- assertion against the recursor below is the cross-check on this and not a
  -- second opinion.
  --
  -- So: peel syntactically first, and only if that does not reach a sort,
  -- re-expose the telescope with a **reducing** telescope and carry on with
  -- the definitionally-equal type that has its binders written out. The retry
  -- is deliberately not the default — every shape that worked before this
  -- reaches the same `memberTy` object it always did, so nothing that was
  -- measured moves.
  let analysis ← analysePrim tname lparams np memberTy exportCtors
  let declaredMemberTy := analysis.declaredMemberTy
  let memberTy := analysis.memberTy
  let ni := analysis.ni
  let w := analysis.w
  let isRec := analysis.isRec
  let rv := analysis.rv
  if let some sourceRecursor := sourceRecursor? then
    validateExactRecursorLayout sourceRecursor rv
  let large := analysis.large
  let v := analysis.v
  let recLs := analysis.recLs
  let nonrecursiveOneConstructor := analysis.nonrecursiveOneConstructor

  let route := analysis.route

  -- **Is the index erasure unnested, and is it linear?** — the two questions arm
  -- C's reach turns on, and the second is the same test the tuple tower
  -- applies ([`InductiveModels.recSlotOf`]). *Unnested* (the historical
  -- `erasureBare` name below): every recursive occurrence reduces to
  -- `∀ z⃗, T p⃗ e⃗`, rather than sitting inside a container. *Linear*:
  -- unnested, and at most one such field per constructor. Erasing the indices
  -- moves neither test — a field `T p⃗ e⃗` erases to `S p⃗`, one field either
  -- way — so both can be asked here, of the family itself, before anything is
  -- built.
  --
  -- Non-throwing on purpose: they are asked of *every* indexed family, and the
  -- ones they say no to are declined with the answer printed, so the Mathlib
  -- census measures the arm's reach instead of estimating it.
  --
  -- **Three reasons, counted apart, and none of the first two still bounds
  -- arm C.** The erasure can fail to be linear by branching (two recursive
  -- fields), by being infinitary (a recursive occurrence under a binder), or
  -- by the occurrence not being an application of `tname` at all. The first
  -- keeps every occurrence bare, which is all that [`InductiveModels.eraseCtorTy`]
  -- and [`InductiveModels.spineSwap`] assume — they replace one recursive field's
  -- occurrence, once per such field, so a constructor with three of them
  -- erases as readily as one. The second keeps the *binders* and moves only
  -- the occurrence under them: `∀ z⃗, T p⃗ e⃗` erases to `∀ z⃗, S p⃗`, and the
  -- three consumers each wrap what they built in the same `z⃗`
  -- ([`InductiveModels.withRecSlot`]). Arm C therefore runs at `erasureBare`, which
  -- is now the third reason alone, and carries **every** recursive slot
  -- through `ctorIdxAt`, `good`'s minor and the constructor's carve proof; the
  -- spliced skeleton that comes out branches and is infinitary, and arm W is
  -- what models *it*.
  --
  -- `erasureLinear` survives because it is what the *decline message* reports,
  -- what the census counts the populations by, and — the load-bearing use —
  -- what says a **non-indexed** declaration is arm W's rather than the tuple
  -- tower's. Relaxing `erasureBare` alone would have taken every infinitary
  -- non-indexed declaration away from arm W and handed it to a tower that
  -- cannot express it, so the infinitary test is split out rather than
  -- deleted.
  let erasureBare := analysis.erasureBare
  let erasureLinear := analysis.erasureLinear

  -- What each route can carry. The Church routes gained indices and recursion
  -- (`churchSwapAt` and the strong-induction fold below); the `Nat`-tagged sum
  -- has neither. At a maybe-zero sort, small elimination uses the Church pair
  -- with `down`/`up` at the carrier boundary, including for indices and
  -- recursion. The lifted arm-F construction below carries the remaining
  -- indexed shape: the large-eliminating nonrecursive singleton.
  -- ── the singleton's index shape, settled before anything is spliced ──
  --
  -- **One analysis for two arms**, because the two limits that used to be
  -- stated separately are one limit. A large-eliminating one-constructor
  -- `Prop` is exactly a declaration each of whose fields is either a *proof*
  -- or a piece of *data that is literally one of the conclusion's index
  -- arguments* — that is the kernel's own subsingleton rule: the
  -- non-`Prop` telescope elements must be a **subset** of the applied
  -- parameters and indices, by identity and not by occurrence), and it is what
  -- makes a model possible at all. A model of a `Prop` can extract its proof
  -- fields by small elimination and has *no way whatever* to extract data, so
  -- the index vector is the only place data can come back from.
  --
  -- Each index position is therefore one of two things:
  --
  -- * a **pivot** — literally one of the constructor's data fields. The model
  --   recovers that field by reading the recursor's own index argument, so it
  --   **substitutes** rather than quantifies. `Acc`'s `x`, `IsHomLift`'s `a`,
  --   `b` and `φ`.
  -- * anything else — an arbitrary expression over the parameters, the data
  --   fields and the *proof* fields: `BadC`'s constant `N.z`, `IsHomLift`'s
  --   `p.obj a`, `Acc.below`'s `Acc.intro x h`, `Inf.below`'s `Inf.mk a`.
  --   Such a position carries nothing the substitution can use and is
  --   discharged instead by a **Henry-Ford equation at the non-pivot
  --   subsequence** — which is what arm F's carrier already was, back when the
  --   arm demanded that *every* position be of this kind.
  --
  -- Read that way the two arms' old refusals were the same refusal seen from
  -- the two ends: arm F took only all-non-pivot index vectors and arm G took
  -- only all-pivot ones, and everything in between — `MixI`, `SvIx`,
  -- `IsHomLift`, every `.below` Lean mints beside a recursive `Prop`, and
  -- `Acc.below` — fell through the gap between them.
  -- `test/fixtures/inductive-models/prim_idx.lean` is the grid.
  let armGRec := (route matches PrimRoute.prop) && large && nc == 1 && isRec
  let armFNonRec := ((route matches PrimRoute.prop) || (route matches PrimRoute.bare)) &&
    large && nc == 1 && ni > 0 && !isRec
  let mut gIsData : Array Bool := #[]
  let mut gIdxPos : Array Nat := #[]
  let mut gRecNb : Array (Option Nat) := #[]
  let mut gNf := 0
  -- Constructor field / pivot-position pairs whose declared index type moves
  -- with a non-pivot. Arm F's zipper transports all of them in field order.
  let mut gPivotTransports : Array (Nat × Nat) := #[]
  -- The index positions that are **not** pivots, in telescope order.
  let mut gNonPiv : Array Nat := #[]
  if armGRec || armFNonRec then
    if armGRec then for n in graphNames do taken n
    let (a, b, cc, npv, pt) ← forallBoundedTelescope memberTy (some np) fun ps _ => do
      let (cn, cty) := exportCtors[0]!
      let tele ← instForall cty ps
      let nfg := numForalls tele
      let flds ← classifyCtor tname nfg tele
      forallBoundedTelescope tele (some nfg) fun fs res => do
        let some args ← ownerAppArgs? tname np ni res
          | badShape s!"{cn} does not end in {tname} at {np} parameters and {ni} indices"
        let idx := args.extract np args.size
        let mut isD : Array Bool := #[]
        let mut pos : Array Nat := #[]
        -- A pivot and the data field which supplies it are one fact, not two.
        -- Keeping the field index here makes the formerly defensive
        -- "pivot with no field" state unrepresentable: an index is a pivot
        -- exactly when this slot is `some i`.
        let mut pivotField : Array (Option Nat) := Array.replicate ni none
        for i in [0:nfg] do
          if (← ilevel (← ityp fs[i]!)).normalize.isZero then
            isD := isD.push false
            pos := pos.push 0
          else
            let mut at? : Option Nat := none
            for k in [0:ni] do
              if at?.isNone && idx[k]! == fs[i]! then at? := some k
            -- **Unreachable from a kernel-accepted declaration, and kept for
            -- inconsistent unchecked exports.** This block is entered only
            -- when the installed recursor is `large`. For a one-constructor
            -- proposition (including the maybe-zero `Sort u` analogue), the
            -- kernel mints that recursor only when every non-proof field is
            -- literally recoverable as a conclusion index. A declaration may
            -- contain an unrecoverable data field and still be accepted, but
            -- its recursor is small and `armFNonRec` / `armGRec` are false.
            -- `arm_f_guards` pins that route boundary. Only a raw export whose
            -- recursor metadata contradicts the installed kernel declaration
            -- can arrive here, and that remains a named decline rather than a
            -- wrong model.
            let some k := at?
              | badShape s!"{cn} has a data field that is not one of the conclusion's \
index arguments, so nothing in the model can recover it — the kernel's own \
subsingleton rule refuses that shape and mints no large eliminator for it"
            isD := isD.push true
            pos := pos.push k
            if pivotField[k]!.isNone then pivotField := pivotField.set! k (some i)
        -- **A pivot's own type may mention an earlier non-pivot index.** Arm
        -- F records every such field.  Its carrier zipper inserts an equality
        -- for the complete earlier index prefix, transports the caller's pivot
        -- back to the constructor field type, and only then binds later proof
        -- fields or recovers another pivot.  `prim_idx`'s `Fmid` and `FChain`
        -- pin the one-pivot cases; `arm_f_zip` adds two pivots, a later proof,
        -- and a final endpoint mentioning the recovered pivot.
        forallBoundedTelescope (← instForall memberTy ps) (some ni) fun is _ => do
          let mut pivotTransports : Array (Nat × Nat) := #[]
          for j in [0:ni] do
            if let some i := pivotField[j]! then
              let jt ← ityp is[j]!
              for m in [0:ni] do
                if pivotField[m]!.isNone && jt.containsFVar is[m]!.fvarId! then
                  unless pivotTransports.contains (i, j) do
                    pivotTransports := pivotTransports.push (i, j)
          return (isD, pos, flds.map (·.rec?),
            (Array.range ni).filter (pivotField[·]!.isNone),
            pivotTransports)
    gIsData := a; gIdxPos := b; gRecNb := cc; gNf := a.size; gNonPiv := npv
    gPivotTransports := pt

  -- **Arm G's half of the index axis.** `GraphInv ι⃗ t val` carries one
  -- equality at the dependent tuple of non-pivot indices.  Its continuation
  -- transports the constructor step from `ι⃗_ctor` to `ι⃗`; pivots stay
  -- fixed because their data fields are supplied from the caller's indices.
  -- Proof-valued non-pivots still reduce for free by proof irrelevance, while
  -- data-valued ones (`BadC`, `Rgd`, and their `.below` declarations) now take
  -- the same explicit packed transport as arm F.
  let armG := armGRec

  let (eqi, eqDecls) ← ensureEq
  let mut out : Array Declaration := eqDecls
  let mut requires : Array Name := #[]
  let mut spliced : Array Name := eqDecls.flatMap (·.getNames.toArray)
  let mut projectionOverrides : Array (Name × Nat × Expr × Expr) := #[]

  let withParams := fun {α : Type} (k : Array Expr → GenM α) =>
    forallBoundedTelescope memberTy (some np) fun ps _ => k ps

  let ctorPairs := (Array.range nc).map fun j => (exportCtors[j]!.1, ctorN j)
  let tbl := modelTable (← getEnv) #[tname]
    { decls := #[], levelParams := lparams, members := #[], selfNames := #[selfN]
      numAll := 1, ctors := ctorPairs, recs := #[recN], iotas := #[], spliced := #[] }
  let installedRecTy := restore tbl rv.type
  -- The one-layer adapter publishes the source interface verbatim modulo
  -- names.  Unlike `restore`, this map retains every source occurrence's
  -- exact universe arguments; installed metadata remains the proof/layout
  -- oracle in `installedRecTy`.
  let exactSource? := interface?.map fun _ => fun expression =>
    mapConstsE (fun name =>
      if name == tname then some selfN
      else if name == ern then some recN
      else ctorPairs.findSome? fun (source, target) =>
        if name == source then some target else none) expression
  let publicSource := fun expression => match exactSource? with
    | some exact => exact expression
    | none => restore tbl expression
  let publicRecTy := publicSource (sourceRecursor?.map (·.type) |>.getD rv.type)

  -- **Arm E**: a non-indexed `Type` every one of whose constructors has a
  -- **bare** recursive field is empty. The tuple tower below deliberately
  -- starts from a base-constructor fibre, so this shape is not a degenerate
  -- tower: its exact model is the empty carrier already provided by the derived
  -- lift of `False`. Each constructor maps to its own recursive field — an
  -- argument of the empty carrier is what it would have to be applied to — and
  -- the recursor and its ι rules eliminate that same empty value. Compute the
  -- slots here so the route branches before the tuple tower asks for its
  -- nonexistent fibre.
  --
  -- **The class is not about linearity, and the guard no longer says it is.**
  -- It used to ask [`InductiveModels.recSlotOf`], which is the *tuple tower's*
  -- question — one recursive field per constructor, that occurrence bare — so
  -- arm E reached only the linear corner of a shape class linearity has nothing
  -- to do with. A constructor with two bare recursive fields is exactly as
  -- unapplicable as one with a single one, and `empty_no_base`'s `NbBr` was
  -- paying a two-hundred-declaration W core and `Classical.choice` for a
  -- carrier that is `⊥`, with `NbLin` beside it paying neither.
  --
  -- **Bare, and not "no base constructor", is the sound statement.**
  -- `empty_no_base`'s `NbVac` recurses under a binder whose domain is empty, so
  -- `E0 → NbVac` is inhabited vacuously and `NbVac` is *inhabited*; a guard
  -- reading "no base constructor" would model it by `⊥`. Whether a binder
  -- domain is empty is not a question available here, so the class stops at the
  -- occurrences that carry an inhabitant of the owner directly, which is
  -- [`InductiveModels.bareRecSlotOf`]. `NbInf` and `NbVac` stay on arm W, and
  -- the file records both counts.
  let emptySlots : Array (Option Nat) ←
    if (route matches PrimRoute.type) && ni == 0 && isRec then
      withParams fun ps =>
        exportCtors.mapM fun (_, cty) => do
          let tele ← instForall cty ps
          bareRecSlotOf tname np ni (numForalls tele) tele
    else
      pure #[]
  let armE := emptySlots.size == nc && nc > 0 && emptySlots.all Option.isSome

  -- A one-field singleton at a maybe-zero sort must retain its field.  The
  -- ordinary Church/lift route records only a proof of inhabitation; at a
  -- positive instantiation two constructor payloads then become equal, so no
  -- intrinsic projection can satisfy both constructor rules.
  --
  -- There are two field-preserving cases this arm implements.
  -- If the field's sort is definitionally the carrier sort, the field itself
  -- is the carrier (`PI`). If the field is exactly a proposition, the derived
  -- lift raises it to the carrier sort without forgetting its proof (`PF`). Test
  -- identity first: `PI.{0}` has a proposition-valued instantiation, but its
  -- polymorphic field sort is the carrier's `u`, not the constant level zero.
  --
  -- **A third case is a gap rather than a boundary.** A field at `Sort u`
  -- under a carrier at `Sort (max u v)` is retained by neither, and the
  -- declaration reaches this arm and no other: the guard above has already
  -- decided that a nonrecursive one-constructor maybe-zero owner is Direct's,
  -- and the Church fallback below would record only inhabitation and lose the
  -- field. The never-zero route closes exactly this level gap with a pad
  -- ([`InductiveModels.unitAt`], [`InductiveModels.dsingAt`]) and this arm has
  -- no pad, so what stops the model is an unfinished arm rather than a shape
  -- the construction decided against. It used to be an internal tool error,
  -- which aborted the stream at an owner the contract says passes through.
  let directFieldRoute? : Option DirectFieldRoute ←
    if (route matches PrimRoute.bare) && nonrecursiveOneConstructor && ni == 0 &&
        numForalls exportCtors[0]!.2 - np == 1 then
      withParams fun ps => do
        let tele ← instForall exportCtors[0]!.2 ps
        let .forallE _ fieldType _ _ := tele
          | badShape s!"{exportCtors[0]!.1} is not a one-field constructor"
        let fieldLevel ← ilevel fieldType
        if ← isLevelDefEq fieldLevel w then return some .identity
        if fieldLevel.normalize.isZero then return some .propLift
        declineWith (.shapeUnsupported tname .incomplete
          s!"{exportCtors[0]!.1}'s only field inhabits Sort {fieldLevel} while the carrier \
inhabits Sort {w}, so neither identity nor the exact-sort lift retains it, and the \
field-preserving arm at a maybe-zero sort has no pad for the level gap the never-zero \
tuple tower pads")
    else
      pure none

  -- Two or more exact-sort fields are retained by a right-nested `PSigma'`.
  let directTightRoute ← planDirectTightRoute tname (route matches PrimRoute.bare)
    nonrecursiveOneConstructor np ni memberTy exportCtors w
  let directRoute? : Option DirectRoute := directFieldRoute?.map DirectRoute.field <|>
    if directTightRoute then some .tight else none

  -- The indexed subsingleton has a different carrier from the Church routes —
  -- a packed index equation, not a fold — so it branches before them. At a
  -- maybe-zero sort this proposition is wrapped in the derived lift, just like the
  -- ordinary Church route; the construction below inserts the matching
  -- `up`/`down` at its boundary.
  -- **Any number of fields.** The arm used to decline above one, because at
  -- zero fields (`HEq`) and one (`TagS`) there is nothing to order and no
  -- fixture could catch a threading bug. `prim_shapes`'s `TagS2`, `TagS3` and
  -- `TagS4` are the two- and three-field occupants that were added to ask, and
  -- the sequential extraction below is correct at all three — kernel-accepted,
  -- statements compared, and red under the field-order mutations.
  --
  -- **Any index shape**, too. The arm's index vector used to have to be built
  -- from the parameters alone; it may now carry **pivots** — positions that
  -- are literally one of the constructor's data fields — anywhere in the
  -- telescope, which is what brings `MixI`, `SvIx` and
  -- `CategoryTheory.Functor.IsHomLift` inside. The analysis above is what says
  -- which positions those are; everything below reads `gNonPiv`.
  let armF := armFNonRec

  -- **Arm S**: the indexed non-recursive singleton whose data the index vector
  -- does **not** carry — arm F's Henry-Ford equation over Direct's exact-sort
  -- storage, and the other half of one axis.
  --
  -- `armF` above is the same declaration shape asked one question: is every
  -- non-proof field literally one of the conclusion's index arguments? That is
  -- also the kernel's own subsingleton rule, so the answer is `large` and the
  -- two are the same fact read at two places. Where the answer is yes, arm F
  -- **substitutes**: it reads each data field off the recursor's own index
  -- argument and Church-conjoins the proof fields, because at a maybe-zero
  -- carrier there is no room to store anything — `Acc.intro`'s `x : α` sits at
  -- a level the `Prop` carrier cannot hold, and the index vector is the only
  -- place it can come back from.
  --
  -- Where the answer is no, that route is not merely narrower, it is
  -- unavailable: a data field the index vector does not mention is recoverable
  -- from nothing at all. **So the model has to store it**, which is exactly
  -- what the direct routes do at `ni == 0`, and the index telescope is then
  -- discharged the way arm F discharges its non-pivots — one packed equation:
  --
  --     T p⃗ ι⃗ := Σ'(t : Store p⃗), pack ι⃗_ctor(proj⃗ t) = pack ι⃗
  --
  -- The two are genuinely different constructions for a statable reason, and
  -- the reason is which side of the carrier the data comes back from. Neither
  -- is a widening of the other: arm F cannot store, and this route cannot
  -- recover a field the storage does not hold.
  --
  -- **`Store` is a definition and not a spliced inductive**, which is what
  -- separates this from arm C. Arm C's erase-and-carve is the same idea — build
  -- the index-free skeleton, then cut the family out of it — but it splices the
  -- skeleton as an *inductive* so the kernel mints its large eliminator, and it
  -- needs that eliminator twice. A maybe-zero skeleton has no large eliminator
  -- to mint, so the stepping stone here is [`InductiveModels.tightTowerTy`], a
  -- `PSigma'` tower whose projections are structure projections and need no
  -- elimination grant at all.
  --
  -- Restricted to the maybe-zero route on purpose. At a never-zero sort this
  -- shape is arm C's; at a literal `Prop` the storage would have to land at
  -- `Sort 0`, which means every field is a proof, which means arm F has already
  -- fired — and a `Prop` owner is asked for no data projection in the first
  -- place ([`InductiveModels.eligibleProjectionFieldsM`]'s `ownerIsProp` gate),
  -- so there is nothing there for this route to retain.
  let armS ← planIndexedStoreRoute tname
    ((route matches PrimRoute.bare) && nc == 1 && !isRec && ni > 0 && !armF)
    np memberTy exportCtors w

  -- **Arm C**: an indexed family at a never-zero sort, carved out of its own
  -- index erasure. Gated on the erasure being
  -- **bare** — every recursive occurrence a `T p⃗ e⃗` whose whole domain the
  -- erasure can replace — and no longer on its being *linear*: the carve
  -- carries an arbitrary number of recursive slots per constructor, and the
  -- branching skeleton that results is modelled by arm W. A family whose
  -- skeleton does not model is still a decline and never an emission, which is
  -- `Iso.requires`' job and not this guard's.
  let armC := (route matches PrimRoute.type) && ni > 0 && erasureBare

  -- **Arm W**: the tagged W construction, and the **decision** that splits the
  -- non-indexed recursive `Type` class in two.
  --
  -- Two constructions model that class and they are not ranked by reach: the
  -- tuple tower expresses a *linear* spine and nothing else, because its spine
  -- is one `Nat` and a step constructor takes exactly one predecessor; the W
  -- scheme expresses an arbitrary branching, infinitary tree. `erasureLinear`
  -- is precisely the shape question those two differ on — one bare recursive
  -- field per constructor, which is exactly [`InductiveModels.recSlotOf`]'s two
  -- refusals complemented — so the class partitions on it with no overlap and
  -- no remainder.
  --
  -- **`!erasureLinear` is therefore a decision, not a refusal boundary**, and
  -- what decides it is cost rather than reach: on the linear side the tower
  -- costs `Nat`, `PSigma'` and no axiom and every ι rule is `Eq.refl`, while W
  -- splices a two-hundred-declaration core and proves its ι rules through
  -- `WT.Wrec_iota`. Taking W wherever it *applies* would move six thousand
  -- models onto the heavier construction for nothing. Neither side is a
  -- fallback for the other: a declaration this sends to W is one the tower
  -- cannot express, and a declaration it sends to the tower is one W would
  -- overcharge.
  --
  -- **What is *not* part of that decision** are the two conditions that turn
  -- `armW` off below. Neither is a statement about the shape: they are gaps in
  -- the arm as it stands, and [`InductiveModels.primIsoWithInterface`] reports
  -- a declaration they stop as `.shapeUnsupported .incomplete`, naming the
  -- guard, before anything is installed. That verdict is the whole point of the
  -- separation — "no construction represents this" and "the construction that
  -- owns this is short a piece" are different facts, and the tuple tower must
  -- never be the place either of them is discovered.
  --
  -- * **the internal carrier is `Type u`.** `WT.W.{u,w}` fixes `A` and `B'`
  --   at `Type u`. Ordinarily the public carrier already has that shape; at a
  --   never-zero carrier with no syntactic predecessor the arm runs the core
  --   at `Type` and stores that low carrier in a `PSigma'` whose second
  --   component is the derived lift of `True`, landing at the exact public
  --   `Sort w` with no cumulative definition conversion assumed. Where
  --   neither is available the core has no level to be written at.
  -- * **`labelFactored`.** The core is generic in `K`, `B' : K → Type u` and
  --   `tg : A → K`, and the arm runs it at **two** instantiations of one
  --   construction. At `K := Nat`, `tg := PSigma'.fst` the branch type is a
  --   function of the *tag* and cannot see the label's data, which is
  --   [`InductiveModels.tagFactored`]; at `K := A`, `tg := id` it sees all of
  --   it and only an earlier *recursive* field is out of reach, which is
  --   [`InductiveModels.labelFactored`]. `tagFactored` picks the column — the
  --   tagged instantiation takes `instDecidableEqNat` and stays at
  --   `[propext, Quot.sound]`, the untagged one takes `WT.decEqAll` and pays
  --   `Classical.choice`.
  --
  --   **It is not the dead guard it reads as, and the reason is worth
  --   recording.** Its *semantic* content — a recursive field's binder type
  --   naming an earlier recursive field — has an empty refusal class for a
  --   kernel-accepted plain inductive: the binder would have to apply a type
  --   former to a value of the type being declared, which Lean's positivity and
  --   nesting rules leave no spelling of (`Projection.lean`'s argument, written
  --   out for the kernel to reject in
  --   `test/fixtures/inductive-models/nested_value_dependency.lean`). But the
  --   test is `mentionsAny` on the field's domain **as written**, and that is
  --   deliberate: [`InductiveModels.wShapeOf`] splits the two towers by exactly
  --   the same written-domain test, so a field whose owner mention βζ discards
  --   is a *branch* to the arm and must be one here too. Such a field makes
  --   this answer `false` on a declaration the kernel accepts, and correctly:
  --   arm W's own tower check refuses it a few lines later. So it is a live
  --   guard on an over-approximated question, not an invariant — which is why
  --   it stays a conjunct and is reported as `incomplete` rather than asserted.
  --
  -- **`!armE` is part of the decision and not part of the shape.** A branching
  -- declaration with no base constructor is in the W class by every question
  -- above and is *empty*, and W would duly build a W-type with no leaves — a
  -- spliced core, `Classical.choice`, two hundred declarations, for a carrier
  -- that is `⊥`. Arm E's carrier *is* `⊥`, at the declaration's own sort, with
  -- no axiom. Where both apply the exact model wins, and saying so here rather
  -- than in the dispatcher's `if`-order is what makes these booleans mutually
  -- exclusive *facts* of the site: the arms and [`InductiveModels.primIotaRules`]
  -- read the same decision instead of each re-deriving it from the order they
  -- happen to test in.
  let wTagged := tagFactored tname np exportCtors
  let wShapeEligible :=
    (route matches PrimRoute.type) && ni == 0 && isRec && !erasureLinear && !armE &&
    labelFactored tname np exportCtors
  let wPlan ← wCarrierPlan wShapeEligible w
  let armW := wShapeEligible && (w.normalize.dec.isSome || wPlan.lifted)
  let wW := wPlan.coreLevel
  -- Arm W's **internal** names, guarded exactly like arm C's and arm G's, and
  -- only when the arm is taken.
  let wDN := Name.str impl "wD"
  let wTelN := Name.str impl "wTel"
  let wBN := Name.str impl "wB"
  let wAN := Name.str impl "wA"
  let wTgN := Name.str impl "wtg"
  let wFN := Name.str impl "wF"

  -- ── the kit arm C needs: Church conjunction's two projections and its
  -- introduction, built here because [`InductiveModels.andCOf`] gives the type only.
  let andCMk := fun (A B a b : Expr) => withLocalDeclD `D (.sort .zero) fun D => do
    withLocalDeclD `k (.forallE `a A (.forallE `b B D .default) .default) fun kk =>
      mkLambdaFVars #[D, kk] (mkAppN kk #[a, b])
  let andCFst := fun (A B p : Expr) => do
    let sel ← withLocalDeclD `a A fun a => withLocalDeclD `b B fun b =>
      mkLambdaFVars #[a, b] a
    pure (mkAppN p #[A, sel])
  let andCSnd := fun (A B p : Expr) => do
    let sel ← withLocalDeclD `a A fun a => withLocalDeclD `b B fun b =>
      mkLambdaFVars #[a, b] b
    pure (mkAppN p #[B, sel])

  -- ── arm W's builders ──
  -- Defined here rather than inside the arm because the **ι block below needs
  -- them too**: an arm W ι rule is `WT.Wrec_iota` at this declaration's own
  -- `F`, its label and its dispatch, and those have to be rebuilt at the ι
  -- theorem's telescope. Defining a closure costs nothing to a declaration
  -- that never calls it, and every one of these declines rather than returning
  -- a wrong answer when it is called at a shape arm W does not reach.
  let wNatT : Expr := .const `Nat []
  -- `Type u` for the internal `Sort wW` carrier. Meaningless — and unused —
  -- unless `armW`, whose carrier plan proved `wW` successor-shaped.
  let uL := wW.normalize.dec.getD .zero
  -- **The core's `K` level**, and the one place the two instantiations differ
  -- in the level lists rather than in a term: `K = Nat : Type 0` tagged and
  -- `K = A p⃗ : Type u` untagged. The core's own binders are
  -- `WT.W.{u,w}`, `WT.sup.{u,w}`, `WT.Wrec.{u,v,w}` and
  -- `WT.Wrec_iota.{u,v,w}` with `w` last, so every list below gains it there.
  let wKL := if wTagged then Level.zero else uL

  -- **Constructor `k`'s field split**, as positions into its own telescope.
  -- The data tower holds the non-recursive fields and the branch tower the
  -- recursive ones, and the two index *different* subsequences of one
  -- telescope: a generator that took "the fields before the first recursive
  -- one" as the data would silently lose every field that sits after a child.
  --
  -- There is deliberately no second guard for a later data field whose type
  -- mentions an earlier child. A kernel-accepted plain inductive cannot
  -- inspect a recursive value while the inductive is still being declared:
  -- putting that value in a later field's type requires a foreign dependent
  -- family/container application, which Lean classifies as nesting and rejects
  -- when the occurrence depends on a constructor local (the exact rejected
  -- shape documented in `indexed_decl.lean` and `nest_fam_arg.lean`). Nested
  -- input does not reach `genPrim` in any case: `Driver` sends it through
  -- `Plan.plan`, whose `mimicFor` repeats that constructor-local check before
  -- specialising the block. The former `hasLooseBVar` refusal here was thus a
  -- guard for metadata the replaying kernel cannot install, not a model shape.
  let wShapeOf : Nat → GenM (Array Nat × Array Nat) := fun k => do
    let (cn, cty) := exportCtors[k]!
    let mut t := cty
    for _ in [0:np] do
      let .forallE _ _ b _ := t
        | badShape s!"{cn}'s telescope is shorter than {np} parameters"
      t := b
    let mut nrs : Array Nat := #[]
    let mut rcs : Array Nat := #[]
    let mut i := 0
    while t matches .forallE .. do
      let .forallE _ dom b _ := t | unreachable!
      if mentionsAny #[tname] dom then rcs := rcs.push i
      else
        nrs := nrs.push i
      t := b
      i := i + 1
    return (nrs, rcs)
  let wRecCount : Nat → GenM Nat := fun k => return (← wShapeOf k).2.size

  -- The five definitions the core is instantiated at, as applications of the
  -- names declared in the arm. `D` and `Tel` are the towers; `B'`, `A` and
  -- `tg` are one line each and exist as declarations rather than as inlined
  -- terms so that `self`, every constructor and `rec_0` name them instead of
  -- carrying a copy.
  let wDAt : Array Expr → Expr := fun ps => mkAppN (.const wDN us) ps
  let wAAt : Array Expr → Expr := fun ps => mkAppN (.const wAN us) ps
  -- `⟨t, d⟩ : A p⃗`, with the tag as an *expression* — the recursor's cascade
  -- needs it at a variable index. `A` is `Σ' t : Nat, D p⃗ t` in **both**
  -- instantiations: what the untagged one changes is `K`, not the label.
  let wLabel : Array Expr → Expr → Expr → Expr := fun ps t d =>
    psigmaMk (.succ .zero) wW wNatT (wDAt ps) t d
  -- **The core's `K`, and the value in it a constructor's branch type is taken
  -- at.** Tagged: `Nat`, and the value is the tag. Untagged: the label type
  -- itself, and the value is that constructor's whole label — which is why
  -- everything below threads `key` where the tagged transcription threaded a
  -- `Nat` literal. `wKeyOf` is the *only* place the two differ.
  let wKTy : Array Expr → Expr := fun ps => if wTagged then wNatT else wAAt ps
  let wKeyOf : Array Expr → Nat → Expr → Expr := fun ps k d =>
    if wTagged then natNumeral k else wLabel ps (natNumeral k) d
  let wTelFn : Array Expr → Expr → GenM Expr := fun ps key =>
    withLocalDeclD `j wNatT fun j =>
      mkLambdaFVars #[j] (mkAppN (.const wTelN us) (ps ++ #[key, j]))
  let wBAt : Array Expr → Expr → GenM Expr := fun ps key =>
    return psigmaT (.succ .zero) wW wNatT (← wTelFn ps key)
  let wBFn : Array Expr → Expr := fun ps => mkAppN (.const wBN us) ps
  let wTgAt : Array Expr → Expr := fun ps => mkAppN (.const wTgN us) ps
  -- **`DecidableEq K`, and the whole of the second bill.** One declaration,
  -- `[propext, Quot.sound]` on the left of it and
  -- `[propext, Classical.choice, Quot.sound]` on the right.
  let wDecEq : Array Expr → Expr := fun ps =>
    if wTagged then .const wCoreDecEqNat []
    else mkApp (.const wCoreDecEqAll [wW]) (wAAt ps)
  let wSup : Array Expr → Expr → Expr → Expr := fun ps a f =>
    mkAppN (.const wCoreSup [uL, wKL])
      #[wKTy ps, wAAt ps, wBFn ps, wDecEq ps, wTgAt ps, a, f]
  let wLowSelfAt : Array Expr → Expr := fun ps =>
    mkAppN (.const wCoreSelf [uL, wKL]) #[wKTy ps, wAAt ps, wBFn ps, wTgAt ps]
  -- At the constrained-lift instantiation the low W lives in `Type` while the
  -- public carrier must live in the literal `Sort w`. `PSigma'` supplies that
  -- exact result sort; the second field is a canonical inhabitant of
  -- the derived lift of `True`, so wrapping and unwrapping reduce by the structure
  -- projection and eta rules and add no axiom.
  -- `⟨j, tel⟩ : B' p⃗ key`, with the branch index as an expression for the same
  -- reason.
  let wBranch : Array Expr → Expr → Expr → Expr → GenM Expr := fun ps key j tel =>
    return psigmaMk (.succ .zero) wW wNatT (← wTelFn ps key) j tel

  -- The two towers, at a parameter scope.
  let wDataTy : Array Expr → Nat → GenM Expr := fun ps k => do
    let (nrs, _) ← wShapeOf k
    let tele ← instForall exportCtors[k]!.2 ps
    forallBoundedTelescope tele (some (numForalls tele)) fun fs _ =>
      wTowerTyOf wW (nrs.map (fs[·]!))
  -- **The data tower's components, read out of a label's data** — the values
  -- the branch tower's binder types are written in terms of wherever only the
  -- label is in hand, which is everywhere but a constructor's own body.
  let wNrProjs : Array Expr → Nat → Expr → GenM (Array Expr) := fun ps k d => do
    let (nrs, _) ← wShapeOf k
    let tele ← instForall exportCtors[k]!.2 ps
    forallBoundedTelescope tele (some (numForalls tele)) fun fs _ =>
      wTowerProjsOf wW (nrs.map (fs[·]!)) d
  -- **Constructor `k`'s recursive field `r`, at its own non-recursive fields
  -- replaced by `nrv`** — and this substitution is the untagged arm.
  --
  -- Tagged, `Tel` is a function of the tag and `labelFactored`'s stronger
  -- sibling guarantees the domain mentions no field at all, so `replaceFVars`
  -- finds nothing and the tagged transcription is byte-identical. Untagged, the
  -- domain may mention the constructor's non-recursive fields — `WType.mk`'s
  -- `β a → WType β` is the shape — and what stands in their place is whatever
  -- the caller has: the fields themselves inside the constructor, the label's
  -- projections inside `F`.
  let wRecDom : Array Expr → Nat → Nat → Array Expr → GenM Expr := fun ps k r nrv => do
    let (nrs, rcs) ← wShapeOf k
    let tele ← instForall exportCtors[k]!.2 ps
    forallBoundedTelescope tele (some (numForalls tele)) fun fs _ => do
      return (← ityp fs[rcs[r]!]!).replaceFVars (nrs.map (fs[·]!)) nrv
  let wTelTy : Array Expr → Nat → Array Expr → Nat → GenM Expr := fun ps k nrv r => do
    forallTelescope (← wRecDom ps k r nrv) fun zs _ => wTowerTyOf wW zs

  -- **The dispatch cascade at tag `k`**, as a function of the branch index:
  -- `wDispAt ps k child sc : Tel p⃗ k sc → T._model.self p⃗`. `child r zs vs` is
  -- the `r`-th child at the binder values `vs` — the constructor's own field
  -- where a constructor is being built, and `f ⟨r, ⟨z⃗⟩⟩` where the recursor
  -- is. One builder for both is what makes the eta lemma's `rfl` hold: the
  -- term the lemma's left side reduces to is *this* term.
  let wDispAt : Array Expr → Nat → Expr → Array Expr →
      (Nat → Array Expr → Array Expr → GenM Expr) → Expr → GenM Expr :=
    fun ps k key nrv child sc => do
    let (_, rcs) ← wShapeOf k
    let selfTy := wLowSelfAt ps
    let dom := fun (jj : Expr) => mkAppN (.const wTelN us) (ps ++ #[key, jj])
    let s ← ilevel (.forallE `tel (dom (natNumeral 0)) selfTy .default)
    let motAt : Nat → GenM Expr := fun r =>
      withLocalDeclD `j wNatT fun j =>
        mkLambdaFVars #[j] (.forallE `tel (dom (natSuccs r j)) selfTy .default)
    let armAt : Nat → GenM Expr := fun r => do
      forallTelescope (← wRecDom ps k r nrv) fun zs _ => do
        withLocalDeclD `tel (← wTowerTyOf wW zs) fun tel => do
          mkLambdaFVars #[tel] (← child r zs (← wTowerProjsOf wW zs tel))
    let junkAt : Expr → GenM Expr := fun t =>
      withLocalDeclD `tel (dom (natSuccs rcs.size t)) fun tel => do
        mkLambdaFVars #[tel] (← emptyAtElim eqi wW wW selfTy tel)
    natCascade s rcs.size motAt armAt junkAt 0 sc
  -- The same, packaged as `fun b : B' p⃗ key => …`. The eta lemma below is
  -- stated against **these** `b.1` and `b.2`, so the two must be built here.
  let wDispLam : Array Expr → Nat → Expr → Array Expr →
      (Nat → Array Expr → Array Expr → GenM Expr) → GenM Expr :=
    fun ps k key nrv child => do
    let β ← wTelFn ps key
    withLocalDeclD `b (← wBAt ps key) fun b => do
      let b1 := psigmaFst (.succ .zero) wW wNatT β b
      let b2 := psigmaSnd (.succ .zero) wW wNatT β b
      mkLambdaFVars #[b] (mkApp (← wDispAt ps k key nrv child b1) b2)

  -- **The eta lemma** — `dispatch = f`, and the whole of the per-constructor
  -- glue. It is
  -- enough to prove `∀ j tel, dispatch j tel = f ⟨j, tel⟩` and instantiate at
  -- `b.1, b.2`, because `⟨b.1, b.2⟩ ≡ b` is `PSigma'`'s definitional eta — so
  -- **no `PSigma'.rec'` appears in the proof at all**. Every real branch is
  -- `Eq.refl`: at branch `r` the left side reduces to `f ⟨r, ⟨tel.1, …, ⟨⟩⟩⟩`
  -- and the right is `f ⟨r, tel⟩`, and those are the same term by that eta
  -- once more and by the terminating unit's own canonicity. Off the end of the
  -- telescope the branch is uninhabited and the arm is its eliminator.
  let wEtaAt : Array Expr → Nat → Expr → Array Expr → Expr → GenM Expr :=
    fun ps k key nrv f => do
    let (_, rcs) ← wShapeOf k
    let selfTy := wLowSelfAt ps
    let dom := fun (jj : Expr) => mkAppN (.const wTelN us) (ps ++ #[key, jj])
    let child : Nat → Array Expr → Array Expr → GenM Expr := fun r zs vs =>
      return mkApp f (← wBranch ps key (natNumeral r) (← wTowerMkOf wW zs vs))
    let stmt : Expr → Expr → GenM Expr := fun jj tel => do
      let lhs := mkApp (← wDispAt ps k key nrv child jj) tel
      return eqi.mk' wW selfTy lhs (mkApp f (← wBranch ps key jj tel))
    let motAt : Nat → GenM Expr := fun r =>
      withLocalDeclD `j wNatT fun j => do
        let jj := natSuccs r j
        let body ← withLocalDeclD `tel (dom jj) fun tel => do
          mkForallFVars #[tel] (← stmt jj tel)
        mkLambdaFVars #[j] body
    let armAt : Nat → GenM Expr := fun r => do
      forallTelescope (← wRecDom ps k r nrv) fun zs _ => do
        withLocalDeclD `tel (← wTowerTyOf wW zs) fun tel => do
          mkLambdaFVars #[tel]
            (eqi.refl' wW selfTy (mkApp f (← wBranch ps key (natNumeral r) tel)))
    let junkAt : Expr → GenM Expr := fun t => do
      let jj := natSuccs rcs.size t
      withLocalDeclD `tel (dom jj) fun tel => do
        mkLambdaFVars #[tel] (← emptyAtElim eqi .zero wW (← stmt jj tel) tel)
    let β ← wTelFn ps key
    let bTy ← wBAt ps key
    let pointwise ← withLocalDeclD `b bTy fun b => do
      let b1 := psigmaFst (.succ .zero) wW wNatT β b
      let b2 := psigmaSnd (.succ .zero) wW wNatT β b
      mkLambdaFVars #[b] (mkApp (← natCascade .zero rcs.size motAt armAt junkAt 0 b1) b2)
    let cod ← withLocalDeclD `x bTy fun x => mkLambdaFVars #[x] selfTy
    return mkAppN (.const wCoreFunext [wW, wW])
      #[bTy, cod, ← wDispLam ps k key nrv child, f, pointwise]

  -- **One constructor's label and dispatch, from its own field vector** — the
  -- constructor's body, and the two arguments the ι rule hands `Wrec_iota`.
  let wCtorParts : Array Expr → Nat → Array Expr → GenM (Expr × Expr) :=
    fun ps k fields => do
      let (nrs, rcs) ← wShapeOf k
      let nrv := nrs.map (fields[·]!)
      let tower ← wTowerMkOf wW nrv nrv
      let child : Nat → Array Expr → Array Expr → GenM Expr := fun r _ vs =>
        return wPlan.unwrap (wLowSelfAt ps) (mkAppN fields[rcs[r]!]! vs).headBeta
      -- The branch tower is written at the constructor's **own** fields here
      -- rather than at projections of the tower it just built: the two are
      -- definitionally equal by `PSigma'`'s ι rule, and the fields are what the
      -- dispatch's children are applied to anyway.
      return (wLabel ps (natNumeral k) tower,
              ← wDispLam ps k (wKeyOf ps k tower) nrv child)

  -- **`F`, the minor the core's recursor takes** — one `Nat.rec` cascade over
  -- the tag whose motive must be well-typed at *every* tag, the eta lemma's
  -- transport inside each arm, and the junk arm discharged from the emptiness
  -- of `D`. This is the term whose construction validates the emitted shape.
  let wMkF : Array Expr → Expr → Array Expr → GenM Expr := fun ps motive minors => do
    let selfTy := wLowSelfAt ps
    let coreMotive ← wPlan.motive (wLowSelfAt ps) motive
    -- The frame every arm and the motive share: `(d : D p⃗ t)
    -- (f : B' p⃗ key → self) (ih : (b : B' p⃗ key) → C (f b))`, and the label
    -- `⟨t, d⟩` built from `d`.
    --
    -- **`d` is introduced before the branch type is written**, which the
    -- tagged transcription had no reason to do: untagged, `key` *is* the label
    -- and the label holds `d`. The core asks for `B' (tg ⟨t,d⟩)`, and `key` is
    -- that reduced — `t` tagged, `⟨t,d⟩` untagged.
    let frame : Expr → (Expr → Expr → Expr → Expr → Expr → GenM Expr) → GenM Expr :=
      fun tag k => do
        withLocalDeclD `d (mkAppN (.const wDN us) (ps ++ #[tag])) fun d => do
          let a := wLabel ps tag d
          let key := if wTagged then tag else a
          let bt ← wBAt ps key
          withLocalDeclD `f (.forallE `b bt selfTy .default) fun f => do
            let ihT ← withLocalDeclD `b bt fun b =>
              mkForallFVars #[b] (mkApp coreMotive (mkApp f b))
            withLocalDeclD `ih ihT fun ih => k d f ih a key
    let motBody : Nat → Expr → GenM Expr := fun kk t =>
      frame (natSuccs kk t) fun d f ih a _ =>
        mkForallFVars #[d, f, ih] (mkApp coreMotive (wSup ps a f))
    let s ← withLocalDeclD `t wNatT fun t => do ilevel (← motBody 0 t)
    let motAt : Nat → GenM Expr := fun kk =>
      withLocalDeclD `t wNatT fun t => do mkLambdaFVars #[t] (← motBody kk t)
    let armAt : Nat → GenM Expr := fun kk => do
      let (nrs, rcs) ← wShapeOf kk
      let tag := natNumeral kk
      frame tag fun d f ih a key => do
        -- **The data tower's components come first**, because untagged they are
        -- what the branch tower's own binder types are written in terms of —
        -- `WType.mk`'s child is `β a → WType β` and the `a` here is `d.1`.
        let projs ← wNrProjs ps kk d
        -- the children and their induction hypotheses, read off `f` and `ih`
        let child : Nat → Array Expr → Array Expr → GenM Expr := fun r zs vs =>
          return mkApp f (← wBranch ps key (natNumeral r) (← wTowerMkOf wW zs vs))
        let disp ← wDispLam ps kk key projs child
        let tele ← instForall exportCtors[kk]!.2 ps
        let nf := numForalls tele
        let mut kids : Array Expr := #[]
        let mut ihs : Array Expr := #[]
        for r in [0:rcs.size] do
          let (kd, ihv) ← forallTelescope (← wRecDom ps kk r projs) fun zs _ => do
            let bv ← wBranch ps key (natNumeral r) (← wTowerMkOf wW zs zs)
            return (← mkLambdaFVars zs (wPlan.wrap (wLowSelfAt ps) (mkApp f bv)),
              ← mkLambdaFVars zs (mkApp ih bv))
          kids := kids.push kd
          ihs := ihs.push ihv
        -- Lean's minor takes the fields in declaration order and then the
        -- hypotheses, which is what the two towers have to be re-interleaved
        -- into: the data tower's components and the branch tower's children
        -- index different subsequences of one telescope.
        let mut args : Array Expr := #[]
        for i in [0:nf] do
          match nrs.findIdx? (· == i) with
          | some q => args := args.push projs[q]!
          | none =>
            let some r := rcs.findIdx? (· == i)
              | badShape s!"{exportCtors[kk]!.1}'s field {i} is in neither tower"
            args := args.push kids[r]!
        let base := mkAppN minors[kk]! (args ++ ihs)
        -- The minor's result is `C` at the constructor **rebuilt from the
        -- children**, which is `sup ⟨k, d⟩ dispatch` and not `sup ⟨k, d⟩ f`.
        -- The eta lemma is what closes that, and it is the one place this arm
        -- spends anything the tuple tower does not.
        let h ← wEtaAt ps kk key projs f
        let αf := Expr.forallE `b (← wBAt ps key) selfTy .default
        mkLambdaFVars #[d, f, ih]
          (← transportAlong eqi v wW αf disp f h base fun z =>
            pure (mkApp coreMotive (wSup ps a z)))
    let junkAt : Expr → GenM Expr := fun t => do
      let tag := natSuccs nc t
      frame tag fun d f ih a _ => do
        mkLambdaFVars #[d, f, ih]
          (← emptyAtElim eqi v wW (mkApp coreMotive (wSup ps a f)) d)
    withLocalDeclD `a (wAAt ps) fun a => do
      let a1 := psigmaFst (.succ .zero) wW wNatT (wDAt ps) a
      let a2 := psigmaSnd (.succ .zero) wW wNatT (wDAt ps) a
      mkLambdaFVars #[a] (mkApp (← natCascade s nc motAt armAt junkAt 0 a1) a2)

  return ({ tname, root, lparams, np, memberTy, exportCtors, reserved, sourceRecursor?, interface?, us, model, impl, selfN, ern, recN, ctorN, iotaN, indN, skelN, goodN, skelCtorN, nc, taken, declaredMemberTy, ni, w, isRec, rv, large, v, recLs, nonrecursiveOneConstructor, route, erasureBare, erasureLinear, gIsData, gIdxPos, gRecNb, gNf, gPivotTransports, gNonPiv, armG, eqi, ctorPairs, tbl, installedRecTy, exactSource?, publicSource, publicRecTy, emptySlots, armE, directRoute?, armF, armS, armC, wTagged, wPlan, armW, wW, wDN, wTelN, wBN, wAN, wTgN, wFN, andCMk, andCFst, andCSnd, wNatT, uL, wKL, wShapeOf, wRecCount, wDAt, wAAt, wLabel, wKTy, wKeyOf, wTelFn, wBAt, wBFn, wTgAt, wDecEq, wSup, wLowSelfAt, wBranch, wDataTy, wNrProjs, wRecDom, wTelTy, wDispAt, wDispLam, wEtaAt, wCtorParts, wMkF },
          { out, requires, spliced, projectionOverrides })

end InductiveModels
