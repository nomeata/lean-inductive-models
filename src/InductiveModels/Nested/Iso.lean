import InductiveModels.Naming
import InductiveModels.Plan
import InductiveModels.Gen.Iso
import InductiveModels.Gen.Prelude
import InductiveModels.Gen.WCore
import InductiveModels.Nested.Rules

/-!
# The nested construction's driver

`iso` builds one nested declaration's model, or says which shape stopped it.
`mimicGroups` decides the order the mimics' `pack`s are emitted in, and
`Gen.iotaDecls` emits one member's recursor's ι rules.
-/

open Lean Meta

namespace InductiveModels
/-- **The ι rules of one member's recursor**, one per rule `Bₖ.rec` carries, in
the order it carries them.

Each comes back as `(the export's constructor, the theorem's name, the
theorem)`. The constructor is the key the *installed* `T.rec_k` files its rule
under — `Tree.node` at the root, `List.cons` at a mimic — so a consumer can line
the two up without knowing how the block was named. -/
def Gen.iotaDecls (g : Gen) (sh : Gen.RecShape) (ctorTys : Array (Name × Name × Expr))
    (sourceRecursor? : Option ERec := none) (exactSource : Expr → Expr := id) :
    GenM (Array (Name × Name × Declaration)) := do
  let minorBase := (Array.range sh.k).foldl (fun a i => a + g.blockCtors[i]!.size) 0
  -- The export's constructors are flattened in `all` order, so a **real**
  -- member's `j`-th is at this offset; a mimic's key is the real container's.
  let ctorBase := (Array.range (min sh.k g.numAll)).foldl
    (fun a i => a + g.blockCtors[i]!.size) 0
  let cs := g.blockCtors[sh.k]!
  (Array.range cs.size).mapM fun j =>
    forallBoundedTelescope sh.ty (some (g.np + sh.nm + sh.nmin)) fun pre _ => do
      let ps := pre.extract 0 g.np
      let motives := pre.extract g.np (g.np + sh.nm)
      let minors := pre.extract (g.np + sh.nm) pre.size
      let bcn := cs[j]!
      let key : Name × Name × List Level × Array Expr × Expr ←
        if g.isReal sh.k then do
          let (exportC, modelC, mty) := ctorTys[ctorBase + j]!
          pure (exportC, modelC, g.us, ps, ← instForall mty ps)
        else do
          let real ← g.realCtor (g.mimicOf sh.k) ps bcn
          let (_, cls, qs) ← g.container (g.mimicOf sh.k) ps
          pure (real, real, cls, qs, ← instCtor real cls qs)
      let (exportKey, head, hls, hpre, ectorTy) := key
      withFields ectorTy fun fields extTys => do
        -- Open the block constructor at the **same field variables** as the
        -- export constructor. Opening it independently and returning its
        -- field types leaks temporary binders whenever a later field type
        -- depends on an earlier one (`C.step`'s nested field is indexed by its
        -- preceding `j`). Those leaked variables made the generated iota
        -- theorem fail the kernel's closedness check.
        let blkTys ← fieldTypesAt (← instCtor bcn g.us ps) fields
        if fields.size != blkTys.size then
          badShape s!"{bcn}: the export binds {fields.size} fields, the block {blkTys.size}"
        let mem := blkTys.map g.memberOf
        let packed ← blkTys.mapM g.mimicUnder?
        -- **The hypothesis vector, in the minor's own order.** `Bₖ.rec` gives a
        -- field of type `∀ x⃗, Bₘ …` an induction hypothesis too — Lean supports
        -- infinitary constructors and `FTree.branch : (N → FTree) → FTree` is
        -- one — so the vector has an entry for it and the right-hand side below
        -- writes `fun x⃗ => T._model.rec_m … (f x⃗)` there.
        let (ihAt, _) ← g.ihVector blkTys
        let moving := (Array.range blkTys.size).filter fun x => packed[x]!.isSome
        -- **The hypothesis types, read off the minor and not rebuilt.** The
        -- minor binds the export-side fields, so instantiating it at `fields`
        -- leaves the hypothesis telescope in their terms; taking the binder
        -- names from there is what makes `fun (a_1 : N) => rec_0 … (a a_1)`
        -- compare equal to the rule the export carries.
        let minorIx := minorBase + j
        let nIh := (ihAt.filter (·.isSome)).size
        let ihTyVec ← forallBoundedTelescope
          (← instantiateForall (← ityp minors[minorIx]!) fields) (some nIh)
          fun vs _ => vs.mapM ityp
        let mut ihTys : Array (Option Expr) := #[]
        let mut t := 0
        for a in ihAt do
          if a.isSome then ihTys := ihTys.push ihTyVec[t]?; t := t + 1
          else ihTys := ihTys.push none
        let r : Rule :=
          { g, k := sh.k, v := sh.v, ps, motives, minors, minorIx
            head, headLevels := hls, headPrefix := hpre
            fields, extTys, bcn, blkTys, mem, packed, ihAt, ihTys, moving }
        let tel := pre ++ fields
        let installedStatement ← r.statement
        let (statement, fieldTelescope, recursorTelescope) ← match sourceRecursor? with
          | none => pure (installedStatement, ectorTy, sh.ty)
          | some sourceRecursor => do
            let some sourceRule := sourceRecursor.rules[j]?
              | badShape s!"{sourceRecursor.name} has no exported rule {j}"
            unless sourceRule.ctor == exportKey do
              badShape s!"{sourceRecursor.name}'s exported rule {j} is for {
                sourceRule.ctor}, not {exportKey}"
            unless sourceRule.nfields == fields.size do
              badShape s!"{sourceRecursor.name}'s exported rule {j} has {
                sourceRule.nfields} fields, not {fields.size}"
            let some exactFields := exactRecursorFieldTelescope? sourceRecursor j pre
              | badShape s!"{sourceRecursor.name}'s exported rule {j} has no exact field telescope"
            let equality := installedStatement.getAppFn
            let arguments := installedStatement.getAppArgs
            unless arguments.size == 3 do
              badShape s!"{g.iotaName sh.k j}'s installed statement is not a binary equality"
            let rhs := (exactSource sourceRule.rhs).beta (pre ++ fields)
            pure (mkAppN equality #[arguments[0]!, arguments[1]!, rhs],
              exactSource exactFields, exactSource sourceRecursor.type)
        let some fieldsType := closeForallsExact? fieldTelescope fields statement
          | badShape s!"{head}'s exact exported telescope has fewer fields than its installed type"
        let some ty := closeForallsExact? recursorTelescope pre fieldsType
          | badShape s!"{sh.src}'s exact exported telescope is shorter than its recursor prefix"
        let val ← mkLambdaFVars tel (← r.value)
        let nm := g.iotaName sh.k j
        return (exportKey, nm,
          .thmDecl { name := nm, levelParams := sh.lparams, type := ty, value := val })

/-- **The mimics, grouped into strongly connected components and put in an
order that emits a group's dependencies before it.**

Assuming that nesting strictly decreases would imply a topological order, but
that is false in two different ways, and the second is the one that
matters:

* **A backward edge without a cycle.** Discovery is breadth first, so a mimic
  may perfectly well mention one discovered before it. Descending index is then
  not a topological order, and the check this replaces called that a cycle.
* **A real cycle.** `T` nests into `Tree T`; `Tree`'s own `node` field is `List
  (Tree T)`; *that* copy's `cons` head is `Tree T` again. `pack₀` and `pack₁`
  are mutually recursive and **no** emission order exists for them one at a
  time.

A group of size one is emitted the way it always was. A larger one is one
simultaneous recursion, and [`InductiveModels.familyFor`] finds the recursors Lean
already generated for it. -/
def mimicGroups (pl : Plan) : Except String (Array (Array Nat)) := Id.run do
  let m := pl.mimics.size
  let r := pl.numAll
  let mut adj : Array (Array Bool) := Array.replicate m (Array.replicate m false)
  for i in [0:m] do
    for (_, cty) in pl.types[i + r]!.ctors do
      for j in [0:m] do
        if j != i && mentions pl.mimics[j]!.name cty then
          adj := adj.modify i (·.set! j true)
  -- Reachability, and then mutual reachability: the components.
  let mut re := adj
  for k in [0:m] do
    for i in [0:m] do
      if re[i]![k]! then
        for j in [0:m] do
          if re[k]![j]! then re := re.modify i (·.set! j true)
  let mut seen : Array Bool := Array.replicate m false
  let mut groups : Array (Array Nat) := #[]
  for i in [0:m] do
    unless seen[i]! do
      let mut grp := #[i]
      seen := seen.set! i true
      for j in [i + 1:m] do
        if !seen[j]! && re[i]![j]! && re[j]![i]! then
          grp := grp.push j
          seen := seen.set! j true
      groups := groups.push grp
  -- The condensation is a DAG; emit a group only once everything it depends on
  -- has been emitted.
  let ng := groups.size
  let dependsOn := fun (a b : Nat) =>
    groups[a]!.any fun i => groups[b]!.any fun j => adj[i]![j]!
  let mut order : Array (Array Nat) := #[]
  let mut placed : Array Bool := Array.replicate ng false
  for _ in [0:ng] do
    for a in [0:ng] do
      if !placed[a]! then
        if (Array.range ng).all fun bb => bb == a || placed[bb]! || !dependsOn a bb then
          order := order.push groups[a]!
          placed := placed.set! a true
          break
  if order.size != ng then return .error "the mimic condensation graph is cyclic"
  return .ok order

/-- **Build the model, or say which shape stopped it.**

Generated declarations are first installed through [`InductiveModels.addChecked`]
in the disposable construction view. The exact serialized island is checked
once at its close boundary iff generated kernel checking is enabled. -/
def iso (all : Array Name) (lparams : List Name) (numParams : Nat)
    (exportCtors : Array (Array (Name × Expr))) (exportRecursors : Array ERec) (pl : Plan)
    (reserved : Std.HashSet Name) (buildRoot? : Option Name := none) : GenM Iso := do
  -- **The declaration's own level parameters are carried, not refused.** Every
  -- generated constant is declared at `lparams` and referenced at `us`; a
  -- recursor is declared at its motive universe *followed by* `lparams`, which
  -- is the order Lean itself writes.
  -- `test/fixtures/inductive-models/poly_nested.lean` is the fixture, and it
  -- is arranged so that a generator writing a container's *declared* parameter
  -- where the occurrence's instantiation belongs cannot pass.
  let us := lparams.map Level.param
  let np := numParams
  let r := pl.numAll
  let some root := all[0]? | badShape "the declaration has no members"
  let buildRoot := buildRoot?.getD root
  let some rootT := pl.types[0]? | badShape "the plan has no members"
  -- The block's resultant sort and each member's index count. **The
  -- declaration's indices are carried**: what is left after the parameters is
  -- an index telescope, and every index vector in the model is read off a type
  -- in hand rather than rebuilt. **Every real member's sort, not just the
  -- first's**: a mutual block whose members land at different sorts would give
  -- `Eq` two universes and one `g.u` to write them at.
  let sortOf : Expr → GenM (Nat × Level) := fun t => do
    let mut cur := t
    for _ in [0:np] do
      match cur with
      | .forallE _ _ b _ => cur := b
      | _ => badShape "the declaration has fewer binders than parameters"
    let mut ni := 0
    repeat
      match cur with
      | .forallE _ _ b _ => cur := b; ni := ni + 1
      | _ => break
    let .sort u := cur | badShape "a block member does not land in a sort"
    return (ni, u)
  let nidx ← pl.types.mapM fun t => do return (← sortOf t.type).1
  let u := (← sortOf rootT.type).2
  for k in [0:r] do
    unless (← sortOf pl.types[k]!.type).2 == u do
      badShape "a mutual block whose members land at different sorts"
  let primaryCarrier := Naming.modelName buildRoot
  let exactPrimaryCarrier := Naming.modelName root
  let model := Name.str primaryCarrier "_impl"
  let b := fun (i : Nat) => Name.num model i
  let exportCtorNames := exportCtors.flatMap fun ctors => ctors.map (·.1)
  let exportRecs := (Array.range pl.types.size).map (exportRecName all)
  -- **One carrier per real member.** `A.rec` and `B.rec` are distinct
  -- recursors over distinct majors, and a consumer keys `⟦A⟧` and `⟦B⟧`
  -- separately; a single carrier could stand for only one of them. For a
  -- one-member block this is exactly `T._model`.
  let selfNames := all.extract 0 r |>.map fun n =>
    Naming.modelName (Naming.relocateSource root buildRoot n)
  let blockCtors := (Array.range pl.types.size).map fun i =>
    pl.types[i]!.ctors.map fun (cn, _) => Name.str (b i) (lastStr cn)

  -- The public contract is declaration-local. Census its exact names as one
  -- atomic request, including every nested recursor's rule theorems, before
  -- adding any implementation declaration to the environment.
  let mut publicNames : Naming.Table := .empty
  for name in all.extract 0 r do
    publicNames := publicNames.addDeclaration .typeFormer name
  for name in exportCtorNames do
    publicNames := publicNames.addDeclaration .constructor name
  for k in [0:exportRecs.size] do
    publicNames := publicNames.addRecursor exportRecs[k]! pl.types[k]!.ctors.size
    if (exportRecursors.find? (·.name == exportRecs[k]!)).any (·.k) then
      publicNames := publicNames.addMetadata .ruleK exportRecs[k]!
  let mut helpers : Array Name := (Array.range pl.types.size).map b
  helpers := helpers ++ blockCtors.flatten
  for k in [0:pl.types.size] do helpers := helpers.push (Name.str (b k) "rec")
  for i in [0:pl.mimics.size] do
    for suffix in [s!"pack_{i}", s!"unpack_{i}", s!"unpackPack_{i}",
        s!"packUnpack_{i}", s!"congrPack_{i}"] do
      helpers := helpers.push (Name.str model suffix)
  helpers := helpers.push (Name.str model "funext")
  let exactHelper := fun n =>
    if primaryCarrier.isPrefixOf n then n.replacePrefix primaryCarrier exactPrimaryCarrier else n
  let helperNames := helpers.foldl
    (fun names helper => names.insert (exactHelper helper)) ({} : Std.HashSet Name)
  let census := publicNames.collisionCensusReservedWith reserved helperNames
  if let some name := census.duplicateRequirements[0]? then
    badShape s!"the public naming contract requires {name} more than once"
  if let some name := census.taken[0]? then declineWith (.nameTaken name)
  for name in publicNames.requiredNames do
    if (← getEnv).constants.contains name then declineWith (.nameTaken name)
  -- **The whole file, not just the prefix.** A contract name may be declared
  -- after its source declaration. A guard that only looked at the environment
  -- as it stands would then emit a duplicate declaration.
  let taken : Name → GenM Unit := fun n => do
    let exact := exactHelper n
    if reserved.contains exact || (← getEnv).constants.contains exact then
      declineWith (.nameTaken exact)
    if buildRoot != root && (reserved.contains n || (← getEnv).constants.contains n) then
      declineWith (.nameTaken n)
  for i in [0:pl.types.size] do taken (b i)
  for n in selfNames do taken n
  -- **The `Eq` first, because everything downstream is written at it** — and
  -- spliced in when the input has none, which is the whole of what
  -- `test/fixtures/inductive-models/decline_no_eq.lean` used to refuse. It goes at the
  -- head of `out`, ahead
  -- of the block, so that it precedes its first use in the round trips no
  -- matter how the rest of the emission is ordered.
  let (eqi, eqDecls) ← ensureEq
  let mut out : Array Declaration := eqDecls
  let mut spliced : Array Name := eqDecls.flatMap (·.getNames.toArray)

  -- ── 1. the block, renamed ──────────────────────────────────────────────
  --
  -- Member 0 is the export's own `T` and must not keep that name: `T` is a
  -- primitive inductive in the caller's environment and this development is
  -- about a different constant.
  let ren : Std.HashMap Name (Nat × Expr) :=
    (Array.range pl.types.size).foldl
      (fun m i => m.insert pl.types[i]!.name (0, .const (b i) us)) {}
  let its : List InductiveType := (Array.range pl.types.size).toList.map fun i =>
    { name := b i, type := pl.types[i]!.type
      ctors := (Array.range pl.types[i]!.ctors.size).toList.map fun j =>
        { name := blockCtors[i]![j]!, type := restore ren pl.types[i]!.ctors[j]!.2 } }
  let blockDecl := Declaration.inductDecl lparams np its false
  addChecked blockDecl
  out := out.push blockDecl

  -- ── 2. the carriers, one per real member ───────────────────────────────
  let b0ty := (← constInfo (b 0)).type
  let withParams := fun {α : Type} (k : Array Expr → GenM α) =>
    forallBoundedTelescope b0ty (some np) fun ps _ => k ps
  for k in [0:r] do
    let carrier ← withParams fun ps => mkLambdaFVars ps (mkAppN (.const (b k) us) ps)
    let selfDecl := Declaration.defnDecl
      { name := selfNames[k]!, levelParams := lparams, type := pl.types[k]!.type, value := carrier
        hints := ← hintsFor carrier, safety := .safe }
    addChecked selfDecl
    out := out.push selfDecl

  -- Every occurrence, with the export's own members rewritten to their carriers.
  let toSelf : Std.HashMap Name (Nat × Expr) :=
    (Array.range r).foldl (fun m k => m.insert all[k]! (0, .const selfNames[k]! us)) {}
  let occs := pl.mimics.map fun m => restore toSelf m.occ
  -- **Does the block support large elimination?** Read off the recursor Lean
  -- just minted for it rather than inferred from the sort: `Eq` is `Prop` and
  -- has a motive universe, `S : Prop | mk : PL S → S` is `Prop` and has none.
  let largeElim ← do
    let .recInfo rv ← constInfo (.str (b 0) "rec") | badShape "the block has no recursor"
    pure (rv.levelParams.length == us.length + 1)
  let g0 : Gen := { owner := root, buildOwner := buildRoot,
                    model, exportCtors := exportCtorNames, exportRecs,
                    selfNames, numAll := r, np, u, us
                    members := (Array.range pl.types.size).map b
                    blockCtors, nidx, occs, eqi, fx := none, largeElim }

  -- **Dependent fields, checked once and only where they bite.** Every
  -- congruence fold in this file moves the *packed* positions of one of the
  -- block's constructors, so the condition is the same for all of them and is
  -- settled here rather than at each telescope: no field's type may mention an
  -- earlier field the block holds at a mimic. See [`InductiveModels.noDepOnPacked`].
  --
  -- **And whether any packed position sits under a binder**, which is the one
  -- shape whose proofs need `funext`: the block types such a field `∀ x⃗, Bₘ ι⃗`
  -- and the round trips, the recursor's minor and the ι rules all transport
  -- along `(fun x⃗ => pack (unpack (f x⃗))) = f`. `funext` is read from the
  -- export **only when a declaration has such a field** — it is in no public
  -- statement, only in these proofs, so requiring it of every export would
  -- decline every otherwise-supported declaration. Lean accepts all three places
  -- the binder can sit: the root (`HTree`), the container's own recursive
  -- field (`RTree` over `Rose`) and a container's field into another mimic
  -- (`OTree` over `Outer`), and `test/fixtures/inductive-models/infinitary.lean` has all
  -- three.
  let anyUnderBinder ← withParams fun ps => do
    let mut any := false
    for k in [0:pl.types.size] do
      for cn in blockCtors[k]! do
        any := any || (← forallTelescope (← instCtor cn us ps) fun fs _ => do
          let tys ← fs.mapM ftyp
          -- **The positions the folds move**, which is
          -- [`InductiveModels.Gen.mimicUnder?`] and not a bare head test: a field at a
          -- mimic under a binder is one, and so is the redex `(fun x => Bₘ) k`
          -- a family parameter leaves behind. Both questions below are about
          -- that same set, so both read it the same way.
          let under ← tys.mapM g0.mimicUnder?
          let packed := (Array.range fs.size).filterMap fun x =>
            if under[x]!.isSome then some fs[x]! else none
          noDepOnPacked packed fs tys
          -- A binder, and only a binder, costs a `funext`; `nb = 0` — including
          -- the redex, which reduces to the mimic with no telescope at all —
          -- writes no lambda and transports nothing pointwise.
          return under.any fun u => (u.getD (0, 0)).2 > 0)
    return any
  let (fxName?, fxDecls) ←
    if anyUnderBinder then do
      let (n, ds) ← ensureFunext model eqi reserved
      pure (some n, ds)
    else pure (none, #[])
  for d in fxDecls do
    out := out.push d
    spliced := spliced ++ d.getNames.toArray
  let g : Gen := { g0 with fx := fxName? }
  -- Raw public recursor syntax names the original declaration.  Rewrite only
  -- those constant names: unlike `restore`, `mapConstsE` retains every level
  -- expression on the occurrence itself. Installed block names remain the
  -- proof/layout oracle and never enter this public statement map.
  let mut sourceNames : Std.HashMap Name Name := {}
  for k in [0:r] do sourceNames := sourceNames.insert all[k]! selfNames[k]!
  for j in [0:exportCtorNames.size] do
    sourceNames := sourceNames.insert exportCtorNames[j]! (g.ctorName j)
  for k in [0:exportRecs.size] do
    sourceNames := sourceNames.insert exportRecs[k]! (g.recName k)
  let exactSource := mapConstsE (fun name => sourceNames[name]?)

  -- ── 3. pack, unpack, and the two round trips, group by group ───────────
  --
  -- **A group of mimics, not a mimic.** `packᵢ` for a container whose field is
  -- another occurrence calls that occurrence's `pack`, so the emission has to
  -- follow the dependency order — and when the dependency is *mutual*, no such
  -- order exists and the group is one simultaneous recursion instead
  -- ([`InductiveModels.mimicGroups`], [`InductiveModels.familyFor`]). Only `pack` and the
  -- retraction change: `unpack` never calls another `unpack`, and the section
  -- already goes through the block's own recursor, which does every member at
  -- once.
  let groups ← match mimicGroups pl with
    | .ok gs => pure gs
    | .error message => badShape message
  let mut done := Array.replicate pl.mimics.size false
  let emit := fun (nm : Name) (ty val : Expr) (isThm : Bool) => do
    let hint ← hintsFor val
    let d : Declaration :=
      if isThm then .thmDecl { name := nm, levelParams := lparams, type := ty, value := val }
      else .defnDecl { name := nm, levelParams := lparams, type := ty, value := val
                       hints := hint, safety := .safe }
    addChecked d
    return d
  for grp in groups do
    let solo := grp.size == 1
    for i in grp do
      for n in [g.packName i, g.unpackName i, g.retractName i, g.sectionName i] do taken n
    -- pack, every component of the group before anything reads one
    -- **The container's index telescope sits between `p⃗` and the argument**, in
    -- all five signatures, and is empty unless the container has indices — so
    -- nothing about an unindexed container's contract has moved.
    for i in grp do
      let (ty, val) ← withParams fun ps => do
        let ty ← g.withOccIndices i ps fun idxs =>
          mkForallFVars (ps ++ idxs)
            (.forallE `l (g.occAtIdx i ps idxs) (mkAppN (g.memAt (i + r) ps) idxs) .default)
        let val ← mkLambdaFVars ps (←
          if solo then g.packValue i (i + r) ps
          else do let f ← g.familyFor grp ps; g.packFamilyValue f (f.indexOf i) ps)
        return (ty, val)
      out := out.push (← emit (g.packName i) ty val false)
    for i in grp do
      let (ty, val) ← withParams fun ps => do
        let ty ← g.withIndices (i + r) ps fun idxs =>
          mkForallFVars (ps ++ idxs)
            (.forallE `b (mkAppN (g.memAt (i + r) ps) idxs) (g.occAtIdx i ps idxs) .default)
        let val ← mkLambdaFVars ps (← g.unpackValue (i + r) ps)
        return (ty, val)
      out := out.push (← emit (g.unpackName i) ty val false)
    for i in grp do
      let (ty, val) ← withParams fun ps => do
        let ty ← g.withOccIndices i ps fun idxs => do
          let occ := g.occAtIdx i ps idxs
          withLocalDeclD `l occ fun l =>
            mkForallFVars (ps ++ idxs ++ #[l])
              (eqi.mk' u occ
                (g.call (g.unpackName i) ps idxs (g.call (g.packName i) ps idxs l)) l)
        let val ← mkLambdaFVars ps (←
          if solo then g.retractValue i ps
          else do let f ← g.familyFor grp ps; g.retractFamilyValue f (f.indexOf i) ps)
        return (ty, val)
      out := out.push (← emit (g.retractName i) ty val true)
    -- The section is proved by the **block's** recursor, so the whole group is
    -- live at once and one call proves every component.
    let live := fun (k : Nat) =>
      !g.isReal k && (grp.contains (g.mimicOf k) || done[g.mimicOf k]!)
    for i in grp do
      let (ty, val) ← withParams fun ps => do
        let ty ← g.withIndices (i + r) ps fun idxs => do
          let mem := mkAppN (g.memAt (i + r) ps) idxs
          withLocalDeclD `b mem fun x =>
            mkForallFVars (ps ++ idxs ++ #[x])
              (eqi.mk' u mem
                (g.call (g.packName i) ps idxs (g.call (g.unpackName i) ps idxs x)) x)
        let val ← mkLambdaFVars ps (← g.sectionValue (i + r) ps live)
        return (ty, val)
      out := out.push (← emit (g.sectionName i) ty val true)
    for i in grp do done := done.set! i true

  -- ── 4. the declared type's own constructors ────────────────────────────
  --
  -- After the maps, because a field at a mimic is packed on the way in. The
  -- model's constructor carries the **export's** declared type with `T`
  -- rewritten to the carrier, so that the keying is an alias.
  --
  -- **Flattened over the real members, in the export's `all` order** so the
  -- constructor table remains aligned with the order of the block's minors.
  let mut ctors : Array (Name × Name) := #[]
  let mut ctorTys : Array (Name × Name × Expr) := #[]
  for k in [0:r] do
    for jj in [0:exportCtors[k]!.size] do
      let (cn, cty) := exportCtors[k]![jj]!
      let j := ctorTys.size
      let nm := g.ctorName j
      taken nm
      let ty := restore toSelf cty
      let val ← withParams fun ps => do mkLambdaFVars ps (← g.ctorValue k jj ty ps)
      let d := Declaration.defnDecl
        { name := nm, levelParams := lparams, type := ty, value := val
          hints := ← hintsFor val, safety := .safe }
      addChecked d
      out := out.push d
      ctors := ctors.push (cn, nm)
      ctorTys := ctorTys.push (cn, nm, ty)

  -- ── 5. one recursor per block member ───────────────────────────────────
  let mut heads : Std.HashMap Name (Nat × Expr) := {}
  for k in [0:r] do
    heads := heads.insert (b k) (0, .const selfNames[k]! us)
  for k in [0:r] do
    let base := (Array.range k).foldl (fun a i => a + exportCtors[i]!.size) 0
    for jj in [0:exportCtors[k]!.size] do
      heads := heads.insert (Name.str (b k) (lastStr exportCtors[k]![jj]!.1))
        (0, .const (g.ctorName (base + jj)) us)
  for i in [0:pl.mimics.size] do
    heads := heads.insert (b (i + r)) (np, occs[i]!)
    for (mc, real) in pl.mimics[i]!.ctors do
      -- The real constructor's own parameters mention the **export's** members,
      -- because the mimic table is built before the model exists.
      heads := heads.insert (Name.str (b (i + r)) (lastStr mc)) (np, restore toSelf real)
  for k in [0:pl.types.size] do
    taken (g.recName k)
    heads := heads.insert (Name.str (b k) "rec") (0, .const (g.recName k) us)
  let mut shapes : Array Gen.RecShape := #[]
  for k in [0:pl.types.size] do
    let sh ← g.recShape k heads
    let val ← g.recValue sh
    let d := Declaration.defnDecl
      { name := g.recName k, levelParams := sh.lparams, type := sh.ty, value := val
        hints := ← hintsFor val, safety := .safe }
    addChecked d
    out := out.push d
    shapes := shapes.push sh

  -- ── 6. the congruences the ι rules are stated along ────────────────────
  for i in [0:pl.mimics.size] do
    taken (g.congrPackName i)
    let (ty, val) ← withParams fun ps => g.congrPackDecl i ps
    let d := Declaration.thmDecl
      { name := g.congrPackName i, levelParams := lparams, type := ty, value := val }
    addChecked d
    out := out.push d

  -- ── 7. the ι rules themselves ──────────────────────────────────────────
  let mut iotas : Array (Nat × Name × Name) := #[]
  for k in [0:shapes.size] do
    -- Exact raw syntax is authoritative for the block's real public
    -- recursors. Nested mimic recursors have a different generated field/IH
    -- telescope; beta-applying the source rule to that telescope can shift a
    -- deeper container field (for example `DTree.rec_2`'s `List.cons`) into
    -- the element slot. Their installed statement is the public contract and
    -- was already constructed at the exact emitted names.
    let sourceRecursor? := if g.isReal k then
        exportRecursors.find? (·.name == exportRecs[k]!)
      else none
    for (key, nm, d) in ← g.iotaDecls shapes[k]! ctorTys sourceRecursor? exactSource do
      taken nm
      addChecked d
      out := out.push d
      iotas := iotas.push (k, key, nm)

  -- ── 8. K-like reduction at the constructor's index fiber ──────────────
  let mut ruleKs : Array (Name × Name) := #[]
  for k in [0:shapes.size] do
    let some exported := exportRecursors.find? (·.name == exportRecs[k]!)
      | badShape s!"the export has no recursor record for {exportRecs[k]!}"
    if exported.k then
      let sh := shapes[k]!
      let .recInfo rv ← constInfo sh.src | badShape s!"{sh.src} is not a recursor"
      unless rv.k do badShape s!"{exported.name} is K-like but {sh.src} is not"
      unless rv.rules.length == 1 do
        badShape s!"{sh.src} is K-like with {rv.rules.length} rules"
      let nm := g.ruleKName k
      taken nm
      let iotaType? := out.findSome? fun declaration => match declaration with
        | .thmDecl value => if value.name == g.iotaName k 0 then some value.type else none
        | _ => none
      let some iotaType := iotaType?
        | badShape s!"the K-like recursor {exported.name} has no iota theorem"
      let d ← ruleKDecl eqi sh.lparams (rv.numParams + rv.numMotives + rv.numMinors)
        nm iotaType
      addChecked d
      out := out.push d
      ruleKs := ruleKs.push (exported.name, nm)

  let mut aliases := Naming.AliasMap.empty
  if buildRoot != root then
    aliases := Naming.AliasMap.forRetry primaryCarrier (Naming.modelName root)
      (out.flatMap (·.getNames.toArray))
    for k in [0:r] do
      aliases := aliases.insert selfNames[k]! (Naming.modelName all[k]!)
    for j in [0:exportCtorNames.size] do
      aliases := aliases.insert (g.ctorName j) (Naming.modelName exportCtorNames[j]!)
    for k in [0:exportRecs.size] do
      aliases := aliases.insert (g.recName k) (Naming.modelName exportRecs[k]!)
      if (exportRecursors.find? (·.name == exportRecs[k]!)).any (·.k) then
        aliases := aliases.insert (g.ruleKName k) (Naming.ruleKName exportRecs[k]!)
      for j in [0:pl.types[k]!.ctors.size] do
        aliases := aliases.insert (g.iotaName k j) (Naming.iotaName exportRecs[k]! j)
  let containerImplementations ← (Array.range pl.mimics.size).mapM fun i => do
    let implementationCarrier := g.members[r + i]!
    let sourceRecursor := g.exportRecs[r + i]!
    let implementationShape := shapes[r + i]!
    let implementationRecursor := implementationShape.src
    let implementationRecursorWrapper := g.recName (r + i)
    let sourceMatches := exportRecursors.filter fun recursor => recursor.name == sourceRecursor
    unless sourceMatches.size == 1 do
      badShape s!"the exact source export has {sourceMatches.size} records for {sourceRecursor}"
    let sourceRecursorEvidence := IsoSourceRecursor.ofERec sourceMatches[0]!
    let implementationRecursorInfo ← constInfo implementationRecursor
    let implementationRecursorWrapperInfo ← constInfo implementationRecursorWrapper
    let .recInfo implementationRecursorValue := implementationRecursorInfo
      | badShape s!"{implementationRecursor} is not the installed private mimic recursor"
    unless implementationRecursorWrapperInfo.type == implementationShape.ty &&
        implementationShape.nm == sourceRecursorEvidence.numMotives &&
        implementationShape.nmin == sourceRecursorEvidence.numMinors &&
        implementationShape.nidx == sourceRecursorEvidence.numIndices do
      badShape s!"{implementationRecursorWrapper}'s checked wrapper layout differs from {sourceRecursor}"
    let sourceRuleKeys := sourceRecursorEvidence.rules.map (·.ctor)
    let implementationRules := implementationRecursorValue.rules.toArray
    unless implementationRules.size == sourceRecursorEvidence.rules.size do
      badShape s!"{sourceRecursor} and {implementationRecursor} have different rule keys"
    let mut recursorRuleKeys := #[]
    for sourceRule in sourceRecursorEvidence.rules do
      let realMatches := pl.mimics[i]!.ctors.filter fun (_, real) =>
        real.getAppFn.constName? == some sourceRule.ctor
      unless realMatches.size == 1 do
        badShape s!"{sourceRecursor}'s rule {sourceRule.ctor} has {realMatches.size} mimic sources"
      let syntheticConstructor := realMatches[0]!.1
      let syntheticMatches := (Array.range pl.types[r + i]!.ctors.size).filter fun index =>
        pl.types[r + i]!.ctors[index]!.1 == syntheticConstructor
      unless syntheticMatches.size == 1 do
        badShape s!"{sourceRule.ctor}'s synthetic constructor occurs {syntheticMatches.size} times"
      let implementationConstructor := blockCtors[r + i]![syntheticMatches[0]!]!
      let implementationMatches := implementationRules.filter fun rule =>
        rule.ctor == implementationConstructor && rule.nfields == sourceRule.nfields
      unless implementationMatches.size == 1 do
        badShape s!"{sourceRule.ctor}'s private rule association is absent or ambiguous"
      recursorRuleKeys := recursorRuleKeys.push (sourceRule.ctor, implementationConstructor)
    unless implementationRules.map (·.ctor) == recursorRuleKeys.map (·.2) &&
        sourceRuleKeys == recursorRuleKeys.map (·.1) do
      badShape s!"{sourceRecursor} and {implementationRecursor} have differently ordered rules"
    let interfaceRuleKeys := sourceRecursorEvidence.rules.map fun rule =>
      (rule.ctor, sourceNames[rule.ctor]?.getD rule.ctor)
    let forward := g.packName i
    let backward := g.unpackName i
    let backwardForward := g.retractName i
    let forwardBackward := g.sectionName i
    return {
      parameterArity := np
      indexArity := g.midx i
      implementationCarrier
      sourceRecursor
      sourceRecursorEvidence
      implementationRecursor
      implementationRecursorWrapper
      sourceRecursorType := sourceRecursorEvidence.type
      implementationRecursorType := implementationRecursorInfo.type
      implementationRecursorWrapperType := implementationRecursorWrapperInfo.type
      recursorRuleKeys
      implementationRecursorRules := implementationRules.map fun rule =>
        { ctor := rule.ctor, nfields := rule.nfields, rhs := rule.rhs }
      interfaceRuleKeys
      forward
      backward
      backwardForward
      forwardBackward
      forwardType := (← constInfo forward).type
      backwardType := (← constInfo backward).type
      backwardForwardType := (← constInfo backwardForward).type
      forwardBackwardType := (← constInfo forwardBackward).type
      implementationCarrierType := (← constInfo implementationCarrier).type }
  return { decls := out, levelParams := lparams, members := g.members, selfNames
           numAll := r, ctors
           recs := (Array.range pl.types.size).map g.recName, iotas, ruleKs, spliced, aliases,
           containerImplementations, funext? := fxName? }

end InductiveModels
