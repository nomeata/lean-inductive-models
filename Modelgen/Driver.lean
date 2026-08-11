import Modelgen.Simple
import Modelgen.Cli
import Modelgen.Naming

/-!
# The filter

`.ndjson` in, `.ndjson` out. The input is **trusted**: every declaration is
replayed into a `Lean.Environment` with checking off, because the owner's
instruction is to trust the export and that is where the speed comes from. Only
the declarations this tool *generates* are checked, and they are checked by the
kernel, one at a time.

Beside each nested inductive and each plain mutual block the output carries that
declaration's model — before it for the first and, when the input's own `Eq`
gets in the way, just after the block for the second (`MODELGEN.md` §1.6). The
input's own records are otherwise unchanged, and a file with neither kind of
declaration is copied **byte for byte** rather than re-serialised.

There are **three** constructions and they are separate files. `Modelgen/
Model.lean` specialises a nested declaration into a mutual block and proves the
export's recursors over it; `Modelgen/Mutual.lean` packs a plain mutual block
into an implementation tag and one auxiliary inductive; `Modelgen/Simple.lean`
models a single inductive from the primitive basis. None is a degenerate case
of another, and this driver is the only thing that composes them.

## Why the whole file is re-interned when anything is spliced

`nanoda`'s parser rejects a back-reference that is not the current count, so a
model cannot be inserted into an existing file with fresh high indices. When
there is a model to write, [`Modelgen.Export.render`] re-interns from scratch.

## The free oracle

Lean's kernel builds the nested construction itself: given `Tree`'s
`inductDecl` it generates **both** `Tree.rec` and `Tree.rec_1`, at the shapes
the export declares. So replaying the input already compares every recursor in
the file against Lean's own, and `--check-recursors` reports the difference.
That is `mini/tests/mutual.rs`'s `the_generated_recursors_are_the_ones_lean_
exports` obtained for nothing, over the whole corpus rather than the fixtures.
-/

open Lean Meta

namespace Modelgen

/-- What one run did. -/
structure Report where
  generated : Array (Name × Nat) := #[]
  declined : Array (Name × String) := #[]
  /-- **The basis exemption, which is not a decline** ([`Modelgen.primBasis`],
  `MODELGEN.md` §8.17). `Eq`, `Nat`, `PSigma` and `PULiftP` are the primitives
  the third construction is written in, so a run leaves them unmodelled *by
  definition*; counting them among the declines made every census in §8 report
  a number it then had to walk back in the next sentence. Reported on their own
  lines and counted in their own row. -/
  exempt : Array (Name × String) := #[]
  /-- **Prelude constants the input did not declare and a model spliced in**,
  per declaration. `Eq`, the quotient and `Quot.sound` come out under Lean's
  own names and `funext` under the model's; `Modelgen.ensureEq` and
  `Modelgen.ensureFunext` say why the two are named differently. Printed,
  always: an insertion is a decision on record. -/
  spliced : Array (Name × Array Name) := #[]
  /-- Recursors whose replayed shape differs from the export's own. -/
  recMismatch : Array Name := #[]
  recChecked : Nat := 0
  /-- Statements compared against the installed recursors' own rules, and the
  ones that did not match. -/
  stmtChecked : Nat := 0
  stmtErrors : Array String := #[]
  /-- The input stopped replaying here: a declaration Lean's kernel will not
  load at all. The filter then becomes the identity, which is what a filter
  should be when it can do nothing. -/
  unreplayable : Option String := none
  deriving Inhabited

/-- A generated model waiting for its statements to be compared with the
exact recursor records of the declaration it models. -/
structure PendingModel where
  all : Array Name
  numParams : Nat
  iso : Iso
  /-- The export's recursors, in its own order. For a block generated inside
  this pass, [`Modelgen.recursorsOfNames`] reads back the exact records that
  this driver just emitted. -/
  recursors : Array ERec

/-- Add the equality theorem for every member on which Lean's kernel enables
its unit-like shortcut.  The proof does not appeal to that shortcut: it runs
the model recursor twice, once for each side of the equality.  Constant
equality motives discharge the unrelated arms of a mutual/nested recursor. -/
def addUnitlikeTheorems (types : Array EIndType) (constructors : Array ECtor)
    (recursors : Array ERec) (reserved : Std.HashSet Name) (is : Iso) : GenM Iso := do
  let eligible := (Array.range types.size).filter fun k =>
    types[k]!.isKernelUnitlike constructors.toList
  if eligible.isEmpty then return is
  unless types.size == is.numAll && is.selfNames.size == is.numAll do
    badShape "the unit-like member table does not match the generated model"

  -- Collisions are tested at the emitted names.  A simple model built under an
  -- alias is renamed only when serialized, so its environment-local theorem
  -- name is derived separately from `selfNames` below.
  let publicTable := eligible.foldl (fun table k =>
    table.addMetadata .unitlike types[k]!.name) Naming.Table.empty
  let occupied := reserved.fold (fun names name => names.push name) #[]
  let census := publicTable.collisionCensus occupied
  if let some name := census.taken[0]? <|> census.duplicateRequirements[0]? then
    declineWith (.nameTaken name)

  let env ← getEnv
  let eqi ← match EqInfo.check env with
    | .ok eqi => pure eqi
    | .error message => badShape message
  let us := is.levelParams.map Level.param
  let mut out := is.decls
  let mut unitlikes := is.unitlikes

  for k in eligible do
    let type := types[k]!
    let [constructorName] := type.ctors
      | badShape s!"{type.name} changed shape while generating its unit-like theorem"
    let some constructorIndex := constructors.findIdx? (·.name == constructorName)
      | badShape s!"{constructorName} has no constructor record"
    let some recursor := recursors[k]?
      | badShape s!"{type.name} has no corresponding exported recursor"
    let some motiveIndex := recursor.all.idxOf? type.name
      | badShape s!"{recursor.name} has no motive for {type.name}"
    unless recursor.numIndices == 0 do
      badShape s!"unit-like recursor {recursor.name} unexpectedly has indices"
    unless recursor.numMotives == recursor.all.length &&
        recursor.numMinors == constructors.size do
      badShape s!"{recursor.name} has an unexpected mutual telescope"

    let modelType := is.selfNames[k]!
    let modelConstructor := is.ctors[constructorIndex]!.2
    let modelRecursor := is.recs[k]!
    let theoremName := Name.str modelType "unitlike"
    if env.constants.contains theoremName then declineWith (.nameTaken theoremName)
    let typeInfo ← constInfo modelType
    let recInfo ← constInfo modelRecursor
    let recLevels ←
      if recInfo.levelParams.length == is.levelParams.length + 1 then
        pure (.zero :: us)
      else if recInfo.levelParams.length == is.levelParams.length then
        pure us
      else
        badShape s!"{modelRecursor} carries unexpected universe parameters"
    let recType := recInfo.type.instantiateLevelParams recInfo.levelParams recLevels
    let ctorInfo ← constInfo modelConstructor
    let ctorType := ctorInfo.type.instantiateLevelParams ctorInfo.levelParams us

    let declaration ← forallBoundedTelescope typeInfo.type (some type.numParams) fun ps _ => do
      let carrier := mkAppN (.const modelType us) ps
      let constructor ← do
        let ctorTail ← instForall ctorType ps
        unless numForalls ctorTail == 0 do
          badShape s!"unit-like constructor {modelConstructor} has fields"
        pure (mkAppN (.const modelConstructor us) ps)
      let eqcc := eqi.mk' (← ilevel carrier) carrier constructor constructor
      let refl := eqi.refl' (← ilevel carrier) carrier constructor
      let carrierLevel ← ilevel carrier

      let constantMotive := fun (domain proposition : Expr) =>
        forallTelescope domain fun binders _ => mkLambdaFVars binders proposition
      let applyRec := fun (targetMotive targetMinor major : Expr) => do
        let mut current ← instForall recType ps
        let mut args := ps
        for motive in [0:recursor.numMotives] do
          let .forallE _ domain body _ := current
            | badShape s!"{modelRecursor} has too few motive binders"
          let value ← if motive == motiveIndex then pure targetMotive
            else constantMotive domain eqcc
          args := args.push value
          current := body.instantiate1 value
        for minor in [0:recursor.numMinors] do
          let .forallE _ domain body _ := current
            | badShape s!"{modelRecursor} has too few minor binders"
          let value ← if minor == constructorIndex then pure targetMinor
            else forallTelescope domain fun binders _ => mkLambdaFVars binders refl
          args := args.push value
          current := body.instantiate1 value
        let .forallE _ majorType _ _ := current
          | badShape s!"{modelRecursor} has no major premise"
        unless ← isDefEq majorType carrier do
          badShape s!"{modelRecursor}'s major premise is not {modelType}"
        pure (mkAppN (.const modelRecursor recLevels) (args.push major))

      let innerMotive ← withLocalDeclD `y carrier fun y =>
        mkLambdaFVars #[y] (eqi.mk' carrierLevel carrier constructor y)
      let innerMinor := refl
      let outerMinor ← withLocalDeclD `y carrier fun y => do
        mkLambdaFVars #[y] (← applyRec innerMotive innerMinor y)
      let outerMotive ← withLocalDeclD `x carrier fun x => do
        let body ← withLocalDeclD `y carrier fun y =>
          mkForallFVars #[y] (eqi.mk' carrierLevel carrier x y)
        mkLambdaFVars #[x] body

      let theoremType ← withLocalDeclD `x carrier fun x =>
        withLocalDeclD `y carrier fun y =>
          mkForallFVars (ps ++ #[x, y]) (eqi.mk' carrierLevel carrier x y)
      let theoremValue ← withLocalDeclD `x carrier fun x => do
        mkLambdaFVars (ps.push x) (← applyRec outerMotive outerMinor x)
      pure <| Declaration.thmDecl
        { name := theoremName, levelParams := is.levelParams
          type := theoremType, value := theoremValue }
    addChecked declaration
    out := out.push declaration
    unitlikes := unitlikes.push (k, theoremName)
  return { is with decls := out, unitlikes }

private abbrev FilterState := Array EDecl × Report × Array PendingModel

/-- Read one inductive block back out of the environment, including the
recursors the **kernel** generated for it. -/
def indEDecl (names : Array Name) : MetaM EDecl := do
  let env ← getEnv
  let mut ts : Array EIndType := #[]
  let mut cs : Array ECtor := #[]
  let mut rs : Array ERec := #[]
  for n in names do
    let some (.inductInfo iv) := env.constants.find? n | throwError "{n} is not an inductive"
    ts := ts.push
      { name := iv.name, levelParams := iv.levelParams, type := iv.type, all := iv.all
        ctors := iv.ctors, numParams := iv.numParams, numIndices := iv.numIndices
        numNested := iv.numNested, isRec := iv.isRec, isReflexive := iv.isReflexive
        isUnsafe := iv.isUnsafe }
    for cn in iv.ctors do
      let some (.ctorInfo cv) := env.constants.find? cn | throwError "{cn} is not a constructor"
      cs := cs.push
        { name := cv.name, levelParams := cv.levelParams, type := cv.type, cidx := cv.cidx
          numParams := cv.numParams, numFields := cv.numFields, induct := cv.induct
          isUnsafe := cv.isUnsafe }
  for n in names do
    if let some (.recInfo rv) := env.constants.find? (Name.str n "rec") then
      rs := rs.push
        { name := rv.name, levelParams := rv.levelParams, type := rv.type, all := rv.all
          numParams := rv.numParams, numIndices := rv.numIndices, numMotives := rv.numMotives
          numMinors := rv.numMinors, k := rv.k, isUnsafe := rv.isUnsafe
          rules := rv.rules.map fun r =>
            { ctor := r.ctor, nfields := r.nfields, rhs := r.rhs } }
  return .induct ts.toList cs.toList rs.toList

/-- Installed-block adapter for the two generation routes which run after the
original inductive has been replayed. -/
def addInstalledUnitlikeTheorems (names : Array Name) (reserved : Std.HashSet Name)
    (is : Iso) : GenM Iso := do
  let .induct types constructors recursors ← indEDecl names
    | badShape s!"{names} did not read back as an inductive block"
  addUnitlikeTheorems types.toArray constructors.toArray recursors.toArray reserved is

/-- Read the exact recursor records of a block generated inside this pass. -/
def recursorsOfNames (names : Array Name) : MetaM (Array ERec) := do
  let .induct _ _ recursors ← indEDecl names
    | throwError "{names} did not read back as an inductive block"
  return recursors.toArray

/-- A generated declaration as an export record. -/
def toEDecl : Declaration → MetaM EDecl
  | .defnDecl v => return .defn v.name v.levelParams v.type v.value (hintsOf v.hints) "safe" [v.name]
  | .thmDecl v => return .thm v.name v.levelParams v.type v.value [v.name]
  | .axiomDecl v => return .ax v.name v.levelParams v.type v.isUnsafe
  | .opaqueDecl v => return .opaq v.name v.levelParams v.type v.value v.isUnsafe [v.name]
  | .inductDecl _ _ ts _ => indEDecl (ts.toArray.map (·.name))
  | d => throwError "cannot serialise {d.getTopLevelNames}"

/-- The export's word for each of the four quotient records. Read off the
`QuotKind` the kernel stamped on the constant, so the record is recognised
**structurally** on the way back out exactly as `MONOMORPH.md`'s carried
built-ins recognise it on the way in. -/
def quotKindStr : QuotKind → String
  | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"

/-- A generated declaration as export records — **plural**, because
`Declaration.quotDecl` is one kernel declaration and four records. Everything
else is one record and goes through [`Modelgen.toEDecl`]. -/
def toEDecls (d : Declaration) : MetaM (Array EDecl) := do
  match d with
  | .quotDecl =>
    let env ← getEnv
    let mut out : Array EDecl := #[]
    for n in [`Quot, `Quot.mk, `Quot.lift, `Quot.ind] do
      let some (.quotInfo qi) := env.constants.find? n
        | throwError "{n} was not installed by the quotient declaration"
      out := out.push (.quot qi.name qi.levelParams qi.type (quotKindStr qi.kind))
    return out
  | _ => return #[← toEDecl d]

/-- Read a generated model back from the environment, register every name Lean
minted for its inductive blocks, and serialize through exact alias lookups.
The returned `Iso` carries the completed table for reporting and delayed
checking. -/
def serialiseIso (is : Iso) : MetaM (Array EDecl × Iso) := do
  let mut records : Array EDecl := #[]
  for declaration in is.decls do
    records := records ++ (← toEDecls declaration)
  let names := records.flatMap fun record => record.names.toArray
  let aliases := is.aliases.register names
  let renamed := records.map (·.renameAliases aliases)
  let spliced := is.spliced.map fun name => aliases.exact name
  let unitlikes := is.unitlikes.map fun (member, theoremName) =>
    (member, aliases.exact theoremName)
  return (renamed, { is with aliases := aliases, spliced := spliced, unitlikes := unitlikes })

/-- Compare the export's own recursors against the ones the kernel just
regenerated. Returns the names that differ. -/
def checkRecs (rs : List ERec) : MetaM (Nat × Array Name) := do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let mut n := 0
  for r in rs do
    n := n + 1
    let some (.recInfo rv) := env.constants.find? r.name | bad := bad.push r.name; continue
    let sameRules :=
      rv.rules.length == r.rules.length &&
      (rv.rules.zip r.rules).all fun (a, b) => a.ctor == b.ctor && a.rhs == b.rhs
    unless rv.type == r.type && rv.numMotives == r.numMotives && rv.numMinors == r.numMinors
        && rv.numParams == r.numParams && rv.numIndices == r.numIndices && rv.k == r.k
        && sameRules do
      bad := bad.push r.name
  return (n, bad)

/-- **The model's recursors and ι theorems state the export's own.**

`addDeclCore` says the generator's proof proves the generator's *statement*, and
a generator that stated a different well-typed equation — the rule of the wrong
member, the induction hypothesis at `T.rec` where the export says `T.rec_1`, a
minor applied to its fields in the wrong order — would satisfy it and be wrong.
So every emitted statement is rebuilt here from the rule the **installed**
`T.rec_k` carries, reading the constructor's field telescope off the recursor's
own major type rather than off the plan, and compared syntactically.

This is `mini/tests/nested.rs`'s `check_recursors` and `check_iotas`, ported. It
is what forced a real bug out of the Rust — recursors rewritten at no levels. -/
def checkModel (all : Array Name) (np : Nat) (is : Iso) (recursors : Array ERec) :
    MetaM (Nat × Array String) := do
  let env ← getEnv
  let mut tbl := modelTable env all is
  let exportedFor := fun (modelRecursor : Name) =>
    recursors.find? fun recursor => Naming.modelName recursor.name == modelRecursor
  -- `modelTable` is also used below the driver and retains its structural
  -- fallback. Here the export's exact names are available, so make those the
  -- authoritative recursor keys rather than reconstructing `T.rec_k`.
  for modelRecursor in is.recs do
    if let some recursor := exportedFor modelRecursor then
      tbl := tbl.insert recursor.name
        (0, .const modelRecursor (recursor.levelParams.map Level.param))
  let mut n := 0
  let mut errs : Array String := #[]
  unless recursors.size == is.recs.size do
    errs := errs.push s!"the export carries {recursors.size} recursors but the model carries \
      {is.recs.size}"
  for k in [0:is.recs.size] do
    let some rv := exportedFor is.recs[k]!
      | errs := errs.push s!"model recursor {is.recs[k]!} has no exported recursor"; continue
    let ern := rv.name
    let some (.recInfo _) := env.constants.find? ern
      | errs := errs.push s!"{ern} was not installed"; continue
    let some mi := env.constants.find? is.recs[k]!
      | errs := errs.push s!"{is.recs[k]!} was not generated"; continue
    let want := restore tbl rv.type
    unless mi.type == want do
      errs := errs.push s!"{is.recs[k]!} is not {ern} at the model"
    n := n + 1
    let mine := is.iotas.filter (·.1 == k)
    unless mine.size == rv.rules.length do
      errs := errs.push s!"{is.recs[k]!} has {mine.size} ι theorems against {ern}'s \
        {rv.rules.length} rules"
      continue
    -- **A block that eliminates only into `Prop` has no motive universe**, and
    -- then the rule's `Eq` is at `Prop` and the recursor's level list is the
    -- declaration's own. `S : Prop | mk : PL S → S` is one; `Eq` itself is
    -- `Prop` and has a motive universe, so this is read off the level list and
    -- not off the sort.
    let large := rv.levelParams.length == is.levelParams.length + 1
    let v ← if large then
        match rv.levelParams[0]? with
        | some lp => pure (Level.param lp)
        | none => pure Level.zero
      else pure Level.zero
    let recLs := if large then v :: is.levelParams.map Level.param
                 else is.levelParams.map Level.param
    let nb := np + rv.numMotives + rv.numMinors
    -- **The indices sit between the minors and the major.** A rule binds no
    -- index of its own — they are determined by the constructor's result — so
    -- the ι theorem's telescope is still `p⃗ M⃗ S⃗ f⃗` and the index vector is
    -- read off the major's own type below.
    let ni := rv.numIndices
    let (es, extra) ← forallBoundedTelescope want (some (nb + ni + 1)) fun bs _ => do
      let pre := bs.extract 0 nb
      let ps := bs.extract 0 np
      let motiveK := bs[np + k]!
      let majorTy ← inferType bs[nb + ni]!
      let mut es : Array String := #[]
      let mut cnt := 0
      for (rule, mineJ) in rv.rules.zip mine.toList do
        let (_, key, thm) := mineJ
        unless rule.ctor == key do
          es := es.push s!"{thm} is about {key}, not {ern}'s rule for {rule.ctor}"
          continue
        -- The constructor as it is applied, and its field telescope: at the
        -- root the model's own constructor, at a mimic the **real** container's
        -- at the arguments the major's own type carries — which is where this
        -- reads the occurrence from rather than from the plan.
        let (headC, hls, hpre, cty) ←
          if k < is.numAll then do
            let some (_, modelC) := is.ctors.find? (·.1 == key)
              | es := es.push s!"{key} has no model constructor"; continue
            let some ci := env.constants.find? modelC
              | es := es.push s!"{modelC} was not generated"; continue
            pure (modelC, is.levelParams.map Level.param, ps, ← instantiateForall ci.type ps)
          else do
            let .const _ cls := majorTy.getAppFn
              | es := es.push s!"{ern}'s major is not a type"; continue
            -- The container at its **parameters**: the major's own type is the
            -- occurrence at this recursor's indices, and the indices are the
            -- last `ni` arguments of it.
            let mas := majorTy.getAppArgs
            let qs := mas.extract 0 (mas.size - ni)
            let some ci := env.constants.find? key
              | es := es.push s!"{key} is not declared"; continue
            pure (key, cls, qs,
              ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams cls) qs)
        let e ← forallTelescope cty fun fields _ => do
          let major := mkAppN (.const headC hls) (hpre ++ fields)
          let mas := (← inferType major).getAppArgs
          let idxs := mas.extract (mas.size - ni) mas.size
          let lhs := mkAppN (.const is.recs[k]! recLs) ((pre ++ idxs).push major)
          -- The rule's own right-hand side, at the model's names. Lean states it
          -- as `fun p⃗ M⃗ S⃗ f⃗ => …`, which is this telescope exactly.
          let rhs := (restore tbl rule.rhs).beta (pre ++ fields)
          let body := mkAppN (.const `Eq [v]) #[mkAppN motiveK (idxs.push major), lhs, rhs]
          let wantTy ← mkForallFVars (pre ++ fields) body
          let some ti := env.constants.find? thm | return some s!"{thm} was not generated"
          if ti.levelParams != rv.levelParams then
            return some s!"{thm} is not at {ern}'s motive universe"
          if ti.type != wantTy then return some s!"{thm} is not {ern}'s rule for {rule.ctor}"
          return none
        if let some m := e then es := es.push m
        cnt := cnt + 1
      return (es, cnt)
    n := n + extra
    errs := errs ++ es
  return (n, errs)

/-- **One installed inductive block, read back out of the environment** as the
member types and constructor lists [`Modelgen.mutualIso`] wants.

The block a nested declaration's model *is* — `T._model.0 … T._model.{n−1}` —
is not in the input, so there is no `EDecl` to take these off; it exists only in
the environment the generator just put it in. This is how the composition
(§1.7) hands the second construction its input. -/
def blockOf (names : Array Name) : MetaM (Array Expr × Array (Array (Name × Expr))) := do
  let env ← getEnv
  let mut tys : Array Expr := #[]
  let mut cs : Array (Array (Name × Expr)) := #[]
  for n in names do
    let some (.inductInfo iv) := env.constants.find? n | throwError "{n} is not an inductive"
    tys := tys.push iv.type
    let mut ct : Array (Name × Expr) := #[]
    for cn in iv.ctors do
      let some ci := env.constants.find? cn | throwError "{cn} is not declared"
      ct := ct.push (cn, ci.type)
    cs := cs.push ct
  return (tys, cs)

/-- **Can a model be written here?** — which is only ever a question about `Eq`.

`true` when the environment already has one, and when the input declares none
anywhere, because then §1.5 splices Lean's own. `false` in the one remaining
case: the input declares an `Eq` the replay has not reached yet, where a splice
is refused by the name guard and would be wrong anyway. -/
def eqReady (reserved : Std.HashSet Name) : MetaM Bool := do
  if (← getEnv).constants.contains `Eq then return true
  return !(reserved.contains `Eq || reserved.contains `Eq.refl)

/-- **Can a prim model be written here?** — [`Modelgen.eqReady`]'s question,
asked of every basis constant a prim model may splice: each must be already
installed or not declared by the input at all, else the model waits for the
input's own declaration to be replayed. -/
def primReady (reserved : Std.HashSet Name) : MetaM Bool := do
  let env ← getEnv
  for n in [`Eq, `Eq.refl, `False, `Nat, `Nat.zero, `Nat.succ, `PSigma, `PSigma.mk] do
    unless env.constants.contains n || !reserved.contains n do return false
  return true

/-- **The names beyond the basis that a prim model may splice** — the ones
[`Modelgen.primReady`] does not cover and that an input may therefore declare
*later* than the model that needs them.

Two groups, and they are one list because the wait is the same wait:

* the quotient-side names deriving `funext` may splice
  ([`Modelgen.ensureFunext`]). A prim model reaches them on the singleton route
  and wherever a pad at a level `dsingOk` cannot build is discharged by
  transport — `PUnit`'s and `PULift`'s shapes.
* `Nonempty` and `Classical.choice`, which **arm G** splices
  (`MODELGEN.md` §8.12) and which the W core's fragment now also carries. An
  input that declares `Acc` before `Nonempty` — `modelgen/tests/w_core.ndjson`
  is one, since the fragment's `Acc` comes in through `WellFounded.fix` and its
  `Nonempty` only through `Classical.propDecidable` — used to lose `Acc`'s model
  to `prim model name taken (Nonempty)`. That is §8.16.5's class exactly: a
  primitive that is **late**, not a name that is lost. -/
def lateSpliceNames : List Name :=
  [`Quot, `Quot.mk, `Quot.lift, `Quot.ind, `Quot.sound,
   `Nonempty, `Nonempty.intro, `Nonempty.rec, `Classical.choice]

/-- [`Modelgen.primReady`]'s question, asked of the late names. Not folded into
`primReady` itself: most prim models never touch `funext` or choice, and
waiting on the quotient for all of them would move every pre-`Quot` model of a
`Quot`-late export for no reason. This is asked only of a model that has
already *declined* at one of these names. -/
def primLateReady (reserved : Std.HashSet Name) : MetaM Bool := do
  let env ← getEnv
  for n in lateSpliceNames do
    unless env.constants.contains n || !reserved.contains n do return false
  return true

/-- Did the model stop at a late name the replay has not reached? That is
a **wait**, not a decline: the input's own is coming, and the model
is generated after it, exactly as a mutual model waits for the input's own
`Eq`. -/
def Decline.isLateWait : Decline → Bool
  | .nameTaken n => lateSpliceNames.contains n
  | _ => false

/-- An exact public name generated by an earlier composed step is not part of
the input's `reserved` set.  Check those spellings before a collision-safe
retry so aliasing can never weaken `nameTaken`. -/
def exactPrimNameTaken? (tname : Name) (ctors : Array (Name × Expr)) : MetaM (Option Name) := do
  let env ← getEnv
  let recursor := Name.str tname "rec"
  for n in #[Naming.modelName tname, Naming.modelName recursor] do
    if env.constants.contains n then return some n
  for (ctor, _) in ctors do
    let n := Naming.modelName ctor
    if env.constants.contains n then return some n
  for j in [0:ctors.size] do
    let n := Naming.iotaName recursor j
    if env.constants.contains n then return some n
  return none

/-- One simple inductive's model from the primitives, generated and
accounted for — the third construction, [`Modelgen.primIso`], behind
`--prim-models`. Shared by the input's own simple inductives and the
composition (the single inductives the other two constructions emit).

`canWait` says whether the caller can hold the model back: a decline at a
quotient name the replay has not reached ([`Modelgen.Decline.isLateWait`]) then
comes back as `true` in the second component — recorded nowhere, generated
later — instead of a decline. The composition and the end-of-file drain pass
`false`: there, nothing more is coming.

**And, with `basicModels`, models for whatever that model had to splice.**

The second half closes a structural hole rather than adding a convenience.
`ensurePrim` and friends put a spliced inductive into the environment and into
the output, and nothing ever ran the third construction over it — so layer 3
was **unable to model anything it introduced**, and no coverage figure could
show it, because a spliced declaration was never a candidate to begin with.
`MODELGEN.md` §8.13 records what the earlier figures were therefore measuring.

Only *non-basis* splices are modelled: the four on
[`Modelgen.primBasis`] are the exemption that makes the construction
well-founded and must stay unmodelled. That is also what bounds the recursion
— a model's own splices are basis members or already present.

**Ordering is safe.** A spliced inductive is pushed to the output before the
model that needed it, and its own model is appended after; the export only
requires a declaration to precede its uses. -/
partial def genPrim (tname : Name) (lparams : List Name) (np : Nat) (ty : Expr)
    (ctors : Array (Name × Expr)) (recursors : Array ERec)
    (reserved : Std.HashSet Name) (basicModels : Bool)
    (canWait : Bool)
    (st : FilterState) : MetaM (FilterState × Bool) := do
  let (out, rep, pending) := st
  let saved ← getEnv
  -- **The retry under an alias root**, and it is a retry rather than a
  -- decision taken up front on purpose: aliasing changes nothing about the
  -- output and everything about the risk, so it runs only where the collision
  -- has actually fired. Every declaration that models today takes exactly the
  -- path it took before, byte for byte.
  --
  -- The alias embeds the exact original below a public namespace.  This is
  -- injective even for distinct raw private names that normalize to the same
  -- user name, because `_private` is no longer the leading component.
  let aliasRoot : Name := Naming.retryRoot tname
  let mut root := tname
  let exactTaken ← exactPrimNameTaken? tname ctors
  let initial ← match exactTaken with
    | some n => pure (.error (.nameTaken n))
    | none => (do
        let is ← primIso tname root lparams np ty ctors reserved
        addInstalledUnitlikeTheorems #[tname] reserved is).run
  let mut res := initial
  if let .error (.nameLost _) := res then
    setEnv saved
    root := aliasRoot
    res ← (do
      let is ← primIso tname root lparams np ty ctors reserved
      addInstalledUnitlikeTheorems #[tname] reserved is).run
  match res with
  | .error dec =>
    setEnv saved
    if canWait && dec.isLateWait && !(← primLateReady reserved) then
      return ((out, rep, pending), true)
    -- **Exempt is not declined.** A basis primitive is what the construction
    -- is written in, so its absence from the models is the thing that makes
    -- the construction well-founded rather than a shape it cannot reach; it
    -- gets its own row and is out of the decline count (`MODELGEN.md` §8.17).
    if dec matches .basisExempt then
      return ((out, { rep with exempt := rep.exempt.push (tname, dec.labelAs "prim") },
        pending), false)
    return ((out, { rep with declined := rep.declined.push (tname, dec.labelAs "prim") },
      pending), false)
  | .ok is =>
    let (records, is) ← serialiseIso is
    let mut out := out
    out := out ++ records
    let mut rep := { rep with generated := rep.generated.push (tname, is.decls.size) }
    unless is.spliced.isEmpty do
      rep := { rep with spliced := rep.spliced.push (tname, is.spliced) }
    let mut st2 := (out, rep, pending.push
      { all := #[tname], numParams := np, iso := is, recursors := recursors })
    if basicModels then
      for n in is.spliced do
        if primBasis.contains n then continue
        let some (.inductInfo iv) := (← getEnv).constants.find? n | continue
        -- the block's own name only, and only a simple one
        unless iv.all == [n] && iv.numNested == 0 do continue
        -- Already modeled: the declaration-local carrier itself is the key.
        if (← getEnv).constants.contains (Naming.modelName n) then continue
        let mut cts : Array (Name × Expr) := #[]
        for cn in iv.ctors do
          if let some ci := (← getEnv).constants.find? cn then cts := cts.push (cn, ci.type)
        let supportRecursors ← recursorsOfNames #[n]
        st2 :=
          (← genPrim n iv.levelParams iv.numParams iv.type cts supportRecursors reserved
            basicModels false st2).1
    -- **A model may not leave an inductive it introduced unmodelled.** Arm C
    -- (`MODELGEN.md` §8.15) splices the index erasure of the family it is
    -- carving, so its output contains an inductive that was in nobody's
    -- input; if the descent above could not model it, emitting would put a
    -- fifth inductive in front of a consumer, which is the hole §8.13 closed.
    -- So the whole model is withdrawn and the declaration declines.
    --
    -- Checked **after** the descent and not predicted before it. A cheap test
    -- that says "this skeleton will model" is the shape of "skip is not
    -- pass": it reports success and leaves the hole open on the case it got
    -- wrong. This asks the environment.
    if basicModels then
      for n in is.requires do
        unless (← getEnv).constants.contains (Naming.modelName n) do
          -- **Withdraw everything**, and off `st` rather than off the locals:
          -- `out`, `rep` and `pending` have all been added to by the emission
          -- and the descent above, and returning any of those would leave the
          -- skeleton's records in the export with the model that needed them
          -- gone. `st` is the state as it stood before this declaration.
          setEnv saved
          -- **Carry the skeleton's own reason.** The descent recorded why it
          -- could not model it, and that entry is about to be discarded with
          -- the rest of the withdrawn state; a message that says only "the
          -- skeleton did not model" names where a value stopped rather than
          -- why, which is the defect class this repository has paid for most.
          let inner := (st2.2.1.declined.find? fun (m, _) => m == n).map (·.2)
          -- **"spliced inductive", not "spliced index erasure".** Arm C's
          -- skeleton was the only occupant when this was written; arm W's
          -- fragment (§8.16) is seventeen more, and none of them is an index
          -- erasure. A reason that misnames what stopped is the defect class
          -- this line already exists to avoid.
          let why := s!"prim model shape: the spliced inductive {n} did not model, so \
            emitting would leave an unmodelled inductive in front of a consumer \
            (MODELGEN.md §8.15's rule) — {inner.getD "and the descent recorded no reason"}"
          return ((st.1, { st.2.1 with declined := st.2.1.declined.push (tname, why) },
            st.2.2), false)
    return (st2, false)

/-- **One prim model held back until the input has caught up.**
[`Modelgen.runFilter`]'s `waitingPrim` queue, named because
[`Modelgen.primCompose`] now returns entries for it. The leading `Bool` says
*which* wait: `false` for the basis ([`Modelgen.primReady`]) and `true` for the
quotient behind `funext` ([`Modelgen.primLateReady`]). -/
abbrev PrimJob :=
  Bool × Name × List Name × Nat × Expr × Array (Name × Expr) × Array ERec

/-- **The composition's third step**: the implementation inductives a mutual
model just emitted — `T._model._impl.tag` and `T._model._impl.aux` — are
declarations of the output like any other, so the simple branch runs on them
too. The tag is a plain sum and models; the auxiliary is indexed and takes
arm C. Their own public carriers are the declaration-local names
`T._model._impl.tag._model` and `T._model._impl.aux._model`.

**And it can wait, exactly as an input declaration can.** A prim model may
splice `Eq`, `False`, `Nat` and `PSigma`, and a splice is refused at a name the
input declares *later* — so `runFilter` holds such a model in `waitingPrim`
until [`Modelgen.primReady`] and generates it after the input's own. The third
step had no way to reach that queue: it was called from inside `genMutual` and
from the nested arm, both of which thread only `(out, rep, pending)`, so it
passed `canWait := false` and every model here declined at a primitive that was
merely *late*. On the Mathlib export that is `Lean.Syntax`, replayed at line
9,948 against `PSigma` at line 95,424: both of its members declined
`prim model name taken (PSigma)`, and both are models once they are allowed to
wait.

**This is not the exact-alias retry's class** and the two must not be
confused. That retry answers [`Modelgen.Decline.nameLost`] — *our* name,
normalised onto another of ours, which we may rename because nothing in the
input holds it. This is [`Modelgen.Decline.nameTaken`] — the *input's* name,
arriving later, which we may not take at any spelling and must simply wait for.

So the deferred jobs are **returned** rather than run, and the caller puts them
where the input declarations' own jobs go. `canWait := false` at the
end-of-file drain, where nothing more is coming and a decline is the honest
answer. -/
def primCompose (members : Array Name) (lparams : List Name) (np : Nat)
    (reserved : Std.HashSet Name) (basicModels : Bool) (canWait : Bool)
    (st : FilterState) : MetaM (FilterState × Array PrimJob) := do
  let mut st := st
  let mut wait : Array PrimJob := #[]
  -- Asked once, of the environment as it stands at the block: every member of
  -- one block is at the same point in the replay.
  let ready ← primReady reserved
  for n in members do
    let some (.inductInfo iv) := (← getEnv).constants.find? n | continue
    let mut cts : Array (Name × Expr) := #[]
    for cn in iv.ctors do
      let some ci := (← getEnv).constants.find? cn | continue
      cts := cts.push (cn, ci.type)
    let recursors ← recursorsOfNames #[n]
    if canWait && !ready then
      -- The type and the constructor types are read **here**, at the block,
      -- because that is where the member is known to be installed; the drain
      -- only needs to call `genPrim` with them.
      wait := wait.push (false, n, lparams, np, iv.type, cts, recursors)
    else
      st := (← genPrim n lparams np iv.type cts recursors reserved basicModels false st).1
  return (st, wait)

/-- One plain mutual block's model, generated and accounted for.

A function rather than two copies inline because it is called from two places
in [`Modelgen.runFilter`] — at the block, and again at the input's own `Eq` for
a block that had to wait for it.

The second component is [`Modelgen.primCompose`]'s deferred jobs, which the
caller adds to its own `waitingPrim`; it is empty unless the simple layer is on
and the basis is late. The basic layer is passed separately and controls the
support closure of each generated implementation tag and auxiliary model. -/
def genMutual (all : Array Name) (lparams : List Name) (np : Nat)
    (tys : Array Expr) (ctors : Array (Array (Name × Expr))) (recursors : Array ERec)
    (reserved : Std.HashSet Name) (simpleModels basicModels canWait : Bool)
    (st : FilterState) : MetaM (FilterState × Array PrimJob) := do
  let (out, rep, pending) := st
  let saved ← getEnv
  let mut result ← (do
    let is ← mutualIso all lparams np tys ctors reserved
    addInstalledUnitlikeTheorems all reserved is).run
  if let .error (.nameLost _) := result then
    setEnv saved
    result ← (do
      let is ← mutualIso all lparams np tys ctors reserved
        (some (Naming.retryRoot all[0]!))
      addInstalledUnitlikeTheorems all reserved is).run
  match result with
  | .error dec =>
    setEnv saved
    return ((out, { rep with declined := rep.declined.push (all[0]!, dec.labelAs "mutual") },
      pending), #[])
  | .ok is =>
    let (records, is) ← serialiseIso is
    let mut out := out
    out := out ++ records
    let mut rep := { rep with generated := rep.generated.push (all[0]!, is.decls.size) }
    unless is.spliced.isEmpty do
      rep := { rep with spliced := rep.spliced.push (all[0]!, is.spliced) }
    let st := (out, rep, pending.push
      { all := all, numParams := np, iso := is, recursors := recursors })
    if simpleModels then
      primCompose is.members is.levelParams np reserved basicModels canWait st
    else
      return (st, #[])

/-- Generation settings matching the legacy `primModels` switch: nested and
mutual models are always enabled, while simple models and their bootstrap
closure move together. This is the compatibility adapter for callers that have
not adopted [`Modelgen.Cli.parseArgs`] yet. -/
def legacyGenerationConfig (primModels : Bool) : Cli.Config :=
  { simple := primModels, basic := primModels }

/-- **The filter.** -/
def runFilter (x : Export) (checkRecursors : Bool) (generation : Cli.Config) :
    MetaM (Array EDecl × Report) := do
  let mut out : Array EDecl := #[]
  let mut rep : Report := {}
  -- Held back until the export's own declaration is installed, so the
  -- statements can be compared against the recursors it then mints.
  let mut pending : Array PendingModel := #[]
  -- Plain mutual blocks whose model is waiting for the input's own `Eq`.
  let mut waiting : Array (Array Name × List Name × Nat × Array Expr ×
    Array (Array (Name × Expr)) × Array ERec) := #[]
  -- Simple inductives waiting for the input's own basis
  -- declarations. The leading `Bool` says *which* wait: `false` for the basis
  -- ([`Modelgen.primReady`]) and `true` for the quotient behind `funext`
  -- ([`Modelgen.primLateReady`]) — kept apart so a model that never touches
  -- `funext` is not moved past a `Quot` it does not need.
  -- **The composition's third step queues here too** ([`Modelgen.PrimJob`]'s
  -- type): a `T._model._impl.tag` or `T._model._impl.aux` whose model needs a
  -- primitive the input declares later waits exactly as one of the input's own
  -- declarations does, instead of declining at a name that is merely late.
  let mut waitingPrim : Array PrimJob := #[]
  -- Every name the input declares anywhere, so that a model cannot collide
  -- with one the file itself introduces *later*.
  let reserved : Std.HashSet Name :=
    x.decls.foldl (fun s d => d.names.foldl (·.insert ·) s) {}
  for d in x.decls do
    -- The model, if this is a nested declaration. Generated **before** the
    -- declaration is added, which is where `mini/src/nested.rs` also stands:
    -- nothing in the model mentions `T`.
    if let .induct ts cs inputRecursors := d then
      -- **A mutual block whose members nest is one block, not several.** Lean
      -- specialises the whole block at once — `nest_mutual_both`'s `A`/`B`
      -- become four members with four recursors over one shared motive vector
      -- — so the model does too, under the first member's `_model` namespace
      -- and with one carrier per real member.
      if let t :: _ := ts then
        if generation.nested && ts.any (·.numNested > 0) then
          let all := ts.toArray.map (·.name)
          let ctorsOfMember := fun (n : Name) =>
            (cs.filter (·.induct == n)).toArray.map fun c => (c.name, c.type)
          let ptypes : Array PType := ts.toArray.map fun m =>
            { name := m.name, type := m.type, ctors := ctorsOfMember m.name }
          match plan (← getEnv) t.levelParams t.numParams ptypes with
          | .error e => rep := { rep with declined := rep.declined.push (t.name, e) }
          | .ok none => pure ()
          | .ok (some pl) =>
            let saved ← getEnv
            let ctors := all.map ctorsOfMember
            let mut result ← (do
              let is ← iso all t.levelParams t.numParams ctors pl reserved
              addUnitlikeTheorems ts.toArray cs.toArray inputRecursors.toArray reserved is).run
            if let .error (.nameLost _) := result then
              setEnv saved
              result ← (do
                let is ← iso all t.levelParams t.numParams ctors pl reserved
                  (some (Naming.retryRoot t.name))
                addUnitlikeTheorems ts.toArray cs.toArray inputRecursors.toArray reserved is).run
            match result with
            | .error dec =>
              setEnv saved
              rep := { rep with declined := rep.declined.push (t.name, dec.label) }
            | .ok is =>
              let (records, is) ← serialiseIso is
              out := out ++ records
              rep := { rep with generated := rep.generated.push (t.name, is.decls.size) }
              unless is.spliced.isEmpty do
                rep := { rep with spliced := rep.spliced.push (t.name, is.spliced) }
              pending := pending.push
                { all, numParams := t.numParams, iso := is,
                  recursors := inputRecursors.toArray }
              -- ── the model of the model (§1.7) ─────────────────────────────
              --
              -- **What has just been emitted is a `mutual … end` block**, and
              -- the second construction is the one that models exactly that.
              -- So it runs here, on `T._model.0 … T._model.{n−1}`, and the
              -- output carries a nested declaration's development twice over:
              -- the mutual model of `T`, and the *simple* model of that.
              --
              -- The block is still written — a model is emitted **beside** the
              -- thing it models and never in place of it (§1) — so what this
              -- buys is not that the output has no mutual block in it, but
              -- that **every** mutual block in the output has a model beside
              -- it, the ones this tool wrote included. A consumer that can add
              -- only a single inductive can now skip all of them.
              --
              -- **Here and not by re-running the filter.** The composition is
              -- one pass by construction; §1.7 is the boundary and §1.5's
              -- idempotence is unaffected, because on an already-filtered
              -- input every name below is taken and the name guard declines.
              --
              -- `Eq` is certainly present: `Modelgen.iso` above went through
              -- `ensureEq`, which either found the input's or spliced Lean's.
              -- So this never joins the `waiting` set.
              if generation.mutualModels && is.members.size > 1 then
                let saved2 ← getEnv
                let (tys2, ctors2) ← blockOf is.members
                let composedRoot := is.members[0]!
                let mut mutualResult ← (do
                  let is2 ← mutualIso is.members is.levelParams t.numParams
                    tys2 ctors2 reserved
                  addInstalledUnitlikeTheorems is.members reserved is2).run
                if let .error (.nameLost _) := mutualResult then
                  setEnv saved2
                  mutualResult ← (do
                    let is2 ← mutualIso is.members is.levelParams t.numParams
                      tys2 ctors2 reserved (some (Naming.retryRoot composedRoot))
                    addInstalledUnitlikeTheorems is.members reserved is2).run
                match mutualResult with
                | .error dec =>
                  setEnv saved2
                  rep := { rep with
                    declined := rep.declined.push (is.members[0]!, dec.labelAs "mutual") }
                | .ok is2 =>
                  let (records, is2) ← serialiseIso is2
                  out := out ++ records
                  rep := { rep with
                    generated := rep.generated.push (is.members[0]!, is2.decls.size) }
                  let modelRecursors ← recursorsOfNames is.members
                  pending := pending.push
                    { all := is.members, numParams := t.numParams, iso := is2,
                      recursors := modelRecursors }
                  -- ── the third step of the chain (`--prim-models`) ─────────
                  -- The mutual model's own single inductives, modelled from
                  -- the primitives — nested → mutual → primitives, one pass.
                  if generation.simple then
                    let (st3, jobs) ← primCompose is2.members is2.levelParams
                      t.numParams reserved generation.basic true (out, rep, pending)
                    (out, rep, pending) ← pure st3
                    waitingPrim := waitingPrim ++ jobs
    -- Replay, unchecked: the input is trusted. Lean's kernel still runs the
    -- *inductive* elaboration, which is not skippable, so a deliberately
    -- ill-formed inductive stops the replay here. Nothing has been spliced yet
    -- when that happens, so the file passes through untouched.
    if let some dcl := toDeclaration (← getEnv) d then
      -- `Environment.addDeclCore` and not `Kernel.Environment.
      -- addDeclWithoutChecking`, even though the elaborator-side bookkeeping is
      -- unwanted here: `Environment.find?` — which `MetaM`'s `inferType` goes
      -- through — reads the *imported* half of the constant map and then the
      -- **async** map, so a constant added at the kernel level is invisible to
      -- it and the generator cannot so much as name `List.rec`. The price is
      -- one `panic!` from `AsyncConsts.add` on
      -- `vendor/arena-tests/good/perf/grind-ring-5.ndjson`, where two private
      -- names from different modules normalise alike — normal in an export,
      -- which is many modules flattened into one file, and impossible during
      -- elaboration. It is not fatal: the entry is dropped from an index this
      -- tool never reads, and that file's model is still accepted by `nanoda`.
      match (← getEnv).addDeclCore 0 dcl none false with
      | .ok e => setEnv e
      | .error ex =>
        let msg ← (ex.toMessageData {}).toString
        return (x.decls, { rep with unreplayable := some s!"{d.names}: {msg}" })
    -- **The model of a plain mutual block, and it is generated *after* the
    -- replay** where the nested one is generated before it. The reason is that
    -- there is nothing else to read the statements off: a nested declaration's
    -- model restates the recursors of the *specialised* block, which this tool
    -- builds itself, and a plain mutual block has no such second inductive —
    -- the implementation auxiliary's recursor is not `R_k.rec` at any
    -- renaming. So `Modelgen.mutualIso` reads the recursors Lean minted for the
    -- input's own block, which exist only once it is installed
    -- (`Modelgen/Mutual.lean`'s header).
    --
    -- The **records** still go out ahead of the declaration's whenever they
    -- can, because `out` has not been pushed yet.
    if let .induct ts cs inputRecursors := d then
      if let t :: _ := ts then
        -- **No "is this a block I wrote?" test here**, and that is deliberate.
        -- On this tool's own output the block `T._model.0 … T._model.{n−1}` is
        -- an input record like any other and does reach this branch — and
        -- declines, because every name its model would want is already in the
        -- file and the name guard says so. Idempotence is carried by the same
        -- mechanism that carries it for a nested declaration (§1.7), which is
        -- one mechanism rather than two things to keep in step.
        if generation.mutualModels && ts.length > 1 && !ts.any (·.numNested > 0) then
          let all := ts.toArray.map (·.name)
          let ctors := all.map fun n =>
            (cs.filter (·.induct == n)).toArray.map fun c => (c.name, c.type)
          let tys := ts.toArray.map (·.type)
          let job := (all, t.levelParams, t.numParams, tys, ctors, inputRecursors.toArray)
          -- **The model may have to wait for the input's own `Eq`.** Its ι
          -- theorems are stated at one, and an export's dependency order
          -- routinely puts `Eq` *after* a block that does not itself use it —
          -- `mutual_iota_reduction`, `mutual_parameters` and
          -- `mutual_index_sorts` all do, and `mini/src/mutual_aux.rs`'s
          -- `expand` holds its rule theorems back for the same reason. A file
          -- that declares no `Eq` at all does not wait: §1.5 splices one.
          if ← eqReady reserved then
            let (st3, jobs) ← genMutual all t.levelParams t.numParams tys ctors
              inputRecursors.toArray reserved
              generation.simple generation.basic true (out, rep, pending)
            (out, rep, pending) ← pure st3
            waitingPrim := waitingPrim ++ jobs
          else
            waiting := waiting.push job
        -- ── a simple inductive (`--prim-models`): the third construction ──
        -- Generated after the replay, like the plain mutual block and for
        -- the same reason: the statements are the installed recursor's own,
        -- restored, and there is nothing else to read them off.
        if generation.modelsSimpleInput t.name && ts.length == 1 && t.numNested == 0 then
          let ctors := (cs.filter (·.induct == t.name)).toArray.map fun c => (c.name, c.type)
          if ← primReady reserved then
            let (st, lateWait) ← genPrim t.name t.levelParams t.numParams t.type ctors
              inputRecursors.toArray reserved generation.basic true (out, rep, pending)
            if lateWait then
              waitingPrim := waitingPrim.push
                (true, t.name, t.levelParams, t.numParams, t.type, ctors,
                  inputRecursors.toArray)
            else
              (out, rep, pending) ← pure st
          else
            waitingPrim := waitingPrim.push
              (false, t.name, t.levelParams, t.numParams, t.type, ctors,
                inputRecursors.toArray)
    out := out.push d
    -- The input's own `Eq` has just arrived: every block that was waiting for
    -- it gets its model here, **after** the `Eq` record, which is where
    -- dependency order puts it.
    if !waiting.isEmpty && (← eqReady reserved) then
      for (all, lp, np, tys, ctors, recursors) in waiting do
        let (st3, jobs) ← genMutual all lp np tys ctors recursors reserved generation.simple
          generation.basic true
          (out, rep, pending)
        (out, rep, pending) ← pure st3
        waitingPrim := waitingPrim ++ jobs
      waiting := #[]
    -- A prim model may also splice `False`, `Nat` and `PSigma`, so it waits
    -- for whichever of those the input declares later, not only for `Eq` —
    -- and one whose proofs need `funext` waits for the input's own quotient
    -- on top of that, re-queued with the flag flipped if the basis drain
    -- discovers the need.
    if !waitingPrim.isEmpty then
      let basisOk ← primReady reserved
      let lateOk ← primLateReady reserved
      if basisOk || lateOk then
        let mut keep : Array PrimJob := #[]
        for job in waitingPrim do
          let (needsLate, n, lp, np, ty, ctors, recursors) := job
          if (if needsLate then lateOk else basisOk) then
            let (st, lateWait) ← genPrim n lp np ty ctors recursors reserved
              generation.basic true
              (out, rep, pending)
            if lateWait then
              keep := keep.push (true, n, lp, np, ty, ctors, recursors)
            else
              (out, rep, pending) ← pure st
          else
            keep := keep.push job
        waitingPrim := keep
    for model in pending do
      let (m, errs) ← checkModel model.all model.numParams model.iso model.recursors
      rep := { rep with stmtChecked := rep.stmtChecked + m, stmtErrors := rep.stmtErrors ++ errs }
    pending := #[]
    if checkRecursors then
      if let .induct _ _ rs := d then
        let (n, b) ← checkRecs rs
        rep := { rep with recChecked := rep.recChecked + n, recMismatch := rep.recMismatch ++ b }
  -- A block still waiting at the end of the file declared an `Eq` the replay
  -- never reached — so the name is taken and no splice may use it, and this
  -- pass **declines with that reason** rather than dropping the block without
  -- saying anything. Nothing in the tree reaches it: over all 230 files the
  -- decline list gains nothing at all against the run before §1.6 existed, and
  -- a block left waiting would have put a `mutual model name taken (Eq)` in it.
  for (all, lp, np, tys, ctors, recursors) in waiting do
    let (st3, jobs) ← genMutual all lp np tys ctors recursors reserved generation.simple
      generation.basic false
      (out, rep, pending)
    (out, rep, pending) ← pure st3
    waitingPrim := waitingPrim ++ jobs
  for (_, n, lp, np, ty, ctors, recursors) in waitingPrim do
    (out, rep, pending) ← pure
      (← genPrim n lp np ty ctors recursors reserved generation.basic false
        (out, rep, pending)).1
  for model in pending do
    let (m, errs) ← checkModel model.all model.numParams model.iso model.recursors
    rep := { rep with stmtChecked := rep.stmtChecked + m, stmtErrors := rep.stmtErrors ++ errs }
  return (out, rep)

end Modelgen
