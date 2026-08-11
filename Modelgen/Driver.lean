import Modelgen.Simple
import Modelgen.Cli

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

There are **two** constructions and they are separate files. `Modelgen/
Model.lean` specialises a nested declaration into a mutual block and proves the
export's recursors over it; `Modelgen/Mutual.lean` packs a plain mutual block
into a tag and one single inductive. Neither is the other at a degenerate
setting — §1.6 — and this driver is the only thing that knows both.

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
def checkModel (all : Array Name) (np : Nat) (is : Iso) : MetaM (Nat × Array String) := do
  let env ← getEnv
  let tbl := modelTable env all is
  let mut n := 0
  let mut errs : Array String := #[]
  for k in [0:is.recs.size] do
    let ern := exportRecName all k
    let some (.recInfo rv) := env.constants.find? ern
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
    (ctors : Array (Name × Expr)) (reserved : Std.HashSet Name) (basicModels : Bool)
    (canWait : Bool)
    (st : Array EDecl × Report × Array (Array Name × Nat × Iso)) :
    MetaM ((Array EDecl × Report × Array (Array Name × Nat × Iso)) × Bool) := do
  let (out, rep, pending) := st
  let saved ← getEnv
  -- **The retry under an alias root**, and it is a retry rather than a
  -- decision taken up front on purpose: aliasing changes nothing about the
  -- output and everything about the risk, so it runs only where the collision
  -- has actually fired. Every declaration that models today takes exactly the
  -- path it took before, byte for byte.
  --
  -- The alias has to be unique per *original* name and not merely per
  -- declaration, because the collisions in Mathlib are not only
  -- private-against-public: three private `Lean.Compiler.LCNF.State`s from
  -- three different modules normalize alike, so a single `_mgalt` component
  -- would put all three back on top of each other. The original name flattened
  -- into one component is the discriminator, and it survives
  -- `privateToUserName` because that only strips a prefix.
  let aliasRoot : Name :=
    Name.str (Name.str tname "_mgalt") ((toString tname).replace "." "_")
  let mut root := tname
  let mut res ← (primIso tname root lparams np ty ctors reserved).run
  if let .error (.nameLost _) := res then
    setEnv saved
    root := aliasRoot
    res ← (primIso tname root lparams np ty ctors reserved).run
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
    let out0 := out.size
    let mut out := out
    for gd in is.decls do
      for e in ← toEDecls gd do out := out.push e
    let mut rep := { rep with generated := rep.generated.push (tname, is.decls.size) }
    unless is.spliced.isEmpty do
      rep := { rep with spliced := rep.spliced.push (tname, is.spliced) }
    let mut st2 := (out, rep, pending.push (#[tname], np, is))
    if basicModels then
      for n in is.spliced do
        if primBasis.contains n then continue
        let some (.inductInfo iv) := (← getEnv).constants.find? n | continue
        -- the block's own name only, and only a simple one
        unless iv.all == [n] && iv.numNested == 0 do continue
        -- already modelled (a second declaration spliced the same thing)
        if (← getEnv).constants.contains (Name.str (Name.str n "_model") "self") then continue
        let mut cts : Array (Name × Expr) := #[]
        for cn in iv.ctors do
          if let some ci := (← getEnv).constants.find? cn then cts := cts.push (cn, ci.type)
        st2 :=
          (← genPrim n iv.levelParams iv.numParams iv.type cts reserved basicModels false st2).1
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
    -- **The rename, over the slice this call produced** — its own records and
    -- the descent's, which is why it is here and over `EDecl`s rather than
    -- over `is.decls`: arm C's spliced skeleton is modelled by a recursive
    -- `genPrim` whose names are built off the alias root too.
    if let some (fr, to) := is.emitAs? then
      let mut o2 := (st2.1).extract 0 out0
      for e in (st2.1).extract out0 (st2.1).size do
        o2 := o2.push (e.renameRoot fr to)
      st2 := (o2, { st2.2.1 with
        spliced := st2.2.1.spliced.map fun (n, ns) =>
          (Modelgen.renameRoot fr to n, ns.map (Modelgen.renameRoot fr to)) }, st2.2.2)
    if basicModels then
      for n in is.requires do
        unless (← getEnv).constants.contains (Name.str (Name.str n "_model") "self") do
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
abbrev PrimJob := Bool × Name × List Name × Nat × Expr × Array (Name × Expr)

/-- **The composition's third step**: the single inductives a mutual model
just emitted — `T._model.tag` and `T._model.aux` — are declarations of the
output like any other, so `--prim-models` runs on them too. The tag is a
plain sum and models; `aux` is indexed and takes arm C.

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

**This is not the `_mgalt` alias-root retry's class** and the two must not be
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
    (st : Array EDecl × Report × Array (Array Name × Nat × Iso)) :
    MetaM ((Array EDecl × Report × Array (Array Name × Nat × Iso)) × Array PrimJob) := do
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
    if canWait && !ready then
      -- The type and the constructor types are read **here**, at the block,
      -- because that is where the member is known to be installed; the drain
      -- only needs to call `genPrim` with them.
      wait := wait.push (false, n, lparams, np, iv.type, cts)
    else
      st := (← genPrim n lparams np iv.type cts reserved basicModels false st).1
  return (st, wait)

/-- One plain mutual block's model, generated and accounted for.

A function rather than two copies inline because it is called from two places
in [`Modelgen.runFilter`] — at the block, and again at the input's own `Eq` for
a block that had to wait for it.

The second component is [`Modelgen.primCompose`]'s deferred jobs, which the
caller adds to its own `waitingPrim`; it is empty unless the simple layer is on
and the basis is late. The basic layer is passed separately and controls the
support closure of each generated tag and auxiliary model. -/
def genMutual (all : Array Name) (lparams : List Name) (np : Nat)
    (tys : Array Expr) (ctors : Array (Array (Name × Expr)))
    (reserved : Std.HashSet Name) (simpleModels basicModels canWait : Bool)
    (st : Array EDecl × Report × Array (Array Name × Nat × Iso)) :
    MetaM ((Array EDecl × Report × Array (Array Name × Nat × Iso)) × Array PrimJob) := do
  let (out, rep, pending) := st
  let saved ← getEnv
  match ← (mutualIso all lparams np tys ctors reserved).run with
  | .error dec =>
    setEnv saved
    return ((out, { rep with declined := rep.declined.push (all[0]!, dec.labelAs "mutual") },
      pending), #[])
  | .ok is =>
    let mut out := out
    for gd in is.decls do
      for e in ← toEDecls gd do out := out.push e
    let mut rep := { rep with generated := rep.generated.push (all[0]!, is.decls.size) }
    unless is.spliced.isEmpty do
      rep := { rep with spliced := rep.spliced.push (all[0]!, is.spliced) }
    let st := (out, rep, pending.push (all, np, is))
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
  let mut pending : Array (Array Name × Nat × Iso) := #[]
  -- Plain mutual blocks whose model is waiting for the input's own `Eq`.
  let mut waiting : Array (Array Name × List Name × Nat × Array Expr ×
    Array (Array (Name × Expr))) := #[]
  -- Simple inductives waiting for the input's own basis
  -- declarations. The leading `Bool` says *which* wait: `false` for the basis
  -- ([`Modelgen.primReady`]) and `true` for the quotient behind `funext`
  -- ([`Modelgen.primLateReady`]) — kept apart so a model that never touches
  -- `funext` is not moved past a `Quot` it does not need.
  -- **The composition's third step queues here too** ([`Modelgen.PrimJob`]'s
  -- type): a `T._model.tag` or `T._model.aux` whose model needs a primitive the
  -- input declares later waits exactly as one of the input's own declarations
  -- does, instead of declining at a name that is merely late.
  let mut waitingPrim : Array PrimJob := #[]
  -- Every name the input declares anywhere, so that a model cannot collide
  -- with one the file itself introduces *later*.
  let reserved : Std.HashSet Name :=
    x.decls.foldl (fun s d => d.names.foldl (·.insert ·) s) {}
  for d in x.decls do
    -- The model, if this is a nested declaration. Generated **before** the
    -- declaration is added, which is where `mini/src/nested.rs` also stands:
    -- nothing in the model mentions `T`.
    if let .induct ts cs _ := d then
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
            match ← (iso all t.levelParams t.numParams ctors pl reserved).run with
            | .error dec =>
              setEnv saved
              rep := { rep with declined := rep.declined.push (t.name, dec.label) }
            | .ok is =>
              for gd in is.decls do
                for e in ← toEDecls gd do out := out.push e
              rep := { rep with generated := rep.generated.push (t.name, is.decls.size) }
              unless is.spliced.isEmpty do
                rep := { rep with spliced := rep.spliced.push (t.name, is.spliced) }
              pending := pending.push (all, t.numParams, is)
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
                match ← (mutualIso is.members is.levelParams t.numParams
                          tys2 ctors2 reserved).run with
                | .error dec =>
                  setEnv saved2
                  rep := { rep with
                    declined := rep.declined.push (is.members[0]!, dec.labelAs "mutual") }
                | .ok is2 =>
                  for gd in is2.decls do
                    for e in ← toEDecls gd do out := out.push e
                  rep := { rep with
                    generated := rep.generated.push (is.members[0]!, is2.decls.size) }
                  pending := pending.push (is.members, t.numParams, is2)
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
    -- `aux.rec` is not `R_k.rec` at any renaming. So `Modelgen.mutualIso` reads
    -- the recursors Lean minted for the input's own block, which exist only
    -- once it is installed (`Modelgen/Mutual.lean`'s header).
    --
    -- The **records** still go out ahead of the declaration's whenever they
    -- can, because `out` has not been pushed yet.
    if let .induct ts cs _ := d then
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
          let job := (all, t.levelParams, t.numParams, tys, ctors)
          -- **The model may have to wait for the input's own `Eq`.** Its ι
          -- theorems are stated at one, and an export's dependency order
          -- routinely puts `Eq` *after* a block that does not itself use it —
          -- `mutual_iota_reduction`, `mutual_parameters` and
          -- `mutual_index_sorts` all do, and `mini/src/mutual_aux.rs`'s
          -- `expand` holds its rule theorems back for the same reason. A file
          -- that declares no `Eq` at all does not wait: §1.5 splices one.
          if ← eqReady reserved then
            let (st3, jobs) ← genMutual all t.levelParams t.numParams tys ctors reserved
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
              reserved generation.basic true (out, rep, pending)
            if lateWait then
              waitingPrim := waitingPrim.push
                (true, t.name, t.levelParams, t.numParams, t.type, ctors)
            else
              (out, rep, pending) ← pure st
          else
            waitingPrim := waitingPrim.push
              (false, t.name, t.levelParams, t.numParams, t.type, ctors)
    out := out.push d
    -- The input's own `Eq` has just arrived: every block that was waiting for
    -- it gets its model here, **after** the `Eq` record, which is where
    -- dependency order puts it.
    if !waiting.isEmpty && (← eqReady reserved) then
      for (all, lp, np, tys, ctors) in waiting do
        let (st3, jobs) ← genMutual all lp np tys ctors reserved generation.simple
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
        let mut keep : Array (Bool × Name × List Name × Nat × Expr × Array (Name × Expr)) := #[]
        for job in waitingPrim do
          let (needsLate, n, lp, np, ty, ctors) := job
          if (if needsLate then lateOk else basisOk) then
            let (st, lateWait) ← genPrim n lp np ty ctors reserved generation.basic true
              (out, rep, pending)
            if lateWait then
              keep := keep.push (true, n, lp, np, ty, ctors)
            else
              (out, rep, pending) ← pure st
          else
            keep := keep.push job
        waitingPrim := keep
    for (all, np, is) in pending do
      let (m, errs) ← checkModel all np is
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
  for (all, lp, np, tys, ctors) in waiting do
    let (st3, jobs) ← genMutual all lp np tys ctors reserved generation.simple
      generation.basic false
      (out, rep, pending)
    (out, rep, pending) ← pure st3
    waitingPrim := waitingPrim ++ jobs
  for (_, n, lp, np, ty, ctors) in waitingPrim do
    (out, rep, pending) ← pure
      (← genPrim n lp np ty ctors reserved generation.basic false (out, rep, pending)).1
  for (all, np, is) in pending do
    let (m, errs) ← checkModel all np is
    rep := { rep with stmtChecked := rep.stmtChecked + m, stmtErrors := rep.stmtErrors ++ errs }
  return (out, rep)

end Modelgen
