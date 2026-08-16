import InductiveModels.Simple.Site

/-!
# The ι rules, one per constructor

Every one is `Eq.refl` except arms E, G and W, and the *statement* is the
shared one in all three cases — which is what keeps the oracle's syntactic
comparison honest across the arms.
-/

open Lean Meta

namespace InductiveModels

def primIotaRules (site : PrimSite) (st : PrimOut) :
    GenM (PrimOut × Array (Nat × Name × Name)) := do
  -- The site, under the names this arm has always read it by.
  let tname := site.tname
  let np := site.np
  let exportCtors := site.exportCtors
  let sourceRecursor? := site.sourceRecursor?
  let interface? := site.interface?
  let us := site.us
  let impl := site.impl
  let selfN := site.selfN
  let ern := site.ern
  let recN := site.recN
  let iotaN := site.iotaN
  let nc := site.nc
  let ni := site.ni
  let w := site.w
  let rv := site.rv
  let v := site.v
  let recLs := site.recLs
  let gRecNb := site.gRecNb
  let gNf := site.gNf
  let armG := site.armG
  let eqi := site.eqi
  let ctorPairs := site.ctorPairs
  let installedRecTy := site.installedRecTy
  let publicSource := site.publicSource
  let publicRecTy := site.publicRecTy
  let emptySlots := site.emptySlots
  let armE := site.armE
  let wPlan := site.wPlan
  let armW := site.armW
  let wFN := site.wFN
  let uL := site.uL
  let wKL := site.wKL
  let wAAt := site.wAAt
  let wKTy := site.wKTy
  let wBFn := site.wBFn
  let wTgAt := site.wTgAt
  let wDecEq := site.wDecEq
  let wLowSelfAt := site.wLowSelfAt
  let wCtorParts := site.wCtorParts
  let mut out := st.out
  -- ── the ι rules ──
  let mut iotas : Array (Nat × Name × Name) := #[]
  unless rv.rules.length == nc do
    badShape s!"{ern} has {rv.rules.length} rules where {tname} has {nc} constructors"
  for j in [0:nc] do
    let rule := rv.rules[j]!
    let publicRule := sourceRecursor?.bind (·.rules[j]?)
    let (cn, modelC) := ctorPairs[j]!
    unless rule.ctor == cn do
      badShape s!"{ern}'s rule {j} is for {rule.ctor}, not {cn}"
    -- Walk the exact exported constructor type at the model's names. Reading
    -- the installed definition back with `constInfo` is not syntax preserving:
    -- the kernel may βζ-normalise a field domain while storing it. The public
    -- constructor declaration still carries the exported redex literally, and
    -- the iota theorem's telescope is part of the same literal interface.
    let modelCTy := publicSource exportCtors[j]!.2
    let d ← forallBoundedTelescope installedRecTy (some (np + 1 + nc)) fun pre _ => do
      let ps := pre.extract 0 np
      let motive := pre[np]!
      let cty ← instForall modelCTy ps
      forallBoundedTelescope cty (some (numForalls modelCTy - np)) fun fields res => do
        let major := mkAppN (.const modelC us) (ps ++ fields)
        -- The constructor's own index expressions, read off its result type
        -- `T._model.self p⃗ ι⃗_j`. The recursor takes them between the minors
        -- and the major, and the motive takes them before it.
        let some args ← ownerAppArgs? selfN np ni res
          | badShape s!"{modelC}'s result is not {selfN} at {np} parameters and {ni} indices"
        let isj := args.extract np args.size
        let lhs := mkAppN (.const recN recLs) (pre ++ isj ++ #[major])
        let rhsSyntax := publicRule.map (·.rhs) |>.getD rule.rhs
        let rhs := (publicSource rhsSyntax).beta (pre ++ fields)
        let α ← match interface?, sourceRecursor? with
          | some _, some sourceRecursor =>
            let some exactResult := exactRecursorMotiveResult? sourceRecursor j pre fields
              | badShape s!"{sourceRecursor.name}'s exported rule {j} has no exact motive result"
            pure (publicSource exactResult)
          | _, _ => pure (mkAppN motive (isj.push major))
        let tel := pre ++ fields
        let proposition := eqi.mk' v α lhs rhs
        let exactFieldTelescope ← match sourceRecursor? with
          | none => pure cty
          | some sourceRecursor =>
            let some telescope := exactRecursorFieldTelescope? sourceRecursor j pre
              | badShape s!"{sourceRecursor.name}'s exported rule {j} has no exact field telescope"
            pure (publicSource telescope)
        let some fieldsType := closeForallsExact? exactFieldTelescope fields proposition
          | badShape s!"{modelC}'s public recursor telescope has fewer fields than its installed type"
        let some theoremType := closeForallsExact? publicRecTy pre fieldsType
          | badShape s!"{ern}'s exported telescope is shorter than its recursor prefix"
        -- **Every ι theorem is `Eq.refl` except arms E, G and W.**
        --
        -- Arm G's value is a `Classical.choice` application, which reduces to
        -- nothing, so the rule is proved instead: both sides are graph points
        -- at this constructor and the graph is single-valued.
        --
        -- Arm W's is `WT.Wrec_iota` and nothing else, at this declaration's own
        -- `F`, label and dispatch — `Wrec` is a well-founded recursion, so its
        -- ι is a theorem rather than a conversion. **That theorem is the pin
        -- for a collapsed tag assignment**, which is the one wrong model no
        -- type error stops: two constructors of the same shape sharing a tag
        -- have minors of the same type, so the two model constructors simply
        -- become the same term and every other check still passes. It is the
        -- narrowest of seven checked mutations.
        --
        -- The *statement* is the shared one in all three cases, which is what
        -- keeps the oracle's syntactic comparison honest across the arms.
        --
        -- The site's route booleans are mutually exclusive by construction
        -- ([`InductiveModels.mkPrimSite`] settles `armW` against `armE`
        -- explicitly), so the order of the tests below carries no decision:
        -- reading them in a different order would select the same arm.
        let proof ←
          if armW then do
            let (a, disp) ← wCtorParts ps j fields
            let coreMotive ← wPlan.motive (wLowSelfAt ps) motive
            pure (mkAppN (.const wCoreIota [uL, v, wKL])
              #[wKTy ps, wAAt ps, wBFn ps, wDecEq ps, wTgAt ps, coreMotive,
                mkAppN (.const wFN recLs) pre, a, disp])
          else if armE then do
            let some k := emptySlots[j]!
              | badShape s!"{cn} has no recursive field in the empty route"
            emptyAtElim eqi .zero w (eqi.mk' v α lhs rhs) fields[k]!
          else if !armG then pure (eqi.refl' v α lhs) else do
            let rsI := (Array.range gNf).filter fun i => gRecNb[i]!.isSome
            let atSlot := fun (nm : Name) => rsI.mapM fun i => do
              let fty ← ityp fields[i]!
              forallBoundedTelescope fty (some (gRecNb[i]!.getD 0)) fun zs r2 => do
                let a2 := r2.getAppArgs
                mkLambdaFVars zs (mkAppN (.const nm recLs)
                  (pre ++ a2.extract np a2.size ++ #[mkAppN fields[i]! zs]))
            let ghat ← atSlot recN
            let hhat ← atSlot (Name.str impl "rec_graph")
            let gv := mkAppN (.const (Name.str impl "rec_graph") recLs)
              (pre ++ isj ++ #[major])
            let gw := mkAppN (.const (Name.str impl "graph_mk") recLs)
              (pre ++ fields ++ ghat ++ hhat)
            pure (mkAppN (.const (Name.str impl "graph_unique") recLs)
              (pre ++ isj ++ #[major, lhs, rhs, gv, gw]))
        return Declaration.thmDecl
          { name := iotaN j, levelParams := rv.levelParams
            type := theoremType
            value := ← mkLambdaFVars tel proof }
    addChecked d
    out := out.push d
    iotas := iotas.push (0, cn, iotaN j)
  return ({ st with out }, iotas)

end InductiveModels
