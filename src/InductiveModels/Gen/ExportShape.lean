import Lean
import InductiveModels.Format.Types

/-!
# Reading shapes off an export, without a monad

Pure `Name`/`Expr` functions over exported recursors: what the export calls a
block member's recursor, how the specialisation's names are rewritten back,
and how an exported recursor's *exact* binder telescope is recovered.

These deliberately avoid `GenM`. A telescope opened through `MetaM` loses the
export's own binder names and binder info, which the public statements are
required to reproduce literally, so these open the binders by hand.
-/

open Lean Meta

namespace InductiveModels
/-- **The name the export gives block index `k`'s recursor**, for a block whose
own members are `all`.

Measured on Lean's own export of
`test/fixtures/inductive-models/nest_mutual_both.ndjson`,
where the mutual block `A`/`B` nesting at `List B` and `Box A` comes back with
`A.rec`, `B.rec`, `A.rec_1` and `A.rec_2`: a **real** member's recursor is in
that member's own namespace and a **mimic**'s is in the first member's,
numbered from 1. For a one-member block that is `T.rec`, `T.rec_1`, … and
nothing has moved.

The whole family is `all.size + numNested` long — Lean mints one recursor per
motive, and the motives are the real members followed by the nested
occurrences. -/
def exportRecName (all : Array Name) (k : Nat) : Name :=
  match all[k]? with
  | some n => .str n "rec"
  | none => .str all[0]! s!"rec_{k - all.size + 1}"

/-! ## Restoring: rewriting the block's names to the model's -/

/-- Rewrite every name the specialisation introduced back to what it stands
for. A head that consumes `p` arguments has them substituted into its
replacement — that is how `Tree._nested.1 α` becomes `List (Tree α)` under a
parameter — and a head that consumes none is a plain rename. -/
partial def restore (heads : Std.HashMap Name (Nat × Expr)) (e : Expr) : Expr :=
  if heads.isEmpty then e else
  match e with
  | .const n _ => match heads[n]? with
    | some (0, repl) => repl
    | _ => e
  | .app .. =>
    let h := e.getAppFn
    let args := e.getAppArgs.map (restore heads)
    match h with
    | .const n _ =>
      match heads[n]? with
      | some (take, repl) =>
        if args.size ≥ take then
          mkAppN (repl.instantiateRev (args.extract 0 take)) (args.extract take args.size)
        else mkAppN h args
      | none => mkAppN h args
    | _ => mkAppN (restore heads h) args
  | .lam n t b bi => .lam n (restore heads t) (restore heads b) bi
  | .forallE n t b bi => .forallE n (restore heads t) (restore heads b) bi
  | .letE n t v b nd => .letE n (restore heads t) (restore heads v) (restore heads b) nd
  | .proj tn i s =>
    let restoredType := match heads[tn]? with
      | some (0, .const name _) => name
      | _ => tn
    .proj restoredType i (restore heads s)
  | .mdata data body => .mdata data (restore heads body)
  | _ => e

/-- Close `body` over the already-opened `values`, taking each binder's name,
domain and binder info from the exact `telescope` rather than from the local
context.  Meta may normalize a local declaration's type when a telescope is
opened; rebuilding a public theorem type with `mkForallFVars` would then lose
literal syntax which the export correspondence deliberately preserves.

The telescope is instantiated left-to-right at the supplied locals, so a
later exact domain may mention earlier locals.  Closing right-to-left then
abstracts those locals through both the body and the exact inner domains. -/
def closeForallsExact? (telescope : Expr) (values : Array Expr) (body : Expr) : Option Expr :=
  Id.run do
    let mut current := telescope
    let mut binders : Array (Name × Expr × BinderInfo × Expr) := #[]
    for value in values do
      let .forallE name domain rest info := current | return none
      binders := binders.push (name, domain, info, value)
      current := rest.instantiate1 value
    let mut result := body
    for binder in binders.reverse do
      let (name, domain, info, value) := binder
      result := .forallE name domain (result.abstract #[value]) info
    return some result

/-- A binder opened without consulting `MetaM`, retaining its exact exported
domain for public recursor and iota statements. -/
private structure ExactRecBinder where
  name : Name
  type : Expr
  info : BinderInfo
  value : Expr

private partial def openExactRecForalls (tag : Name) (expression : Expr) :
    Array ExactRecBinder × Expr :=
  let rec loop (expression : Expr) (binders : Array ExactRecBinder) :=
    match expression with
    | .forallE name type body info =>
      let value := mkFVar (FVarId.mk (tag.mkNum binders.size))
      loop (body.instantiate1 value) (binders.push { name, type, info, value })
    | body => (binders, body)
  loop expression #[]

private def closeExactRecForalls (binders : Array ExactRecBinder) (body : Expr) : Expr :=
  binders.reverse.foldl (fun body binder =>
    .forallE binder.name binder.type (body.abstract #[binder.value]) binder.info) body

/-- Recover the exact constructor-field telescope presented by one exported
recursor minor premise. Installed recursor metadata remains the proof/layout
oracle; this syntax is used only to close a public iota statement. -/
def exactRecursorFieldTelescope? (recursor : ERec) (ruleIndex : Nat)
    (pre : Array Expr) : Option Expr := do
  let rule ← recursor.rules[ruleIndex]?
  if rule.nfields == 0 then
    return .sort .zero
  let (recBinders, _) := openExactRecForalls ((`_exact_rec).append recursor.name)
    recursor.type
  let numPre := recursor.numParams + recursor.numMotives + recursor.numMinors
  unless pre.size == numPre do none
  let sourcePre := recBinders.extract 0 numPre |>.map (·.value)
  let minors := recBinders.extract (recursor.numParams + recursor.numMotives) numPre
  minors.findSome? fun minor => do
    let minorType := minor.type.replace fun expression =>
      sourcePre.findIdx? (fun value => value == expression) |>.map fun index => pre[index]!
    let (minorBinders, motiveResult) :=
      openExactRecForalls ((`_exact_minor).append rule.ctor) minorType
    let major ← motiveResult.getAppArgs.back?
    let .const constructor _ := major.getAppFn | none
    unless constructor == rule.ctor do none
    let majorArgs := major.getAppArgs
    unless majorArgs.size >= rule.nfields do none
    let fieldValues := majorArgs.extract (majorArgs.size - rule.nfields) majorArgs.size
    let mut fields : Array ExactRecBinder := #[]
    for value in fieldValues do
      let some binder := minorBinders.find? (·.value == value) | fields := #[]; break
      fields := fields.push binder
    unless fields.size == rule.nfields do none
    return closeExactRecForalls fields (.sort .zero)

/-- Recover the exact motive application at one exported recursor minor after
substituting the generator's current prefix and constructor fields.  This is
the type of the public iota equality; rebuilding it from installed recursor
locals would preserve meaning while losing source-authored universe syntax. -/
def exactRecursorMotiveResult? (recursor : ERec) (ruleIndex : Nat)
    (pre fields : Array Expr) : Option Expr := do
  let rule ← recursor.rules[ruleIndex]?
  unless fields.size == rule.nfields do none
  let (recBinders, _) := openExactRecForalls ((`_exact_rec_result).append recursor.name)
    recursor.type
  let numPre := recursor.numParams + recursor.numMotives + recursor.numMinors
  unless pre.size == numPre do none
  let sourcePre := recBinders.extract 0 numPre |>.map (·.value)
  let minors := recBinders.extract (recursor.numParams + recursor.numMotives) numPre
  minors.findSome? fun minor => do
    let minorType := minor.type.replace fun expression =>
      sourcePre.findIdx? (fun value => value == expression) |>.map fun index => pre[index]!
    let (minorBinders, motiveResult) :=
      openExactRecForalls ((`_exact_minor_result).append rule.ctor) minorType
    let major ← motiveResult.getAppArgs.back?
    let .const constructor _ := major.getAppFn | none
    unless constructor == rule.ctor do none
    let majorArgs := major.getAppArgs
    unless majorArgs.size >= rule.nfields do none
    let fieldValues := majorArgs.extract (majorArgs.size - rule.nfields) majorArgs.size
    let mut sourceFields : Array Expr := #[]
    for value in fieldValues do
      let some binder := minorBinders.find? (·.value == value)
        | sourceFields := #[]; break
      sourceFields := sourceFields.push binder.value
    unless sourceFields.size == fields.size do none
    return motiveResult.replace fun expression =>
      sourceFields.findIdx? (· == expression) |>.map fun index => fields[index]!

end InductiveModels
