import InductiveModels.Driver

namespace ComposedRecursorSyntaxTest

/-!
# Composed exact-recursor syntax regression

The three composition seams consume inductives generated earlier in the same
island: nested to mutual, mutual auxiliary to simple, and carve-arm skeleton to
simple splice closure. The focused transform perturbs the exact recursor minor
domain at its serialization boundary, before the immediate composed consumer.
Every generated public statement must follow that syntax while proof terms
continue to use installed kernel metadata.

[`runBinderFidelity`] pins the same claim at the one granularity the checker's
own comparison cannot see. `BEq Expr` is `Expr.eqv`, which ignores binder names
and binder info, so every comparison above holds of a statement that renamed a
parameter or turned an explicit binder implicit. `Expr.equal` is the test that
does not, and the generated public interface satisfies it: type formers,
constructors, recursors and ι rules are all spelled from the export's own
records, so their binders are the owner's own.
-/

open Lean Meta InductiveModels

def noGeneration : Cli.Config :=
  { nested := false, mutualModels := false, simple := false, basic := false }

structure Route where
  label : String
  fixture : String
  generation : Cli.Config
  owner : Name

def routes : Array Route := #[
  { label := "nested-to-mutual", fixture := "nested_iota_arm.ndjson",
    generation := { noGeneration with nested := true, mutualModels := true },
    owner := Name.num `Tree._model._impl 0 },
  { label := "mutual-to-simple", fixture := "mutual_nonrec.ndjson",
    generation := { noGeneration with mutualModels := true, simple := true },
    owner := `OA._model._impl.aux },
  { label := "carve-arm-splice-closure", fixture := "prim_carve.ndjson",
    generation := { noGeneration with simple := true, basic := true },
    owner := `Bif._model._impl.skel }
]

def mapForallDomainAt (expression : Expr) (target : Nat) (f : Expr → Expr) : Expr :=
  match target, expression with
  | 0, .forallE name domain body info => .forallE name (f domain) body info
  | index + 1, .forallE name domain body info =>
    .forallE name domain (mapForallDomainAt body index f) info
  | _, _ => expression

partial def containsConstant (target : Name) (expression : Expr) : Bool :=
  expression.find? (fun subexpression => match subexpression with
    | .const name _ => name == target
    | _ => false) |>.isSome

def perturbRecursor (recursor : ERec) : ERec :=
  let type := Id.run do
    let mut type := recursor.type
    for index in [:recursor.rules.length] do
      if recursor.rules[index]!.nfields > 0 then
        type := mapForallDomainAt type
          (recursor.numParams + recursor.numMotives + index) fun minor =>
            mapForallDomainAt minor 0 (fun domain => .mdata {} domain)
    return type
  { recursor with type }

def perturbRuleSyntax (owner : Name) (declaration : EDecl) : EDecl :=
  match declaration with
  | .induct types constructors recursors =>
    if types.any (·.name == owner) then
      .induct types constructors (recursors.map fun recursor =>
        if recursor.all.contains owner then
          perturbRecursor recursor
        else recursor)
    else declaration
  | _ => declaration

def breakRuleLayout (owner : Name) (declaration : EDecl) : EDecl :=
  match declaration with
  | .induct types constructors recursors =>
    if types.any (·.name == owner) then
      .induct types constructors (recursors.map fun recursor =>
        if recursor.all.contains owner then
          { recursor with rules := recursor.rules.mapIdx fun index rule =>
              if index == 0 then { rule with nfields := rule.nfields + 1 } else rule }
        else recursor)
    else declaration
  | _ => declaration

def runRoute (root : String) (route : Route) : IO Bool := do
  let path := s!"{root}/test/fixtures/inductive-models/{route.fixture}"
  let .ok input := InductiveModels.parse (← IO.FS.readFile path)
    | throw <| IO.userError s!"cannot parse {path}"
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := s!"<composed-recursor-syntax-{route.label}>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let action : MetaM Bool := do
    let (declarations, report) ← runFilterWithExactBlockTransform input false
      route.generation (perturbRuleSyntax route.owner)
    unless report.generated.any (·.1 == route.owner) do
      throwError "{route.label} did not generate a model for {route.owner}: \
        generated={report.generated}, declined={report.declined}"
    let output : Export := { input with decls := declarations }
    let owners : Std.HashSet Name := ({} : Std.HashSet Name).insert route.owner
    let checked := Check.checkStatementsFor output owners
    let exact := report.stmtErrors.isEmpty && checked.violations.isEmpty
    IO.println s!"{route.label}: report={report.stmtErrors.size}, \
      independent-check={checked.violations.size}"
    return exact
  return (← Core.CoreM.toIO (MetaM.run' action) context { env }).1

def runLayoutFailure (root : String) (route : Route) : IO Bool := do
  let path := s!"{root}/test/fixtures/inductive-models/{route.fixture}"
  let .ok input := InductiveModels.parse (← IO.FS.readFile path)
    | throw <| IO.userError s!"cannot parse {path}"
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := s!"<composed-recursor-layout-{route.label}>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let action : MetaM Unit := do
    discard <| runFilterWithExactBlockTransform input false route.generation
      (breakRuleLayout route.owner)
  try
    discard <| Core.CoreM.toIO (MetaM.run' action) context { env }
    IO.println s!"{route.label}: malformed layout was not rejected"
    return false
  catch exception =>
    let rejected := exception.toString.contains "exact rule"
    IO.println s!"{route.label}: malformed layout internal failure={rejected}"
    return rejected

def runPublicRawRecursor (root : String) : IO Bool := do
  let path := s!"{root}/test/fixtures/inductive-models/nested_default_iota.ndjson"
  let .ok input := InductiveModels.parse (← IO.FS.readFile path)
    | throw <| IO.userError s!"cannot parse {path}"
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<public-raw-recursor-syntax>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let action : MetaM Bool := do
    let sourceSeam := input.decls.any fun declaration => match declaration with
      | .induct _ constructors recursors =>
        let constructorWrapped := constructors.any fun constructor =>
          constructor.induct == `NestedDefault && containsConstant `optParam constructor.type
        let recursorReduced := recursors.any fun recursor =>
          recursor.all.contains `NestedDefault && !containsConstant `optParam recursor.type
        constructorWrapped && recursorReduced
      | _ => false
    unless sourceSeam do
      throwError "public raw-recursor fixture does not separate constructor and recursor syntax"
    let (declarations, report) ← runFilter input false
      { noGeneration with nested := true, mutualModels := true }
    unless report.generated.any (·.1 == `NestedDefault) do
      throwError "public raw-recursor fixture did not generate NestedDefault: generated={
        report.generated}, declined={report.declined}"
    let output : Export := { input with decls := declarations }
    let owners : Std.HashSet Name := ({} : Std.HashSet Name).insert `NestedDefault
    let checked := Check.checkStatementsFor output owners
    IO.println s!"public raw recursor: report={report.stmtErrors.size}, \
      independent-check={checked.violations.size}"
    return report.stmtErrors.isEmpty && checked.violations.isEmpty
  return (← Core.CoreM.toIO (MetaM.run' action) context { env }).1

/-- The exported `(levelParams, type)` of one declaration name. -/
def declarationType? (declarations : Array EDecl) (name : Name) : Option (List Name × Expr) :=
  declarations.findSome? fun declaration => match declaration with
    | .ax got params type _ | .quot got params type _ =>
        if got == name then some (params, type) else none
    | .defn got params type .. | .thm got params type .. | .opaq got params type .. =>
        if got == name then some (params, type) else none
    | .induct types constructors recursors =>
        (types.find? (·.name == name)).map (fun type => (type.levelParams, type.type)) <|>
        (constructors.find? (·.name == name)).map (fun ctor => (ctor.levelParams, ctor.type)) <|>
        (recursors.find? (·.name == name)).map (fun recursor =>
          (recursor.levelParams, recursor.type))

/-- **Binder names and binder info are the owner's, not merely equivalent to
them.** Every public slot of `owner` is rebuilt from the export exactly as
[`InductiveModels.Check.checkStatementsFor`] rebuilds it, and compared with
`Expr.equal` rather than `BEq Expr`. The two differ on precisely this: a
recursor whose second parameter reads `{α : Type}` where the export's record
writes `{β : Type}` is `Expr.eqv`-equal to it and `Expr.equal`-different.

`nest_fam_arg`'s `PTP` is the shape that has a name to lose. It carries two
parameters at the same sort, and an export interns expressions up to
`Expr.eqv`, so its *type former* record collapsed
onto an earlier node and reads `∀ (α : Type) (α : Type), Type` while its
*recursor* record kept `α` and `β`. A model that reads its recursor's shape off
the block Lean minted from that type former inherits `α` twice; one spelled
from the export's own recursor record does not.

This is an in-memory claim about the generated declarations. It is not made of
written bytes and cannot be: [`InductiveModels.Interner`] keys on `Expr.eqv`
too, so two written types that differ only in a binder carry whichever binder
the first of them interned. -/
def runBinderFidelity (root : String) : IO Bool := do
  let path := s!"{root}/test/fixtures/inductive-models/nest_fam_arg.ndjson"
  let .ok input := InductiveModels.parse (← IO.FS.readFile path)
    | throw <| IO.userError s!"cannot parse {path}"
  let owner := `PTP
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := "<public-binder-fidelity>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let action : MetaM Bool := do
    let (declarations, report) ← runFilter input false
      { noGeneration with nested := true, mutualModels := true }
    unless report.generated.any (·.1 == owner) do
      throwError "binder-fidelity fixture did not generate {owner}: \
        generated={report.generated}, declined={report.declined}"
    let output : Export := { input with decls := declarations }
    let some ownerDecl := output.decls.findIdx? (·.names.contains owner)
      | throwError "binder-fidelity fixture has no owner record for {owner}"
    let some table := Check.correspondenceAt? output ownerDecl
      | throwError "binder-fidelity fixture has no correspondence for {owner}"
    let mut compared := 0
    let mut inexact : Array Name := #[]
    for pair in table.entries do
      let some (ownerParams, ownerType) := declarationType? output.decls pair.owner
        | throwError "no exported type for {pair.owner}"
      let some (modelParams, modelType) := declarationType? output.decls pair.model
        | throwError "no generated type for {pair.model}"
      compared := compared + 1
      unless modelType.equal (table.expectedType ownerParams modelParams ownerType) do
        inexact := inexact.push pair.model
    for iota in table.iotas do
      let some (ownerParams, ownerType) :=
          Check.iotaProposition? output ownerDecl iota.recursor iota.ruleIndex
        | throwError "no exported ι proposition for {iota.name}"
      let some (modelParams, modelType) := declarationType? output.decls iota.name
        | throwError "no generated type for {iota.name}"
      compared := compared + 1
      unless modelType.equal (table.expectedIotaType ownerParams modelParams ownerType) do
        inexact := inexact.push iota.name
    IO.println s!"public binder fidelity: {compared} slots compared, \
      {inexact.size} inexact{if inexact.isEmpty then "" else s!" ({inexact})"}"
    return compared > 0 && inexact.isEmpty
  return (← Core.CoreM.toIO (MetaM.run' action) context { env }).1

def run (root : String) : IO UInt32 := do
  let mut exactPassed := 0
  let mut layoutPassed := 0
  for route in routes do
    if ← runRoute root route then exactPassed := exactPassed + 1
    if ← runLayoutFailure root route then layoutPassed := layoutPassed + 1
  let publicRawPassed ← runPublicRawRecursor root
  let binderPassed ← runBinderFidelity root
  IO.println s!"composed exact recursors: syntax {exactPassed}/{routes.size}; \
    fail-closed {layoutPassed}/{routes.size}; public-raw={publicRawPassed}; \
    binder-exact={binderPassed}"
  return if exactPassed == routes.size && layoutPassed == routes.size && publicRawPassed &&
    binderPassed then 0 else 1

def main (args : List String) : IO UInt32 :=
  run (args.head?.getD ".")

end ComposedRecursorSyntaxTest
