import Modelgen.Driver

/-!
# Composed exact-recursor syntax diagnostic

The three composition seams consume inductives generated earlier in the same
island: nested to mutual, mutual auxiliary to simple, and arm-C skeleton to
simple splice closure.  This diagnostic perturbs the exact recursor rule in
the serialized owner record after current generation.  The statement checker
then demonstrates that each already-generated iota theorem followed installed
metadata instead of that exact record.
-/

open Lean Meta Modelgen

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
  { label := "arm-C-splice-closure", fixture := "prim_carve.ndjson",
    generation := { noGeneration with simple := true, basic := true },
    owner := `Bif._model._impl.skel }
]

def mapForallDomainAt (expression : Expr) (target : Nat) (f : Expr → Expr) : Expr :=
  match target, expression with
  | 0, .forallE name domain body info => .forallE name (f domain) body info
  | index + 1, .forallE name domain body info =>
    .forallE name domain (mapForallDomainAt body index f) info
  | _, _ => expression

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

def runRoute (root : String) (route : Route) : IO Bool := do
  let path := s!"{root}/test/fixtures/modelgen/{route.fixture}"
  let .ok input := Modelgen.parse (← IO.FS.readFile path) (analyse := false)
    | throw <| IO.userError s!"cannot parse {path}"
  let env ← importModules #[] {}
  let context : Core.Context :=
    { fileName := s!"<composed-recursor-syntax-{route.label}>", fileMap := default,
      maxHeartbeats := 0, maxRecDepth := 8192 }
  let action : MetaM Bool := do
    let (declarations, report) ← runFilter input false route.generation
    unless report.stmtErrors.isEmpty do
      throwError "unperturbed {route.label} already differs: {report.stmtErrors}"
    unless report.generated.any (·.1 == route.owner) do
      throwError "{route.label} did not generate a model for {route.owner}"
    let output : Export := { input with decls := declarations }
    let perturbed : Export :=
      { output with decls := output.decls.map (perturbRuleSyntax route.owner) }
    let owners : Std.HashSet Name := ({} : Std.HashSet Name).insert route.owner
    let checked := Check.checkStatementsFor perturbed owners
    let recursor := Name.str route.owner "rec"
    let witnessed := checked.violations.any fun violation => match violation with
      | .declarationType owner declaration =>
        owner == recursor && (Array.range 64).any fun index =>
          declaration == Naming.iotaName recursor index
      | _ => false
    IO.println s!"{route.label}: {checked.violations.size} perturbed violations; \
      exact iota mismatch={witnessed}"
    return witnessed
  return (← Core.CoreM.toIO (MetaM.run' action) context { env }).1

def run (root : String) : IO UInt32 := do
  let mut passed := 0
  for route in routes do
    if ← runRoute root route then passed := passed + 1
  IO.println s!"composed recursor diagnostic: {passed}/{routes.size} routes witnessed"
  return if passed == routes.size then 0 else 1

def main (args : List String) : IO UInt32 :=
  run (args.head?.getD ".")
