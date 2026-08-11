import Modelgen.Check

/-!
# Focused tests for the structural model checker

Run from the repository root with `lake exe checktest [ROOT]`.

The baseline is an actual lean4export fixture.  Two independent declarations
are inserted immediately before its `Tree` inductive record to form the public
family `Tree._model`: its conventional carrier and a deliberately generic
helper.  The adversarial cases are mutations of that baseline, not parallel
handwritten examples, so each test changes only the invariant named by it.
-/

open Lean Modelgen Modelgen.Check

structure TestState where
  passed : Nat := 0
  failed : Nat := 0

def TestState.check (state : TestState) (label : String) (condition : Bool) : IO TestState := do
  if condition then
    return { state with passed := state.passed + 1 }
  else
    IO.eprintln s!"FAIL: {label}"
    return { state with failed := state.failed + 1 }

def ownerIndex? (x : Export) (owner : Name) : Option Nat :=
  x.decls.findIdx? fun declaration =>
    match declaration with
    | .induct types _ _ => types.any (·.name == owner)
    | _ => false

def modelAxiom (name : Name) : EDecl :=
  .ax name [] (.sort (.succ .zero)) false

def withValidModel (x : Export) (ownerDecl : Nat) (helper carrier : Name) : Export :=
  { x with decls :=
      x.decls.extract 0 ownerDecl ++ #[modelAxiom helper, modelAxiom carrier] ++
        x.decls.extract ownerDecl x.decls.size }

def withLateCarrier (x : Export) (ownerDecl : Nat) (helper carrier : Name) : Export :=
  { x with decls :=
      x.decls.extract 0 ownerDecl ++
        #[modelAxiom helper, x.decls[ownerDecl]!, modelAxiom carrier] ++
        x.decls.extract (ownerDecl + 1) x.decls.size }

def withOwnerType (x : Export) (ownerDecl : Nat) (type : Expr) : Export :=
  let declaration := match x.decls[ownerDecl]! with
    | .induct (first :: rest) ctors recursors =>
        .induct ({ first with type } :: rest) ctors recursors
    | declaration => declaration
  { x with decls := x.decls.set! ownerDecl declaration }

def isLateCarrier (owner carrier : Name) : Violation → Bool
  | .modelNotBefore gotOwner declaration _ _ => gotOwner == owner && declaration == carrier
  | _ => false

def isBackreference (owner target : Name) : Violation → Bool
  | .ownerBackreference gotOwner gotTarget => gotOwner == owner && gotTarget == target
  | _ => false

def run (root : String) : IO UInt32 := do
  let path := s!"{root}/tests/nested_iota_arm.ndjson"
  let text ← IO.FS.readFile path
  match Modelgen.parse text (analyse := false) with
  | .error error =>
      IO.eprintln s!"checktest: could not parse {path}: {error}"
      return 1
  | .ok raw =>
    let owner := `Tree
    let modelRoot := `Tree._model
    let carrier := `Tree._model.self
    let helper := `Tree._model.helper
    let some rawOwnerDecl := ownerIndex? raw owner | do
      IO.eprintln s!"checktest: {path} does not declare {owner}"
      return 1

    let valid := withValidModel raw rawOwnerDecl helper carrier
    let validOwnerDecl := rawOwnerDecl + 2
    let families := discover valid
    let mut state : TestState := {}
    state ← state.check "one public family discovered" (families.size == 1)
    if let some family := families[0]? then
      state ← state.check "family key" <|
        family.owner == owner && family.modelRoot == modelRoot &&
          family.carrier == carrier && family.ownerDecl == validOwnerDecl
      state ← state.check "helper belongs to established family" <|
        family.decls == #[rawOwnerDecl, rawOwnerDecl + 1] &&
          family.names.contains helper && family.names.contains carrier
    else
      state ← state.check "family key" false
      state ← state.check "helper belongs to established family" false
    state ← state.check "valid ordering and independence" (check valid).isEmpty

    let late := withLateCarrier raw rawOwnerDecl helper carrier
    let lateViolations := check late
    state ← state.check "carrier after owner is rejected" <|
      lateViolations.any (isLateCarrier owner carrier)

    let constantBackref := withOwnerType valid validOwnerDecl (.const carrier [])
    state ← state.check "constant backreference is rejected" <|
      (check constantBackref).any (isBackreference owner carrier)

    -- `Expr.getUsedConstants` does not include this name: it lives in the
    -- projection node's `typeName` field, so this pins the checker's explicit
    -- projection traversal.  Referring to the helper also pins that helpers
    -- belong to the established family's forbidden target set.
    let projectionBackref :=
      withOwnerType valid validOwnerDecl (.proj helper 0 (.bvar 0))
    state ← state.check "projection type-name helper backreference is rejected" <|
      (check projectionBackref).any (isBackreference owner helper)

    if state.failed == 0 then
      IO.println s!"checktest: {state.passed} tests passed"
      return 0
    else
      IO.eprintln s!"checktest: {state.failed} failed, {state.passed} passed"
      return 1

def main (args : List String) : IO UInt32 :=
  run (args.head?.getD ".")
