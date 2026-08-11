import Modelgen.Check

/-!
# Focused tests for the structural model checker

Run from the repository root with `lake exe checktest [ROOT]`.

The synthetic baseline starts from an actual lean4export fixture.  Exact public
carrier and constructor axioms, plus a deliberately generic helper, are
inserted before its `Tree` inductive record.  Their types are obtained by the
same public correspondence operation the checker exposes, with fresh universe
parameter names to exercise positional alignment.  The adversarial cases are
mutations of that baseline, so each changes only the invariant named by it.

The final checks read a real modelgen-filtered fixture and validate its public
`Tree` family without manufacturing any declarations.
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

def declarationType? (declaration : EDecl) (name : Name) : Option (List Name × Expr) :=
  match declaration with
  | .ax got params type _ | .quot got params type _ =>
      if got == name then some (params, type) else none
  | .defn got params type .. | .thm got params type .. | .opaq got params type .. =>
      if got == name then some (params, type) else none
  | .induct types ctors recursors =>
      (types.find? (·.name == name)).map (fun type => (type.levelParams, type.type)) <|>
      (ctors.find? (·.name == name)).map (fun ctor => (ctor.levelParams, ctor.type)) <|>
      (recursors.find? (·.name == name)).map (fun recursor =>
        (recursor.levelParams, recursor.type))

def exportDeclarationType? (x : Export) (name : Name) : Option (List Name × Expr) :=
  x.decls.findSome? (declarationType? · name)

def modelParams (params : List Name) : List Name :=
  (List.range params.length).map fun index => Name.str .anonymous s!"model_u_{index}"

def modelAxiom (table : Correspondence) (x : Export) (pair : ConstantPair) : Option EDecl := do
  let (ownerParams, ownerType) ← exportDeclarationType? x pair.owner
  let params := modelParams ownerParams
  return .ax pair.model params (table.expectedType ownerParams params ownerType) false

def modelDeclarations (x : Export) (table : Correspondence) (helper : Name) : Array EDecl :=
  #[EDecl.ax helper [] (.sort (.succ .zero)) false] ++
    (table.typeFormers ++ table.constructors).filterMap (modelAxiom table x)

def withValidModel (x : Export) (ownerDecl : Nat) (models : Array EDecl) : Export :=
  { x with decls := x.decls.extract 0 ownerDecl ++ models ++
      x.decls.extract ownerDecl x.decls.size }

def withLateCarrier (x : Export) (ownerDecl : Nat) (models : Array EDecl)
    (carrier : Name) : Export :=
  match models.find? (·.names.contains carrier) with
  | none => x
  | some carrierDecl =>
    let early := models.filter (!·.names.contains carrier)
    { x with decls := x.decls.extract 0 ownerDecl ++ early ++
        #[x.decls[ownerDecl]!, carrierDecl] ++
        x.decls.extract (ownerDecl + 1) x.decls.size }

def withOwnerType (x : Export) (ownerDecl : Nat) (type : Expr) : Export :=
  let declaration := match x.decls[ownerDecl]! with
    | .induct (first :: rest) ctors recursors =>
        .induct ({ first with type } :: rest) ctors recursors
    | declaration => declaration
  { x with decls := x.decls.set! ownerDecl declaration }

def withDeclarationType (x : Export) (name : Name) (type : Expr) : Export :=
  { x with decls := x.decls.map fun declaration =>
      match declaration with
      | .ax got params _ isUnsafe =>
          if got == name then .ax got params type isUnsafe else declaration
      | .defn got params _ value hints safety all =>
          if got == name then .defn got params type value hints safety all else declaration
      | .thm got params _ value all =>
          if got == name then .thm got params type value all else declaration
      | .opaq got params _ value isUnsafe all =>
          if got == name then .opaq got params type value isUnsafe all else declaration
      | _ => declaration }

def withoutDeclaration (x : Export) (name : Name) : Export :=
  { x with decls := x.decls.filter (!·.names.contains name) }

def insertBeforeOwner (x : Export) (owner : Name) (declaration : EDecl) : Export :=
  match ownerIndex? x owner with
  | none => x
  | some index =>
      { x with decls := x.decls.extract 0 index ++ #[declaration] ++
          x.decls.extract index x.decls.size }

def isLateCarrier (owner carrier : Name) : Violation → Bool
  | .modelNotBefore gotOwner declaration _ _ => gotOwner == owner && declaration == carrier
  | _ => false

def isBackreference (owner target : Name) : Violation → Bool
  | .ownerBackreference gotOwner gotTarget => gotOwner == owner && gotTarget == target
  | _ => false

def isMissing (owner declaration : Name) : Violation → Bool
  | .missingPublic gotOwner gotDeclaration =>
      gotOwner == owner && gotDeclaration == declaration
  | _ => false

def isExtra (owner declaration : Name) : Violation → Bool
  | .extraConstructor gotOwner gotDeclaration =>
      gotOwner == owner && gotDeclaration == declaration
  | _ => false

def isTypeMismatch (owner declaration : Name) : Violation → Bool
  | .declarationType gotOwner gotDeclaration =>
      gotOwner == owner && gotDeclaration == declaration
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
    let some table := correspondenceAt? raw rawOwnerDecl | do
      IO.eprintln s!"checktest: no correspondence table for {owner}"
      return 1
    let models := modelDeclarations raw table helper

    let valid := withValidModel raw rawOwnerDecl models
    let validOwnerDecl := rawOwnerDecl + models.size
    let families := discover valid
    let mut state : TestState := {}
    state ← state.check "one public family discovered" (families.size == 1)
    if let some family := families[0]? then
      state ← state.check "family key" <|
        family.owner == owner && family.modelRoot == modelRoot &&
          family.carrier == carrier && family.ownerDecl == validOwnerDecl &&
          family.correspondence == table
      state ← state.check "helper belongs to established family" <|
        family.decls.size == models.size &&
          family.names.contains helper && family.names.contains carrier
    else
      state ← state.check "family key" false
      state ← state.check "helper belongs to established family" false
    state ← state.check "valid ordering and independence" (check valid).isEmpty

    let eqOwner := `Eq
    let some rawEqDecl := ownerIndex? raw eqOwner | do
      IO.eprintln s!"checktest: {path} does not declare {eqOwner}"
      return 1
    let some eqTable := correspondenceAt? raw rawEqDecl | do
      IO.eprintln s!"checktest: no correspondence table for {eqOwner}"
      return 1
    let eqModels := modelDeclarations raw eqTable `Eq._model.helper
    let validEq := withValidModel raw rawEqDecl eqModels
    state ← state.check "universe parameters align positionally" <|
      (discover validEq).any (·.owner == eqOwner) &&
        (check validEq).all (·.familyOwner != eqOwner)

    let late := withLateCarrier raw rawOwnerDecl models carrier
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

    let some firstCtor := table.constructors[0]? | do
      IO.eprintln "checktest: Tree has no constructor correspondence"
      return 1
    let missingCtor := withoutDeclaration valid firstCtor.model
    state ← state.check "missing constructor slot is rejected" <|
      (check missingCtor).any (isMissing owner firstCtor.model)

    -- Constructor slots still claim the family when the carrier is missing,
    -- so exactness cannot disappear with the declaration it must diagnose.
    let missingCarrier := withoutDeclaration valid carrier
    state ← state.check "missing carrier slot is rejected" <|
      (check missingCarrier).any (isMissing owner carrier)

    let extraCtorName := Name.str modelRoot s!"ctor_{table.constructors.size}"
    let extraCtor := insertBeforeOwner valid owner
      (.ax extraCtorName [] (.sort (.succ .zero)) false)
    state ← state.check "extra constructor slot is rejected" <|
      (check extraCtor).any (isExtra owner extraCtorName)

    -- `IdxP.at_a` and `IdxP.at_b` have the same binder shape and differ only
    -- in their result indices.  The numeric model slots must follow export
    -- order rather than being paired by a type-shape heuristic.
    let shapesPath := s!"{root}/tests/prim_shapes.ndjson"
    let shapesText ← IO.FS.readFile shapesPath
    match Modelgen.parse shapesText (analyse := false) with
    | .error error =>
        IO.eprintln s!"checktest: could not parse {shapesPath}: {error}"
        state ← state.check "swapped equal-looking constructors" false
    | .ok shapes =>
      let idxOwner := `IdxP
      match ownerIndex? shapes idxOwner with
      | none => state ← state.check "swapped equal-looking constructors" false
      | some idxOwnerDecl =>
        match correspondenceAt? shapes idxOwnerDecl with
        | none => state ← state.check "swapped equal-looking constructors" false
        | some idxTable =>
          let idxModels := modelDeclarations shapes idxTable `IdxP._model.helper
          let idxValid := withValidModel shapes idxOwnerDecl idxModels
          match idxTable.constructors[0]?, idxTable.constructors[1]? with
          | some first, some second =>
            match exportDeclarationType? idxValid first.model,
                exportDeclarationType? idxValid second.model with
            | some (_, firstType), some (_, secondType) =>
              let swapped := withDeclarationType
                (withDeclarationType idxValid first.model secondType) second.model firstType
              state ← state.check "swapped equal-looking constructors" <|
                (check swapped).any (isTypeMismatch idxOwner first.model) &&
                  (check swapped).any (isTypeMismatch idxOwner second.model)
            | _, _ => state ← state.check "swapped equal-looking constructors" false
          | _, _ => state ← state.check "swapped equal-looking constructors" false

    let some (_, carrierType) := exportDeclarationType? valid carrier | do
      IO.eprintln s!"checktest: no declaration for {carrier}"
      return 1
    -- `let x : Type 1 := carrierType; x` is definitionally equal to the
    -- universe-free fixture's carrier type (`Type`) but not syntactically the
    -- same exported expression.
    let defeqCarrierType :=
      .letE `x (.sort (.succ (.succ .zero))) carrierType (.bvar 0) false
    let defeqCarrier := withDeclarationType valid carrier defeqCarrierType
    state ← state.check "definitionally equal carrier syntax is rejected" <|
      (check defeqCarrier).any (isTypeMismatch owner carrier)

    let generatedPath := s!"{root}/tests/filtered/nested_iota_arm.ndjson"
    let generatedText ← IO.FS.readFile generatedPath
    match Modelgen.parse generatedText (analyse := false) with
    | .error error =>
        IO.eprintln s!"checktest: could not parse {generatedPath}: {error}"
        state ← state.check "real generated family" false
    | .ok generated =>
        let treeFamilies := (discover generated).filter (·.owner == owner)
        let treeViolations := (check generated).filter (·.familyOwner == owner)
        state ← state.check "real generated family discovered" (treeFamilies.size == 1)
        state ← state.check "real generated carrier and constructors match" treeViolations.isEmpty

    if state.failed == 0 then
      IO.println s!"checktest: {state.passed} tests passed"
      return 0
    else
      IO.eprintln s!"checktest: {state.failed} failed, {state.passed} passed"
      return 1

def main (args : List String) : IO UInt32 :=
  run (args.head?.getD ".")
