import Modelgen.Check

/-!
# Focused tests for the structural model checker

Run from the repository root with `lake exe checktest [ROOT]`.

The synthetic baseline starts from an actual lean4export fixture.  Exact public
type-former, constructor and recursor axioms and iota propositions, plus a
generic helper, are inserted before its `Tree` inductive record.  Their types are obtained by the
same public correspondence operation the checker exposes, with fresh universe
parameter names to exercise positional alignment.  The adversarial cases are
mutations of that baseline, so each changes only the invariant named by it.
They include missing, duplicate, swapped and definitionally-but-not-syntactically
equal recursor and rule declarations.

Additional cases cover declaration names which contain `_model`, raw private
names, and a multi-member mutual record whose public slots do not depend on the
first member or export position.
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

def exportDeclaration? (x : Export) (name : Name) : Option EDecl :=
  x.decls.find? (·.names.contains name)

def modelParams (params : List Name) : List Name :=
  (List.range params.length).map fun index => Name.str .anonymous s!"model_u_{index}"

partial def forallBody : Expr → Expr
  | .forallE _ _ body _ => forallBody body
  | body => body

def modelAxiom (table : Correspondence) (x : Export) (pair : ConstantPair) : Option EDecl := do
  let (ownerParams, ownerType) ← exportDeclarationType? x pair.owner
  let params := modelParams ownerParams
  return .ax pair.model params (table.expectedType ownerParams params ownerType) false

def modelIotaAxiom (table : Correspondence) (x : Export) (ownerDecl : Nat)
    (iota : Naming.Iota) : Option EDecl := do
  let (ownerParams, ownerType) ←
    iotaProposition? x ownerDecl iota.recursor iota.ruleIndex
  let params := modelParams ownerParams
  return .ax iota.name params (table.expectedIotaType ownerParams params ownerType) false

def modelDeclarations (x : Export) (table : Correspondence) (helper : Name) : Array EDecl :=
  let constants := (table.typeFormers ++ table.constructors ++ table.recursors).filterMap
    (modelAxiom table x)
  let iotas := match table.typeFormers[0]?.bind (ownerIndex? x ·.owner) with
    | some ownerDecl => table.iotas.filterMap (modelIotaAxiom table x ownerDecl)
    | none => #[]
  #[EDecl.ax helper [] (.sort (.succ .zero)) false] ++ constants ++ iotas

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

def isTypeMismatch (owner declaration : Name) : Violation → Bool
  | .declarationType gotOwner gotDeclaration =>
      gotOwner == owner && gotDeclaration == declaration
  | _ => false

def isDuplicate (owner declaration : Name) : Violation → Bool
  | .duplicatePublic gotOwner gotDeclaration count =>
      gotOwner == owner && gotDeclaration == declaration && count > 1
  | _ => false

def isExtraRule (owner declaration : Name) : Violation → Bool
  | .extraRule gotOwner gotDeclaration =>
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
    let modelRoot := Naming.modelName owner
    let carrier := Naming.modelName owner
    let helper := `Tree._model._impl.helper
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
      state ← state.check "only exact public records establish the family" <|
        family.decls.size + 1 == models.size &&
          !family.names.contains helper && family.names.contains carrier
    else
      state ← state.check "family key" false
      state ← state.check "only exact public records establish the family" false
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
    state ← state.check "modeling Eq retains ambient equality" <|
      eqTable.iotas[0]?.bind (fun rule =>
        exportDeclarationType? validEq rule.name |>.map fun (_, type) =>
          match (forallBody type).getAppFn with
          | .const name _ => name == ``Eq
          | _ => false) |>.getD false

    let late := withLateCarrier raw rawOwnerDecl models carrier
    let lateViolations := check late
    state ← state.check "carrier after owner is rejected" <|
      lateViolations.any (isLateCarrier owner carrier)

    let constantBackref := withOwnerType valid validOwnerDecl (.const carrier [])
    state ← state.check "constant backreference is rejected" <|
      (check constantBackref).any (isBackreference owner carrier)

    -- `Expr.getUsedConstants` does not include this name: it lives in the
    -- projection node's `typeName` field, so this pins the checker's explicit
    -- projection traversal.
    let some firstCtor := table.constructors[0]? | do
      IO.eprintln "checktest: Tree has no constructor correspondence"
      return 1
    let projectionBackref :=
      withOwnerType valid validOwnerDecl (.proj firstCtor.model 0 (.bvar 0))
    state ← state.check "projection type-name public backreference is rejected" <|
      (check projectionBackref).any (isBackreference owner firstCtor.model)

    let missingCtor := withoutDeclaration valid firstCtor.model
    state ← state.check "missing constructor slot is rejected" <|
      (check missingCtor).any (isMissing firstCtor.owner firstCtor.model)

    -- Constructor slots still claim the family when the carrier is missing,
    -- so exactness cannot disappear with the declaration it must diagnose.
    let missingCarrier := withoutDeclaration valid carrier
    state ← state.check "missing carrier slot is rejected" <|
      (check missingCarrier).any (isMissing owner carrier)

    let some firstRec := table.recursors[0]? | do
      IO.eprintln "checktest: Tree has no recursor correspondence"
      return 1
    let some secondRec := table.recursors[1]? | do
      IO.eprintln "checktest: Tree has no second recursor correspondence"
      return 1
    state ← state.check "missing recursor is rejected" <|
      (check (withoutDeclaration valid firstRec.model)).any
        (isMissing firstRec.owner firstRec.model)
    let some firstRecDecl := exportDeclaration? valid firstRec.model | do
      IO.eprintln "checktest: modeled recursor declaration missing"
      return 1
    let duplicateRec := insertBeforeOwner valid owner firstRecDecl
    state ← state.check "extra recursor occurrence is rejected" <|
      (check duplicateRec).any (isDuplicate firstRec.owner firstRec.model)
    let some (_, firstRecType) := exportDeclarationType? valid firstRec.model | do
      IO.eprintln "checktest: modeled recursor type missing"
      return 1
    let some (_, secondRecType) := exportDeclarationType? valid secondRec.model | do
      IO.eprintln "checktest: second modeled recursor type missing"
      return 1
    let swappedRecs := withDeclarationType
      (withDeclarationType valid firstRec.model secondRecType) secondRec.model firstRecType
    state ← state.check "swapped recursors are rejected" <|
      (check swappedRecs).any (isTypeMismatch firstRec.owner firstRec.model) &&
        (check swappedRecs).any (isTypeMismatch secondRec.owner secondRec.model)
    let defeqRecType :=
      .letE `recType (.sort (.succ (.succ .zero))) firstRecType (.bvar 0) false
    state ← state.check "definitionally equal recursor syntax is rejected" <|
      (check (withDeclarationType valid firstRec.model defeqRecType)).any
        (isTypeMismatch firstRec.owner firstRec.model)

    let firstRules := table.iotas.filter (·.recursor == firstRec.owner)
    let some firstRule := firstRules[0]? | do
      IO.eprintln "checktest: Tree recursor has no first rule"
      return 1
    let some secondRule := firstRules[1]? | do
      IO.eprintln "checktest: Tree recursor has no second rule"
      return 1
    state ← state.check "missing iota theorem is rejected" <|
      (check (withoutDeclaration valid firstRule.name)).any
        (isMissing firstRule.recursor firstRule.name)
    let some firstRuleDecl := exportDeclaration? valid firstRule.name | do
      IO.eprintln "checktest: first iota declaration missing"
      return 1
    state ← state.check "extra iota occurrence is rejected" <|
      (check (insertBeforeOwner valid owner firstRuleDecl)).any
        (isDuplicate firstRule.recursor firstRule.name)
    let extraRuleName := Naming.iotaName firstRec.owner firstRules.size
    let extraRule := insertBeforeOwner valid owner
      (.ax extraRuleName [] (.sort .zero) false)
    state ← state.check "out-of-range iota theorem is rejected" <|
      (check extraRule).any (isExtraRule firstRec.owner extraRuleName)
    let some (_, firstRuleType) := exportDeclarationType? valid firstRule.name | do
      IO.eprintln "checktest: first iota type missing"
      return 1
    let some (_, secondRuleType) := exportDeclarationType? valid secondRule.name | do
      IO.eprintln "checktest: second iota type missing"
      return 1
    let swappedRules := withDeclarationType
      (withDeclarationType valid firstRule.name secondRuleType) secondRule.name firstRuleType
    state ← state.check "swapped iota statements are rejected" <|
      (check swappedRules).any (isTypeMismatch firstRule.recursor firstRule.name) &&
        (check swappedRules).any (isTypeMismatch secondRule.recursor secondRule.name)
    let defeqRuleType := .letE `ruleType (.sort .zero) firstRuleType (.bvar 0) false
    state ← state.check "definitionally equal iota syntax is rejected" <|
      (check (withDeclarationType valid firstRule.name defeqRuleType)).any
        (isTypeMismatch firstRule.recursor firstRule.name)

    let legacySlot := Name.str modelRoot "ctor_99"
    let unrelatedLegacyName := insertBeforeOwner valid owner
      (.ax legacySlot [] (.sort (.succ .zero)) false)
    state ← state.check "legacy numbered name is not a public slot" <|
      (discover unrelatedLegacyName).all fun family => !family.names.contains legacySlot

    -- `IdxP.at_a` and `IdxP.at_b` have the same binder shape and differ only
    -- in their result indices.  Exact declaration-local names must prevent a
    -- type-shape heuristic from pairing them interchangeably.
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
                (check swapped).any (isTypeMismatch first.owner first.model) &&
                  (check swapped).any (isTypeMismatch second.owner second.model)
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

    let modelNamedOwner := `Tree._model
    let modelNamedRaw :=
      { raw with decls := raw.decls.map (EDecl.renameRoot owner modelNamedOwner) }
    let some modelNamedOwnerDecl := ownerIndex? modelNamedRaw modelNamedOwner | do
      IO.eprintln "checktest: renamed _model owner missing"
      return 1
    let some modelNamedTable := correspondenceAt? modelNamedRaw modelNamedOwnerDecl | do
      IO.eprintln "checktest: renamed _model correspondence missing"
      return 1
    let modelNamedModels := modelDeclarations modelNamedRaw modelNamedTable
      `Tree._model._model._impl.helper
    let modelNamedValid := withValidModel modelNamedRaw modelNamedOwnerDecl modelNamedModels
    state ← state.check "original _model component is preserved exactly" <|
      modelNamedTable.typeFormers[0]?.map (·.model) == some `Tree._model._model &&
        (discover modelNamedValid).any (·.owner == modelNamedOwner) &&
        (check modelNamedValid).isEmpty

    let privateOwner := (`_private.CheckTest).mkNum 0 |>.str "Tree"
    let privateRaw :=
      { raw with decls := raw.decls.map (EDecl.renameRoot owner privateOwner) }
    let some privateOwnerDecl := ownerIndex? privateRaw privateOwner | do
      IO.eprintln "checktest: private owner missing"
      return 1
    let some privateTable := correspondenceAt? privateRaw privateOwnerDecl | do
      IO.eprintln "checktest: private correspondence missing"
      return 1
    let privateModels := modelDeclarations privateRaw privateTable
      (Name.str (Naming.modelName privateOwner) "_impl")
    let privateValid := withValidModel privateRaw privateOwnerDecl privateModels
    state ← state.check "private originals retain raw correspondence names" <|
      privateTable.typeFormers[0]?.map (·.model) == some (Naming.modelName privateOwner) &&
        (discover privateValid).any (·.owner == privateOwner) &&
        (check privateValid).isEmpty

    let mutualPath := s!"{root}/tests/mutual_shapes.ndjson"
    let mutualText ← IO.FS.readFile mutualPath
    match Modelgen.parse mutualText (analyse := false) with
    | .error error =>
        IO.eprintln s!"checktest: could not parse {mutualPath}: {error}"
        state ← state.check "valid exact mutual family" false
    | .ok mutualExport =>
      let some mutualOwnerDecl := ownerIndex? mutualExport `A | do
        IO.eprintln "checktest: mutual owner missing"
        return 1
      let some mutualTable := correspondenceAt? mutualExport mutualOwnerDecl | do
        IO.eprintln "checktest: mutual correspondence missing"
        return 1
      let mutualModels := modelDeclarations mutualExport mutualTable `A._model._impl.helper
      let mutualValid := withValidModel mutualExport mutualOwnerDecl mutualModels
      state ← state.check "mutual correspondence is declaration-local" <|
        mutualTable.typeFormers.any (fun pair =>
          pair.owner == `B && pair.model == Naming.modelName `B) &&
        mutualTable.constructors.any (fun pair =>
          pair.owner == `B.bC && pair.model == Naming.modelName `B.bC) &&
        mutualTable.recursors.any (fun pair =>
          pair.owner == `C.rec && pair.model == Naming.modelName `C.rec) &&
        mutualTable.iotas.any (fun rule =>
          rule.recursor == `C.rec && rule.ruleIndex == 2 &&
            rule.name == Naming.iotaName `C.rec 2)
      state ← state.check "valid exact mutual family" <|
        (discover mutualValid).any (fun family =>
          family.owner == `A && family.correspondence == mutualTable) &&
        (check mutualValid).isEmpty
      let some bCtor := mutualTable.constructors.find? (·.owner == `B.bC) | do
        IO.eprintln "checktest: B.bC correspondence missing"
        return 1
      state ← state.check "mutual diagnostic belongs to exact constructor" <|
        (check (withoutDeclaration mutualValid bCtor.model)).any
          (isMissing bCtor.owner bCtor.model)

    if state.failed == 0 then
      IO.println s!"checktest: {state.passed} tests passed"
      return 0
    else
      IO.eprintln s!"checktest: {state.failed} failed, {state.passed} passed"
      return 1

def main (args : List String) : IO UInt32 :=
  run (args.head?.getD ".")
