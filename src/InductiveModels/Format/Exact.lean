import InductiveModels.Format.Export
/-!
# Exact export-syntax normalization

The deliberately bounded normalizer (β, ζ, metadata erasure and transparent
`defn` unfolding, and nothing else), the export-only type inference built on
it, and the kernel's `infer_proj` field walk expressed over export records.
-/
open Lean

namespace InductiveModels

/-! ## Intrinsic projection eligibility

An `Expr.proj T j self` is not valid for every field of every structure-like
type.  In particular, when `T` is `Prop` the selected field must be a
proposition; and each earlier non-proof field on which the remaining telescope
depends also makes the projection invalid.  This is the literal field walk in
the kernel's `infer_proj`, expressed over export records so generation,
checking, and serialization enumerate the same slots without consulting a
named projection wrapper. -/

/-- One transparent definition available to the format-only normalizer. -/
structure ExactNormalizationDef where
  levelParams : List Name
  value : Expr

/-- The deliberately bounded environment used for exact export-syntax
normalization.  It contains only values of transparent `defn` records from the
export: opaque declarations, theorems, and any ambient kernel environment are
invisible. -/
structure ExactNormalizationEnv where
  /-- The immutable export-derived base table. Syntax-index replay/island
  updates stay in the private sparse overlay so this public `Std.HashMap`
  remains source-compatible and is never copied by a disposable overlay. -/
  definitions : Std.HashMap Name ExactNormalizationDef
  /-- Sparse replacements used by disposable syntax overlays. `none` is a
  tombstone for a definition removed from the immutable public base table. -/
  private overrides : Lean.PersistentHashMap Name (Option ExactNormalizationDef) := {}

private def ExactNormalizationEnv.definition? (env : ExactNormalizationEnv)
    (name : Name) : Option ExactNormalizationDef :=
  match env.overrides.find? name with
  | some replacement => replacement
  | none => env.definitions[name]?

/-- Add or replace one transparent definition without copying the public base
table.  This is the sparse update operation used by syntax-index overlays. -/
def ExactNormalizationEnv.insertDefinition (env : ExactNormalizationEnv)
    (name : Name) (definition : ExactNormalizationDef) : ExactNormalizationEnv :=
  { env with overrides := env.overrides.insert name (some definition) }

/-- Hide one transparent definition without copying the public base table. -/
def ExactNormalizationEnv.eraseDefinition (env : ExactNormalizationEnv)
    (name : Name) : ExactNormalizationEnv :=
  { env with overrides := env.overrides.insert name none }

/-- Build the exact normalizer's environment from export records alone.
Keeping the first occurrence agrees with the other format prepasses and makes
malformed duplicate-name input deterministic. -/
def Export.exactNormalizationEnv (x : Export) : ExactNormalizationEnv := Id.run do
  let mut definitions : Std.HashMap Name ExactNormalizationDef := {}
  for declaration in x.decls do
    if let .defn name levelParams _ value .. := declaration then
      unless definitions.contains name do
        definitions := definitions.insert name { levelParams, value }
  return { definitions }

private partial def ExactNormalizationEnv.whnfCore (env : ExactNormalizationEnv)
    (expression : Expr) (reduceLets unfoldDefinitions : Bool)
    (seen : Std.HashSet Name) : Expr :=
  match expression with
  | .mdata _ body => env.whnfCore body reduceLets unfoldDefinitions seen
  | .letE _ _ value body _ => if reduceLets then
      env.whnfCore (body.instantiate1 value) true unfoldDefinitions seen
    else expression
  | .app .. =>
    let reduced := expression.headBeta
    if reduced != expression then env.whnfCore reduced reduceLets unfoldDefinitions seen
    else if !unfoldDefinitions then expression
    else match expression.getAppFn with
      | .const name levels =>
        if seen.contains name then expression
        else match env.definition? name with
          | some definition =>
            if definition.levelParams.length == levels.length then
              let value := definition.value.instantiateLevelParams definition.levelParams levels
              env.whnfCore (mkAppN value expression.getAppArgs) reduceLets true
                (seen.insert name)
            else expression
          | none => expression
      | _ => expression
  | .const name levels =>
    if !unfoldDefinitions || seen.contains name then expression
    else match env.definition? name with
      | some definition =>
        if definition.levelParams.length == levels.length then
          env.whnfCore (definition.value.instantiateLevelParams definition.levelParams levels)
            reduceLets true (seen.insert name)
        else expression
      | none => expression
  | _ => expression

/-- Weak-head normalize using only β, ζ, metadata erasure, and transparent
named definitions present in this export.  `seen` is the recursion guard for
self-recursive definitions and cycles of transparent aliases.  Public
declaration expressions are never rewritten in place; this operation is only
an exact observation used while reconstructing kernel-visible interfaces. -/
def ExactNormalizationEnv.whnf (env : ExactNormalizationEnv) (expression : Expr) : Expr :=
  env.whnfCore expression true true {}

/-- The β-only face of the same bounded normalizer.  Projection theorem
telescopes use it where kernel insertion has reduced a head application in a
local binder type while retaining both a written `let` and named public model
constants literally. -/
def ExactNormalizationEnv.beta (env : ExactNormalizationEnv) (expression : Expr) : Expr :=
  env.whnfCore expression false false {}

/-- Whether an exported former ends in `Prop` after exact syntax-only
normalization.  Π binders remain part of the former; only their final codomain
decides propositionhood. -/
partial def ExactNormalizationEnv.isPropositionFormer
    (env : ExactNormalizationEnv) (expression : Expr) : Bool :=
  match env.whnf expression with
  | .forallE _ _ body _ => env.isPropositionFormer body
  | .sort .zero => true
  | _ => false

private structure ExactDeclType where
  levelParams : List Name
  type : Expr

private abbrev ExactDeclarationTypes := Std.HashMap Name ExactDeclType
private abbrev ExactLocals := Array (FVarId × Expr)

private def exactDeclarationTypes (x : Export) : ExactDeclarationTypes := Id.run do
  let mut result : ExactDeclarationTypes := {}
  for declaration in x.decls do
    match declaration with
    | .ax name levelParams type _ | .quot name levelParams type _ |
      .defn name levelParams type .. | .thm name levelParams type .. |
      .opaq name levelParams type .. =>
        unless result.contains name do result := result.insert name { levelParams, type }
    | .induct types constructors recursors =>
      for type in types do
        unless result.contains type.name do
          result := result.insert type.name { levelParams := type.levelParams, type := type.type }
      for constructor in constructors do
        unless result.contains constructor.name do
          result := result.insert constructor.name
            { levelParams := constructor.levelParams, type := constructor.type }
      for recursor in recursors do
        unless result.contains recursor.name do
          result := result.insert recursor.name
            { levelParams := recursor.levelParams, type := recursor.type }
  return result

private def ExactLocals.typeOf? (locals : ExactLocals) (id : FVarId) : Option Expr :=
  (locals.find? (·.1 == id)).map (·.2)

private def structureOwner? (x : Export) (owner : Name) : Option (EIndType × List ECtor) :=
  x.decls.findSome? fun declaration => match declaration with
    | .induct types constructors _ =>
      (types.find? (·.name == owner)).map fun type => (type, constructors)
    | _ => none

mutual

private partial def inferExactType? (x : Export) (normalizer : ExactNormalizationEnv)
    (declarations : ExactDeclarationTypes)
    (locals : ExactLocals) : Expr → Option Expr
  | .sort level => some (.sort (.succ level))
  | .fvar id => locals.typeOf? id
  | .const name levels => do
      let declaration ← declarations[name]?
      unless declaration.levelParams.length == levels.length do none
      return declaration.type.instantiateLevelParams declaration.levelParams levels
  | .app function argument => do
      let functionType := normalizer.whnf
        (← inferExactType? x normalizer declarations locals function)
      let .forallE _ _ body _ := functionType | none
      return body.instantiate1 argument
  | .lam name domain body info => do
      let value := mkFVar (FVarId.mk ((`_format.exactLam).mkNum locals.size))
      let bodyType ← inferExactType? x normalizer declarations
        (locals.push (value.fvarId!, domain)) (body.instantiate1 value)
      return .forallE name domain (bodyType.abstract #[value]) info
  | .forallE _ domain body _ => do
      let domainLevel ← inferExactSortLevel? x normalizer declarations locals domain
      let value := mkFVar (FVarId.mk ((`_format.exactPi).mkNum locals.size))
      let bodyLevel ← inferExactSortLevel? x normalizer declarations
        (locals.push (value.fvarId!, domain)) (body.instantiate1 value)
      return .sort (Level.imax domainLevel bodyLevel).normalize
  | .letE _ _ value body _ =>
      inferExactType? x normalizer declarations locals (body.instantiate1 value)
  | .mdata _ body => inferExactType? x normalizer declarations locals body
  | .proj owner fieldIndex struct => do
      let structType := normalizer.whnf
        (← inferExactType? x normalizer declarations locals struct)
      let .const structOwner levels := structType.getAppFn | none
      unless structOwner == owner do none
      let (type, constructors) ← structureOwner? x owner
      let constructorName ← type.ctors.head?
      let constructor ← constructors.find? fun constructor =>
        constructor.name == constructorName && constructor.induct == owner
      unless type.ctors == [constructorName] do none
      let ownerArguments := structType.getAppArgs
      unless ownerArguments.size == type.numParams + type.numIndices do none
      let params := ownerArguments.extract 0 type.numParams
      let mut current := constructor.type.instantiateLevelParams constructor.levelParams levels
      for param in params do
        let .forallE _ _ body _ := normalizer.whnf current | none
        current := body.instantiate1 param
      let ownerIsProp := normalizer.isPropositionFormer type.type
      for earlier in [0:fieldIndex + 1] do
        let .forallE _ fieldType body _ := normalizer.whnf current | none
        let fieldIsProp :=
          inferExactSortLevel? x normalizer declarations locals fieldType == some .zero
        if earlier == fieldIndex then
          if ownerIsProp && !fieldIsProp then none else return fieldType
        if ownerIsProp && body.hasLooseBVars && !fieldIsProp then none
        current := body.instantiate1 (.proj owner earlier struct)
      none
  | .lit (.natVal _) => some (.const ``Nat [])
  | .lit (.strVal _) => some (.const ``String [])
  | .bvar _ | .mvar _ => none

private partial def inferExactSortLevel? (x : Export) (normalizer : ExactNormalizationEnv)
    (declarations : ExactDeclarationTypes)
    (locals : ExactLocals) (expression : Expr) : Option Level := do
  let .sort level := normalizer.whnf
    (← inferExactType? x normalizer declarations locals expression) | none
  return level

end

private partial def projectionFieldEligible? (x : Export)
    (normalizer : ExactNormalizationEnv) (declarations : ExactDeclarationTypes)
    (ownerIsProp : Bool) (fieldIndex : Nat)
    (current : Expr) (locals : ExactLocals) : Option Bool := do
  let .forallE _ fieldType body _ := normalizer.whnf current | none
  let fieldIsProp :=
    inferExactSortLevel? x normalizer declarations locals fieldType == some .zero
  if fieldIndex == 0 then return !ownerIsProp || fieldIsProp
  if ownerIsProp && body.hasLooseBVars && !fieldIsProp then return false
  let value := mkFVar (FVarId.mk ((`_format.projectionField).mkNum locals.size))
  projectionFieldEligible? x normalizer declarations ownerIsProp (fieldIndex - 1)
    (body.instantiate1 value) (locals.push (value.fvarId!, fieldType))

/-- Zero-based constructor fields for which the kernel projection expression
is well typed.  The kernel requires one constructor, but does not require the
owner to be non-recursive or unindexed. -/
def Export.intrinsicProjectionFieldsFor (x : Export) (type : EIndType)
    (constructors : List ECtor) : Array Nat := Id.run do
  let [constructorName] := type.ctors | return #[]
  let some constructor := constructors.find? fun constructor =>
      constructor.name == constructorName && constructor.induct == type.name
    | return #[]
  let declarations := exactDeclarationTypes x
  let normalizer := x.exactNormalizationEnv
  let mut ownerType := type.type
  while ownerType.isForall do ownerType := ownerType.bindingBody!
  let ownerIsProp := normalizer.isPropositionFormer ownerType
  let mut current := constructor.type
  let mut locals : ExactLocals := #[]
  for parameterIndex in [:type.numParams] do
    let .forallE _ parameterType body _ := normalizer.whnf current | return #[]
    let value := mkFVar (FVarId.mk ((`_format.projectionParam).mkNum parameterIndex))
    locals := locals.push (value.fvarId!, parameterType)
    current := body.instantiate1 value
  let mut result := #[]
  for fieldIndex in [:constructor.numFields] do
    if projectionFieldEligible? x normalizer declarations ownerIsProp fieldIndex current locals ==
        some true then
      result := result.push fieldIndex
  return result

end InductiveModels
