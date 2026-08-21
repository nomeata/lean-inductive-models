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
  /-- Definition source consulted only where `overrides` and `definitions` both
  miss.  It exists so an *installed environment* can drive the same bounded
  unfolding through this one [`ExactNormalizationEnv.whnfCore`] instead of a
  second copy of it, which could drift from it.  Every export-derived
  normalizer leaves this `none`, so their answers are unchanged node for node;
  [`ExactNormalizationEnv.ofEnvironment`] is the only constructor that sets it. -/
  private fallback? : Option (Name → Option ExactNormalizationDef) := none

private def ExactNormalizationEnv.definition? (env : ExactNormalizationEnv)
    (name : Name) : Option ExactNormalizationDef :=
  match env.overrides.find? name with
  | some replacement => replacement
  | none => match env.definitions[name]? with
    | some definition => some definition
    | none => env.fallback?.bind (· name)

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

/-- One transparent definition as an *installed environment* spells it.

This is the environment-backed face of the export-derived table above, and the
two are meant to answer identically.  They can, because the driver replays
every source record through [`InductiveModels.toDeclaration`], which copies a
`.defn` record's `levelParams` and `value` into `Declaration.defnDecl`
verbatim: the installed constant shares the very expression the export table
would have handed back.

Only `defnInfo` qualifies, and that is the whole eligibility rule rather than a
restriction invented here.  `toDeclaration` maps `.defn` records and nothing
else onto `defnDecl`, so a theorem, opaque, axiom, quotient or inductive
constant is invisible to the bounded normalizer from either side, exactly as
this module's opening comment says.

**Shape and eligibility only.**  This never becomes the authority for a literal
statement comparison.  The environment does not carry exported recursors at all
— `toDeclaration` drops them and lets the kernel mint its own — so every
literal comparison stays on the `EDecl` export syntax already in hand, which is
the same split [`InductiveModels.validateExactRecursorLayout`] documents for
recursor slots. -/
def environmentDefinition? (env : Environment) (name : Name) :
    Option ExactNormalizationDef :=
  match env.find? name with
  | some (.defnInfo value) =>
    some { levelParams := value.levelParams, value := value.value }
  | _ => none

/-- The bounded normalizer served entirely from an installed environment.

It reuses [`ExactNormalizationEnv.whnf`] and every query built on it, so this is
the same β/ζ/δ-transparent reduction rather than a second implementation.  The
base table is deliberately empty: nothing is retained per definition here,
because the environment already holds each body. -/
def ExactNormalizationEnv.ofEnvironment (env : Environment) : ExactNormalizationEnv :=
  { definitions := {}, fallback? := some (environmentDefinition? env) }

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

/-! ### Recursion, decided by what survives reduction

An export carries `isRec`, and Lean computes it **syntactically**: a block is
flagged recursive when a constructor field type *mentions* a member of the
block, whether or not the mention means anything.  A field written
`cst T N` — `cst` the constant function on sorts — mentions `T` in the
argument it throws away, so the flag reads `true` of an owner whose recursor
binds no induction hypothesis at all.

**This tool follows the recursor.**  A field is recursive exactly when an
owner occurrence *survives full reduction*, which is the notion
[`InductiveModels.deltaFieldDomain`] already decides the constructions by; the
two questions below are that same notion asked of the export records, so the
structure route and the constructions answer one question rather than two.

The reduction is [`ExactNormalizationEnv.whnf`], which is where an export's
own transparent definitions live, and the walk is cheap for the same reason
the construction's is: **no constant an export declares before `T` can mention
`T`**, so reduction only ever removes mentions and a subterm the syntactic
test clears is never reduced at all.  A declaration with no dead mention
therefore pays one `Expr.find?` per field. -/

/-- Whether an occurrence of one of `owners` **survives full reduction** in
`expression`.

Head-normalise; if the mention is gone the answer is `no`, and otherwise ask
the same of the parts that still mention an owner.  A subterm the syntactic
test clears is returned `no` without being reduced.  The walk needs no local
context: it looks only at constant heads, so a loose bound variable is a leaf
like any other. -/
partial def ExactNormalizationEnv.occurrenceSurvives (env : ExactNormalizationEnv)
    (owners : Array Name) (expression : Expr) : Bool :=
  if !mentionsAny owners expression then false else
  let expression := env.whnf expression
  if !mentionsAny owners expression then false else
  match expression with
  | .app .. =>
    env.occurrenceSurvives owners expression.getAppFn ||
      expression.getAppArgs.any (env.occurrenceSurvives owners)
  | .forallE _ domain body _ | .lam _ domain body _ =>
    env.occurrenceSurvives owners domain || env.occurrenceSurvives owners body
  | .letE _ t v b _ =>
    env.occurrenceSurvives owners t || env.occurrenceSurvives owners v ||
      env.occurrenceSurvives owners b
  | .mdata _ body | .proj _ _ body => env.occurrenceSurvives owners body
  -- A leaf that still mentions an owner is the owner's own constant.
  | _ => true

/-- Whether one constructor's **field** domains carry an owner occurrence that
survives reduction.  The `numParams` parameter binders and the conclusion are
not fields and are not asked; the conclusion names the owner in every case. -/
private def ExactNormalizationEnv.constructorRecurses (env : ExactNormalizationEnv)
    (owners : Array Name) (numParams : Nat) (type : Expr) : Bool :=
  let rec fields : Expr → Bool
    | .forallE _ domain body _ => env.occurrenceSurvives owners domain || fields body
    | _ => false
  let rec params : Nat → Expr → Bool
    | 0, type => fields type
    | k + 1, .forallE _ _ body _ => params k body
    | _, _ => false
  params numParams type

/-- Whether this inductive **block** is recursive: some constructor of some
member has a field whose domain still mentions a member after full reduction.

Block-wide, because that is the question `isRec` itself asks — Lean sets the
flag for every member of a block in which any member occurs — and this is the
same question with reduction in place of syntax rather than a different one.
`test/fixtures/inductive-models/mutual_nonrec.lean` is the argument for the
scope: a replay that recomputed recursion *per member* would disagree with the
export about a non-recursive member of a recursive block. -/
def ExactNormalizationEnv.blockRecurses (env : ExactNormalizationEnv)
    (type : EIndType) (constructors : List ECtor) : Bool :=
  let owners := type.all.toArray
  constructors.any fun constructor =>
    owners.contains constructor.induct &&
      env.constructorRecurses owners constructor.numParams constructor.type

/-- Whether this member has Lean's kernel-level structure treatment, with
recursion read off what survives reduction rather than off the exported flag.

This is deliberately per member.  A non-recursive mutual block may contain
several structure-like members even though the elaborator's `StructureInfo`
extension (and therefore any source-level `structure` grouping) is absent from
the export. -/
def EIndType.isKernelStructureLike (type : EIndType) (constructors : List ECtor)
    (normalizer : ExactNormalizationEnv) : Bool :=
  !normalizer.blockRecurses type constructors && type.numIndices == 0 &&
    (type.soleConstructor? constructors).isSome

/-- Whether this member has Lean's kernel-level unit-like treatment.

This is [`InductiveModels.EIndType.isKernelStructureLike`] followed by the
zero-field test in the kernel's `is_def_eq_unit_like`: the member is
non-recursive, has no indices and exactly one constructor, and that constructor
has no fields.  The test is deliberately per member; a non-recursive mutual
block may have more than one such member. -/
def EIndType.isKernelUnitlike (type : EIndType) (constructors : List ECtor)
    (normalizer : ExactNormalizationEnv) : Bool :=
  type.isKernelStructureLike constructors normalizer &&
    (type.soleConstructor? constructors).any (·.numFields == 0)

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

/-- [`Export.intrinsicProjectionFieldsFor`] with the transparent-definition
source supplied rather than derived from `x`.  Declaration types still come
from the export, so this isolates the normalizer as the one variable — which is
what lets `ExactEnvironmentAgreementTest` attribute any difference in the field
walk to the definition source and to nothing else. -/
def Export.intrinsicProjectionFieldsWith (x : Export)
    (normalizer : ExactNormalizationEnv) (type : EIndType)
    (constructors : List ECtor) : Array Nat := Id.run do
  let [constructorName] := type.ctors | return #[]
  let some constructor := constructors.find? fun constructor =>
      constructor.name == constructorName && constructor.induct == type.name
    | return #[]
  let declarations := exactDeclarationTypes x
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

/-- Zero-based constructor fields for which the kernel projection expression
is well typed.  The kernel requires one constructor, but does not require the
owner to be non-recursive or unindexed. -/
def Export.intrinsicProjectionFieldsFor (x : Export) (type : EIndType)
    (constructors : List ECtor) : Array Nat :=
  x.intrinsicProjectionFieldsWith x.exactNormalizationEnv type constructors

end InductiveModels
