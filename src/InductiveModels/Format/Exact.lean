import InductiveModels.Format.Export
/-!
# Exact export-syntax normalization

The deliberately bounded normalizer (β, ζ, metadata erasure and transparent
`defn` unfolding, and nothing else); the reading of an owner's type as the
kernel reads it, which adds ι and projection steps on literal constructor
applications and nothing else; the export-only type inference built on them;
and the kernel's `infer_proj` field walk expressed over export records.
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

/-- What an ι step needs of one exported recursor: its arities and its rules,
exactly as the export states them. The recursor's *type* is not kept — an ι
step never reads it — so a syntax index built record by record retains the
rule right-hand sides and nothing else of a recursor's graph. -/
structure ExactIotaRecursor where
  levelParams : List Name
  all : List Name
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  rules : List ERecRule
  deriving Inhabited

def ExactIotaRecursor.ofERec (recursor : ERec) : ExactIotaRecursor :=
  { levelParams := recursor.levelParams, all := recursor.all
    numParams := recursor.numParams, numIndices := recursor.numIndices
    numMotives := recursor.numMotives, numMinors := recursor.numMinors
    rules := recursor.rules }

/-- One constant the owner-former reading
([`ExactNormalizationEnv.kernelFormer?`]) may take an ι or projection step
through: an exported recursor, whose rules it applies exactly as the export
states them, or an exported constructor, which is what a major premise or a
projected structure has to be headed by for the step to fire at all. -/
inductive ExactIotaEntry where
  | recursor (value : ExactIotaRecursor)
  | constructor (value : ECtor)
  deriving Inhabited

/-- The deliberately bounded environment used for exact export-syntax
normalization.  It contains only values of transparent `defn` records from the
export: opaque declarations, theorems, and any ambient kernel environment are
invisible.  Beside them it keeps the export's recursor and constructor records,
which only the owner-former reading consults, for ι and projection steps on
literal constructor applications ([`ExactNormalizationEnv.kernelFormer?`]). -/
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
  /-- Exported recursors and constructors, by name, for the owner-former
  reading's ι and projection steps. First occurrence wins, like `definitions`. -/
  iota : Std.HashMap Name ExactIotaEntry := {}
  /-- Sparse replacements of `iota`, as `overrides` is of `definitions`. -/
  private iotaOverrides : Lean.PersistentHashMap Name (Option ExactIotaEntry) := {}
  /-- The installed environment's recursors and constructors, consulted where
  `iotaOverrides` and `iota` both miss; set only by
  [`ExactNormalizationEnv.ofEnvironment`], like `fallback?`. -/
  private iotaFallback? : Option (Name → Option ExactIotaEntry) := none

private def ExactNormalizationEnv.definition? (env : ExactNormalizationEnv)
    (name : Name) : Option ExactNormalizationDef :=
  match env.overrides.find? name with
  | some replacement => replacement
  | none => match env.definitions[name]? with
    | some definition => some definition
    | none => env.fallback?.bind (· name)

private def ExactNormalizationEnv.iotaEntry? (env : ExactNormalizationEnv)
    (name : Name) : Option ExactIotaEntry :=
  match env.iotaOverrides.find? name with
  | some replacement => replacement
  | none => match env.iota[name]? with
    | some entry => some entry
    | none => env.iotaFallback?.bind (· name)

/-- Add or replace one transparent definition without copying the public base
table.  This is the sparse update operation used by syntax-index overlays. -/
def ExactNormalizationEnv.insertDefinition (env : ExactNormalizationEnv)
    (name : Name) (definition : ExactNormalizationDef) : ExactNormalizationEnv :=
  { env with overrides := env.overrides.insert name (some definition) }

/-- Hide one transparent definition without copying the public base table. -/
def ExactNormalizationEnv.eraseDefinition (env : ExactNormalizationEnv)
    (name : Name) : ExactNormalizationEnv :=
  { env with overrides := env.overrides.insert name none }

/-- Add or replace one inductive record's recursors and constructors in the ι
table, without copying the public base table: the sparse update syntax-index
overlays use for a replayed or island inductive record. -/
def ExactNormalizationEnv.insertInductive (env : ExactNormalizationEnv)
    (constructors : List ECtor) (recursors : List ERec) : ExactNormalizationEnv :=
  let overrides := constructors.foldl
    (fun overrides constructor =>
      overrides.insert constructor.name (some (.constructor constructor)))
    env.iotaOverrides
  let overrides := recursors.foldl
    (fun overrides recursor => overrides.insert recursor.name (some (.recursor (.ofERec recursor))))
    overrides
  { env with iotaOverrides := overrides }

/-- Hide one recursor or constructor from the ι table without copying it. -/
def ExactNormalizationEnv.eraseIota (env : ExactNormalizationEnv)
    (name : Name) : ExactNormalizationEnv :=
  { env with iotaOverrides := env.iotaOverrides.insert name none }

/-- One inductive record's recursors and constructors added to a base ι
table, keeping the first occurrence of a name. -/
def ExactNormalizationEnv.addIotaEntries (table : Std.HashMap Name ExactIotaEntry)
    (constructors : List ECtor) (recursors : List ERec) : Std.HashMap Name ExactIotaEntry :=
  let table := constructors.foldl (fun table constructor =>
    if table.contains constructor.name then table
    else table.insert constructor.name (.constructor constructor)) table
  recursors.foldl (fun table recursor =>
    if table.contains recursor.name then table
    else table.insert recursor.name (.recursor (.ofERec recursor))) table

/-- Build the exact normalizer's environment from export records alone.
Keeping the first occurrence agrees with the other format prepasses and makes
malformed duplicate-name input deterministic. -/
def Export.exactNormalizationEnv (x : Export) : ExactNormalizationEnv := Id.run do
  let mut definitions : Std.HashMap Name ExactNormalizationDef := {}
  let mut iota : Std.HashMap Name ExactIotaEntry := {}
  for declaration in x.decls do
    if let .defn name levelParams _ value .. := declaration then
      unless definitions.contains name do
        definitions := definitions.insert name { levelParams, value }
    if let .induct _ constructors recursors := declaration then
      iota := ExactNormalizationEnv.addIotaEntries iota constructors recursors
  return { definitions, iota }

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

/-- One recursor or constructor as an installed environment spells it, for the
environment-backed face of the ι table.  An installed environment's recursors
are the ones Lean's kernel minted when it accepted the block (`toDeclaration`
drops exported ones), which is exactly what the generator's
[`InductiveModels.kernelFormer`] reduces with. -/
def environmentIotaEntry? (env : Environment) (name : Name) : Option ExactIotaEntry :=
  match env.find? name with
  | some (.recInfo value) => some <| .recursor
      { levelParams := value.levelParams, all := value.all
        numParams := value.numParams, numIndices := value.numIndices
        numMotives := value.numMotives, numMinors := value.numMinors
        rules := value.rules.map fun rule =>
          { ctor := rule.ctor, nfields := rule.nfields, rhs := rule.rhs } }
  | some (.ctorInfo value) => some <| .constructor
      { name := value.name, levelParams := value.levelParams, type := value.type,
        cidx := value.cidx, numParams := value.numParams, numFields := value.numFields,
        induct := value.induct, isUnsafe := value.isUnsafe }
  | _ => none

/-- The bounded normalizer served entirely from an installed environment.

It reuses [`ExactNormalizationEnv.whnf`] and every query built on it, so this is
the same β/ζ/δ-transparent reduction rather than a second implementation.  The
base table is deliberately empty: nothing is retained per definition here,
because the environment already holds each body. -/
def ExactNormalizationEnv.ofEnvironment (env : Environment) : ExactNormalizationEnv :=
  { definitions := {}, fallback? := some (environmentDefinition? env)
    iotaFallback? := some (environmentIotaEntry? env) }

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

/-! ### An inductive's type as the kernel reads it

`add_inductive` does not read an inductive's type as written: it whnf's the
type, peels a `Π`, and whnf's again until a `Sort` is left, so a member may be
declared at a term that *reduces* to its sort or to any part of its index
telescope — through a chain of definitions, and also through a `match`, a
`casesOn` or a projection of a structure literal (`inductive XM : pick true`
with `pick` defined by `match`).

The statement checker restates that telescope with its own head normaliser,
below. It is not a second kernel: it takes δ, β and ζ steps, and ι and
projection steps **only on a literal constructor application**, and nothing
else.

* **ι.** `R.rec p⃗ m⃗ c⃗ i⃗ (C a⃗ f⃗) e⃗` steps to rule `C`'s right-hand side,
  exactly as the export states `R.rec`'s rules, instantiated at the
  recursor's levels and applied to `p⃗ m⃗ c⃗`, the fields `f⃗` and `e⃗`: the
  kernel's `inductive_reduce_rec`. The major premise is head-normalised by the
  same reader first, and the step fires only if it then is a *saturated*
  application of one of `R`'s constructors (a `Nat` literal counts as
  `Nat.zero`/`Nat.succ` of the literal below it, as in the kernel). A
  `casesOn`, a matcher and a structural recursion compiled through `brecOn`
  are definitions that unfold to `R.rec`, so they take the same step.
* **Projection.** `Expr.proj S i s` steps to field `i` when `s` head-normalises
  to a saturated application of a constructor of `S`: the kernel's
  `reduce_proj`.
* **Excluded:** K-like reduction (a major premise *replaced* by the constructor
  its type determines), structure η on a major premise or a projected term,
  proof irrelevance, quotient reduction, `Nat`/`String` literal arithmetic, and
  any step on a stuck term. A major premise that is a variable, or an
  application of an opaque constant, leaves the recursor application as it is,
  and the reading ends in no former.

**The owner's own block is never used.** Reading the type of a member of the
block `block` names, no ι step goes through a recursor of that block and no ι
or projection step through one of its constructors: the rules of the block
under test are what the checker validates models against, so they must not
also decide what it compares. In a well-scoped export this excludes nothing —
a type cannot mention its own block — and the exclusion makes that a property
of the reading rather than an assumption about the input.

**Bounded.** Every δ, β, ζ, ι and projection step spends one unit of
[`kernelFormerFuel`]; a reading that runs out is `outOfFuel`, never a partial
answer. Each head normalisation is memoized on the expression within one
reading, so a major premise or a projected term that recurs is reduced once;
the reading follows spines and never walks under a binder it does not peel. A
type already written as `∀ p⃗ i⃗, Sort u` is returned as it is, without a step.
-/

/-- The most reduction steps one reading of one owner's type may take
([`ExactNormalizationEnv.readKernelFormer`]). A type former the elaborator
writes behind definitions takes a handful; one computed by a `match` a few
dozen. Running out is a hard stop, reported as such. -/
def kernelFormerFuel : Nat := 100000

/-- The outcome of reading one owner's type as the kernel reads it. -/
inductive KernelFormerReading where
  /-- `∀ p⃗ i⃗, Sort u`, with every binder written. -/
  | former (value : Expr)
  /-- Head normalisation stopped at a term that is neither a `Π` nor a sort:
  a stuck recursor, a projection of a variable, an opaque constant. -/
  | stuck
  /-- The reading spent [`kernelFormerFuel`] steps without ending. -/
  | outOfFuel
  deriving Inhabited

private structure FormerReadState where
  fuel : Nat
  memo : Dag.Memo Expr := {}

private abbrev FormerReadM := ExceptT Unit (StateM FormerReadState)

private def FormerReadM.tick : FormerReadM Unit := do
  let state ← get
  if state.fuel == 0 then throw ()
  set { state with fuel := state.fuel - 1 }

/-- `e` as a saturated application of an exported constructor outside `block`,
with that constructor's record and the application's arguments. -/
private def ExactNormalizationEnv.constructorApp? (env : ExactNormalizationEnv)
    (block : List Name) (e : Expr) : Option (ECtor × Array Expr) := do
  let .const name levels := e.getAppFn | none
  let some (.constructor constructor) := env.iotaEntry? name | none
  guard (!block.contains constructor.induct)
  guard (constructor.levelParams.length == levels.length)
  let args := e.getAppArgs
  guard (args.size == constructor.numParams + constructor.numFields)
  return (constructor, args)

/-- The head normaliser of an owner-former reading (see the section comment). -/
private partial def ExactNormalizationEnv.formerWhnf (env : ExactNormalizationEnv)
    (block : List Name) (e : Expr) : FormerReadM Expr := do
  if let some reduct := (← get).memo[(e : Dag.Key)]? then return reduct
  let reduct ← step e
  modify fun state => { state with memo := state.memo.insert e reduct }
  return reduct
where
  step (e : Expr) : FormerReadM Expr := do
    match e with
    | .mdata _ body => env.formerWhnf block body
    | .letE _ _ value body _ =>
      FormerReadM.tick
      env.formerWhnf block (body.instantiate1 value)
    | .const name levels =>
      match delta? name levels with
      | some value => FormerReadM.tick; env.formerWhnf block value
      | none => return e
    | .proj structName index struct =>
      match ← project? structName index struct with
      | some field => FormerReadM.tick; env.formerWhnf block field
      | none => return e
    | .app .. =>
      let head := e.getAppFn
      let args := e.getAppArgs
      let head' ← env.formerWhnf block head
      if head'.isLambda then
        FormerReadM.tick
        env.formerWhnf block (head'.beta args)
      else if head' != head then
        env.formerWhnf block (mkAppN head' args)
      else match head with
        | .const name levels =>
          match ← iota? name levels args with
          | some reduct => FormerReadM.tick; env.formerWhnf block reduct
          | none => return e
        | _ => return e
    | _ => return e
  delta? (name : Name) (levels : List Level) : Option Expr := do
    let definition ← env.definition? name
    guard (definition.levelParams.length == levels.length)
    return definition.value.instantiateLevelParams definition.levelParams levels
  /-- The kernel's `nat_lit_to_constructor`, for `Nat.rec`'s major only. -/
  natLiteral (recursor : ExactIotaRecursor) : Expr → Expr
    | .lit (.natVal n) =>
      if recursor.all != [``Nat] then .lit (.natVal n)
      else if n == 0 then .const ``Nat.zero []
      else .app (.const ``Nat.succ []) (.lit (.natVal (n - 1)))
    | major => major
  iota? (name : Name) (levels : List Level) (args : Array Expr) :
      FormerReadM (Option Expr) := do
    let some (.recursor recursor) := env.iotaEntry? name | return none
    if recursor.all.any block.contains then return none
    unless recursor.levelParams.length == levels.length do return none
    let prefixSize := recursor.numParams + recursor.numMotives + recursor.numMinors
    let majorIndex := prefixSize + recursor.numIndices
    let some major := args[majorIndex]? | return none
    let major := natLiteral recursor (← env.formerWhnf block major)
    let some (constructor, majorArgs) := env.constructorApp? block major | return none
    let some rule := recursor.rules.find? (·.ctor == constructor.name) | return none
    unless rule.nfields == constructor.numFields do return none
    let rhs := rule.rhs.instantiateLevelParams recursor.levelParams levels
    return some <| mkAppN
      (mkAppN (mkAppN rhs (args.extract 0 prefixSize))
        (majorArgs.extract constructor.numParams majorArgs.size))
      (args.extract (majorIndex + 1) args.size)
  project? (structName : Name) (index : Nat) (struct : Expr) :
      FormerReadM (Option Expr) := do
    let some (constructor, args) := env.constructorApp? block (← env.formerWhnf block struct)
      | return none
    unless constructor.induct == structName && index < constructor.numFields do return none
    return args[constructor.numParams + index]?

/-- **An inductive's type as the kernel reads it**, on the statement checker's
side: the one place the checker, and every walk here that generation and
checking share, reads an owner's parameters, indices and sort. `block` is the
owner's block (`EIndType.all`), whose own recursors and constructors the
reading never steps through.

Returns `∀ p⃗ i⃗, Sort u` with every binder written, or why there is none. A
type already written so is returned as it is, without a step.

The generator's reading is `InductiveModels.kernelFormer`, which asks Lean's
kernel itself. On every owner the tool models, `Driver/Filter.lean` requires
the two to be the same expression before any construction, and stops the run
otherwise. -/
partial def ExactNormalizationEnv.readKernelFormer (env : ExactNormalizationEnv)
    (type : Expr) (block : List Name) : KernelFormerReading :=
  if written type then .former type else
  match ((go 0 type).run).run' { fuel := kernelFormerFuel } with
  | .ok (some former) => .former former
  | .ok none => .stuck
  | .error () => .outOfFuel
where
  written : Expr → Bool
    | .forallE _ _ body _ => written body
    | .sort _ => true
    | _ => false
  go (depth : Nat) (type : Expr) : FormerReadM (Option Expr) := do
    match ← env.formerWhnf block type with
    | .forallE name domain body info =>
      let value := mkFVar (FVarId.mk ((`_format.kernelFormer).mkNum depth))
      return (← go (depth + 1) (body.instantiate1 value)).map fun rest =>
        .forallE name domain (rest.abstract #[value]) info
    | .sort level => return some (.sort level)
    | _ => return none

/-- [`ExactNormalizationEnv.readKernelFormer`]'s former, or `none` when there
is none (stuck or out of fuel). Every consumer that selects a route or spells
a statement from it fails closed on `none`; the one place a `none` must be
explained, the stop in `Driver/Filter.lean`, reads the reason itself. -/
def ExactNormalizationEnv.kernelFormer? (env : ExactNormalizationEnv)
    (type : Expr) (block : List Name) : Option Expr :=
  match env.readKernelFormer type block with
  | .former former => some former
  | _ => none

/-- The sort a former in [`ExactNormalizationEnv.kernelFormer?`]'s exposed form
ends in, and how many binders precede it. -/
def exposedFormerShape : Expr → Nat × Option Level
  | .forallE _ _ body _ => let (n, level) := exposedFormerShape body; (n + 1, level)
  | .sort level => (0, some level)
  | _ => (0, none)

/-- Whether an exported former ends in *literally* `Prop`, read as the kernel
reads it ([`ExactNormalizationEnv.kernelFormer?`]). -/
def ExactNormalizationEnv.isPropositionFormer
    (env : ExactNormalizationEnv) (expression : Expr) (block : List Name) : Bool :=
  match env.kernelFormer? expression block with
  | some former => (exposedFormerShape former).2 == some .zero
  | none => false

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
  (go expression).run' ({}, {})
where
  /-- Memoized twice over: the answer per node, and the syntactic mention test
  per node, which every visited node asks of itself and of its reduct. -/
  go (e : Expr) : StateM (Dag.Memo Bool × Dag.Memo Bool) Bool := do
    if let some r := (← get).1[(e : Dag.Key)]? then return r
    let r ← survives e
    modify fun (answers, mentions) => (answers.insert e r, mentions)
    return r
  mentions (e : Expr) : StateM (Dag.Memo Bool × Dag.Memo Bool) Bool :=
    modifyGet fun (answers, table) =>
      let (r, table) := (Dag.anyMemo (fun
        | .const n _ => owners.contains n
        | _ => false) e).run table
      (r, (answers, table))
  survives (e : Expr) : StateM (Dag.Memo Bool × Dag.Memo Bool) Bool := do
    if !(← mentions e) then return false
    let e := env.whnf e
    if !(← mentions e) then return false
    match e with
    | .app .. => go e.getAppFn <||> e.getAppArgs.anyM go
    | .forallE _ domain body _ | .lam _ domain body _ => go domain <||> go body
    | .letE _ t v b _ => go t <||> go v <||> go b
    | .mdata _ body | .proj _ _ body => go body
    -- A leaf that still mentions an owner is the owner's own constant.
    | _ => return true

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

/-- Every declaration's type by name, for the exact type inference below. An
inductive type's is its former as the kernel reads it
([`ExactNormalizationEnv.kernelFormer?`]), where there is one: the one
head-normalisation that may take ι and projection steps, so that a field
`XM 0` of `inductive XM : pick true` has a type here as it has to the kernel. -/
private def exactDeclarationTypes (x : Export) (normalizer : ExactNormalizationEnv) :
    ExactDeclarationTypes := Id.run do
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
          result := result.insert type.name
            { levelParams := type.levelParams
              type := (normalizer.kernelFormer? type.type type.all).getD type.type }
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

/-- The state of one exact type inference: the next fresh local, and the
answers so far by expression.  Every local the inference opens is fresh, so an
expression that mentions it has one type wherever it recurs, and the answer
can be memoized on the expression alone; the walk is then linear in the DAG.
Unmemoized, a `Π` whose domain and body share a subterm —
`P₀ → P₀`, `P₁ → P₁`, … — costs one visit per path, `2^depth`. -/
private structure ExactInferState where
  next : Nat := 0
  memo : Dag.Memo (Option Expr) := {}

private abbrev ExactInferM := StateM ExactInferState

private def freshExactLocal (tag : Name) : ExactInferM Expr :=
  modifyGet fun st => (mkFVar (FVarId.mk (tag.mkNum st.next)), { st with next := st.next + 1 })

mutual

private partial def inferExactType? (x : Export) (normalizer : ExactNormalizationEnv)
    (declarations : ExactDeclarationTypes)
    (locals : ExactLocals) (e : Expr) : ExactInferM (Option Expr) := do
  if let some r := (← get).memo[(e : Dag.Key)]? then return r
  let r ← (inferExactTypeNode x normalizer declarations locals e).run
  modify fun st => { st with memo := st.memo.insert e r }
  return r

private partial def inferExactTypeNode (x : Export) (normalizer : ExactNormalizationEnv)
    (declarations : ExactDeclarationTypes)
    (locals : ExactLocals) : Expr → OptionT ExactInferM Expr
  | .sort level => return .sort (.succ level)
  | .fvar id => OptionT.mk (pure (locals.typeOf? id))
  | .const name levels => do
      let some declaration := declarations[name]? | failure
      unless declaration.levelParams.length == levels.length do failure
      return declaration.type.instantiateLevelParams declaration.levelParams levels
  | .app function argument => do
      let functionType := normalizer.whnf
        (← OptionT.mk (inferExactType? x normalizer declarations locals function))
      let .forallE _ _ body _ := functionType | failure
      return body.instantiate1 argument
  | .lam name domain body info => do
      let value ← freshExactLocal `_format.exactLam
      let bodyType ← OptionT.mk (inferExactType? x normalizer declarations
        (locals.push (value.fvarId!, domain)) (body.instantiate1 value))
      return .forallE name domain (bodyType.abstract #[value]) info
  | .forallE _ domain body _ => do
      let domainLevel ← OptionT.mk (inferExactSortLevel? x normalizer declarations locals domain)
      let value ← freshExactLocal `_format.exactPi
      let bodyLevel ← OptionT.mk (inferExactSortLevel? x normalizer declarations
        (locals.push (value.fvarId!, domain)) (body.instantiate1 value))
      return .sort (Level.imax domainLevel bodyLevel).normalize
  | .letE _ _ value body _ =>
      OptionT.mk (inferExactType? x normalizer declarations locals (body.instantiate1 value))
  | .mdata _ body => OptionT.mk (inferExactType? x normalizer declarations locals body)
  | .proj owner fieldIndex struct => do
      let structType := normalizer.whnf
        (← OptionT.mk (inferExactType? x normalizer declarations locals struct))
      let .const structOwner levels := structType.getAppFn | failure
      unless structOwner == owner do failure
      let some (type, constructors) := structureOwner? x owner | failure
      let some constructorName := type.ctors.head? | failure
      let some constructor := constructors.find? (fun constructor =>
        constructor.name == constructorName && constructor.induct == owner) | failure
      unless type.ctors == [constructorName] do failure
      let ownerArguments := structType.getAppArgs
      unless ownerArguments.size == type.numParams + type.numIndices do failure
      let params := ownerArguments.extract 0 type.numParams
      let mut current := constructor.type.instantiateLevelParams constructor.levelParams levels
      for param in params do
        let .forallE _ _ body _ := normalizer.whnf current | failure
        current := body.instantiate1 param
      let ownerIsProp := normalizer.isPropositionFormer type.type type.all
      for earlier in [0:fieldIndex + 1] do
        let .forallE _ fieldType body _ := normalizer.whnf current | failure
        let fieldLevel : Option Level ← (monadLift
          (inferExactSortLevel? x normalizer declarations locals fieldType) :
            OptionT ExactInferM (Option Level))
        let fieldIsProp := fieldLevel == some .zero
        if earlier == fieldIndex then
          if ownerIsProp && !fieldIsProp then failure else return fieldType
        if ownerIsProp && body.hasLooseBVars && !fieldIsProp then failure
        current := body.instantiate1 (.proj owner earlier struct)
      failure
  | .lit (.natVal _) => return .const ``Nat []
  | .lit (.strVal _) => return .const ``String []
  | .bvar _ | .mvar _ => failure

private partial def inferExactSortLevel? (x : Export) (normalizer : ExactNormalizationEnv)
    (declarations : ExactDeclarationTypes)
    (locals : ExactLocals) (expression : Expr) : ExactInferM (Option Level) := do
  let some type ← inferExactType? x normalizer declarations locals expression | return none
  let .sort level := normalizer.whnf type | return none
  return some level

end

private partial def projectionFieldEligible? (x : Export)
    (normalizer : ExactNormalizationEnv) (declarations : ExactDeclarationTypes)
    (ownerIsProp : Bool) (fieldIndex : Nat)
    (current : Expr) (locals : ExactLocals) : ExactInferM (Option Bool) := do
  let .forallE _ fieldType body _ := normalizer.whnf current | return none
  let fieldIsProp :=
    (← inferExactSortLevel? x normalizer declarations locals fieldType) == some .zero
  if fieldIndex == 0 then return some (!ownerIsProp || fieldIsProp)
  if ownerIsProp && body.hasLooseBVars && !fieldIsProp then return some false
  let value ← freshExactLocal `_format.projectionField
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
  let declarations := exactDeclarationTypes x normalizer
  let ownerIsProp := normalizer.isPropositionFormer type.type type.all
  let mut current := constructor.type
  let mut locals : ExactLocals := #[]
  for parameterIndex in [:type.numParams] do
    let .forallE _ parameterType body _ := normalizer.whnf current | return #[]
    let value := mkFVar (FVarId.mk ((`_format.projectionParam).mkNum parameterIndex))
    locals := locals.push (value.fvarId!, parameterType)
    current := body.instantiate1 value
  let mut result := #[]
  -- One inference state for the whole walk: its locals stay fresh against the
  -- parameter locals above, and each field type is inferred once.
  let mut inferState : ExactInferState := {}
  for fieldIndex in [:constructor.numFields] do
    let (eligible, next) := (projectionFieldEligible? x normalizer declarations ownerIsProp
      fieldIndex current locals).run inferState
    inferState := next
    if eligible == some true then
      result := result.push fieldIndex
  return result

/-- Zero-based constructor fields for which the kernel projection expression
is well typed.  The kernel requires one constructor, but does not require the
owner to be non-recursive or unindexed. -/
def Export.intrinsicProjectionFieldsFor (x : Export) (type : EIndType)
    (constructors : List ECtor) : Array Nat :=
  x.intrinsicProjectionFieldsWith x.exactNormalizationEnv type constructors

end InductiveModels
