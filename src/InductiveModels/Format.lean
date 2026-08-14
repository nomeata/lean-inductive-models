import Lean
import InductiveModels.Naming
/-!
# The Lean 4 export format, read and written

`lean4export` 3.1.0's `.ndjson`: one JSON object per line, each either a
*record* interning a name (`in`), a level (`il`) or an expression (`ie`), or a
**declaration** naming earlier records by index.

The parser here is the whole of the tool's trust boundary and it does **no
checking**: an export is read into `Lean.Name` / `Lean.Level` / `Lean.Expr`
verbatim. Input validation is deliberately separate from parsing, and nothing
below runs a typechecker.

Two properties the rest of the tool depends on:

* **References must name an explicitly defined arena entry.** Arena IDs may be
  sparse, out of order, or overwritten, but an absent ID is never an implicit
  anonymous name, zero level, or bound variable. [`Writer`] emits a fresh dense
  arena when transforming an export.
* **The writer's key order is alphabetical and it emits no whitespace.** This
  is the canonical `lean4export` spelling, so canonical dense fixtures retain
  their bytes on a no-op run. Sparse, overwritten, metadata-bearing, or
  differently formatted valid input is normalized when it is written again.
-/
open Lean

namespace InductiveModels

/-- One constructor, as the export declares it. -/
structure ECtor where
  name : Name
  levelParams : List Name
  type : Expr
  cidx : Nat
  numParams : Nat
  numFields : Nat
  induct : Name
  isUnsafe : Bool
  deriving Inhabited, BEq

/-- One ι rule of an exported recursor. -/
structure ERecRule where
  ctor : Name
  nfields : Nat
  rhs : Expr
  deriving Inhabited, BEq

/-- One recursor, as the export declares it. A nested declaration carries more
than one: `Tree.rec` and `Tree.rec_1`. -/
structure ERec where
  name : Name
  levelParams : List Name
  type : Expr
  all : List Name
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  rules : List ERecRule
  k : Bool
  isUnsafe : Bool
  deriving Inhabited, BEq

/-- One member of an inductive block. `numNested > 0` is the whole reason this
tool exists. -/
structure EIndType where
  name : Name
  levelParams : List Name
  type : Expr
  all : List Name
  ctors : List Name
  numParams : Nat
  numIndices : Nat
  numNested : Nat
  isRec : Bool
  isReflexive : Bool
  isUnsafe : Bool
  deriving Inhabited, BEq

/-- Whether this member has Lean's kernel-level structure treatment.

This is deliberately per member.  A non-recursive mutual block may contain
several structure-like members even though the elaborator's `StructureInfo`
extension (and therefore any source-level `structure` grouping) is absent from
the export. -/
def EIndType.isKernelStructureLike (type : EIndType)
    (constructors : List ECtor) : Bool :=
  !type.isRec && type.numIndices == 0 && match type.ctors with
  | [constructorName] =>
      constructors.any fun constructor =>
        constructor.name == constructorName && constructor.induct == type.name
  | _ => false

/-- Whether this member has Lean's kernel-level unit-like treatment.

This is the export-metadata spelling of `Lean.isStructureLike` followed by the
zero-field test in the kernel's `is_def_eq_unit_like`: the member is
non-recursive, has no indices and exactly one constructor, and that constructor
has no fields.  The test is deliberately per member; a non-recursive mutual
block may have more than one such member. -/
def EIndType.isKernelUnitlike (type : EIndType) (constructors : List ECtor) : Bool :=
  type.isKernelStructureLike constructors && match type.ctors with
  | [constructorName] =>
      constructors.any fun constructor =>
        constructor.name == constructorName && constructor.induct == type.name &&
          constructor.numFields == 0
  | _ => false

/-- A definition's reducibility hint, kept verbatim so a round trip is exact. -/
inductive EHints where
  | abbrev
  | «opaque»
  | regular (h : Nat)
  deriving Inhabited, BEq

/-- One declaration record. -/
inductive EDecl where
  | ax (name : Name) (levelParams : List Name) (type : Expr) (isUnsafe : Bool)
  | defn (name : Name) (levelParams : List Name) (type value : Expr)
      (hints : EHints) (safety : String) (all : List Name)
  | thm (name : Name) (levelParams : List Name) (type value : Expr) (all : List Name)
  | opaq (name : Name) (levelParams : List Name) (type value : Expr)
      (isUnsafe : Bool) (all : List Name)
  | quot (name : Name) (levelParams : List Name) (type : Expr) (kind : String)
  | induct (types : List EIndType) (ctors : List ECtor) (recs : List ERec)
  deriving Inhabited, BEq

namespace EDecl

/-- Every top-level name a declaration introduces — used to key the model's
insertion point and to detect a name the model would collide with. -/
def names : EDecl → List Name
  | .ax n .. | .defn n .. | .thm n .. | .opaq n .. | .quot n .. => [n]
  | .induct ts cs rs => ts.map (·.name) ++ cs.map (·.name) ++ rs.map (·.name)

end EDecl

/-! ## A record as a kernel declaration

The one function that turns a parsed record into something the kernel takes,
and the two hint/safety translations it needs. **It lives here rather than
beside its callers because it has three of them at three different heights of
the import graph**: the input replay in `InductiveModels.Driver`, the replay in
`InductiveModels.Mono` — which deliberately does not import `Driver` — and the
fragment splice in `InductiveModels.Simple`, which sits *below* `Driver`. `Format` is
the shared floor, and the function is pure in its argument, so nothing but the
name resolution moves. -/

def hintsOf : ReducibilityHints → EHints
  | .abbrev => .abbrev
  | .opaque => .opaque
  | .regular h => .regular h.toNat

def hintsTo : EHints → ReducibilityHints
  | .abbrev => .abbrev
  | .opaque => .opaque
  | .regular h => .regular h.toUInt32

def safetyOf? : String → Option DefinitionSafety
| "unsafe" => some .unsafe
| "partial" => some .partial
| "safe" => some .safe
| _ => none

def quotKindOf? : String → Option QuotKind
| "type" => some .type
| "ctor" => some .ctor
| "lift" => some .lift
| "ind" => some .ind
| _ => none

/-- The exact lean4export spelling of a kernel definition-safety annotation. -/
def safetyTo : DefinitionSafety → String
  | .unsafe => "unsafe"
  | .partial => "partial"
  | .safe => "safe"

/-- An export record as a kernel declaration. `none` for the three `quot`
records that `Declaration.quotDecl` already covers. -/
def toDeclaration (env : Environment) : EDecl → Option Declaration
  | .ax n lp t u => some <| .axiomDecl { name := n, levelParams := lp, type := t, isUnsafe := u }
  | .defn n lp t v h sf all => do
      let safety ← safetyOf? sf
      some <| .defnDecl
        { name := n, levelParams := lp, type := t, value := v
          hints := hintsTo h, safety, all }
  | .thm n lp t v all => some <| .thmDecl
      { name := n, levelParams := lp, type := t, value := v, all }
  | .opaq n lp t v u all => some <| .opaqueDecl
      { name := n, levelParams := lp, type := t, value := v, isUnsafe := u, all }
  | .quot .. => if env.constants.contains `Quot then none else some .quotDecl
  | .induct ts cs _ =>
    let its := ts.map fun t =>
      ({ name := t.name, type := t.type
         ctors := (cs.filter (·.induct == t.name)).map fun c =>
           ({ name := c.name, type := c.type } : Constructor) } : InductiveType)
    match ts with
    | [] => none
    | t :: _ => some <| .inductDecl t.levelParams t.numParams its t.isUnsafe

/-! ## Renaming generated declarations by exact aliases -/

/-- **Every constant an expression names, rewritten** — and there are two kinds
of node that name one, not one.

`Expr.const` is the obvious kind. The other is `Expr.proj`, whose `typeName`
field is the structure the projection is *of*: a `proj` left pointing at the
old name after its structure has been renamed is `(kernel) invalid projection`,
which is exactly how this was found, splicing a fragment whose `Sigma.fst` is a
`proj` at `Sigma`. Binder names are not constants and are deliberately not
touched.

`f` returns `none` to mean "not mine", which both keeps the walk allocation-free
on the common subterm and, at a `proj`, lets `Expr.replace` recurse into the
structure the ordinary way. -/
partial def mapConstsE (f : Name → Option Name) (e : Expr) : Expr :=
  e.replace fun sub => match sub with
    | .const n us => (f n).map (Expr.const · us)
    | .proj n i s => (f n).map (fun n' => Expr.proj n' i (mapConstsE f s))
    | _ => none

/-- One export record with **every name it carries** rewritten — every name it
introduces, every name it refers to, and every constant inside its expressions.
`f` is applied to declaration names and `g` to expressions, and they are two
arguments so declaration fields and expression constants share one exhaustive
record walk.

**Every field that can hold a `Name` is listed**, because one missed field is a
record that refers to a constant the output does not contain, and no oracle here
would see it: the statement check reads the environment, which keeps the alias.
This is the single place that enumerates them, so a field added to a record is
caught once. -/
def EDecl.mapNames (f : Name → Name) (g : Expr → Expr) : EDecl → EDecl
  | .ax n lp t u => .ax (f n) lp (g t) u
  | .defn n lp t v h sf all => .defn (f n) lp (g t) (g v) h sf (all.map f)
  | .thm n lp t v all => .thm (f n) lp (g t) (g v) (all.map f)
  | .opaq n lp t v u all => .opaq (f n) lp (g t) (g v) u (all.map f)
  | .quot n lp t k => .quot (f n) lp (g t) k
  | .induct ts cs rs =>
    .induct
      (ts.map fun t => { t with
        name := f t.name, type := g t.type, all := t.all.map f, ctors := t.ctors.map f })
      (cs.map fun c => { c with name := f c.name, type := g c.type, induct := f c.induct })
      (rs.map fun r => { r with
        name := f r.name, type := g r.type, all := r.all.map f,
        rules := r.rules.map fun u => { u with ctor := f u.ctor, rhs := g u.rhs } })

/-- Rewrite one export record by an explicit whole-name alias table.  There is
no namespace fallback: a name absent from the table is left byte-for-byte
alone. -/
def EDecl.renameAliases (aliases : Naming.AliasMap) : EDecl → EDecl :=
  EDecl.mapNames aliases.exact
    (mapConstsE fun n => aliases.exact? n)

/-! ## Collision-safe source replay names

`Lean.Environment` indexes locally replayed constants by
`privateToUserName`.  A flattened export legitimately contains distinct
module-private constants with the same user spelling, so that index cannot
represent every exact source name.  The kernel can: this table is only the
injective build-name view used while generating models.  Source records and
serialized output always retain the exact names in the right-hand column.
-/

/-- One exact source name and its collision-free build name. -/
structure SourceReplayAlias where
  exact : Name
  build : Name
  deriving Inhabited, Repr, BEq

/-- Explicit whole-name aliases for the source replay environment.

There is deliberately no namespace or suffix fallback.  Every changed name
comes from the complete source-name census, and every inverse rewrite is the
same finite table in the opposite direction. -/
structure SourceReplayAliases where
  entries : Array SourceReplayAlias := #[]
  private forward : Std.HashMap Name Name := {}
  private inverse : Std.HashMap Name Name := {}
  deriving Inhabited

/-- Construct and validate both directions of an explicit alias table. -/
def SourceReplayAliases.ofEntries (entries : Array SourceReplayAlias) :
    Except String SourceReplayAliases := do
  let mut forward : Std.HashMap Name Name := {}
  let mut inverse : Std.HashMap Name Name := {}
  for entry in entries do
    if let some first := forward[entry.exact]? then
      throw s!"source replay name {entry.exact} has aliases {first} and {entry.build}"
    if let some first := inverse[entry.build]? then
      throw s!"source replay alias {entry.build} represents {first} and {entry.exact}"
    forward := forward.insert entry.exact entry.build
    inverse := inverse.insert entry.build entry.exact
  return { entries, forward, inverse }

def SourceReplayAliases.isEmpty (aliases : SourceReplayAliases) : Bool :=
  aliases.entries.isEmpty

def SourceReplayAliases.build? (aliases : SourceReplayAliases) (exact : Name) : Option Name :=
  aliases.forward[exact]?

def SourceReplayAliases.exact? (aliases : SourceReplayAliases) (build : Name) : Option Name :=
  aliases.inverse[build]?

def SourceReplayAliases.hasExact (aliases : SourceReplayAliases) (exact : Name) : Bool :=
  aliases.forward.contains exact

def SourceReplayAliases.buildName (aliases : SourceReplayAliases) (exact : Name) : Name :=
  aliases.build? exact |>.getD exact

def SourceReplayAliases.exactName (aliases : SourceReplayAliases) (build : Name) : Name :=
  aliases.exact? build |>.getD build

private def longestAliasPrefix? (entries : Array SourceReplayAlias)
    (name : Name) (buildSide : Bool) : Option SourceReplayAlias :=
  entries.foldl (init := none) fun best entry =>
    let rolePrefix := if buildSide then entry.build else entry.exact
    if rolePrefix.isPrefixOf name &&
        best.all (fun prior =>
          (if buildSide then prior.build else prior.exact).components.length <
            rolePrefix.components.length) then
      some entry
    else best

/-- Rewrite a name below an explicitly aliased source role.  This is used only
to register concrete generated names; record serialization still performs
whole-name table lookup. -/
def SourceReplayAliases.exactDerivedName (aliases : SourceReplayAliases) (build : Name) : Name :=
  match longestAliasPrefix? aliases.entries build true with
  | some entry => build.replacePrefix entry.build entry.exact
  | none => build

def SourceReplayAliases.buildDerivedName (aliases : SourceReplayAliases) (exact : Name) : Name :=
  match longestAliasPrefix? aliases.entries exact false with
  | some entry => exact.replacePrefix entry.exact entry.build
  | none => exact

/-- Every construction spelling induced by an explicit source-role prefix.
Reserved-name guards need all of them, not merely the longest match: an exact
source declaration can itself be moved while also lying below a moved owner. -/
def SourceReplayAliases.buildDerivedNames (aliases : SourceReplayAliases) (exact : Name) :
    Array Name :=
  aliases.entries.filterMap fun entry =>
    if entry.exact.isPrefixOf exact then some (exact.replacePrefix entry.exact entry.build)
    else none

/-- Remove construction-only source identities from a diagnostic string. -/
def SourceReplayAliases.exactMessage (aliases : SourceReplayAliases) (message : String) : String :=
  (aliases.entries.qsort fun left right =>
    left.build.components.length > right.build.components.length).foldl (fun message entry =>
    message.replace entry.build.toString entry.exact.toString) message

/-- Replace one source role while deriving the atomic kernel replay plan. -/
def SourceReplayAliases.replace (aliases : SourceReplayAliases) (exact build : Name) :
    Except String SourceReplayAliases :=
  SourceReplayAliases.ofEntries <|
    if aliases.entries.any (fun entry => entry.exact == exact) then
      aliases.entries.map fun entry => if entry.exact == exact then { exact, build } else entry
    else aliases.entries.push { exact, build }

/-- Register a newly discovered generated name without changing an existing
exact identity. Conflicting registrations fail closed. -/
def SourceReplayAliases.insert (aliases : SourceReplayAliases) (exact build : Name) :
    Except String SourceReplayAliases :=
  match aliases.build? exact with
  | some prior =>
    if prior == build then .ok aliases
    else .error s!"generated exact name {exact} maps to both {prior} and {build}"
  | none => SourceReplayAliases.ofEntries (aliases.entries.push { exact, build })

/-- Explicitly register every generated declaration name lying below a moved
source role. References are then covered because a valid generated record can
refer only to source constants or declarations introduced by its island. -/
def SourceReplayAliases.registerRecords (aliases : SourceReplayAliases)
    (records : Array EDecl) : Except String SourceReplayAliases := do
  let mut result := aliases
  for record in records do
    for build in record.names do
      let exact := aliases.exactDerivedName build
      if exact != build then
        result ← result.insert exact build
  return result

/-- Rename an exact source/output record into the collision-free replay view. -/
def SourceReplayAliases.buildRecord (aliases : SourceReplayAliases) : EDecl → EDecl :=
  EDecl.mapNames aliases.buildName
    (mapConstsE fun name => aliases.build? name)

/-- Return a generated build record to the exact source/output view. -/
def SourceReplayAliases.exactRecord (aliases : SourceReplayAliases) : EDecl → EDecl :=
  EDecl.mapNames aliases.exactName
    (mapConstsE fun name => aliases.exact? name)

/-- Generated-record audit transform for construction identities below an
aliased source role. Unlike `exactRecord`, this follows role prefixes and is
therefore deliberately confined to the post-generation release invariant. -/
def SourceReplayAliases.exactDerivedRecord (aliases : SourceReplayAliases) : EDecl → EDecl :=
  EDecl.mapNames aliases.exactDerivedName
    (mapConstsE fun name =>
      let exact := aliases.exactDerivedName name
      if exact == name then none else some exact)

/-- A whole export: the `meta` line verbatim, then the declarations in order. -/
structure Export where
  metaLine : Json
  decls : Array EDecl
  /-- **The nodes with an `Expr.proj` somewhere in their subtree**, when the
  reader was asked for them (`analyse`), and empty when it was not.

  This is here rather than in the consumer because it is **an arena property and
  the arena is only in scope during the read**. Computing it afterwards, over
  `Expr`s, needs a visited set spanning every distinct node in the file so that
  a shared subterm is not walked once per parent — and that set is enormous and
  almost entirely `false`: at ten million lines of Mathlib, 9,264,612 entries
  of which **90,765 (1.0 %) are `true`**. The reader instead computes the bit
  when each expression record arrives. Every child record precedes its parent,
  even when their numeric IDs are sparse or out of order, so the retained set
  contains only the 1 %.

  A consumer reads it as a **set membership and not a memo**: `e ∈ projNodes`
  is the whole query, there is nothing to fill in, and a node that is not in it
  is not in it. -/
  projNodes : Std.HashSet Expr := {}
  deriving Inhabited

/-- Declaration names are semantic export identities. The library parsers use
this validator by default; the CLI may defer it until after syntactic parsing
so a collision is reported as a rejected export rather than a parser crash. -/
def Export.validateUniqueDeclarationNames (x : Export) : Except String Unit := do
  let mut names : Std.HashSet Name := {}
  for declaration in x.decls do
    for name in declaration.names do
      if names.contains name then throw s!"duplicate declaration {name}"
      names := names.insert name

/-! ## Recovering primitive structure projections

The export format has no record for Lean's projection-function or structure
environment extensions.  What survives is the kernel object itself: a
projection declaration is an ordinary definition (or theorem/opaque
declaration for proof/unsafe fields) whose value is a lambda telescope ending
in `Expr.proj owner fieldIndex self`.

The view below retains exact raw names.  In particular, a private projection's
leading `_private` components are data, not a namespace convention to erase.
-/

/-- A primitive projection declaration recovered from its exported value. -/
structure EProjection where
  name : Name
  levelParams : List Name
  type : Expr
  value : Expr
  owner : Name
  fieldIndex : Nat
  /-- Number of lambdas in the exported projection value, including `self`. -/
  numArguments : Nat
  /-- The declaration-record position, retained for ordering tests/checks. -/
  declIndex : Nat
  deriving Inhabited, BEq

private partial def stripProjectionMData : Expr → Expr
  | .mdata _ body => stripProjectionMData body
  | expression => expression

private partial def projectionBody? (value : Expr) : Option (Name × Nat × Nat) :=
  let rec visit (expression : Expr) (numArguments : Nat) :=
    match stripProjectionMData expression with
    | .lam _ _ body _ => visit body (numArguments + 1)
    | .proj owner fieldIndex struct =>
      if stripProjectionMData struct == .bvar 0 && numArguments > 0 then
        some (owner, fieldIndex, numArguments)
      else
        none
    | _ => none
  visit value 0

/-- View one ordinary export record as a primitive projection declaration.

This intentionally recognizes the kernel expression, not a generated-name
suffix.  A declaration that is observationally the same primitive projection
has the same view; the export has discarded the elaborator extension that
could distinguish two such definitions. -/
def EDecl.projection? (declIndex : Nat) : EDecl → Option EProjection
  | .defn name levelParams type value .. |
    .thm name levelParams type value .. |
    .opaq name levelParams type value .. => do
      let (owner, fieldIndex, numArguments) ← projectionBody? value
      return { name, levelParams, type, value, owner, fieldIndex, numArguments, declIndex }
  | _ => none

/-- Whole-export projection prepass, in source declaration order. -/
def Export.projections (x : Export) : Array EProjection := Id.run do
  let mut projections := #[]
  for index in [0:x.decls.size] do
    if let some projection := x.decls[index]!.projection? index then
      projections := projections.push projection
  return projections

/-- Exact primitive projections whose kernel projection names `owner`. -/
def Export.projectionsFor (x : Export) (owner : Name) : Array EProjection :=
  x.projections.filter (·.owner == owner)

/-! ## Intrinsic projection eligibility

An `Expr.proj T j self` is not valid for every field of every structure-like
type.  In particular, when `T` is `Prop` the selected field must be a
proposition; and each earlier non-proof field on which the remaining telescope
depends also makes the projection invalid.  This is the literal field walk in
the kernel's `infer_proj`, expressed over export records so generation,
checking, and monomorphization enumerate the same slots without consulting a
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

/-! ## Reading -/

private def jField (j : Json) (k : String) : Except String Json :=
  j.getObjVal? k

private def jNat (j : Json) (k : String) : Except String Nat := do
  (← jField j k).getNat?

private def jStr (j : Json) (k : String) : Except String String := do
  (← jField j k).getStr?

private def jBool (j : Json) (k : String) : Except String Bool := do
  (← jField j k).getBool?

private def jArr (j : Json) (k : String) : Except String (Array Json) := do
  (← jField j k).getArr?

/-- Whether a top-level record has exactly these keys.  The Kernel Arena
parser dispatches on the complete top-level key set: extra keys and records
which combine two tags are malformed rather than partially recognized. -/
private def hasExactKeys (j : Json) (keys : List String) : Bool :=
  match j with
  | .obj fields =>
      let actual := fields.toList.map (·.1)
      actual.length == keys.length && keys.all actual.contains
  | _ => false

/-- A compact arena table with an exact sparse fallback.

The dense prefix is the common exporter case.  An out-of-order entry beyond
that prefix lives in `sparse`; when the missing boundary arrives, consecutive
sparse entries are absorbed into the prefix.  Thus an arbitrarily large
malicious ID allocates one hash entry rather than padding an array up to that
ID, while lookup still distinguishes an absent hole from an explicitly written
default-looking value. -/
structure ArenaTable (α : Type) where
  dense : Array α := #[]
  sparse : Std.HashMap Nat α := {}
  deriving Inhabited

namespace ArenaTable

def seed (value : α) : ArenaTable α :=
  { dense := #[value] }

def get? (table : ArenaTable α) (index : Nat) : Option α :=
  if h : index < table.dense.size then some table.dense[index]
  else table.sparse[index]?

private def absorb (dense : Array α) (sparse : Std.HashMap Nat α) : ArenaTable α := Id.run do
  let mut dense := dense
  let mut sparse := sparse
  let mut done := false
  while !done do
    match sparse[dense.size]? with
    | none => done := true
    | some value =>
      sparse := sparse.erase dense.size
      dense := dense.push value
  return { dense, sparse }

/-- Write one explicit arena ID. Repeated IDs overwrite, matching the export
parser used by the Lean Kernel Arena. -/
def set (table : ArenaTable α) (index : Nat) (value : α) : ArenaTable α :=
  if h : index < table.dense.size then
    { table with dense := table.dense.set index value }
  else if index == table.dense.size then
    absorb (table.dense.push value) (table.sparse.erase index)
  else
    { table with sparse := table.sparse.insert index value }

end ArenaTable

/-- The interning tables, grown line by line. -/
structure RCtx where
  names : ArenaTable Name := .seed .anonymous
  levels : ArenaTable Level := .seed .zero
  exprs : ArenaTable Expr := {}
  /-- Whether expression records are being classified for monomorphization. -/
  analyse : Bool := true
  projNodes : Std.HashSet Expr := {}
  deriving Inhabited

namespace RCtx

def name! (c : RCtx) (i : Nat) : Except String Name :=
  match c.names.get? i with
  | some name => .ok name
  | none => .error s!"name index {i} is not defined"

def level! (c : RCtx) (i : Nat) : Except String Level :=
  match c.levels.get? i with
  | some level => .ok level
  | none => .error s!"level index {i} is not defined"

def expr! (c : RCtx) (i : Nat) : Except String Expr :=
  match c.exprs.get? i with
  | some expression => .ok expression
  | none => .error s!"expr index {i} is not defined"

def nameF (c : RCtx) (j : Json) (k : String) : Except String Name := do c.name! (← jNat j k)
def exprF (c : RCtx) (j : Json) (k : String) : Except String Expr := do c.expr! (← jNat j k)

def nameL (c : RCtx) (j : Json) (k : String) : Except String (List Name) := do
  ((← jArr j k).toList.mapM fun x => do c.name! (← x.getNat?))

def levelL (c : RCtx) (j : Json) (k : String) : Except String (List Level) := do
  ((← jArr j k).toList.mapM fun x => do c.level! (← x.getNat?))

end RCtx

private def binderInfo : String → Except String BinderInfo
  | "default" => .ok .default
  | "implicit" => .ok .implicit
  | "strictImplicit" => .ok .strictImplicit
  | "instImplicit" => .ok .instImplicit
  | s => .error s!"unknown binderInfo {s}"

private def readCtor (c : RCtx) (j : Json) : Except String ECtor := do
  return {
    name := ← c.nameF j "name", levelParams := ← c.nameL j "levelParams"
    type := ← c.exprF j "type", cidx := ← jNat j "cidx"
    numParams := ← jNat j "numParams", numFields := ← jNat j "numFields"
    induct := ← c.nameF j "induct", isUnsafe := ← jBool j "isUnsafe" }

private def readRule (c : RCtx) (j : Json) : Except String ERecRule := do
  return { ctor := ← c.nameF j "ctor", nfields := ← jNat j "nfields", rhs := ← c.exprF j "rhs" }

private def readRec (c : RCtx) (j : Json) : Except String ERec := do
  return {
    name := ← c.nameF j "name", levelParams := ← c.nameL j "levelParams"
    type := ← c.exprF j "type", all := ← c.nameL j "all"
    numParams := ← jNat j "numParams", numIndices := ← jNat j "numIndices"
    numMotives := ← jNat j "numMotives", numMinors := ← jNat j "numMinors"
    rules := ← (← jArr j "rules").toList.mapM (readRule c)
    k := ← jBool j "k", isUnsafe := ← jBool j "isUnsafe" }

private def readIndType (c : RCtx) (j : Json) : Except String EIndType := do
  return {
    name := ← c.nameF j "name", levelParams := ← c.nameL j "levelParams"
    type := ← c.exprF j "type", all := ← c.nameL j "all"
    ctors := ← c.nameL j "ctors"
    numParams := ← jNat j "numParams", numIndices := ← jNat j "numIndices"
    numNested := ← jNat j "numNested", isRec := ← jBool j "isRec"
    isReflexive := ← jBool j "isReflexive", isUnsafe := ← jBool j "isUnsafe" }

private def readHints (j : Json) : Except String EHints :=
  match j with
  | .str "abbrev" => .ok .abbrev
  | .str "opaque" => .ok .opaque
  | o => do return .regular (← jNat o "regular")

/-- Whether an expression record contains a primitive projection.  Child
records have already been parsed, so membership in `known` replaces a recursive
walk and remains correct when arena IDs are sparse, out of order, or repeated. -/
private def containsProjection (known : Std.HashSet Expr) : Expr → Bool
  | .proj .. => true
  | .app function argument => known.contains function || known.contains argument
  | .lam _ type body _ | .forallE _ type body _ =>
      known.contains type || known.contains body
  | .letE _ type value body _ =>
      known.contains type || known.contains value || known.contains body
  | .mdata _ body => known.contains body
  | _ => false

/-- Read one line into the context, returning a declaration if the line was one. -/
def readLine (c : RCtx) (j : Json) : Except String (RCtx × Option EDecl) := do
  -- Name records.
  if hasExactKeys j ["in", "str"] then
    let i ← jNat j "in"
    let o ← jField j "str"
    let n := Name.str (← c.nameF o "pre") (← jStr o "str")
    return ({ c with names := c.names.set i n }, none)
  if hasExactKeys j ["in", "num"] then
    let i ← jNat j "in"
    let o ← jField j "num"
    let n := Name.num (← c.nameF o "pre") (← jNat o "i")
    return ({ c with names := c.names.set i n }, none)
  -- Level records.
  if hasExactKeys j ["il", "succ"] then
    let i ← jNat j "il"
    let l := Level.succ (← c.level! (← jNat j "succ"))
    return ({ c with levels := c.levels.set i l }, none)
  if hasExactKeys j ["il", "param"] then
    let i ← jNat j "il"
    let l := Level.param (← c.name! (← jNat j "param"))
    return ({ c with levels := c.levels.set i l }, none)
  if hasExactKeys j ["il", "max"] then
    let i ← jNat j "il"
    let #[left, right] ← jArr j "max" | .error "Level.max invalid"
    let l := Level.max (← c.level! (← left.getNat?)) (← c.level! (← right.getNat?))
    return ({ c with levels := c.levels.set i l }, none)
  if hasExactKeys j ["il", "imax"] then
    let i ← jNat j "il"
    let #[left, right] ← jArr j "imax" | .error "Level.imax invalid"
    let l := Level.imax (← c.level! (← left.getNat?)) (← c.level! (← right.getNat?))
    return ({ c with levels := c.levels.set i l }, none)
  -- Expression records.
  let expression? ←
    if hasExactKeys j ["ie", "bvar"] then
      pure <| some (Expr.bvar (← jNat j "bvar"))
    else if hasExactKeys j ["ie", "sort"] then
      pure <| some (Expr.sort (← c.level! (← jNat j "sort")))
    else if hasExactKeys j ["ie", "const"] then
      let o ← jField j "const"
      pure <| some <| Expr.const (← c.nameF o "name")
        (← (← (← o.getObjVal? "us").getArr?).toList.mapM fun x => do c.level! (← x.getNat?))
    else if hasExactKeys j ["ie", "app"] then
      let o ← jField j "app"
      pure <| some <| Expr.app (← c.exprF o "fn") (← c.exprF o "arg")
    else if hasExactKeys j ["ie", "lam"] then
      let o ← jField j "lam"
      pure <| some <| Expr.lam (← c.nameF o "name") (← c.exprF o "type") (← c.exprF o "body")
        (← binderInfo (← jStr o "binderInfo"))
    else if hasExactKeys j ["ie", "forallE"] then
      let o ← jField j "forallE"
      pure <| some <| Expr.forallE (← c.nameF o "name") (← c.exprF o "type") (← c.exprF o "body")
        (← binderInfo (← jStr o "binderInfo"))
    else if hasExactKeys j ["ie", "letE"] then
      let o ← jField j "letE"
      pure <| some <| Expr.letE (← c.nameF o "name") (← c.exprF o "type") (← c.exprF o "value")
        (← c.exprF o "body") (← jBool o "nondep")
    else if hasExactKeys j ["ie", "proj"] then
      let o ← jField j "proj"
      pure <| some <| Expr.proj (← c.nameF o "typeName") (← jNat o "idx") (← c.exprF o "struct")
    else if hasExactKeys j ["ie", "natVal"] then
      let value ← match (← jStr j "natVal").toNat? with
        | some value => pure value
        | none => .error "Expr.lit natVal invalid"
      pure <| some <| Expr.lit (.natVal value)
    else if hasExactKeys j ["ie", "strVal"] then
      pure <| some <| Expr.lit (.strVal (← jStr j "strVal"))
    else if hasExactKeys j ["ie", "mdata"] then
      let o ← jField j "mdata"
      match ← jField o "data" with
      | .obj _ => pure <| some <| Expr.mdata {} (← c.exprF o "expr")
      | _ => .error "Expr.mdata invalid"
    else pure none
  if let some e := expression? then
    let i ← jNat j "ie"
    let projNodes :=
      if c.analyse && containsProjection c.projNodes e then c.projNodes.insert e
      else c.projNodes
    return ({ c with exprs := c.exprs.set i e, projNodes }, none)
  -- Declaration records.
  if hasExactKeys j ["axiom"] then
    let o ← jField j "axiom"
    return (c, some <| .ax (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") (← jBool o "isUnsafe"))
  if hasExactKeys j ["def"] then
    let o ← jField j "def"
    let safety ← jStr o "safety"
    unless (safetyOf? safety).isSome do
      throw s!"unknown definition safety {safety}"
    return (c, some <| .defn (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") (← c.exprF o "value") (← readHints (← jField o "hints"))
      safety (← c.nameL o "all"))
  if hasExactKeys j ["thm"] then
    let o ← jField j "thm"
    return (c, some <| .thm (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") (← c.exprF o "value") (← c.nameL o "all"))
  if hasExactKeys j ["opaque"] then
    let o ← jField j "opaque"
    let isUnsafe ← match (jField o "isUnsafe").toOption with
      | none => pure false
      | some value => value.getBool?
    return (c, some <| .opaq (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") (← c.exprF o "value") isUnsafe (← c.nameL o "all"))
  if hasExactKeys j ["quot"] then
    let o ← jField j "quot"
    let kind ← jStr o "kind"
    unless (quotKindOf? kind).isSome do throw s!"unknown quotient kind {kind}"
    return (c, some <| .quot (← c.nameF o "name") (← c.nameL o "levelParams")
      (← c.exprF o "type") kind)
  if hasExactKeys j ["inductive"] then
    let o ← jField j "inductive"
    return (c, some <| .induct
      (← (← jArr o "types").toList.mapM (readIndType c))
      (← (← jArr o "ctors").toList.mapM (readCtor c))
      (← (← jArr o "recs").toList.mapM (readRec c)))
  .error s!"unrecognised record: {j.compress}"

/-- Complete name/level/expression tables sufficient to decode declaration
records in any order.  The context is opaque so callers cannot mutate or
observe parser implementation tables. -/
structure DeclarationArena where private context : RCtx

/-- Decode one exact declaration-spool record against a completed arena.  A
span must contain exactly one UTF-8 JSON declaration and its terminating LF;
arena or metadata records fail closed. -/
def DeclarationArena.decode (arena : DeclarationArena)
    (bytes : ByteArray) : Except String EDecl := do
  unless !bytes.isEmpty && bytes[bytes.size - 1]! == 10 do
    throw "declaration span is not LF-terminated"
  let some line := String.fromUTF8? (bytes.extract 0 (bytes.size - 1))
    | throw "declaration span is not valid UTF-8"
  if line.isEmpty || line.contains '\n' || line.contains '\r' then
    throw "declaration span does not contain exactly one canonical line"
  let json ← Json.parse line
  let (_, declaration?) ← readLine arena.context json
  let some declaration := declaration?
    | throw "declaration span decoded as an arena record"
  return declaration

/-- Build the random-decode arena from an arena-only stream using the same
bounded chunk/UTF-8 boundary discipline as the full streaming parser.  This
retains the completed interning tables, but no declaration value. -/
def DeclarationArena.ofStream (stream : IO.FS.Stream) : IO (Except String DeclarationArena) := do
  let context ← IO.mkRef ({ analyse := false } : RCtx)
  let mut carry : ByteArray := .empty
  let mut eof := false
  let mut err : Option String := none
  while !eof && err.isNone do
    let chunk ← stream.read 4194304
    if chunk.size == 0 then eof := true
    let block := if carry.isEmpty then chunk else carry ++ chunk
    let mut cut := block.size
    if !eof then
      cut := 0
      let mut i := block.size
      while i > 0 && cut == 0 do
        i := i - 1
        if block[i]! == 10 then cut := i + 1
      if cut == 0 then
        carry := block
        continue
    carry := block.extract cut block.size
    match String.fromUTF8? (block.extract 0 cut) with
    | none => err := some "the declaration arena is not valid UTF-8"
    | some text =>
      let lines := (text.splitOn "\n").toArray
      for lineIndex in [:lines.size] do
        let line := lines[lineIndex]!
        if line.isEmpty then continue
        match Json.parse line with
        | .error error => err := some error; break
        | .ok json =>
          match ← context.modifyGet fun current =>
              match readLine current json with
              | .error error => (Except.error error, ({} : RCtx))
              | .ok (_, some _) =>
                  (Except.error "declaration record found in arena spool", ({} : RCtx))
              | .ok (next, none) => (Except.ok (), next) with
          | .error error => err := some error; break
          | .ok () => pure ()
  match err with
  | some error => return .error error
  | none =>
    let completed ← context.modifyGet fun current => (current, {})
    return .ok { context := completed }

/-- Handle-specialized completed-arena loader. -/
def DeclarationArena.ofHandle (handle : IO.FS.Handle) : IO (Except String DeclarationArena) :=
  DeclarationArena.ofStream (IO.FS.Stream.ofHandle handle)

/-- Parse a whole export.

`analyse` fills [`Export.projNodes`] and **defaults to on**, because an empty
`projNodes` reads as "no declaration contains a projection" and a consumer that
believed it would emit wrong output silently. A caller that does not look at the
field can turn it off; `monomorphize` refuses a file whose projections it can
see but whose `projNodes` is empty, so the two cannot disagree unnoticed. -/
def parse (text : String) (analyse : Bool := true) : Except String Export := do
  let mut c : RCtx := { analyse }
  let mut decls : Array EDecl := #[]
  let mut metaLine : Json := .null
  let mut first := true
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    let j ← Json.parse line
    if first then
      first := false
      if (jField j "meta").toOption.isSome then
        metaLine := j
        continue
    let (c', d?) ← readLine c j
    c := c'
    if let some d := d? then decls := decls.push d
  let resultExport : Export := { metaLine, decls, projNodes := c.projNodes }
  resultExport.validateUniqueDeclarationNames
  return resultExport

/-! ## Optional raw source capture during streaming parse

The parser may hand each exact UTF-8 record to a transient sink while it is
already in scope.  This is deliberately an optional side channel: ordinary
parsing retains its old result and does no spool allocation. Planned input
replay may use the certified source spool without reopening a mutable path.
-/

/-- Which logical spool consumes one exact input record.  `ignored` covers
blank lines; accepting them remains parser-compatible, but they disqualify the
strict raw-arena fast path. -/
inductive RawRecordKind where
  | metadata | arena | declaration | ignored
  deriving Inhabited, Repr, BEq

/-- A transient exact line, including its original LF when present.  Sinks
must consume `bytes` during the call rather than retaining the parser chunk. -/
structure RawRecord where
  kind : RawRecordKind
  bytes : ByteArray

/-- Optional parse-time consumer for exact raw records. -/
structure RawSink where
  emit : RawRecord → IO Unit

/-- A declaration callback sharing the parser's exact `readLine` result.  The
callback must consume the value during `emit`: discard-mode parsing does not
retain declaration records after the call returns. -/
structure DeclarationSink where
  emit : EDecl → IO Unit

/-- The whole-input facts which survive declaration-discarding parsing.  The
arena itself is owned by the raw tee/`PlannedSourceReader`; this envelope owns
only metadata, projection facts, and cardinality. -/
structure ParsedEnvelope where
  metaLine : Json := .null
  projNodes : Std.HashSet Expr := {}
  declarationCount : Nat := 0
  /-- Observable retention contract for regression tests. -/
  retainedDeclarations : Nat := 0
  deriving Inhabited

def ParsedEnvelope.template (envelope : ParsedEnvelope) : Export :=
  { metaLine := envelope.metaLine, decls := #[], projNodes := envelope.projNodes }

/-- A compact byte span in the declaration-only spool. Both coordinates are
fixed-width and every conversion/addition is checked before publication. -/
structure RawSpan where
  offset : UInt64
  bytes : UInt64
  deriving Inhabited, Repr, BEq

def RawSpan.end? (span : RawSpan) : Option UInt64 :=
  if span.offset.toNat + span.bytes.toNat < UInt64.size then
    some (span.offset + span.bytes)
  else none

/-- Exclusive upper bounds of a strictly progressive input arena. -/
structure RawArenaCursor where
  nextName : Nat := 1
  nextLevel : Nat := 1
  nextExpr : Nat := 0
  deriving Inhabited, Repr, BEq

/-- Certification and compact offsets produced beside a raw spool.

`canonical` is intentionally stronger than parser acceptance: every nonempty
record has canonical compressed JSON spelling and a terminating LF, and name,
level, and expression IDs progress exactly `1,2,…`, `1,2,…`, and `0,1,…`.
Sparse, repeated, or out-of-order arenas therefore fall back to full
re-interning instead of changing the snapshot seen by an earlier declaration.

This is evidence about the input byte stream, not an output backend. Planned
source replay additionally validates every span against the finished spool
size before reading declarations by index.
-/
structure RawCertificate where
  canonical : Bool := true
  cursor : RawArenaCursor := {}
  metadataBytes : UInt64 := 0
  arenaBytes : UInt64 := 0
  declarationBytes : UInt64 := 0
  declarations : Array RawSpan := #[]
  deriving Inhabited, Repr, BEq

/-- Actual sizes of the three completed logical spool files. -/
structure RawSpoolSizes where
  metadata : UInt64
  arena : UInt64
  declarations : UInt64
  deriving Inhabited, Repr, BEq

/-- Validate completed spool totals and the exact declaration partition.  This
is sufficient for random declaration decoding even when a parser-compatible
sparse/repeated arena is ineligible for raw output composition. -/
def RawCertificate.validateDeclarationSpans (certificate : RawCertificate)
    (sizes : RawSpoolSizes) (declarationCount : Nat) : Except String Unit := do
  let expectedSizes : RawSpoolSizes :=
    { metadata := certificate.metadataBytes
      arena := certificate.arenaBytes
      declarations := certificate.declarationBytes }
  unless sizes == expectedSizes do
    throw "raw spool sizes do not match the parser certificate"
  unless certificate.declarations.size == declarationCount do
    throw "raw declaration span count does not match the parsed declarations"
  let mut endpoint : UInt64 := 0
  for span in certificate.declarations do
    unless span.offset == endpoint do
      throw "raw declaration spans are not contiguous"
    let some next := span.end?
      | throw "raw declaration span endpoint overflows UInt64"
    endpoint := next
  unless endpoint == sizes.declarations do
    throw "raw declaration spans do not cover the completed spool"

/-- Validate all persistent offsets and canonical arena evidence before any
raw composition may consume them. -/
def RawCertificate.validate (certificate : RawCertificate) (sizes : RawSpoolSizes)
    (declarationCount : Nat) : Except String RawArenaCursor := do
  unless certificate.canonical do throw "raw input is not canonical"
  certificate.validateDeclarationSpans sizes declarationCount
  return certificate.cursor

private structure RawCertState where
  certificate : RawCertificate := {}

private def addUInt64Bytes (current : UInt64) (bytes : Nat) : UInt64 × Bool :=
  if bytes < UInt64.size && current.toNat ≤ UInt64.size - 1 - bytes then
    (current + bytes.toUInt64, true)
  else
    (current, false)

private def exactRawBytes (line : String) (terminated : Bool) : ByteArray :=
  if terminated then line.toUTF8.push 10 else line.toUTF8

/-- Recognize the whitespace-free JSON spelling emitted by lean4export and
`Writer` without depending on `Json.compress`'s hash-map iteration order.
Object key order is semantically irrelevant and may change when unrelated
imports perturb compiled hash-map layout; whitespace outside strings is the
only spelling freedom which would make the raw line non-compressed.  The line
has already parsed as JSON, so quote/escape well-formedness is not rechecked
here. -/
private def compressedJsonSpelling (line : String) : Bool :=
  let rec loop (chars : List Char) (inString escaped : Bool) : Bool :=
    match chars with
    | [] => !inString && !escaped
    | char :: rest =>
      if inString then
        if escaped then loop rest true false
        else if char == '\\' then loop rest true true
        else if char == '"' then loop rest false false
        else loop rest true false
      else if char == '"' then loop rest true false
      else if char == ' ' || char == '\t' || char == '\r' || char == '\n' then false
      else loop rest false false
  loop line.toList false false

private inductive RawArenaAxis where
  | name | level | expression

private def rawArenaId? (j : Json) : Option (RawArenaAxis × Nat) :=
  if let some id := (jField j "in").toOption.bind fun value => value.getNat?.toOption then
    some (.name, id)
  else if let some id := (jField j "il").toOption.bind fun value => value.getNat?.toOption then
    some (.level, id)
  else if let some id := (jField j "ie").toOption.bind fun value => value.getNat?.toOption then
    some (.expression, id)
  else none

private def RawCertState.addBytes (state : RawCertState) (kind : RawRecordKind)
    (bytes : Nat) : RawCertState :=
  match kind with
  | .metadata =>
      let (total, valid) := addUInt64Bytes state.certificate.metadataBytes bytes
      { state with certificate := { state.certificate with
          canonical := state.certificate.canonical && valid, metadataBytes := total } }
  | .arena =>
      let (total, valid) := addUInt64Bytes state.certificate.arenaBytes bytes
      { state with certificate := { state.certificate with
          canonical := state.certificate.canonical && valid, arenaBytes := total } }
  | .declaration =>
      let (total, validTotal) := addUInt64Bytes state.certificate.declarationBytes bytes
      let validLength := bytes < UInt64.size
      { certificate := { state.certificate with
          canonical := state.certificate.canonical && validTotal && validLength
          declarationBytes := total
          declarations := state.certificate.declarations.push
            { offset := state.certificate.declarationBytes,
              bytes := if validLength then bytes.toUInt64 else 0 } } }
  | .ignored => state

private def RawCertState.observeArena (state : RawCertState) (j : Json) : RawCertState :=
  match rawArenaId? j with
  | some (.name, id) =>
      { state with certificate := { state.certificate with
          canonical := state.certificate.canonical && id == state.certificate.cursor.nextName
          cursor.nextName := state.certificate.cursor.nextName + 1 } }
  | some (.level, id) =>
      { state with certificate := { state.certificate with
          canonical := state.certificate.canonical && id == state.certificate.cursor.nextLevel
          cursor.nextLevel := state.certificate.cursor.nextLevel + 1 } }
  | some (.expression, id) =>
      { state with certificate := { state.certificate with
          -- The ordinary writer erases expression metadata, so a raw source
          -- containing `mdata` is not yet eligible for mixed raw/generated
          -- composition even when its IDs are dense.
          canonical := state.certificate.canonical &&
            (jField j "mdata").toOption.isNone &&
            id == state.certificate.cursor.nextExpr
          cursor.nextExpr := state.certificate.cursor.nextExpr + 1 } }
  | _ => { state with certificate.canonical := false }

private def emitRaw (sink : RawSink) (state : IO.Ref RawCertState)
    (kind : RawRecordKind) (line : String) (terminated : Bool)
    (json? : Option Json := none) : IO Unit := do
  let bytes := exactRawBytes line terminated
  sink.emit { kind, bytes }
  state.modify fun current =>
    let current := current.addBytes kind bytes.size
    let spelling := terminated && json?.isSome && compressedJsonSpelling line
    let current := { current with certificate.canonical :=
      current.certificate.canonical && spelling }
    if kind == .arena then json?.elim current current.observeArena else current

/-- **The same parse, off a handle, a chunk at a time.**

[`parse`] takes the file as one `String`, and on a large export that costs more
than everything it builds. Measured on a 512 MiB prefix of the Mathlib export,
`IO.FS.readFile` peaks at **2× the file** — the
`ByteArray` and the `String` `String.fromUTF8?` copies out of it are live
together, and the `ByteArray` is one large block the small-object allocator
cannot reuse afterwards — and `text.splitOn "\n"` then materialises **every line
of the file** as a live list, 124 bytes a line, before the first one is read.
Those two reach the parse's whole high-water mark **before a single JSON object
is parsed**; adding the JSON costs 0 and building the whole `Export` costs
0.13 % more, because both fit inside what the reader had already taken.

This reads 4 MiB at a time and holds one chunk's lines, and it is not a
different parser: the line handling is [`readLine`]'s, untouched, and the output
is byte-identical on `init-prelude` and on 20 MB, 1 M and 10 M of Mathlib. On
the 10-million-line prefix it takes the parse's peak from 2,381,888 KB to
**618,580 KB** and the whole pass's from 3,083,532 KB to **2,170,272 KB**, for
**1.3 % fewer instructions**. `Handle.getLine` is not the route: it did not
finish a 1-million-line prefix in ten minutes.
-/
private def parseStreamCore (h : IO.FS.Stream) (analyse : Bool)
    (sink? : Option RawSink) (declarationSink? : Option DeclarationSink)
    (retainDeclarations allowDuplicateNames : Bool) :
    IO (Except String (Export × RawCertificate × Nat)) := do
  -- **One ref per growing array, and `modifyGet`.** `RCtx` holds three arrays
  -- that grow by `push`, and a `push` is in-place only while the array is
  -- uniquely referenced. Two shapes lose that and both were measured on a 20 MB
  -- input, against **0.49 s** for the whole pass:
  --   * threading `RCtx` as a `mut` through a `for` nested in a `while` — the
  --     outer loop's state keeps a second reference: **78.8 s**;
  --   * holding it in a record and writing `{ st with c := c' }` — the
  --     projection reads the field while the record still holds it: **79.5 s**.
  -- `modifyGet` takes the value out of the ref, so what `readLine` is handed is
  -- the only reference to it.
  let cRef ← IO.mkRef ({ analyse } : RCtx)
  let declsRef ← IO.mkRef (#[] : Array EDecl)
  let declarationCountRef ← IO.mkRef 0
  let declarationNamesRef ← IO.mkRef ({} : Std.HashSet Name)
  let duplicateRef ← IO.mkRef (none : Option Name)
  let rawRef ← IO.mkRef ({} : RawCertState)
  let mut metaLine : Json := .null
  let mut first := true
  let mut err : Option String := none
  -- The tail of the last chunk, past its final newline: an incomplete line, and
  -- the only thing carried between chunks.
  let mut carry : ByteArray := .empty
  let mut eof := false
  while !eof && err.isNone do
    let chunk ← h.read 4194304
    if chunk.size == 0 then eof := true
    let block := if carry.isEmpty then chunk else carry ++ chunk
    -- Cut at the last newline: only there is the byte boundary guaranteed not
    -- to fall inside a character, so only there can the prefix be decoded.
    let mut cut := block.size
    if !eof then
      cut := 0
      let mut i := block.size
      while i > 0 && cut == 0 do
        i := i - 1
        if block[i]! == 10 then cut := i + 1
      if cut == 0 then
        -- No newline in a whole chunk: keep reading rather than guess.
        carry := block
        continue
    carry := block.extract cut block.size
    match String.fromUTF8? (block.extract 0 cut) with
    | none => err := some "the input is not valid UTF-8"
    | some text =>
      let lines := (text.splitOn "\n").toArray
      for hline : lineIndex in [:lines.size] do
        let line := lines[lineIndex]
        let terminated := lineIndex + 1 < lines.size
        -- `splitOn` leaves one empty sentinel after a final LF.  Other empty
        -- lines remain accepted by the historical parser but disqualify raw
        -- canonical source capture and are handed to the sink exactly.
        if line.isEmpty then
          if terminated then
            if let some sink := sink? then
              emitRaw sink rawRef .ignored line true
          continue
        match Json.parse line with
        | .error e => err := some e; break
        | .ok j =>
          if first then
            first := false
            if (jField j "meta").toOption.isSome then
              metaLine := j
              if let some sink := sink? then
                emitRaw sink rawRef .metadata line terminated (some j)
              continue
          match ← cRef.modifyGet fun c =>
              match readLine c j with
              -- **`{}`, not `c`.** Putting `c` back in the failure arm keeps it
              -- alive across `readLine`, so the arrays it pushes to are at
              -- refcount two and every push reallocates. The parse is over when
              -- this arm fires, so the context is dead either way.
              | .error e => (Except.error e, ({} : RCtx))
              | .ok (c', d?) => (Except.ok d?, c') with
          | .error e => err := some e; break
          | .ok d? =>
            if let some sink := sink? then
              emitRaw sink rawRef (if d?.isSome then .declaration else .arena)
                line terminated (some j)
            if let some d := d? then
              declarationCountRef.modify (· + 1)
              -- Match `Export.validateUniqueDeclarationNames`: remember the
              -- first collision, but report it only after the complete parse
              -- so a later syntax/arena error retains historical precedence.
              unless retainDeclarations do
                for name in d.names do
                  let already ← declarationNamesRef.modifyGet fun names =>
                    (names.contains name, names.insert name)
                  if already then
                    duplicateRef.modify fun duplicate => duplicate.orElse (fun _ => some name)
              if let some declarationSink := declarationSink? then
                declarationSink.emit d
              if retainDeclarations then declsRef.modify (·.push d)
  match err with
  | some e => return .error e
  | none =>
    let decls ← declsRef.get
    -- Take the result out while dropping every arena table held by the ref.
    let projNodes ← cRef.modifyGet fun c => (c.projNodes, {})
    let rawState ← rawRef.get
    let declarationCount ← declarationCountRef.get
    let certificate := if sink?.isSome then rawState.certificate else {}
    let resultExport := { metaLine, decls, projNodes }
    unless allowDuplicateNames do
      if retainDeclarations then
        if let .error message := resultExport.validateUniqueDeclarationNames then
          return .error message
      else if let some name ← duplicateRef.get then
          return .error s!"duplicate declaration {name}"
    return .ok (resultExport, certificate, declarationCount)

/-- Parse while sending exact input records to `sink`. The compact returned
certificate is necessary but not sufficient for a later raw-hoist fast path;
a false certificate unconditionally requires the ordinary writer. -/
def parseStreamWithSink (h : IO.FS.Stream) (sink : RawSink)
    (analyse : Bool := true) (allowDuplicateNames : Bool := false) :
    IO (Except String (Export × RawCertificate)) := do
  return (← parseStreamCore h analyse (some sink) none true allowDuplicateNames).map
    fun (parsed, certificate, _) => (parsed, certificate)

/-- Parse and certify the exact stream while delivering each decoded
declaration to one callback instead of retaining a whole `Export.decls`.
The callback and raw sink observe the same successful `readLine` transition;
there is no second JSON or arena pass. -/
def parseStreamDiscardingDeclarations (h : IO.FS.Stream) (rawSink : RawSink)
    (declarationSink : DeclarationSink) (analyse : Bool := true)
    (allowDuplicateNames : Bool := false) :
    IO (Except String (ParsedEnvelope × RawCertificate)) := do
  return (← parseStreamCore h analyse (some rawSink) (some declarationSink)
    false allowDuplicateNames).map fun (parsed, certificate, declarationCount) =>
      ({ metaLine := parsed.metaLine, projNodes := parsed.projNodes,
         declarationCount, retainedDeclarations := parsed.decls.size }, certificate)

def parseStream (h : IO.FS.Stream) (analyse : Bool := true)
    (allowDuplicateNames : Bool := false) : IO (Except String Export) := do
  return (← parseStreamCore h analyse none none true allowDuplicateNames).map (·.1)

/-- Handle-specialized wrapper around [`parseStream`]. -/
def parseHandle (h : IO.FS.Handle) (analyse : Bool := true)
    (allowDuplicateNames : Bool := false) : IO (Except String Export) :=
  parseStream (IO.FS.Stream.ofHandle h) analyse allowDuplicateNames

/-- Handle-specialized raw-source-capture parser. -/
def parseHandleWithSink (h : IO.FS.Handle) (sink : RawSink)
    (analyse : Bool := true) (allowDuplicateNames : Bool := false) :
    IO (Except String (Export × RawCertificate)) :=
  parseStreamWithSink (IO.FS.Stream.ofHandle h) sink analyse allowDuplicateNames

/-- Handle-specialized declaration-discarding parser. -/
def parseHandleDiscardingDeclarations (h : IO.FS.Handle) (rawSink : RawSink)
    (declarationSink : DeclarationSink) (analyse : Bool := true)
    (allowDuplicateNames : Bool := false) :
    IO (Except String (ParsedEnvelope × RawCertificate)) :=
  parseStreamDiscardingDeclarations (IO.FS.Stream.ofHandle h) rawSink declarationSink
    analyse allowDuplicateNames

/-- Lowercase hexadecimal encoding used for random spool leaf names. Exposed
so the secure workspace tests can pin the entropy-preserving representation. -/
def rawSpoolSuffixOfBytes (bytes : ByteArray) : String :=
  bytes.foldl (fun suffix byte =>
    let value := byte.toNat
    suffix ++ hexDigitRepr (value / 16) ++ hexDigitRepr (value % 16)) ""

/-! ## Writing

Fresh dense interning, in dependency order, with the same key order and spacing
the exporter uses. A canonical exporter file which the tool does not change is
therefore byte-identical; other valid arena layouts and JSON formatting are
normalized.

**The writer streams.** [`Writer.out`] holds the lines of **one record** and is
drained after each; it is never the whole file. That is not a micro-optimisation
but the difference between finishing and not: on Mathlib the pass emits ~110
million lines, and an `Array String` of them intercalated into one ~6 GB
`String` was measured dying at 44.9 GB *after* the whole
computation had succeeded.

[`Export.stream`] is the one fold; [`Export.render`] and [`Export.writeTo`] are
its two consumers, which is what keeps them byte-identical rather than merely
intended to be.
-/

structure Writer where
  /-- The lines of the record being written. Drained by [`Export.stream`] after
  each record — do not accumulate a file here. -/
  out : Array String := #[]
  names : Std.HashMap Name Nat := Std.HashMap.emptyWithCapacity 1024 |>.insert .anonymous 0
  levels : Std.HashMap Level Nat := Std.HashMap.emptyWithCapacity 64 |>.insert .zero 0
  exprs : Std.HashMap Expr Nat := Std.HashMap.emptyWithCapacity 4096
  /-- The next arena IDs.  They are counters rather than table sizes so a
  fresh island-local writer can continue after an earlier island while
  deliberately forgetting its structural interning tables. -/
  nextName : Nat := 1
  nextLevel : Nat := 1
  nextExpr : Nat := 0
  deriving Inhabited

namespace Writer

/-- The exclusive upper bounds of the three independent export arenas. -/
structure Cursor where
  nextName : Nat := 1
  nextLevel : Nat := 1
  nextExpr : Nat := 0
  deriving Inhabited, Repr, BEq

/-- Exact handoff from a validated raw input arena to a generated writer. No
table size or inferred count is substituted for the certified next IDs. -/
def Cursor.ofRaw (cursor : RawArenaCursor) : Cursor :=
  { nextName := cursor.nextName, nextLevel := cursor.nextLevel,
    nextExpr := cursor.nextExpr }

/-- Start a structurally fresh writer at explicit, non-overlapping arena IDs.
Only the format's distinguished anonymous name and zero level remain shared
at index zero.  Equal nontrivial nodes written by another island are therefore
allowed to receive fresh IDs. -/
def fromCursor (cursor : Cursor) : Writer :=
  { nextName := cursor.nextName, nextLevel := cursor.nextLevel,
    nextExpr := cursor.nextExpr }

def cursor (w : Writer) : Cursor :=
  { nextName := w.nextName, nextLevel := w.nextLevel, nextExpr := w.nextExpr }

private def esc (s : String) : String := (Json.str s).compress

private def push (w : Writer) (line : String) : Writer := { w with out := w.out.push line }

partial def name (w : Writer) (n : Name) : Writer × Nat :=
  match w.names[n]? with
  | some i => (w, i)
  | none =>
    match n with
    | .anonymous => (w, 0)
    | .str p s =>
      let (w, pi) := w.name p
      let i := w.nextName
      let w := (w.push s!"\{\"in\":{i},\"str\":\{\"pre\":{pi},\"str\":{esc s}}}")
      ({ w with names := w.names.insert n i, nextName := i + 1 }, i)
    | .num p k =>
      let (w, pi) := w.name p
      let i := w.nextName
      let w := (w.push s!"\{\"in\":{i},\"num\":\{\"i\":{k},\"pre\":{pi}}}")
      ({ w with names := w.names.insert n i, nextName := i + 1 }, i)

partial def level (w : Writer) (l : Level) : Writer × Nat :=
  match w.levels[l]? with
  | some i => (w, i)
  | none =>
    let (w, body) :=
      match l with
      | .zero => (w, "")  -- unreachable: seeded at 0
      | .succ a => let (w, ai) := w.level a; (w, s!"\"succ\":{ai}")
      | .param p => let (w, pi) := w.name p; (w, s!"\"param\":{pi}")
      | .max a b =>
        let (w, ai) := w.level a
        let (w, bi) := w.level b
        (w, s!"\"max\":[{ai},{bi}]")
      | .imax a b =>
        let (w, ai) := w.level a
        let (w, bi) := w.level b
        (w, s!"\"imax\":[{ai},{bi}]")
      | .mvar _ => (w, "\"param\":0")  -- cannot occur in an export
    let i := w.nextLevel
    let w := w.push s!"\{\"il\":{i},{body}}"
    ({ w with levels := w.levels.insert l i, nextLevel := i + 1 }, i)

private def levelsJ (w : Writer) (ls : List Level) : Writer × String :=
  let (w, idxs) := ls.foldl (fun (w, acc) l => let (w, i) := w.level l; (w, acc.push i)) (w, #[])
  (w, "[" ++ String.intercalate "," (idxs.toList.map toString) ++ "]")

private def namesJ (w : Writer) (ns : List Name) : Writer × String :=
  let (w, idxs) := ns.foldl (fun (w, acc) n => let (w, i) := w.name n; (w, acc.push i)) (w, #[])
  (w, "[" ++ String.intercalate "," (idxs.toList.map toString) ++ "]")

private def binderStr : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

partial def expr (w : Writer) (e : Expr) : Writer × Nat :=
  match w.exprs[e]? with
  | some i => (w, i)
  | none =>
    if let .mdata _ b := e then w.expr b else
    let (w, body) :=
      match e with
      | .bvar k => (w, s!"\"bvar\":{k}")
      | .sort l => let (w, li) := w.level l; (w, s!"\"sort\":{li}")
      | .const n us =>
        let (w, ni) := w.name n
        let (w, uj) := w.levelsJ us
        (w, s!"\"const\":\{\"name\":{ni},\"us\":{uj}}")
      | .app f a =>
        let (w, fi) := w.expr f
        let (w, ai) := w.expr a
        (w, s!"\"app\":\{\"arg\":{ai},\"fn\":{fi}}")
      | .lam n t b bi =>
        let (w, ni) := w.name n
        let (w, ti) := w.expr t
        let (w, bd) := w.expr b
        (w, s!"\"lam\":\{\"binderInfo\":\"{binderStr bi}\",\"body\":{bd},\"name\":{ni},\"type\":{ti}}")
      | .forallE n t b bi =>
        let (w, ni) := w.name n
        let (w, ti) := w.expr t
        let (w, bd) := w.expr b
        (w, s!"\"forallE\":\{\"binderInfo\":\"{binderStr bi}\",\"body\":{bd},\"name\":{ni},\"type\":{ti}}")
      | .letE n t v b nd =>
        let (w, ni) := w.name n
        let (w, ti) := w.expr t
        let (w, vi) := w.expr v
        let (w, bd) := w.expr b
        (w, s!"\"letE\":\{\"body\":{bd},\"name\":{ni},\"nondep\":{nd},\"type\":{ti},\"value\":{vi}}")
      | .proj tn k s =>
        let (w, ti) := w.name tn
        let (w, si) := w.expr s
        (w, s!"\"proj\":\{\"idx\":{k},\"struct\":{si},\"typeName\":{ti}}")
      | .lit (.natVal k) => (w, s!"\"natVal\":\"{k}\"")
      | .lit (.strVal s) => (w, s!"\"strVal\":{esc s}")
      | _ => (w, "\"bvar\":0")  -- mdata/fvar/mvar cannot occur in an export
    let i := w.nextExpr
    let w := w.push s!"\{\"ie\":{i},{body}}"
    ({ w with exprs := w.exprs.insert e i, nextExpr := i + 1 }, i)

private def hintsJ : EHints → String
  | .abbrev => "\"abbrev\""
  | .opaque => "\"opaque\""
  | .regular h => s!"\{\"regular\":{h}}"

private def ctorJ (w : Writer) (c : ECtor) : Writer × String :=
  let (w, ni) := w.name c.name
  let (w, lp) := w.namesJ c.levelParams
  let (w, ti) := w.expr c.type
  let (w, ii) := w.name c.induct
  (w, s!"\{\"cidx\":{c.cidx},\"induct\":{ii},\"isUnsafe\":{c.isUnsafe},\"levelParams\":{lp},\
       \"name\":{ni},\"numFields\":{c.numFields},\"numParams\":{c.numParams},\"type\":{ti}}")

private def ruleJ (w : Writer) (r : ERecRule) : Writer × String :=
  let (w, ci) := w.name r.ctor
  let (w, ri) := w.expr r.rhs
  (w, s!"\{\"ctor\":{ci},\"nfields\":{r.nfields},\"rhs\":{ri}}")

private def recJ (w : Writer) (r : ERec) : Writer × String :=
  let (w, al) := w.namesJ r.all
  let (w, lp) := w.namesJ r.levelParams
  let (w, ni) := w.name r.name
  let (w, rules) :=
    r.rules.foldl (fun (w, acc) x => let (w, s) := w.ruleJ x; (w, acc.push s)) (w, #[])
  let (w, ti) := w.expr r.type
  (w, s!"\{\"all\":{al},\"isUnsafe\":{r.isUnsafe},\"k\":{r.k},\"levelParams\":{lp},\
       \"name\":{ni},\"numIndices\":{r.numIndices},\"numMinors\":{r.numMinors},\
       \"numMotives\":{r.numMotives},\"numParams\":{r.numParams},\
       \"rules\":[{String.intercalate "," rules.toList}],\"type\":{ti}}")

private def indTypeJ (w : Writer) (t : EIndType) : Writer × String :=
  let (w, al) := w.namesJ t.all
  let (w, cs) := w.namesJ t.ctors
  let (w, lp) := w.namesJ t.levelParams
  let (w, ni) := w.name t.name
  let (w, ti) := w.expr t.type
  (w, s!"\{\"all\":{al},\"ctors\":{cs},\"isRec\":{t.isRec},\"isReflexive\":{t.isReflexive},\
       \"isUnsafe\":{t.isUnsafe},\"levelParams\":{lp},\"name\":{ni},\"numIndices\":{t.numIndices},\
       \"numNested\":{t.numNested},\"numParams\":{t.numParams},\"type\":{ti}}")

/-- Emit one declaration, interning everything it names first. -/
def decl (w : Writer) (d : EDecl) : Writer :=
  match d with
  | .ax n lp t u =>
    let (w, lpj) := w.namesJ lp
    let (w, ni) := w.name n
    let (w, ti) := w.expr t
    w.push s!"\{\"axiom\":\{\"isUnsafe\":{u},\"levelParams\":{lpj},\"name\":{ni},\"type\":{ti}}}"
  | .defn n lp t v h sf all =>
    let (w, aj) := w.namesJ all
    let (w, lpj) := w.namesJ lp
    let (w, ni) := w.name n
    let (w, ti) := w.expr t
    let (w, vi) := w.expr v
    w.push s!"\{\"def\":\{\"all\":{aj},\"hints\":{hintsJ h},\"levelParams\":{lpj},\
      \"name\":{ni},\"safety\":\"{sf}\",\"type\":{ti},\"value\":{vi}}}"
  | .thm n lp t v all =>
    let (w, aj) := w.namesJ all
    let (w, lpj) := w.namesJ lp
    let (w, ni) := w.name n
    let (w, ti) := w.expr t
    let (w, vi) := w.expr v
    w.push s!"\{\"thm\":\{\"all\":{aj},\"levelParams\":{lpj},\"name\":{ni},\
      \"type\":{ti},\"value\":{vi}}}"
  | .opaq n lp t v u all =>
    let (w, aj) := w.namesJ all
    let (w, lpj) := w.namesJ lp
    let (w, ni) := w.name n
    let (w, ti) := w.expr t
    let (w, vi) := w.expr v
    w.push s!"\{\"opaque\":\{\"all\":{aj},\"isUnsafe\":{u},\"levelParams\":{lpj},\"name\":{ni},\
      \"type\":{ti},\"value\":{vi}}}"
  | .quot n lp t k =>
    let (w, lpj) := w.namesJ lp
    let (w, ni) := w.name n
    let (w, ti) := w.expr t
    w.push s!"\{\"quot\":\{\"kind\":\"{k}\",\"levelParams\":{lpj},\"name\":{ni},\"type\":{ti}}}"
  | .induct ts cs rs =>
    let (w, csj) := cs.foldl (fun (w, a) c => let (w, s) := w.ctorJ c; (w, a.push s)) (w, #[])
    let (w, rsj) := rs.foldl (fun (w, a) r => let (w, s) := w.recJ r; (w, a.push s)) (w, #[])
    let (w, tsj) := ts.foldl (fun (w, a) t => let (w, s) := w.indTypeJ t; (w, a.push s)) (w, #[])
    w.push s!"\{\"inductive\":\{\"ctors\":[{String.intercalate "," csj.toList}],\
      \"recs\":[{String.intercalate "," rsj.toList}],\
      \"types\":[{String.intercalate "," tsj.toList}]}}"

/-- One declaration split into the arena definitions which must precede every
declaration spool, and its single reorderable declaration line. -/
structure DeclSplit where
  before : Cursor
  arena : Array String
  declaration : String
  after : Cursor
  deriving Inhabited, Repr, BEq

/-- Fail closed when a spool segment was produced for a different arena
cursor.  The reader accepts sparse arenas for compatibility, so composition
must enforce the writer's stronger continuous-ID contract itself. -/
def DeclSplit.validateStart (split : DeclSplit) (expected : Cursor) : Except String Unit :=
  if split.before == expected then .ok ()
  else .error s!"arena segment starts at {repr split.before}, expected {repr expected}"

/-- Serialize one declaration while keeping arena and declaration records
separate.  The returned writer retains only this island's interning maps, but
its line buffer is empty and ready for the next declaration in the island. -/
def splitDecl (w : Writer) (d : EDecl) : Writer × DeclSplit :=
  match w with
  | { names, levels, exprs, nextName, nextLevel, nextExpr, .. } =>
    let before := { nextName, nextLevel, nextExpr : Cursor }
    let completed :=
      ({ out := #[], names, levels, exprs, nextName, nextLevel, nextExpr } : Writer).decl d
    match completed with
    | { out, names, levels, exprs, nextName, nextLevel, nextExpr } =>
      let declaration := out.back!
      let arena := out.pop
      let after := { nextName, nextLevel, nextExpr : Cursor }
      ({ out := #[], names, levels, exprs, nextName, nextLevel, nextExpr },
        { before, arena, declaration, after })

end Writer

/-- **Serialise a whole export, one record at a time.**

`emit` is handed the lines of each record — the interned names, levels and
expressions it introduced, then the record itself — in file order, each without
its terminating newline. The interning tables live across the whole fold, which
is what the format requires; the *lines* do not.

Every consumer of the writer goes through here, so there is one definition of
what the file looks like. -/
@[specialize] def Export.stream {m : Type → Type} [Monad m] (x : Export)
    (emit : Array String → m Unit) : m Unit := do
  unless x.metaLine.isNull do emit #[x.metaLine.compress]
  let mut w : Writer := {}
  for d in x.decls do
    w := w.decl d
    emit w.out
    w := { w with out := #[] }

/-- Serialise a whole export into a `String`. Fine for a fixture; on a real
export use [`Export.writeTo`], which does not hold the file in memory. -/
def Export.render (x : Export) : String :=
  let go : StateM String Unit :=
    x.stream fun ls => modify fun s => ls.foldl (fun s l => s ++ l ++ "\n") s
  go.run "" |>.2

/-- Serialise a whole export to a stream, in bounded memory.

A `Stream` rather than a `Handle` because `-o -` is stdout, which `lean-inductive-models`
takes first class rather than through `/dev/stdout`.

Lines are gathered into a buffer of at least [`writeChunk`] bytes before each
write, so the cost is one `putStr` per few thousand lines rather than one per
line; nothing larger than that buffer plus the interning tables is ever
live. -/
def Export.writeTo (x : Export) (h : IO.FS.Stream) : IO Unit := do
  let buf ← IO.mkRef ""
  let n ← IO.mkRef 0
  x.stream fun ls => do
    let mut b ← buf.get
    let mut k ← n.get
    -- Take the buffer out of the ref first, so the append below sees a
    -- uniquely-referenced string and extends it in place.
    buf.set ""
    for l in ls do
      b := b ++ l ++ "\n"
      k := k + l.utf8ByteSize + 1
    if k ≥ writeChunk then
      h.putStr b
      b := ""
      k := 0
    buf.set b
    n.set k
  h.putStr (← buf.get)
where
  /-- 4 MiB: large enough that the per-write overhead vanishes, small enough
  that the buffer is not the thing that runs the machine out of memory. -/
  writeChunk : Nat := 4 * 1024 * 1024

end InductiveModels
