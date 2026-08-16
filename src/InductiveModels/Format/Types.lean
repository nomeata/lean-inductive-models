import Lean
import InductiveModels.Naming
/-!
# Export record types

The kernel-facing data of one `lean4export` `.ndjson` declaration record, the
hint/safety translations that turn a record back into a `Lean.Declaration`, and
the exhaustive name-rewriting walk every alias table is built on.

This is the floor of the format library: it depends on nothing but `Lean` and
`InductiveModels.Naming`.
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
beside its callers because they sit at different heights of the import graph**:
the input replay in `InductiveModels.Driver` and the fragment splice in
`InductiveModels.Simple`, which sits *below* `Driver`. `Format` is
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

end InductiveModels
