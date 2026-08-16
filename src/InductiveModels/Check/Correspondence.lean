import InductiveModels.Format
import InductiveModels.Naming

/-!
# The public constant substitution

One modeled inductive record's correspondence table, the exact positional
universe alignment, and the simultaneous constant rewrite that every later
comparison performs.  Level renaming here deliberately avoids
`Level.instantiateParams`, which canonicalizes the exported syntax.
-/

open Lean

namespace InductiveModels.Check

/-- One entry in the simultaneous public constant substitution. -/
structure ConstantPair where
  owner : Name
  model : Name
  deriving Inhabited, Repr, BEq

/-- The public correspondence table for one modeled inductive record.

Recursors and their ordered reduction theorems share this table with type
formers and constructors, so every comparison uses one simultaneous rewrite. -/
structure Correspondence where
  typeFormers : Array ConstantPair
  constructors : Array ConstantPair
  recursors : Array ConstantPair
  projections : Array Naming.Projection
  iotas : Array Naming.Iota
  metadata : Array Naming.Metadata
  deriving Inhabited, Repr, BEq

def Correspondence.entries (table : Correspondence) : Array ConstantPair :=
  table.typeFormers ++ table.constructors ++ table.recursors

/-- Exact public declarations which can establish this correspondence in an
export.  Recursors and iota theorems participate in discovery even though their
statements are validated by a later checker tranche. -/
def Correspondence.publicNames (table : Correspondence) : Array Name :=
  table.entries.map (·.model) ++ table.iotas.map (·.name) ++
    table.projections.flatMap (fun projection => #[projection.name, projection.iota]) ++
    table.metadata.map (·.name)

/-- The historical driver statement metric: one comparison for each modeled
recursor type and ordinary iota, two for each intrinsic projection (definition
and iota), and one for each rule-K theorem.  Type formers, constructors,
unit-like witnesses and eta are checked by the same structural pass, but were
never included in the CLI's `statements:` count. -/
def Correspondence.statementCount (table : Correspondence) : Nat :=
  table.recursors.size + table.iotas.size + 2 * table.projections.size +
    (table.metadata.filter (·.kind == .ruleK)).size

/-- Every exact source declaration to which a structural diagnostic for this
correspondence may be attributed.  A generated mutual or nested family is
reported under its root, but its violations remain attached to the particular
member, constructor, or recursor whose public slot is wrong. -/
def Correspondence.diagnosticOwners (table : Correspondence) : Array Name :=
  table.entries.foldl
    (fun owners pair => if owners.contains pair.owner then owners else owners.push pair.owner) #[]

/-- The exact original declaration owning one public name in the table. -/
def Correspondence.originalOfPublic? (table : Correspondence) (name : Name) : Option Name :=
  (table.entries.find? (·.model == name)).map (·.owner) <|>
    (table.iotas.find? (·.name == name)).map (·.recursor) <|>
    (table.projections.find? fun projection =>
      projection.name == name || projection.iota == name).map (·.owner) <|>
    (table.metadata.find? (·.name == name)).map (·.owner)

/-- Apply the table simultaneously.  Projection type-name fields are constants
for this purpose just as they are for the backreference invariant. -/
def Correspondence.substitute (table : Correspondence) (expression : Expr) : Expr :=
  let replacements := table.entries.foldl
    (fun map pair => map.insert pair.owner pair.model) ({} : Std.HashMap Name Name)
  mapConstsE (fun name => replacements[name]?) expression

/-- Rename universe parameters without normalizing the exported level syntax.

`Level.instantiateParams` deliberately canonicalizes expressions such as
`max 1 (u+1)`.  That is useful to the kernel, but it is the wrong operation at
the literal public-interface boundary: lean4export records that redundant
`max`, and a generated declaration which retained it must be compared with the
same tree. -/
private partial def renameLevelParamsExact (renames : Std.HashMap Name Name) : Level → Level
  | .zero => .zero
  | .succ level => .succ (renameLevelParamsExact renames level)
  | .max left right =>
    .max (renameLevelParamsExact renames left) (renameLevelParamsExact renames right)
  | .imax left right =>
    .imax (renameLevelParamsExact renames left) (renameLevelParamsExact renames right)
  | .param name => .param (renames[name]?.getD name)
  | .mvar id => .mvar id

/-- The expression analogue of [`renameLevelParamsExact`].  Rebuild only nodes
which can carry levels; ordinary expression syntax and sharing are otherwise
left to `Expr.replace`. -/
private def renameExprLevelParamsExact (ownerParams modelParams : List Name)
    (expression : Expr) : Expr :=
  let renames := (ownerParams.zip modelParams).foldl
    (fun map pair => map.insert pair.1 pair.2) ({} : Std.HashMap Name Name)
  expression.replace fun subexpression => match subexpression with
    | .sort level => some (.sort (renameLevelParamsExact renames level))
    | .const name levels =>
      some (.const name (levels.map (renameLevelParamsExact renames)))
    | _ => none

def renameLevelParamNamesExact (ownerParams modelParams : List Name)
    (level : Level) : Level :=
  let renames := (ownerParams.zip modelParams).foldl
    (fun map pair => map.insert pair.1 pair.2) ({} : Std.HashMap Name Name)
  renameLevelParamsExact renames level

/-- Align the owner's declaration universes with the model declaration's by
position and then apply the simultaneous public constant substitution.  A
length mismatch is rejected by the caller rather than truncated here. -/
def Correspondence.expectedType (table : Correspondence) (ownerParams modelParams : List Name)
    (type : Expr) : Expr :=
  table.substitute (renameExprLevelParamsExact ownerParams modelParams type)

/-- Align and rewrite an iota proposition while retaining its outer ambient
`Eq`.  This distinction matters when the modeled inductive is itself `Eq`: its
arguments and rule use `Eq._model`, but the theorem relating both sides still
uses the export's equality type. -/
def Correspondence.expectedIotaType (table : Correspondence)
    (ownerParams modelParams : List Name) (type : Expr) : Expr :=
  let aligned := renameExprLevelParamsExact ownerParams modelParams type
  let rec rewrite : Expr → Expr
    | .forallE name domain body info =>
      .forallE name (table.substitute domain) (rewrite body) info
    | body =>
      match body.getAppFn with
      | .const ``Eq levels => mkAppN (.const ``Eq levels) (body.getAppArgs.map table.substitute)
      | _ => table.substitute body
  rewrite aligned

end InductiveModels.Check
