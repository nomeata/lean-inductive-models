import Lean
import InductiveModels.EqKit
import InductiveModels.Format.Types
import InductiveModels.Gen.Monad
import InductiveModels.Gen.ExportShape

/-!
# What a construction came to, and the table that keys it

`Iso` is the result record every one of the three constructions returns, and
`modelTable` is the rewriting each of them hands its consumer. They are stated
here, above all three, because correspondence checking and serialization
consume them without caring which construction produced them.
-/

open Lean Meta

namespace InductiveModels
/-! ## The driver -/

/-- The public names of one modeled inductive interface.

Most constructions implement and expose the same family, so [`Iso`] keeps its
historical fields as the public interface and leaves `implementation?` empty.
The one-layer recursive construction is different: it implements the fixpoint
at private names and exposes a separate, exact source-shaped public layer.
Keeping that distinction explicit prevents later consumers from accidentally
publishing the private recursor or using the public wrapper as the recursive
proof oracle. -/
structure IsoInterface where
  selfNames : Array Name
  ctors : Array (Name × Name)
  recs : Array Name
  iotas : Array (Nat × Name × Name)
  deriving Inhabited

/-- One member of a simultaneous private/public family boundary.

Every association is carried by its source name.  In particular, constructors
and recursor rules are not zipped with exporter arrays: mutual recursors need
not be serialized in member order.  `changed` records whether the public
carrier is a genuine one-layer representation or the identity alias used to
keep an ineligible sibling inside the simultaneous certificate. -/
structure IsoFamilyMember where
  owner : Name
  changed : Bool
  publicSelf : Name
  privateSelf : Name
  privateRecursor : Name
  privateConstructors : Array (Name × Name)
  privateIotas : Array (Name × Name × Name)
  privateRules : Array (Name × Name × Name)
  roll : Name
  unroll : Name
  unrollRoll : Name
  rollUnroll : Name
  deriving Inhabited

/-- Complete certificate for a partial simultaneous family adapter.

`support` names the declaration-local mutual implementation support (currently
the tag and auxiliary carrier).  Consumers accept the new literal projection
contract only after validating every support and member slot. -/
structure IsoFamilyImplementation where
  root : Name
  support : Array Name
  members : Array IsoFamilyMember
  deriving Inhabited

/-- One literal rule in source-export recursor evidence. -/
structure IsoSourceRecursorRule where
  ctor : Name
  nfields : Nat
  rhs : Expr
  deriving Inhabited, BEq, Repr

/-- Exact source-export metadata for a recursor that is not yet installed while
its owner's model island is constructed.  This is the literal `ERec` evidence,
not a reconstruction from a generated or subsequently installed declaration. -/
structure IsoSourceRecursor where
  name : Name
  levelParams : List Name
  type : Expr
  all : Array Name
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  rules : Array IsoSourceRecursorRule
  k : Bool
  isUnsafe : Bool
  deriving Inhabited, BEq, Repr

def IsoSourceRecursor.ofERec (recursor : ERec) : IsoSourceRecursor :=
  { name := recursor.name
    levelParams := recursor.levelParams
    type := recursor.type
    all := recursor.all.toArray
    numParams := recursor.numParams
    numIndices := recursor.numIndices
    numMotives := recursor.numMotives
    numMinors := recursor.numMinors
    rules := recursor.rules.toArray.map fun rule =>
      { ctor := rule.ctor, nfields := rule.nfields, rhs := rule.rhs }
    k := recursor.k
    isUnsafe := recursor.isUnsafe }

/-- One already checked equivalence between a source-shaped nested container
and the corresponding named private mimic member. `parameterArity` and `indexArity`
describe the exact prefix of all four declarations; neither is an eligibility
bound. The declaration types are retained so a later shadow can compare the
installed constants and target carrier before assigning maps to source keys. -/
structure IsoContainerImplementation where
  parameterArity : Nat
  indexArity : Nat
  implementationCarrier : Name
  /-- Exact source nested recursor represented by the private mimic recursor. -/
  sourceRecursor : Name
  /-- Literal source-export evidence. The source recursor need not yet be in the
  construction environment because its owner is installed after its model. -/
  sourceRecursorEvidence : IsoSourceRecursor
  /-- Exact installed recursor of the named private mimic. -/
  implementationRecursor : Name
  /-- Checked callable wrapper used only by the model interface and theorem
  left-hand sides. Semantic recursive calls use `implementationRecursor`. -/
  implementationRecursorWrapper : Name
  /-- Installed types retained so consumers can validate both endpoints before
  using the association in a source-to-implementation rewrite. -/
  sourceRecursorType : Expr
  implementationRecursorType : Expr
  implementationRecursorWrapperType : Expr
  /-- Exact source/private constructor keys of every installed recursor rule.
  The sequence is metadata, not an array-position matching contract. -/
  recursorRuleKeys : Array (Name × Name)
  /-- Exact installed internal RecursorVal rules, retained independently of
  the callable equality-theorem statements. -/
  implementationRecursorRules : Array IsoSourceRecursorRule := #[]
  /-- Exact constructor-name portion of the callable `exactSource` map used
  to state the wrapper's iota theorem. This remains distinct from internal
  block-constructor rule keys. -/
  interfaceRuleKeys : Array (Name × Name) := #[]
  forward : Name
  backward : Name
  backwardForward : Name
  forwardBackward : Name
  forwardType : Expr
  backwardType : Expr
  backwardForwardType : Expr
  forwardBackwardType : Expr
  implementationCarrierType : Expr
  deriving Inhabited, BEq, Repr

/-- Everything one nested declaration's model came to. -/
structure Iso where
  /-- Every generated declaration, in dependency order and already accepted. -/
  decls : Array Declaration
  /-- The declaration's own level parameters — the export's, in the export's
  order. Every generated constant carries these; a recursor and its ι theorems
  carry their motive universe in front of them. -/
  levelParams : List Name
  /-- The block's members: the export's own in `all` order, then the mimics. -/
  members : Array Name
  /-- `R_k._model.self` per **real** member, in `all` order. One unless the
  declaration is a mutual block. -/
  selfNames : Array Name
  /-- How many of `members` are the export's own. -/
  numAll : Nat
  /-- `(the export's constructor, the model's)`, in declaration order. -/
  ctors : Array (Name × Name)
  /-- `T._model.rec_k`, in member order. -/
  recs : Array Name
  /-- `(member, the rule's constructor as the export names it, the theorem)`. -/
  iotas : Array (Nat × Name × Name)
  /-- Private fixpoint interface when it differs from the public fields above.
  `none` means the implementation and public interface are identical.  This is
  name-only and does not retain a second declaration array. -/
  implementation? : Option IsoInterface := none
  /-- Owner-keyed simultaneous implementation certificate for a partial mutual
  one-layer family.  This is separate from the historical singleton
  `implementation?` so legacy consumers cannot accidentally interpret a
  partial mutual prefix as a complete certificate. -/
  familyImplementation? : Option IsoFamilyImplementation := none
  /-- Checked nested-container maps, one per private mimic. They are assigned
  to exact source occurrence keys by `FamilyAdapterShadow`; array position is
  not a consumer contract. -/
  containerImplementations : Array IsoContainerImplementation := #[]
  /-- The `funext` this model's own proofs use, present exactly when the block
  stores a packed position under a binder.  [`InductiveModels.ensureFunext`]
  keeps the export's own when the export has a usable one and derives one under
  the block's implementation namespace otherwise, so a consumer which has to
  close a pointwise container equation must read this rather than derive a
  second. -/
  funext? : Option Name := none
  /-- `(member, theorem)` for the real members on which Lean's kernel enables
  its unit-like equality shortcut. -/
  unitlikes : Array (Nat × Name) := #[]
  /-- `(member, theorem)` for the non-propositional members on which Lean's
  kernel enables structure eta.  The theorem reconstructs the value with the
  exact modeled constructor and the intrinsic modeled projections in field
  order. -/
  etas : Array (Nat × Name) := #[]
  /-- `(source recursor, rule-K theorem)` for exactly those exported recursors
  whose literal kernel metadata has `k = true`. -/
  ruleKs : Array (Name × Name) := #[]
  /-- `(type former, zero-based field index, projection, reduction theorem)`.
  Empty when no intrinsic projection has yet been attached.  The generated names may temporarily
  use an alias build root until serialization. -/
  projections : Array (Name × Nat × Name × Name) := #[]
  /-- Route-specific, closed implementations for intrinsic projections whose
  model recursor cannot eliminate into the field sort.  Each entry stores the
  source owner, zero-based field index, complete projection value and complete
  reduction-proof value.  The common driver remains responsible for the
  public types, names, collision checks and declaration ordering. -/
  projectionOverrides : Array (Name × Nat × Expr × Expr) := #[]
  /-- **Prelude constants the input did not declare and this model spliced in**
  — a subset of `Eq`, `Eq.refl`, the four quotient names, `Quot.sound` and
  `T._model.funext`, in the order they were emitted, and **empty** for every
  declaration whose input already had what it needed. The report prints it:
  a splice is a decision on record and not a silent one. -/
  spliced : Array Name
  /-- **Spliced inductives this model is not allowed to leave unmodelled.**
  Arm C splices the *index erasure* of the family it is
  modelling and carves the family out of it, so its output contains an
  inductive declaration that was in nobody's input. If the prim pass then
  cannot model that skeleton, the emission would put an additional unmodelled
  inductive in front of a consumer, so the whole model is
  withdrawn and the declaration declines instead.

  The check is **after** the splice-and-model descent rather than a prediction
  before it, because a prediction is the shape of "skip is not pass": a
  cheap test that says the skeleton will model, and an emission that leaves it
  unmodelled when it does not. [`InductiveModels.genPrim`] is where the withdrawal
  happens. Empty for every other arm, so nothing else changes shape. -/
  requires : Array Name := #[]
  /-- Exact build-name to export-name aliases used only after a normalized-name
  collision.  This is a whole-name table: raw private constructor names need
  not share any prefix with their owner. -/
  aliases : Naming.AliasMap := .empty
  deriving Inhabited

/-- The exact public family consumed by correspondence, serialization, and
the statement checker. -/
def Iso.publicInterface (is : Iso) : IsoInterface :=
  { selfNames := is.selfNames, ctors := is.ctors, recs := is.recs, iotas := is.iotas }

/-- The family whose recursor and iota proofs implement the public model.
Ordinary routes share the public family structurally. -/
def Iso.implementationInterface (is : Iso) : IsoInterface :=
  match is.implementation? with
  | some implementation => implementation
  | none => is.publicInterface

/-- **The export's names rewritten to the model's**: `T._model` for each real
member, `C._model` for each constructor, and `R._model` for each recursor.

The mutual and simple constructions share this table when writing restored
recursor types and rules. A plain mutual block has no second inductive to read a
statement from, so its public recursors and ι rules are the export's own with
this simultaneous renaming. The independent structural checker later rebuilds
the correspondence directly from serialized export records. -/
def modelTable (env : Environment) (all : Array Name) (is : Iso) :
    Std.HashMap Name (Nat × Expr) := Id.run do
  let us := is.levelParams.map Level.param
  let mut t : Std.HashMap Name (Nat × Expr) := {}
  for k in [0:is.numAll] do
    t := t.insert all[k]! (0, .const is.selfNames[k]! us)
  for (exportC, modelC) in is.ctors do
    t := t.insert exportC (0, .const modelC us)
  for k in [0:is.recs.size] do
    let ern := exportRecName all k
    let ls := match env.constants.find? ern with
      | some ci => ci.levelParams.map Level.param
      | none => []
    t := t.insert ern (0, .const is.recs[k]! ls)
  return t

/-- The extra reduction certified by a recursor's literal `k` flag.

Unlike an iota theorem, the major is an arbitrary inhabitant of the unique
constructor's result fiber. Lean's K reduction replaces it by that nullary
constructor and then applies the sole ordinary rule.  Starting from the iota
statement pins any indices to exactly that fiber without reconstructing them. -/
def ruleKDecl (eqi : EqInfo) (recLevelParams : List Name) (numPre : Nat)
    (theoremName : Name) (iotaType : Expr) : GenM Declaration := do
  forallBoundedTelescope iotaType (some numPre) fun pre body => do
    let .const eqName [v] := body.getAppFn
      | badShape s!"{theoremName}'s source iota does not conclude at Eq"
    unless eqName == eqi.eqN do badShape s!"{theoremName}'s source iota uses {eqName}"
    let eqArgs := body.getAppArgs
    unless eqArgs.size == 3 do badShape s!"{theoremName}'s source iota has malformed Eq"
    let α := eqArgs[0]!
    let lhs := eqArgs[1]!
    let rhs := eqArgs[2]!
    let some major := lhs.getAppArgs.back? | badShape s!"{theoremName}'s iota has no major"
    let majorType ← inferType major
    withLocalDeclD `major majorType fun arbitrary => do
      let replaceMajor := fun expression => expression.replace fun sub =>
        if sub == major then some arbitrary else none
      let α := replaceMajor α
      let lhs := replaceMajor lhs
      let binders := pre.push arbitrary
      let type := ← mkForallFVars binders (eqi.mk' v α lhs rhs)
      let value := ← mkLambdaFVars binders (eqi.refl' v α lhs)
      return .thmDecl { name := theoremName, levelParams := recLevelParams, type, value }

end InductiveModels
