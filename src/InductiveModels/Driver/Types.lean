import InductiveModels.Order
import InductiveModels.Simple.Basis

/-!
# What a run reports, and what it may retain

The value-level vocabulary the whole driver is written against: the run
[`Report`], the two retention witnesses a not-yet-closed island holds
([`PendingModel`], [`CompactIsland`]), the compact shadow a discarding run
produces ([`CompactLocator`], [`CompactPlan`], [`StreamOutputStats`]), and the
declaration-wise output event and its callback.

Nothing here constructs a model or names a construction; these are the answers
a run ends with, so every other part of the driver may depend on them and none
of them depends on any other part.
-/

open Lean Meta

namespace InductiveModels

/-- What one run did. -/
structure Report where
  generated : Array (Name × Nat) := #[]
  declined : Array (Name × String) := #[]
  /-- **The inductive-basis exemption, which is not a decline**
  ([`InductiveModels.inductiveBasis`]).
  `Eq`, `Nat`, `PSigma'`, and `PUnit` are the primitives
  the third construction is written in, so a run leaves them unmodelled *by
  definition*; counting them among the declines makes every coverage report
  a number it then had to walk back in the next sentence. Reported on their own
  lines and counted in their own row. -/
  exempt : Array (Name × String) := #[]
  /-- **Prelude constants the input did not declare and a model spliced in**,
  per declaration. `Eq`, the quotient and `Quot.sound` come out under Lean's
  own names and `funext` under the model's; `InductiveModels.ensureEq` and
  `InductiveModels.ensureFunext` say why the two are named differently. Printed,
  always: an insertion is a decision on record. -/
  spliced : Array (Name × Array Name) := #[]
  /-- Recursors whose replayed shape differs from the export's own. -/
  recMismatch : Array Name := #[]
  recChecked : Nat := 0
  /-- Public statements compared syntactically against the exact exported
  owner records, and the ones that did not match. -/
  stmtChecked : Nat := 0
  stmtErrors : Array String := #[]
  /-- Peak number of compact splice summaries retained inside one not-yet-closed
  generated island. `PendingModel` deliberately cannot retain an `Iso`. This
  is a retention invariant, not an output statistic. -/
  maxLivePendingModels : Nat := 0
  /-- Peak number of generated declaration records retained by one island
  before validation, optional generated checking, and emission or compact discard. -/
  maxLiveIslandRecords : Nat := 0
  /-- The input stopped replaying here: a declaration Lean's kernel will not
  load at all. The filter then becomes the identity, which is what a filter
  should be when it can do nothing. -/
  unreplayable : Option String := none
  /-- First exact generated-island kernel rejection. Input declarations are
  trusted dependencies and are never submitted through this gate. -/
  generatedKernelRejected : Option String := none
  /-- Number of generated-island kernel invocations. This value-level counter
  pins that disabling generated checking bypasses the gate entirely. -/
  generatedKernelChecks : Nat := 0
  /-- **The scope verdict of every shape decline**, beside the sentence in
  `declined` rather than only inside it. A decline that classified the
  declaration's *shape* answers one further question — whether the construction
  decided against the shape or merely does not reach it yet
  ([`InductiveModels.ShapeScope`]) — and a reader who has to recover that by
  matching on a message is a reader who will stop checking. Declines about a
  name or a contract have no entry here. -/
  shapeScopes : Array (Name × ShapeScope) := #[]
  deriving Inhabited, Repr, BEq

/-- Record one decline: its report line, and the scope verdict beside it
whenever the decline classified a shape. One function so that the two arrays
cannot drift apart at the seven places a route reports a refusal. -/
def Report.withDecline (rep : Report) (owner : Name) (decline : Decline)
    (what : String) : Report :=
  let reported := { rep with declined := rep.declined.push (owner, decline.labelAs what) }
  match decline.shapeScope? with
  | some scope => { reported with shapeScopes := reported.shapeScopes.push (owner, scope) }
  | none => reported

/-- Whether one reported decline still represents unsupported generation after
accounting for an existing or newly generated model. A noncanonical basis
owner is always unsupported: neither a model-shaped input family nor another
route may turn the reserved-name validation failure into success. -/
def declineIsUnsupported (alreadyCovered generated : Std.HashSet Name)
    (owner : Name) : Bool :=
  inductiveBasis.contains owner ||
    (!alreadyCovered.contains owner && !generated.contains owner)

/-- The compact support-persistence witness retained until an island closes.
The complete `Iso` is needed only while composing and serializing a model;
retaining it here would keep every generated declaration and construction
expression alive until owner-free replay. -/
structure PendingModel where
  spliced : Array Name

/-- Value-free information captured while one accepted island's declarations
are still live. The arrays remain aligned with the island's checked record
order and compact schedule rows. -/
structure CompactIsland where
  summaries : Array Order.DeclSummary
  globalExtras : Array Check.GlobalExtraRecord
  families : Array (Array Check.CompactFamilyCertificate)
  sourceFamilies : Array Check.CompactFamilyCertificate
  sourceGlobalExtra? : Option Check.GlobalExtraRecord
  diagnosticOwners : Std.HashSet Name

/-- Origin of one declaration in the eventual compact record schedule. Source
indices address exact input declarations; generated indices address an
accepted island and the declaration's position within that island. -/
inductive CompactLocator where
  | source (index : Nat)
  | generated (island declaration : Nat)
  deriving Inhabited, Repr, BEq

/-- Value-only accounting for one declaration-wise output stream.  The
largest callback payload is one generated island; source declarations are
delivered separately and no prior payload remains owned by the driver. -/
structure StreamOutputStats where
  generatedRecords : Nat := 0
  sourceRecords : Nat := 0
  maxIslandRecords : Nat := 0
  deriving Inhabited, Repr, BEq

/-- Value-only shadow of a compact generation pass, with no physical payloads
or generated declaration expressions. -/
structure CompactPlan where
  declarations : Array CompactLocator := #[]
  checkReport : Check.Report := { familiesChecked := 0, violations := #[] }
  /-- A regression counter for the payload-retention contract. Compact discard
  never appends generated declarations to a cumulative output array. -/
  retainedGeneratedRecords : Nat := 0
  streamStats : StreamOutputStats := {}
  /-- Source owners whose already-present model family has no final compact
  structural violation. Planned routes use this value-only set to classify
  declines without materializing the source export. -/
  coveredInputOwners : Array Name := #[]

/-- Exact logical output events.  A nonempty generated island is delivered as
one atomic event after its optional kernel gate and compact capture; its source
record is the immediately following event. -/
inductive StreamOutputEvent where
  | generatedIsland (records : Array EDecl)
  | source (record : EDecl)

/-- Declaration-wise output callback.  It is deliberately value-level: no
writer, JSON representation, environment, or physical sink enters generation
or generated-island checking. -/
abbrev StreamOutputEmitter := StreamOutputEvent → MetaM Unit
