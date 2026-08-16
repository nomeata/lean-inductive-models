import Lean
import InductiveModels.Format.Types

/-!
# The generator's monad, and the shapes it can decline

`Decline` is the vocabulary every one of the three constructions reports in,
and `GenM` is the monad all three are written in. Neither knows anything about
nesting: this is the bottom of the shared generator core, imported by the
simple construction and by the nested one alike.

`addChecked` is here rather than beside the constructions because installing a
declaration in the disposable construction environment — and noticing when the
environment loses it — is the same operation for all three.
-/

open Lean Meta

namespace InductiveModels

/-- **Which side of the boundary a shape decline falls on**, and the whole
reason [`InductiveModels.Decline.shapeUnsupported`] carries a field rather than
only a sentence.

A run that reports "declined" collapses two facts a reader has to be able to
separate. One is a decision: this construction has looked at the shape and
positively decided it is not the simple representation's business. The other is
a gap: the arm that owns the shape ought to reach it and does not, and the only
reason no model came out is that nobody has finished the arm. Folding the
second into the first is how an incompleteness becomes invisible and then
permanent — the census counts it beside the deliberate exclusions and nothing
ever asks about it again.

Both are declines: neither is a tool failure, both leave the owner in the
output unchanged, and both reach the CLI's unsupported exit. What differs is
what a reader should do about one. -/
inductive ShapeScope where
  /-- **A shape the construction has decided not to model**, on a boundary it
  states. `README`'s routing boundaries are these: a field mentioning the owner
  other than as `∀ z⃗, T p⃗ e⃗` is a nested occurrence and belongs to layer 1,
  not here. Nothing is missing; a model would be the wrong layer's. -/
  | outOfScope
  /-- **A shape the construction that owns it ought to reach and does not.**
  The route selected an arm — or would have, but for a guard that is narrower
  than the arm's actual reach — and no representation came out. This is a gap
  in the arm, and the message names which arm and which guard so that the gap
  is addressable rather than merely recorded. -/
  | incomplete
  deriving Inhabited, Repr, BEq, DecidableEq

/-- The canonical word for one scope, in a report line and in a test. -/
def ShapeScope.tag : ShapeScope → String
  | .outOfScope => "out of scope"
  | .incomplete => "incomplete"

/-- A positively recognized reason not to emit a requested public interface.

Construction-invariant failures do not belong here; [`InductiveModels.badShape`]
raises an internal tool error for those. -/
inductive Decline where
  /-- **A prelude constant the input declares at something other than Lean's
  statement.** Absence is not this: a prelude constant the input simply does
  not have is *spliced* ([`InductiveModels.ensureEq`], [`InductiveModels.ensureFunext`]).
  This is the case a splice cannot reach, because the name is already bound —
  by the input, in the output, and in every one of the input's own terms — and
  Lean's `Environment` has no way to rebind a constant, so replacing it would
  mean replaying the whole file a second time. The message names the constant
  and what is wrong with it. -/
  | notLeans (n : Name) (why : String)
  | nameTaken (n : Name)
  /-- **The construction environment installed the declaration and then lost it.**
  Distinct from [`InductiveModels.Decline.nameTaken`], which is the input already
  holding the name, because the two want opposite responses. This one is
  Lean's `AsyncConsts.add` refusing a *normalized* duplicate — an export
  flattens many modules, so it holds both `_private.M.0.X` and a public `X`,
  we model both, and `privateToUserName` makes the two model names one. The
  name is ours, nothing in the input is using it,
  and the fix is therefore ours too: regenerate under exact collision-safe
  aliases and translate those names on the way out. The driver does exactly
  that for nested, mutual, and simple generation, and only on this constructor.
  -/
  | nameLost (n : Name)
  /-- **A basis primitive, which is exempt rather than declined.** `Eq`,
  `Nat`, `PSigma'`, and `PUnit` are what the third construction is *written
  in*; modelling one of them would either be circular or would put a second
  `Eq` in the output. Their absence from the models is what makes the
  construction well-founded, so it is not a gap and a census that counts it as
  one is misleading. It is its own constructor so that the *report* can keep it
  in its own
  row ([`InductiveModels.Report.exempt`]) and the decline count can mean what it
  says. -/
  | basisExempt
  /-- **A projected field whose type names an earlier field the model does not
  select definitionally**, so the literal projection ι contract has no
  proposition to state.

  `T._model.proj_j` has the kernel's intrinsic codomain: field `j`'s type with
  every earlier field replaced by that field's own modeled projection at the
  major. The rule states `proj_j … (mk f⃗) = fⱼ` with the constructor's own
  binder on the right ([`InductiveModels.addProjectionModels`]), so the two
  sides are a well-formed equation exactly when each earlier projection in
  field `j`'s dependency closure reduces to its field on the modeled
  constructor. A route that reaches that field without *selecting* it — arm
  E's carrier is empty, so its projection is an elimination of the major, which
  is total but reduces to no field because none is stored — leaves the
  left-hand side at `Aⱼ(proj⃗ (mk f⃗))` and the right at `Aⱼ(f⃗)`, which are
  different types.

  The transported right-hand side that used to bridge them is no longer part
  of the contract, and `test/ProjectionTransportCensusTest.lean` holds it out,
  so there is nothing left to emit: the owner declines. -/
  | projectionCodomain (owner : Name) (field : Nat)
  /-- **A shape the route dispatcher settled on before any arm ran, and no arm
  represents.**

  Every other constructor here is about a *name* or a *contract*; this one is
  about the declaration's own shape, and it exists because the alternative was
  an abort. A shape reaching no arm used to raise
  [`InductiveModels.badShape`] — an internal tool error, exit 3 — which for a
  thirty-minute stream means the run stops partway rather than passing the
  owner through and saying so.

  **Raised where the shape is classified, never where an exception surfaces.**
  Wrapping a construction in a handler and calling whatever it throws a decline
  would turn every real defect — an unknown constant, a kernel-rejected ι — into
  a silent gap, which is worse than aborting. So each of these is a guard the
  dispatcher evaluates on the analysis, before any declaration is installed: the
  answer is "no arm applies", not "an arm applied and failed". An arm that has
  committed and then cannot finish still aborts, and must.

  `scope` says whether that is a decision or a gap
  ([`InductiveModels.ShapeScope`]); `why` names the guard and the arm it
  belongs to. -/
  | shapeUnsupported (owner : Name) (scope : ShapeScope) (why : String)
  deriving Inhabited

/-- The word that reaches a report line, **under the construction's own name**.

There are two models in this package and they share every guard below the
driver — the name reservation, the prelude splice, `constInfo`, `instForall` —
so a decline raised in shared code has to be able to say which construction was
being built. `nested` is the model of a nested declaration
([`InductiveModels.iso`]) and `mutual` is the model of a plain mutual block
([`InductiveModels.mutualIso`]); the prefix is a parameter rather than a second copy of
the enumeration, because a second copy is a second thing to keep in step. -/
def Decline.labelAs (what : String) : Decline → String
  | .notLeans n why => s!"{what} model: the input's {n} is not Lean's ({why})"
  | .nameTaken n => s!"{what} model name taken ({n})"
  | .nameLost n => s!"{what} model name lost to a normalized-name collision ({n})"
  | .basisExempt =>
    s!"{what} model: a basis primitive (the exemption that makes the construction \
well-founded)"
  | .projectionCodomain owner field =>
    s!"{what} model shape: {owner}'s field {field} names an earlier field whose modeled \
projection does not select it definitionally, so the literal projection rule for that \
field would equate two terms of different types"
  | .shapeUnsupported owner scope why =>
    s!"{what} model shape ({scope.tag}): {owner} reaches no generation arm — {why}"

/-- The scope verdict a decline carries, for a caller that wants the
classification rather than the sentence. Only a shape decline has one. -/
def Decline.shapeScope? : Decline → Option ShapeScope
  | .shapeUnsupported _ scope _ => some scope
  | _ => none

/-- The word that reaches a report line for a **nested** declaration's model. -/
def Decline.label : Decline → String := Decline.labelAs "nested"

/-- The generator's monad: `MetaM`, with an explicit non-emission result as its
own error. Internal construction failures remain exceptions in the underlying
`MetaM` and are therefore never reported as deliberate declines. -/
abbrev GenM := ExceptT Decline MetaM

def declineWith (d : Decline) : GenM α := throwThe Decline d
/-- Abort generation after an internal construction invariant has failed.

This is deliberately *not* a [`Decline`]. A decline says that the generator
positively recognized a valid shape it has chosen not to support. Once a route
has committed to constructing declarations, malformed intermediate syntax or
missing metadata is a tool failure and must reach the CLI's exit-3 containment
boundary. Optional exact generated kernel rejection is recorded by the
Driver as `Report.generatedKernelRejected` and reaches the CLI's rejection exit;
it is not raised through this trusted construction helper. -/
def badShape (msg : String) : GenM α :=
  ExceptT.lift (show MetaM α from Lean.throwError msg)

/-- Fail closed unless exact exported syntax and installed kernel metadata
describe the same recursor slots. Literal types and rule RHSs may differ: the
former supplies public syntax while the latter supplies checked proofs. -/
def validateExactRecursorLayout (expected : ERec) (actual : RecursorVal) : GenM Unit := do
  unless expected.name == actual.name &&
      expected.levelParams == actual.levelParams && expected.all == actual.all &&
      expected.numParams == actual.numParams && expected.numIndices == actual.numIndices &&
      expected.numMotives == actual.numMotives && expected.numMinors == actual.numMinors &&
      expected.k == actual.k && expected.isUnsafe == actual.isUnsafe &&
      expected.rules.length == actual.rules.length do
    badShape s!"{expected.name}'s exact recursor layout differs from its installed metadata"
  for index in [0:expected.rules.length] do
    let exported := expected.rules[index]!
    let installed := actual.rules[index]!
    unless exported.ctor == installed.ctor && exported.nfields == installed.nfields do
      badShape s!"{expected.name}'s exact rule {index} layout differs from its installed metadata"

def hintsFor (v : Expr) : GenM ReducibilityHints := do
  return .regular (getMaxHeight (← getEnv) v + 1)

/-- Trusted-install a generated declaration in the disposable construction
environment. Exact serialized records cross the optional kernel boundary only
once, when their completed island closes.

**A declaration the construction environment accepts but then loses is a
decline.** `Environment.addDeclCore` installs the declaration and afterwards
registers each name in the *async* constant map, which keys on
`privateToUserName` — the name with its private prefix stripped.
`AsyncConsts.add` `panic!`s on a duplicate normalized name and returns the map
**unchanged**, so the constant is in the trusted construction map and invisible to
`Environment.find?`. That is not survivable here: `MetaM`'s `inferType` goes
through `find?`, so the very next declaration that names the lost one dies with
`Unknown constant` — an exit 3, the tool's own failure, with nothing emitted.

It is our own names that collide. An export is many modules flattened into one
file, so it can hold both `_private.M.0.X` and a public `X`; we model both, and
`_private.M.0.X._model.self` and `X._model.self` normalize alike. Checking
membership *after* the add catches it however the two are ordered, which no
check on the name alone can do — neither ordering has the other's name in hand
at the time. Costs one map lookup per emitted name.

`Declaration.getNames` omits the auxiliary recursors the kernel computes for
nested inductives, which are legitimately absent from `find?`; that is exactly
the set this must not ask about, and it is why the loop is over `getNames`
rather than over the environment's diff. -/
def addChecked (d : Declaration) : GenM Unit := do
  -- This is the disposable construction view, not the generated kernel gate.
  -- Exact emitted records are checked once at the island boundary when
  -- `typeCheckGenerated` is enabled; construction declarations are otherwise
  -- trusted in exactly the same way as replayed input declarations.
  match (← getEnv).addDeclCore 0 0 d none false with
  | .ok e =>
    setEnv e
    -- **`find?`, not `constants`.** `Environment.constants` is the trusted
    -- construction kernel map; `Environment.find?` also consults the async
    -- map used by MetaM, so it is the visibility boundary generation needs.
    -- The test suite's `runEnvProbe` pins the same distinction from the other
    -- side.
    for n in d.getNames do
      if ((← getEnv).find? n).isNone then
        declineWith (.nameLost n)
  | .error ex =>
    badShape s!"{d.getTopLevelNames} could not be installed for construction: \
      {← (ex.toMessageData {}).toString}"

end InductiveModels
