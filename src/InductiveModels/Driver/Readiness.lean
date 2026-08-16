import InductiveModels.KernelCheck

/-!
# What the export claims, checked against what Lean built

The free oracle: replaying an inductive record installs Lean's own recursors,
so the export's recursor metadata can be compared with the installed one
([`checkRecs`]) without generating anything.  [`blockOf`] reads back the
replayed block a construction is then run on.
-/

open Lean Meta

namespace InductiveModels

/-- The exact exported metadata of one inductive record must be what Lean's
kernel regenerated from that record's type-former and constructor inputs.

`Declaration.inductDecl` does not take the exported `InductiveVal`,
`ConstructorVal`, or `RecursorVal` metadata as input.  Merely adding the
reconstructed declaration therefore proves the constructor types are valid,
but does not validate fields such as constructor indices, recursion flags, or
recursor rule arities.  Compare every exported field here, including the fields
which are bookkeeping rather than kernel declaration inputs. -/
private def exportedRecursorRules (recursor : ERec) : List RecursorRule :=
  recursor.rules.map fun rule : ERecRule =>
    { ctor := rule.ctor, nfields := rule.nfields, rhs := rule.rhs }

private def recursorMetadataMatches (recursor : ERec) (actual : RecursorVal) : Bool :=
  actual.name == recursor.name && actual.levelParams == recursor.levelParams &&
    actual.type == recursor.type && actual.all == recursor.all &&
    actual.numParams == recursor.numParams && actual.numIndices == recursor.numIndices &&
    actual.numMotives == recursor.numMotives && actual.numMinors == recursor.numMinors &&
    actual.rules == exportedRecursorRules recursor && actual.k == recursor.k &&
    actual.isUnsafe == recursor.isUnsafe

def checkInductiveMetadata (types : List EIndType) (constructors : List ECtor)
    (recursors : List ERec) : MetaM (Array String) := do
  return KernelCheck.checkInductiveMetadataIn (← getEnv) types constructors recursors

/-- Optional generation-time recursor audit retained for the library driver.
The generated-island kernel gate additionally checks types and constructors. -/
def checkRecs (recursors : List ERec) : MetaM (Nat × Array Name) := do
  let env ← getEnv
  let mut bad : Array Name := #[]
  for recursor in recursors do
    match env.constants.find? recursor.name with
    | some (.recInfo actual) =>
      unless recursorMetadataMatches recursor actual do bad := bad.push recursor.name
    | _ => bad := bad.push recursor.name
  return (recursors.length, bad)

/-- **One installed inductive block, read back out of the environment** as the
member types and constructor lists [`InductiveModels.mutualIso`] wants.

The block a nested declaration's model *is* — `T._model.0 … T._model.{n−1}` —
is not in the input, so there is no `EDecl` to take these off; it exists only in
the environment the generator just put it in. This is how the composition
hands the second construction its input. -/
def blockOf (names : Array Name) : MetaM (Array Expr × Array (Array (Name × Expr))) := do
  let env ← getEnv
  let mut tys : Array Expr := #[]
  let mut cs : Array (Array (Name × Expr)) := #[]
  for n in names do
    let some (.inductInfo iv) := env.constants.find? n | throwError "{n} is not an inductive"
    tys := tys.push iv.type
    let mut ct : Array (Name × Expr) := #[]
    for cn in iv.ctors do
      let some ci := env.constants.find? cn | throwError "{cn} is not declared"
      ct := ct.push (cn, ci.type)
    cs := cs.push ct
  return (tys, cs)
