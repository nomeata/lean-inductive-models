import InductiveModels.Mutual
import InductiveModels.Naming

/-!
# The simple route's alias table and its K theorem

Both are lifted out of the route dispatcher, which is already close to Lean's
elaboration recursion limit.
-/

open Lean Meta

namespace InductiveModels

/-- Complete the simple generator's explicit retry table. -/
def primAliasMap (tname root model ern recN : Name) (exportCtors : Array (Name × Expr))
    (ctorN iotaN : Nat → Name) (ruleK? : Option Name)
    (out : Array Declaration) : Naming.AliasMap := Id.run do
  if root == tname then return .empty
  let mut aliases := Naming.AliasMap.forRetry model (Naming.modelName tname)
    (out.flatMap (·.getNames.toArray))
  for j in [0:exportCtors.size] do
    aliases := aliases.insert (ctorN j) (Naming.modelName exportCtors[j]!.1)
    aliases := aliases.insert (iotaN j) (Naming.iotaName ern j)
  aliases := aliases.insert recN (Naming.modelName ern)
  if let some name := ruleK? then
    aliases := aliases.insert name (Naming.ruleKName ern)
  return aliases

/-- Emit the simple route's K theorem without adding another large branch to
`primIso`, which is already close to Lean's elaboration recursion limit. -/
def primRuleK (eqi : EqInfo) (rv : RecursorVal)
    (tname root model ern : Name) (reserved : Std.HashSet Name)
    (iotaName : Name)
    (out : Array Declaration) :
    GenM (Array Declaration × Array (Name × Name) × Option Name) := do
  unless rv.k do return (out, #[], none)
  let ruleKN := Naming.ruleKName (Naming.relocateSource tname root ern)
  let emitted :=
    if model.isPrefixOf ruleKN then
      ruleKN.replacePrefix model (Naming.modelName tname)
    else ruleKN
  if reserved.contains emitted || (← getEnv).constants.contains emitted then
    declineWith (.nameTaken emitted)
  if root != tname && ruleKN != emitted &&
      (reserved.contains ruleKN || (← getEnv).constants.contains ruleKN) then
    declineWith (.nameTaken ruleKN)
  unless rv.rules.length == 1 do badShape s!"{ern} is K-like with {rv.rules.length} rules"
  let iotaType? := out.findSome? fun declaration => match declaration with
    | .thmDecl value => if value.name == iotaName then some value.type else none
    | _ => none
  let some iotaType := iotaType?
    | badShape s!"the K-like recursor {ern} has no iota theorem"
  let d ← ruleKDecl eqi rv.levelParams (rv.numParams + rv.numMotives + rv.numMinors)
    ruleKN iotaType
  addChecked d
  return (out.push d, #[(ern, ruleKN)], some ruleKN)

end InductiveModels
