import InductiveModels.Format
import InductiveModels.Naming

open Lean InductiveModels InductiveModels.Naming

structure TestState where
  passed : Nat := 0
  failed : Array String := #[]

def TestState.check (s : TestState) (label : String) (ok : Bool) : TestState :=
  if ok then { s with passed := s.passed + 1 }
  else { s with failed := s.failed.push label }

def privateName (module leaf : String) : Name :=
  Name.str (Name.num (Name.str `_private module) 0) leaf

def hasConst (target : Name) (e : Expr) : Bool :=
  (e.find? fun sub => sub.isConstOf target).isSome

def main : IO UInt32 := do
  let mut state : TestState := {}

  -- The constructor is intentionally not below the public type former.  This
  -- is the shape the old root replacement could not move on retry.
  let owner := `Simple.Box
  let rawCtor := privateName "CtorModule" "mk"
  let buildOwner := retryRoot owner
  let buildCarrier := modelName buildOwner
  let exactCarrier := modelName owner
  let buildCtor := modelName (relocateSource owner buildOwner rawCtor)
  let exactCtor := modelName rawCtor
  let helper := Name.str (Name.str buildCarrier "_impl") "helper"
  let aliases := (AliasMap.forRetry buildCarrier exactCarrier #[buildCarrier, helper])
    |>.insert buildCtor exactCtor
  let decl : EDecl := .defn buildCtor [] (.const buildCarrier [])
    (.const helper []) (.regular 0) "safe" [buildCtor]
  let renamed := decl.renameAliases aliases
  state := state.check "simple raw-private constructor is exact"
    (renamed.names == [exactCtor])
  state := state.check "simple constructor type uses the exact carrier"
    (match renamed with | .defn _ _ ty _ _ _ _ => hasConst exactCarrier ty | _ => false)
  state := state.check "simple helper reference is exact"
    (match renamed with
     | .defn _ _ _ value _ _ _ => hasConst `Simple.Box._model._impl.helper value
     | _ => false)
  state := state.check "no normalized constructor alias leaks"
    (!renamed.names.contains (modelName (privateToUserName rawCtor)) &&
      !renamed.names.contains buildCtor)

  -- A nested block has both a public carrier and a raw private constructor;
  -- registering Lean-minted helper names must still produce exact entries.
  let nestedOwner := `Nested.Tree
  let nestedBuild := retryRoot nestedOwner
  let nestedBuildCarrier := modelName nestedBuild
  let nestedExactCarrier := modelName nestedOwner
  let nestedRawCtor := privateName "NestedCtor" "node"
  let nestedBuildCtor := modelName (relocateSource nestedOwner nestedBuild nestedRawCtor)
  let nestedMemberRec := Name.str (Name.num (Name.str nestedBuildCarrier "_impl") 0) "rec"
  let nestedAliases :=
    (AliasMap.forRetry nestedBuildCarrier nestedExactCarrier #[nestedBuildCarrier])
      |>.insert nestedBuildCtor (modelName nestedRawCtor)
      |>.register #[nestedMemberRec]
  state := state.check "nested private constructor has an explicit entry"
    (nestedAliases.exact? nestedBuildCtor == some (modelName nestedRawCtor))
  state := state.check "nested kernel helper has an explicit entry"
    (nestedAliases.exact? nestedMemberRec ==
      some (Name.str (Name.num `Nested.Tree._model._impl 0) "rec"))

  -- Owners already ending in `_model` compose; aliasing must never collapse
  -- the second component or parse it as a suffix.
  let composedOwner := `Already._model
  let composedBuild := retryRoot composedOwner
  let composedBuildCarrier := modelName composedBuild
  let composedAliases := AliasMap.forRetry composedBuildCarrier (modelName composedOwner)
    #[composedBuildCarrier]
  state := state.check "composed model owner stays exact"
    (composedAliases.exact composedBuildCarrier == `Already._model._model)
  state := state.check "unregistered aliases are not prefix-renamed"
    (composedAliases.exact (Name.str composedBuildCarrier "notRegistered") ==
      Name.str composedBuildCarrier "notRegistered")

  IO.println s!"private aliases: {state.passed} passed, {state.failed.size} failed"
  for failure in state.failed do IO.eprintln s!"FAIL: {failure}"
  return if state.failed.isEmpty then 0 else 1
