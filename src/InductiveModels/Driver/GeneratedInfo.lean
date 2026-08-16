import InductiveModels.Gen

/-!
# The exact public statement of a generated declaration

The construction result, not kernel-normalized metadata, is what a serialized
public statement is read from.  These three names were file-private while the
driver was one file; [`GeneratedDeclInfo`] and [`generatedDeclInfo`] are
module-visible now because the four structure-model parts below all ask this
question.
-/

open Lean Meta

namespace InductiveModels

/-- The exact public type and universe binders of a generated declaration,
read from the construction result rather than from kernel-normalized metadata.
Proof construction may still use the installed declaration; only serialized
public statements cross this interface. -/
structure GeneratedDeclInfo where
  levelParams : List Name
  type : Expr

private def generatedDeclInfo? (is : Iso) (name : Name) : Option GeneratedDeclInfo :=
  is.decls.findSome? fun declaration => match declaration with
    | .axiomDecl value =>
      if value.name == name then some { levelParams := value.levelParams, type := value.type }
      else none
    | .defnDecl value =>
      if value.name == name then some { levelParams := value.levelParams, type := value.type }
      else none
    | .thmDecl value =>
      if value.name == name then some { levelParams := value.levelParams, type := value.type }
      else none
    | .opaqueDecl value =>
      if value.name == name then some { levelParams := value.levelParams, type := value.type }
      else none
    | _ => none

def generatedDeclInfo (is : Iso) (name : Name) : GenM GeneratedDeclInfo := do
  let some info := generatedDeclInfo? is name
    | badShape s!"generated declaration table has no public type for {name}"
  return info
