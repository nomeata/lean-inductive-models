import InductiveModels.Simple.Tuple

/-!
# Build-time naming for one simple implementation family

The public bundle and the eligibility test the indexed fibre adapter's phase 1
asks.
-/

open Lean Meta

namespace InductiveModels

/-- Complete build-time naming for one simple implementation family.  Every
route uses [`PrimInterfaceNames.standard`]. -/
structure PrimInterfaceNames where
  model : Name
  impl : Name
  self : Name
  ctors : Array Name
  recursor : Name
  iotas : Array Name
  deriving Inhabited

def PrimInterfaceNames.standard (tname root : Name)
    (exportCtors : Array (Name × Expr)) : PrimInterfaceNames :=
  let model := Naming.modelName root
  let recursor := Name.str tname "rec"
  { model
    impl := Name.str model "_impl"
    self := model
    ctors := exportCtors.map fun (constructor, _) =>
      Naming.modelName (Naming.relocateSource tname root constructor)
    recursor := Naming.modelName (Naming.relocateSource tname root recursor)
    iotas := (Array.range exportCtors.size).map fun index =>
      Naming.iotaName (Naming.relocateSource tname root recursor) index }

/-- Private certificate names for the indexed fibre adapter.  Every name is
below the collision-safe build model, so the ordinary whole-prefix alias
registration renames it independently of raw/private source constructor
spellings. -/
def PrimInterfaceNames.oneLayerImplementation (root : Name)
    (exportCtors : Array (Name × Expr)) : PrimInterfaceNames :=
  let model := Naming.modelName root
  let impl := Name.str model "_impl"
  { model, impl
    self := Name.str impl "self"
    ctors := (Array.range exportCtors.size).map fun index => Name.str impl s!"ctor_{index}"
    recursor := Name.str impl "rec"
    iotas := (Array.range exportCtors.size).map fun index => Name.str impl s!"rec_iota_{index}" }

/-- Installed-capability half of the indexed fibre adapter boundary.  Exact
source eligibility is replayable through
[`InductiveModels.indexedFibreOneLayerProjectionFamily`]; this check additionally
pins the installed declaration to the bare Arm-C erasure route.

The owner must be indexed, and that is the route boundary rather than a count:
an unindexed owner is the simple construction's own, with no adapter at all —
its public interface is already the exact source syntax and its projections
are already literal
([`InductiveModels.projectionIotaUsesLiteralField`]).  How *many* indices it
carries is never asked — the certificate's `roll`/`unroll` are the identity at
the owner's whole arity. -/
def phase1IndexedFibreOneLayerEligible (tname : Name) (np : Nat)
    (memberTy : Expr) (exportCtors : Array (Name × Expr))
    (sourceType : EIndType) (sourceConstructor : ECtor)
    (sourceRecursor : ERec) : MetaM Bool := do
  let some (.inductInfo type) := (← getEnv).constants.find? tname | return false
  let erasureBare ← match ← (erasureBareFailure? tname np type.numIndices exportCtors).run with
    | .ok reason => pure reason.isNone
    | .error _ => pure false
  return indexedFibreOneLayerTypeShape np type.numIndices memberTy &&
    indexedFibreOneLayerProjectionFamily sourceType sourceConstructor
      sourceRecursor && erasureBare && exportCtors.size == 1 &&
    type.all == [tname] && type.ctors.length == 1 && type.numIndices > 0 &&
    type.numNested == 0 && type.isRec == sourceType.isRec && !type.isUnsafe

end InductiveModels
