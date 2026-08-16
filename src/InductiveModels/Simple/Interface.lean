import InductiveModels.Simple.Tuple

/-!
# Build-time naming for one simple implementation family

The public bundle, the one-layer adapter's private bundle, and the two
one-layer eligibility tests the adapter's phase 1 asks.
-/

open Lean Meta

namespace InductiveModels

/-- Complete build-time naming for one simple implementation family.  Public
routes use [`PrimInterfaceNames.standard`]; the one-layer adapter supplies a
private bundle and later publishes the exact source-shaped names. -/
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

/-- Private fixpoint names for the one-layer adapter.  Every name is below the
collision-safe build model, so the ordinary whole-prefix alias registration
renames it independently of raw/private source constructor spellings. -/
def PrimInterfaceNames.oneLayerImplementation (root : Name)
    (exportCtors : Array (Name × Expr)) : PrimInterfaceNames :=
  let model := Naming.modelName root
  let impl := Name.str model "_impl"
  { model, impl
    self := Name.str impl "self"
    ctors := (Array.range exportCtors.size).map fun index => Name.str impl s!"ctor_{index}"
    recursor := Name.str impl "rec"
    iotas := (Array.range exportCtors.size).map fun index => Name.str impl s!"rec_iota_{index}" }

/-- Source/kernel metadata boundary for the first one-layer production route.
Capability checks which can fail (support, exact recursor layout and carrier
level) still run before this predicate is committed to emission.

**No count of recursive fields is asked.**  The remaining condition on them is
the one the layer's storage tower needs and not an arity: a recursive field may
not occur in a *later* field's type, because the congruence that rebuilds the
layer changes those fields one at a time.  `type.isRec` at one constructor is
what says the constructor has recursive occurrences at all. -/
def phase1DirectTypeOneLayerEligible (tname : Name) (np : Nat) (memberTy : Expr)
    (exportCtors : Array (Name × Expr))
    (sourceRecursor? : Option ERec) : MetaM Bool := do
  let env ← getEnv
  let some (.inductInfo type) := env.constants.find? tname | return false
  let neverZero ← forallBoundedTelescope memberTy (some np) fun _ result => match result with
    | .sort level => pure level.normalize.isNeverZero
    | _ => pure false
  let independentRecursiveFields ← match exportCtors[0]? with
    | some (_, constructorType) =>
      forallBoundedTelescope constructorType (some np) fun parameters _ => do
        match ← (do
          let telescope ← instForall constructorType parameters
          let shape : Array PField ← classifyCtor tname (numForalls telescope) telescope
          let recursive := (Array.range shape.size).filter fun index =>
            (PField.rec? shape[index]!).isSome
          forallBoundedTelescope telescope (some shape.size) fun fields _ => do
            for recursiveIndex in recursive do
              let .fvar recursiveId := fields[recursiveIndex]!
                | badShape "a phase-1 recursive field is not constructor-local"
              for later in [recursiveIndex + 1:fields.size] do
                if (← inferType fields[later]!).containsFVar recursiveId then
                  return false
            return true).run with
        | .error _ => pure false
        | .ok eligible => pure eligible
    | none => pure false
  return neverZero && independentRecursiveFields && sourceRecursor?.isSome && exportCtors.size == 1 && type.all == [tname] &&
    type.ctors.length == 1 && type.numIndices == 0 && type.numNested == 0 && type.isRec &&
    !type.isUnsafe

/-- Installed-capability half of the indexed fibre adapter boundary.  Exact
source eligibility is replayable through
[`InductiveModels.indexedFibreOneLayerProjectionFamily`]; this check additionally
pins the installed declaration to the bare Arm-C erasure route.

The owner must be indexed, and that is the route boundary rather than a count:
an unindexed owner is the direct-type one-layer route's
([`InductiveModels.phase1DirectTypeOneLayerEligible`], selected first) or is
already literal without an adapter
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
