import InductiveModels.Simple

/-!
# One-layer certificates

A one-layer family publishes a public carrier `P`, a private carrier `M` and
an equivalence `roll`/`unroll` between them with both round trips proved, so a
consumer can read the public interface without seeing the encoding underneath.

Two routes still emit that certificate.  The **indexed fibre** adapter at the
bottom of this module wraps arm C's own public family: its `roll`/`unroll` are
the identity and its laws are reflexivity, so the certificate costs eight
aliases and no transport.  The **plain mutual** adapter
(`InductiveModels.MutualOneLayer`) rebuilds a real layer over the tag/aux
encoding, and its ι rules are `Eq.refl` too — not because that layer is
trivial, but because the certificate it publishes makes every transport in
them reduce away.  The note above `buildMutualOneLayerRecursors` states the
invariant and the guard that holds it.

There is no adapter for an *unindexed* single-block owner.  One was built and
removed: the simple construction already publishes that owner's carrier,
constructor, recursor, ι rules and intrinsic projections at the exact source
syntax, so a private fixpoint with a rolled layer over it bought nothing and
cost one `Eq.rec` transport per recursive field (and a `funext` splice per
function-typed one) in every ι rule it published.
-/

open Lean Meta

namespace InductiveModels

/-- Names internal to one private/public one-layer equivalence. -/
structure OneLayerNames where
  publicNames : PrimInterfaceNames
  implementation : PrimInterfaceNames
  roll : Name
  unroll : Name
  unrollRoll : Name
  rollUnroll : Name
  deriving Inhabited

def OneLayerNames.forBuild (tname root : Name)
    (constructors : Array (Name × Expr)) : OneLayerNames :=
  let publicNames := PrimInterfaceNames.standard tname root constructors
  let implementation := PrimInterfaceNames.oneLayerImplementation root constructors
  { publicNames, implementation
    roll := Name.str implementation.impl "roll"
    unroll := Name.str implementation.impl "unroll"
    unrollRoll := Name.str implementation.impl "unroll_roll"
    rollUnroll := Name.str implementation.impl "roll_unroll" }

private def generatedType (name : Name) : GenM Expr := do
  let some info := (← getEnv).constants.find? name
    | badShape s!"generated declaration {name} is absent"
  return info.type

private def ensureFresh (reserved : Std.HashSet Name) (name : Name) : GenM Unit := do
  if reserved.contains name || (← getEnv).constants.contains name then
    declineWith (.nameTaken name)

/-- A retry builds below an alias root, but the serialized certificate lands
at these exact names.  Check them before generation so aliasing cannot turn a
reserved exact helper into a late duplicate or replay failure. -/
private def ensureExactOneLayerRetryFresh (tname : Name)
    (sourceConstructor : Name × Expr) (reserved : Std.HashSet Name) : GenM Unit := do
  let exact := OneLayerNames.forBuild tname tname #[sourceConstructor]
  for name in #[exact.implementation.self, exact.implementation.ctors[0]!,
      exact.implementation.recursor, exact.implementation.iotas[0]!,
      exact.roll, exact.unroll, exact.unrollRoll, exact.rollUnroll] do
    ensureFresh reserved name

private def etaAliasValue (levelParams : List Name) (source : Name)
    (type : Expr) : GenM Expr :=
  forallTelescope type fun arguments _ =>
    mkLambdaFVars arguments
      (mkAppN (.const source (levelParams.map Level.param)) arguments)

private def renameOneLayerCertificateNames (mapping : Array (Name × Name))
    (type : Expr) : Expr :=
  mapConstsE (fun name => mapping.findSome? fun (source, target) =>
    if name == source then some target else none) type

/-- Add the short, exact private/public certificate around the already checked
indexed fibre implementation.  Arm C remains the semantic implementation of
`P p i = Σ layer, resultIndex layer = i`; these declarations expose its two
interfaces and their identity equivalence without rebuilding or normalizing a
single public statement. -/
def indexedFibreOneLayerIso (tname root : Name) (lparams : List Name)
    (np : Nat) (memberTy : Expr)
    (sourceConstructor : Name × Expr) (sourceRecursor : ERec)
    (reserved : Std.HashSet Name) : GenM Iso := do
  if root != tname then
    ensureExactOneLayerRetryFresh tname sourceConstructor reserved
  let publicIso ← primIso tname root lparams np
    memberTy #[sourceConstructor] reserved
    (sourceRecursor? := some sourceRecursor)
  let names := OneLayerNames.forBuild tname root #[sourceConstructor]
  unless publicIso.selfNames == #[names.publicNames.self] &&
      publicIso.ctors == #[(sourceConstructor.1, names.publicNames.ctors[0]!)] &&
      publicIso.recs == #[names.publicNames.recursor] &&
      publicIso.iotas.map (fun (_, _, name) => name) == names.publicNames.iotas do
    badShape s!"{tname}'s indexed public fibre does not match its name plan"
  for name in #[names.implementation.self, names.implementation.ctors[0]!,
      names.implementation.recursor, names.implementation.iotas[0]!,
      names.roll, names.unroll, names.unrollRoll, names.rollUnroll] do
    ensureFresh reserved name
  let mapping := #[(names.publicNames.self, names.implementation.self),
    (names.publicNames.ctors[0]!, names.implementation.ctors[0]!),
    (names.publicNames.recursor, names.implementation.recursor),
    (names.publicNames.iotas[0]!, names.implementation.iotas[0]!)]
  let rename := renameOneLayerCertificateNames mapping
  let declaration := fun (name source : Name) (levelParams : List Name)
      (type : Expr) => do
    let value ← etaAliasValue levelParams source type
    pure <| Declaration.defnDecl
      { name, levelParams, type, value, hints := .abbrev, safety := .safe }
  let makeTheorem := fun (name source : Name) (levelParams : List Name)
      (type : Expr) => do
    let value ← etaAliasValue levelParams source type
    pure <| Declaration.thmDecl { name, levelParams, type, value }
  let publicSelfType ← generatedType names.publicNames.self
  let publicCtorType ← generatedType names.publicNames.ctors[0]!
  let publicRecType ← generatedType names.publicNames.recursor
  let publicIotaType ← generatedType names.publicNames.iotas[0]!
  let privateSelf ← declaration names.implementation.self names.publicNames.self
    lparams publicSelfType
  addChecked privateSelf
  let privateCtor ← declaration names.implementation.ctors[0]!
    names.publicNames.ctors[0]! lparams (rename publicCtorType)
  addChecked privateCtor
  let privateRec ← declaration names.implementation.recursor names.publicNames.recursor
    sourceRecursor.levelParams (rename publicRecType)
  addChecked privateRec
  let privateIota ← makeTheorem names.implementation.iotas[0]!
    names.publicNames.iotas[0]! sourceRecursor.levelParams (rename publicIotaType)
  addChecked privateIota
  let us := lparams.map Level.param
  let eqi ← match EqInfo.check (← getEnv) with
    | .ok information => pure information
    | .error message => badShape s!"{tname}'s indexed fibre needs Eq ({message})"
  let ownerType ← generatedType names.publicNames.self
  let arity := numForalls ownerType
  let equivalenceType ← forallBoundedTelescope ownerType (some arity) fun arguments _ =>
    withLocalDeclD `value (mkAppN (.const names.publicNames.self us) arguments) fun value =>
      mkForallFVars (arguments.push value)
        (mkAppN (.const names.implementation.self us) arguments)
  let rollValue ← forallTelescope equivalenceType fun arguments _ =>
    mkLambdaFVars arguments arguments.back!
  let roll := Declaration.defnDecl
    { name := names.roll, levelParams := lparams, type := equivalenceType,
      value := rollValue, hints := .abbrev, safety := .safe }
  addChecked roll
  let inverseType ← forallBoundedTelescope ownerType (some arity) fun arguments _ =>
    withLocalDeclD `value (mkAppN (.const names.implementation.self us) arguments) fun value =>
      mkForallFVars (arguments.push value)
        (mkAppN (.const names.publicNames.self us) arguments)
  let unrollValue ← forallTelescope inverseType fun arguments _ =>
    mkLambdaFVars arguments arguments.back!
  let unroll := Declaration.defnDecl
    { name := names.unroll, levelParams := lparams, type := inverseType,
      value := unrollValue, hints := .abbrev, safety := .safe }
  addChecked unroll
  let law := fun (name : Name) (publicFirst : Bool) => do
    let carrierName := if publicFirst then names.publicNames.self else names.implementation.self
    let first := if publicFirst then names.roll else names.unroll
    let second := if publicFirst then names.unroll else names.roll
    let type ← forallBoundedTelescope ownerType (some arity) fun arguments _ =>
      withLocalDeclD `value (mkAppN (.const carrierName us) arguments) fun value => do
        let lhs := mkAppN (.const second us)
          (arguments.push (mkAppN (.const first us) (arguments.push value)))
        let carrier := mkAppN (.const carrierName us) arguments
        mkForallFVars (arguments.push value)
          (eqi.mk' (← ilevel carrier) carrier lhs value)
    let value ← forallTelescope type fun arguments result => do
      let #[alpha, lhs, _] := result.getAppArgs
        | badShape s!"{name}'s indexed fibre law is not an equality"
      mkLambdaFVars arguments
        (eqi.refl' (← ilevel alpha) alpha lhs)
    pure <| Declaration.thmDecl { name, levelParams := lparams, type, value }
  let unrollRoll ← law names.unrollRoll true
  addChecked unrollRoll
  let rollUnroll ← law names.rollUnroll false
  addChecked rollUnroll
  let certificate := #[privateSelf, privateCtor, privateRec, privateIota,
    roll, unroll, unrollRoll, rollUnroll]
  let aliases := publicIso.aliases.register
    (certificate.flatMap (·.getNames.toArray))
  return { publicIso with
    decls := publicIso.decls ++ certificate
    aliases
    implementation? := some
      { selfNames := #[names.implementation.self]
        ctors := #[(sourceConstructor.1, names.implementation.ctors[0]!)]
        recs := #[names.implementation.recursor]
        iotas := #[(0, sourceConstructor.1, names.implementation.iotas[0]!)] } }

end InductiveModels
