import InductiveModels.Driver
import InductiveModels.FamilyAdapterConstruction
import family_adapter_generated

open Lean Meta InductiveModels

namespace FamilyAdapterRejectedBoundaries

inductive Index where
  | here

def erasedResultIndex {alpha : Sort u} (_ : alpha) : Index :=
  Index.here

/--
error: (kernel) invalid return type for 'FamilyAdapterRejectedBoundaries.MovingResult.mk'
-/
#guard_msgs in
inductive MovingResult : Index -> Type where
  | mk (child : MovingResult Index.here) :
      MovingResult (erasedResultIndex child)

axiom Witness {alpha : Type u} (_ : alpha) : Type u

/--
error: (kernel) arg #2 of 'FamilyAdapterRejectedBoundaries.LaterDependency.mk' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
inductive LaterDependency : Index -> Type where
  | mk (child : LaterDependency Index.here) (evidence : Witness child) :
      LaterDependency Index.here

end FamilyAdapterRejectedBoundaries

namespace FamilyAdapterConstructionTest

def identityIso (source : EDecl) : Iso :=
  match source with
  | .induct types constructors recursors =>
    let types := types.toArray
    let constructors := constructors.toArray
    let recursors := recursors.toArray
    let all := types.map (·.name)
    let recursorNames := (Array.range types.size).map fun index =>
      (recursors.find? (·.name == exportRecName all index) |>.map (·.name)).getD .anonymous
    let iotas := (Array.range types.size).flatMap fun index =>
      let recursorName := recursorNames[index]!
      (recursors.find? (·.name == recursorName) |>.map (·.rules.toArray) |>.getD #[]).map
        fun rule => (index, rule.ctor, recursorName)
    { decls := #[]
      levelParams := types[0]?.map (·.levelParams) |>.getD []
      members := all
      selfNames := all
      numAll := all.size
      ctors := constructors.map fun constructor => (constructor.name, constructor.name)
      recs := recursorNames
      iotas
      spliced := #[] }
  | _ => default

structure ChangedContainerBoundary where
  implementationCarrier : Name
  forward : Name
  backward : Name
  backwardForward : Name
  forwardBackward : Name

structure ChangedBoundary where
  publicOwner : Name
  privateOwner : Name
  forward : Name
  backward : Name
  backwardForward : Name
  forwardBackward : Name
  container? : Option ChangedContainerBoundary := none

def changedIso (source : EDecl) (boundary : ChangedBoundary) : MetaM Iso := do
  let publicIso := identityIso source
  let publicConstructor := Name.str boundary.publicOwner "mk"
  let privateConstructor := Name.str boundary.privateOwner "mk"
  let publicRecursor := Name.str boundary.publicOwner "rec"
  let privateRecursor := Name.str boundary.privateOwner "rec"
  let member : IsoFamilyMember :=
    { owner := boundary.publicOwner
      changed := true
      publicSelf := boundary.publicOwner
      privateSelf := boundary.privateOwner
      privateRecursor
      privateConstructors := #[(publicConstructor, privateConstructor)]
      privateIotas := #[(publicRecursor, publicConstructor, privateRecursor)]
      privateRules := #[(publicRecursor, publicConstructor, privateRecursor)]
      roll := boundary.forward
      unroll := boundary.backward
      unrollRoll := boundary.backwardForward
      rollUnroll := boundary.forwardBackward }
  let containerImplementations ← match boundary.container? with
    | none => pure #[]
    | some container =>
      let typeOf := fun name => do
        let some information := (← getEnv).constants.find? name
          | throwError "changed container map {name} is not installed"
        return information.type
      pure #[{
        parameterArity := 0
        indexArity := 0
        implementationCarrier := container.implementationCarrier
        forward := container.forward
        backward := container.backward
        backwardForward := container.backwardForward
        forwardBackward := container.forwardBackward
        forwardType := (← typeOf container.forward)
        backwardType := (← typeOf container.backward)
        backwardForwardType := (← typeOf container.backwardForward)
        forwardBackwardType := (← typeOf container.forwardBackward)
        implementationCarrierType := (← typeOf container.implementationCarrier) }]
  return { publicIso with
    familyImplementation? := some
      { root := boundary.publicOwner, support := #[], members := #[member] }
    containerImplementations }

def changedDirect : ChangedBoundary :=
  { publicOwner := `FamilyAdapterGenerated.GeneratedChangedDirectPublic
    privateOwner := `FamilyAdapterGenerated.GeneratedChangedDirectPrivate
    forward := `FamilyAdapterGenerated.generatedChangedDirectRoll
    backward := `FamilyAdapterGenerated.generatedChangedDirectUnroll
    backwardForward := `FamilyAdapterGenerated.generatedChangedDirectUnrollRoll
    forwardBackward := `FamilyAdapterGenerated.generatedChangedDirectRollUnroll }

def changedIndexed : ChangedBoundary :=
  { publicOwner := `FamilyAdapterGenerated.GeneratedChangedIndexedPublic
    privateOwner := `FamilyAdapterGenerated.GeneratedChangedIndexedPrivate
    forward := `FamilyAdapterGenerated.generatedChangedIndexedRoll
    backward := `FamilyAdapterGenerated.generatedChangedIndexedUnroll
    backwardForward := `FamilyAdapterGenerated.generatedChangedIndexedUnrollRoll
    forwardBackward := `FamilyAdapterGenerated.generatedChangedIndexedRollUnroll }

def changedNested : ChangedBoundary :=
  { publicOwner := `FamilyAdapterGenerated.GeneratedChangedNestedPublic
    privateOwner := `FamilyAdapterGenerated.GeneratedChangedNestedPrivate
    forward := `FamilyAdapterGenerated.generatedChangedNestedRoll
    backward := `FamilyAdapterGenerated.generatedChangedNestedUnroll
    backwardForward := `FamilyAdapterGenerated.generatedChangedNestedUnrollRoll
    forwardBackward := `FamilyAdapterGenerated.generatedChangedNestedRollUnroll
    container? := some
      { implementationCarrier := `FamilyAdapterGenerated.GeneratedList
        forward := `FamilyAdapterGenerated.generatedChangedNestedContainerForward
        backward := `FamilyAdapterGenerated.generatedChangedNestedContainerBackward
        backwardForward :=
          `FamilyAdapterGenerated.generatedChangedNestedContainerBackwardForward
        forwardBackward :=
          `FamilyAdapterGenerated.generatedChangedNestedContainerForwardBackward } }

def directSamples : Array Name :=
  #[`FamilyAdapterGenerated.GeneratedDirect0,
    `FamilyAdapterGenerated.GeneratedDirect1,
    `FamilyAdapterGenerated.GeneratedDirect2,
    `FamilyAdapterGenerated.GeneratedDirect3,
    `FamilyAdapterGenerated.GeneratedDirect5,
    `FamilyAdapterGenerated.GeneratedDirect8]

def dependentSamples : Array Name :=
  #[`FamilyAdapterGenerated.GeneratedDependent0,
    `FamilyAdapterGenerated.GeneratedDependent1,
    `FamilyAdapterGenerated.GeneratedDependent2,
    `FamilyAdapterGenerated.GeneratedDependent3,
    `FamilyAdapterGenerated.GeneratedDependent5,
    `FamilyAdapterGenerated.GeneratedDependent8]

def infinitarySamples : Array Name :=
  #[`FamilyAdapterGenerated.GeneratedInfinitary0,
    `FamilyAdapterGenerated.GeneratedInfinitary1,
    `FamilyAdapterGenerated.GeneratedInfinitary2,
    `FamilyAdapterGenerated.GeneratedInfinitary3,
    `FamilyAdapterGenerated.GeneratedInfinitary5,
    `FamilyAdapterGenerated.GeneratedInfinitary8]

def indexedSamples : Array Name :=
  #[`FamilyAdapterGenerated.GeneratedIndexed1x0,
    `FamilyAdapterGenerated.GeneratedIndexed1x1,
    `FamilyAdapterGenerated.GeneratedIndexed1x3,
    `FamilyAdapterGenerated.GeneratedIndexed1x8,
    `FamilyAdapterGenerated.GeneratedIndexed2x0,
    `FamilyAdapterGenerated.GeneratedIndexed2x2,
    `FamilyAdapterGenerated.GeneratedIndexed2x5,
    `FamilyAdapterGenerated.GeneratedIndexed3x0,
    `FamilyAdapterGenerated.GeneratedIndexed3x3,
    `FamilyAdapterGenerated.GeneratedIndexed3x8]

def constructorSamples : Array Name :=
  #[`FamilyAdapterGenerated.GeneratedConstructors1x8,
    `FamilyAdapterGenerated.GeneratedConstructors2x8,
    `FamilyAdapterGenerated.GeneratedConstructors3x8,
    `FamilyAdapterGenerated.GeneratedConstructors5x8]

def mutualSamples : Array (Array Name) :=
  #[#[`FamilyAdapterGenerated.GeneratedMutual1x8_0],
    #[`FamilyAdapterGenerated.GeneratedMutual2x8_0,
      `FamilyAdapterGenerated.GeneratedMutual2x8_1],
    #[`FamilyAdapterGenerated.GeneratedMutual3x8_0,
      `FamilyAdapterGenerated.GeneratedMutual3x8_1,
      `FamilyAdapterGenerated.GeneratedMutual3x8_2],
    #[`FamilyAdapterGenerated.GeneratedMutual5x8_0,
      `FamilyAdapterGenerated.GeneratedMutual5x8_1,
      `FamilyAdapterGenerated.GeneratedMutual5x8_2,
      `FamilyAdapterGenerated.GeneratedMutual5x8_3,
      `FamilyAdapterGenerated.GeneratedMutual5x8_4]]

def completeSamples : Array (Array Name) :=
  (directSamples ++ dependentSamples ++ infinitarySamples ++ indexedSamples ++
    constructorSamples).map (#[·]) ++ mutualSamples

def nestedSamples : Array Name :=
  #[`FamilyAdapterGenerated.GeneratedNested1,
    `FamilyAdapterGenerated.GeneratedNested2,
    `FamilyAdapterGenerated.GeneratedNested3,
    `FamilyAdapterGenerated.GeneratedNested5,
    `FamilyAdapterGenerated.GeneratedNested8]

structure Result where
  complete : Nat := 0
  identityNested : Nat := 0
  changed : Nat := 0
  installedFamily : Nat := 0
  closedContainers : Nat := 0
  invalidMaps : Nat := 0
  invalidContainerMaps : Nat := 0
  wrongTargetMaps : Nat := 0
  failures : Array String := #[]

def runSamples : MetaM Result := do
  let mut result : Result := {}
  for owners in completeSamples do
    let owner := owners[0]!
    let source ← indEDecl owners
    let iso := identityIso source
    let report ← FamilyAdapter.deriveShadowPlan source iso
    let some plan := report.plan? | do
      result := { result with failures := result.failures.push s!"{owner}: no exact plan" }
      continue
    let built ← (FamilyAdapter.buildFamilyPrototype report iso
      ((`_family_adapter_construction_test).append owner)).run
    match built with
    | .error decline =>
      result := { result with failures := result.failures.push s!"{owner}: {decline.label}" }
    | .ok built =>
      match built.certificate with
      | none =>
        result := { result with failures := result.failures.push s!"{owner}: {repr built.issues}" }
      | some certificate =>
        let expectedHypotheses := plan.rules.foldl
          (fun count rule => count + rule.occurrences.size) 0
        let environment ← getEnv
        let declarationsInstalled := built.declarations.all fun declaration =>
          declaration.getNames.all (fun name => environment.constants.contains name)
        if certificate.telescopes.size == plan.constructors.size &&
            certificate.minorHypotheses.size == expectedHypotheses && declarationsInstalled then
          result := { result with complete := result.complete + 1 }
        else
          let failures := result.failures.push s!"{owner}: incomplete kernel certificate"
          result := { result with failures }
  for owner in nestedSamples do
    let source ← indEDecl #[owner]
    let iso := identityIso source
    let report ← FamilyAdapter.deriveShadowPlan source iso
    if report.plan?.isNone then
      result := { result with failures := result.failures.push s!"{owner}: no exact plan" }
      continue
    let built ← (FamilyAdapter.buildFamilyPrototype report iso
      ((`_family_adapter_construction_test).append owner)).run
    match built with
    | .error decline =>
      result := { result with failures := result.failures.push s!"{owner}: {decline.label}" }
    | .ok built =>
      if built.certificate.isSome && built.issues.isEmpty then
        result := { result with identityNested := result.identityNested + 1 }
      else
        let failures := result.failures.push
          s!"{owner}: definitionally equal nested field did not close: {repr built.issues}"
        result := { result with failures }
  for boundary in #[changedDirect, changedIndexed, changedNested] do
    let source ← indEDecl #[boundary.publicOwner]
    let iso ← changedIso source boundary
    let report ← FamilyAdapter.deriveShadowPlan source iso
    if report.plan?.isNone then
      let failures := result.failures.push
        s!"{boundary.publicOwner}: no changed exact plan: {repr report.reasons}"
      result := { result with failures }
      continue
    let built ← (FamilyAdapter.buildFamilyPrototype report iso
      ((`_family_adapter_construction_test_changed).append boundary.publicOwner)).run
    match built with
    | .error decline =>
      let failures := result.failures.push s!"{boundary.publicOwner}: {decline.label}"
      result := { result with failures }
    | .ok built =>
      if boundary.publicOwner == changedNested.publicOwner then
        let keyedPlan := report.plan?.any fun plan => plan.containerMaps.any fun container =>
          container.key.target.owner == boundary.publicOwner &&
            container.maps.forward ==
              `FamilyAdapterGenerated.generatedChangedNestedContainerForward
        let keyedCertificate := built.certificate.any fun certificate =>
          certificate.occurrences.any fun occurrence =>
            occurrence.key.target.owner == boundary.publicOwner &&
              occurrence.maps.forward ==
                `FamilyAdapterGenerated.generatedChangedNestedContainerForward
        if built.issues.isEmpty && keyedPlan && keyedCertificate then
          result := { result with changed := result.changed + 1 }
          result := { result with closedContainers := result.closedContainers + 1 }
        else
          let failures := result.failures.push
            s!"{boundary.publicOwner}: changed nested map did not close generically: {
              repr built.issues}"
          result := { result with failures }
      else if built.certificate.isSome && built.issues.isEmpty then
        result := { result with changed := result.changed + 1 }
      else
        let failures := result.failures.push
          s!"{boundary.publicOwner}: changed boundary did not close: {repr built.issues}"
        result := { result with failures }
  let invalidBoundary := { changedDirect with forward := .anonymous }
  let invalidSource ← indEDecl #[invalidBoundary.publicOwner]
  let invalidIso ← changedIso invalidSource invalidBoundary
  let invalidReport ← FamilyAdapter.deriveShadowPlan invalidSource invalidIso
  let invalidBuilt ← (FamilyAdapter.buildFamilyPrototype invalidReport invalidIso
    `_family_adapter_construction_test_invalid_map).run
  match invalidBuilt with
  | .error decline =>
    let failures := result.failures.push s!"invalid member map: {decline.label}"
    result := { result with failures }
  | .ok built =>
    let keyedMapGap := built.issues.any fun
      | .missingInstalledMemberMap member map =>
          member.owner == invalidBoundary.publicOwner && map.isAnonymous
      | _ => false
    if built.certificate.isNone && keyedMapGap && built.declarations.isEmpty then
      result := { result with invalidMaps := result.invalidMaps + 1 }
    else
      let failures := result.failures.push
        s!"invalid member map was not rejected: {repr built.issues}"
      result := { result with failures }
  let invalidContainerSource ← indEDecl #[changedNested.publicOwner]
  let validContainerIso ← changedIso invalidContainerSource changedNested
  let validContainer := validContainerIso.containerImplementations[0]!
  let invalidContainer := { validContainer with forward := validContainer.backward }
  let invalidContainerIso :=
    { validContainerIso with containerImplementations := #[invalidContainer] }
  let invalidContainerReport ←
    FamilyAdapter.deriveShadowPlan invalidContainerSource invalidContainerIso
  let invalidContainerBuilt ← (FamilyAdapter.buildFamilyPrototype invalidContainerReport
    invalidContainerIso `_family_adapter_construction_test_invalid_container_map).run
  match invalidContainerBuilt with
  | .error decline =>
    let failures := result.failures.push s!"invalid container map: {decline.label}"
    result := { result with failures }
  | .ok built =>
    let exactMismatch := invalidContainerReport.reasons.any fun
      | .installedContainerMapTypeMismatch occurrence name =>
          occurrence.target.owner == changedNested.publicOwner &&
            name == validContainer.backward
      | _ => false
    if exactMismatch && invalidContainerReport.coverage.containerMaps.isEmpty &&
        built.certificate.isNone && built.declarations.isEmpty then
      result := { result with invalidContainerMaps := result.invalidContainerMaps + 1 }
    else
      let failures := result.failures.push
        s!"invalid container metadata was not rejected atomically: shadow={
          repr invalidContainerReport.reasons}, construction={repr built.issues}"
      result := { result with failures }
  let wrongTargetName :=
    `FamilyAdapterGenerated.generatedChangedNestedContainerWrongTarget
  let wrongTargetType := (← getEnv).constants.find! wrongTargetName |>.type
  let wrongTargetContainer :=
    { validContainer with forward := wrongTargetName, forwardType := wrongTargetType }
  let wrongTargetIso :=
    { validContainerIso with containerImplementations := #[wrongTargetContainer] }
  let wrongTargetReport ← FamilyAdapter.deriveShadowPlan invalidContainerSource wrongTargetIso
  let wrongTargetBuilt ← (FamilyAdapter.buildFamilyPrototype wrongTargetReport wrongTargetIso
    `_family_adapter_construction_test_wrong_container_target).run
  match wrongTargetBuilt with
  | .error decline =>
    let failures := result.failures.push s!"wrong container target: {decline.label}"
    result := { result with failures }
  | .ok built =>
    let keyedMissing := wrongTargetReport.reasons.any fun
      | .missingContainerMap occurrence =>
          occurrence.target.owner == changedNested.publicOwner
      | _ => false
    if keyedMissing && wrongTargetReport.coverage.containerMaps.isEmpty &&
        built.certificate.isNone && built.declarations.isEmpty then
      result := { result with wrongTargetMaps := result.wrongTargetMaps + 1 }
    else
      let failures := result.failures.push
        s!"wrong container target entered the plan: shadow={repr wrongTargetReport.reasons}, \
          construction={repr built.issues}"
      result := { result with failures }
  let installedOwners := #[`FamilyAdapterGenerated.GeneratedLayerA,
    `FamilyAdapterGenerated.GeneratedLayerB]
  let installedSource ← indEDecl installedOwners
  match ← (mutualOneLayerIso installedSource {}).run with
  | .error decline =>
    let failures := result.failures.push s!"installed changed family: {decline.label}"
    result := { result with failures }
  | .ok installedIso =>
    let installedReport ← FamilyAdapter.deriveShadowPlan installedSource installedIso
    let installedBuilt ← (FamilyAdapter.buildFamilyPrototype installedReport installedIso
      `_family_adapter_construction_test_installed_family).run
    match installedBuilt with
    | .error decline =>
      let failures := result.failures.push s!"installed family prototype: {decline.label}"
      result := { result with failures }
    | .ok built =>
      if installedIso.familyImplementation?.isSome && built.certificate.isSome &&
          built.issues.isEmpty then
        result := { result with installedFamily := result.installedFamily + 1 }
      else
        let failures := result.failures.push
          s!"installed family did not close: shadow={repr installedReport.reasons}, \
            construction={repr built.issues}"
        result := { result with failures }
  return result

def runMain : IO UInt32 := do
  initSearchPath (← findSysroot)
  let environment ← importModules #[`Init, `family_adapter_generated] {}
  let context : Core.Context :=
    { fileName := "<family-adapter-construction-test>", fileMap := default,
      options := {}, maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, state) ← Core.CoreM.toIO (MetaM.run' runSamples) context { env := environment }
  if result.failures.isEmpty && result.complete == completeSamples.size &&
      result.identityNested == nestedSamples.size && result.changed == 3 &&
      result.closedContainers == 1 && result.invalidMaps == 1 && result.invalidContainerMaps == 1 &&
      result.wrongTargetMaps == 1 &&
      result.installedFamily == 1 &&
      state.messages.toArray.isEmpty then
    IO.println s!"family adapter construction: {result.complete} complete finite plans, \
      {result.identityNested} definitional nested plans, {result.changed} changed plans, \
      one installed family, {result.closedContainers} keyed container map, \
      validated member/container map metadata"
    return 0
  for failure in result.failures do IO.eprintln failure
  for message in state.messages.toArray do IO.eprintln (← message.toString)
  IO.eprintln s!"family adapter construction: complete={result.complete}, \
    identityNested={result.identityNested}, changed={result.changed}, \
    installedFamily={result.installedFamily}, closedContainers={result.closedContainers}, \
    invalidMaps={result.invalidMaps}, invalidContainerMaps={result.invalidContainerMaps}, \
    wrongTargetMaps={result.wrongTargetMaps}"
  return 1

end FamilyAdapterConstructionTest

def main : IO UInt32 := FamilyAdapterConstructionTest.runMain
