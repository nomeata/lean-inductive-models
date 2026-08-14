import InductiveModels.Driver
import InductiveModels.FamilyAdapterConstruction
import family_adapter_generated

open Lean Meta InductiveModels

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

def nestedSamples : Array Name :=
  #[`FamilyAdapterGenerated.GeneratedNested1,
    `FamilyAdapterGenerated.GeneratedNested2,
    `FamilyAdapterGenerated.GeneratedNested3,
    `FamilyAdapterGenerated.GeneratedNested5,
    `FamilyAdapterGenerated.GeneratedNested8]

structure Result where
  complete : Nat := 0
  blocked : Nat := 0
  failures : Array String := #[]

def runSamples : MetaM Result := do
  let mut result : Result := {}
  for owner in directSamples ++ dependentSamples ++ infinitarySamples ++ indexedSamples do
    let source ← indEDecl #[owner]
    let iso := identityIso source
    let report ← FamilyAdapter.deriveShadowPlan source iso
    let some plan := report.plan? | do
      result := { result with failures := result.failures.push s!"{owner}: no exact plan" }
      continue
    let built ← (FamilyAdapter.buildFamilyPrototype plan iso
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
    let some plan := report.plan? | do
      result := { result with failures := result.failures.push s!"{owner}: no exact plan" }
      continue
    let built ← (FamilyAdapter.buildFamilyPrototype plan iso
      ((`_family_adapter_construction_test).append owner)).run
    match built with
    | .error decline =>
      result := { result with failures := result.failures.push s!"{owner}: {decline.label}" }
    | .ok built =>
      let keyedContainerGap := built.issues.any fun
        | .missingContainerMap occurrence => occurrence.target.owner == owner
        | _ => false
      if built.certificate.isNone && keyedContainerGap then
        result := { result with blocked := result.blocked + 1 }
      else
        let failures := result.failures.push
          s!"{owner}: nested map obligation was not explicit: {repr built.issues}"
        result := { result with failures }
  return result

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let environment ← importModules #[`family_adapter_generated] {}
  let context : Core.Context :=
    { fileName := "<family-adapter-construction-test>", fileMap := default,
      options := {}, maxHeartbeats := 0, maxRecDepth := 8192 }
  let (result, state) ← Core.CoreM.toIO (MetaM.run' runSamples) context { env := environment }
  if result.failures.isEmpty && result.complete ==
      (directSamples ++ dependentSamples ++ infinitarySamples ++ indexedSamples).size &&
      result.blocked == nestedSamples.size && state.messages.toArray.isEmpty then
    IO.println s!"family adapter construction: {result.complete} complete finite plans, \
      {result.blocked} keyed container-map obligations"
    return 0
  for failure in result.failures do IO.eprintln failure
  for message in state.messages.toArray do IO.eprintln (← message.toString)
  IO.eprintln s!"family adapter construction: complete={result.complete}, blocked={result.blocked}"
  return 1

end FamilyAdapterConstructionTest
