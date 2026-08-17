import Lake

open System Lake DSL

-- `lake test` is the quick fixture suite, which is now one suite of the one
-- test executable rather than the whole of it: without the argument the
-- dispatcher would print its registry and exit 2.
package lean_inductive_models where
  testDriver := "test"
  testDriverArgs := #["fixtures"]

lean_lib InductiveModels where
  srcDir := "src"
  globs := #[`InductiveModels.+]

@[default_target] lean_exe «lean-inductive-models» where
  srcDir := "src"
  root := `Main
  supportInterpreter := true

-- One binary for every suite, dispatching on its first argument; see
-- `test/TestMain.lean`. `Test.runCli` and `MainCliTest` spawn
-- `.lake/build/bin/lean-inductive-models` as a subprocess, so the CLI target
-- has to be built before those suites run. Without the `needs` they silently
-- assert the CLI contract against whatever stale binary is on disk.
lean_exe test where
  srcDir := "test"
  root := `TestMain
  needs := #[`@/«lean-inductive-models»]
  supportInterpreter := true

/-- The suite modules the dispatcher imports. Lake resolves an import to a
module of a declared library, so a suite that is no longer its own executable
root has to be listed here to be found at all — and a suite missing from this
list fails the build rather than being silently skipped, because `TestMain`
imports every one of them. -/
lean_lib TestSuites where
  srcDir := "test"
  roots := #[
    `Test, `CliTest, `GenerationFlagsTest, `CheckTest, `KernelCheckTest,
    `OrderTest, `IncrementalOrderTest, `NamingTest, `DriverNamingTest,
    `PrivateAliasTest, `SourceReplayAliasTest, `SimpleNamingTest, `RuleKTest,
    `DefaultCtorIotaTest, `SourceStructureSyntaxTest, `ComposedRecursorSyntaxTest,
    `MainCliTest, `ProjectionTest, `ProjectionTransportCensusTest,
    `EmissionOrderCensusTest, `IndexedFibreDiagnosticTest,
    `MutualOneLayerDiagnosticTest, `StructureEtaTest, `DeepImaxBoxTest,
    `PSigmaPrimeTest, `ExactSortLiftTest, `TightPSigmaPrimeRouteTest,
    `VanishingErasureTest, `TransparentOwnerAliasTest,
    `ExportSyntaxNormalizationTest, `BasisValidationTest, `ArenaFormatTest,
    `FamilyAdapterPlanTest, `FamilyAdapterShadowTest, `FamilyAdapterConstructionTest,
    `MemoryProbe]

lean_lib FamilyAdapterGeneratedFixtures where
  srcDir := "test/fixtures/inductive-models"
  roots := #[`family_adapter_generated]

/-- The parked family-adapter experiment, in its three layers. All three are
test-only: no module under `src/` imports any of them, and the experiment emits
nothing. `Driver` reaches an observation only through the opaque
`IslandObserver` seam, so it names no type from these modules and the shipped
executable's object closure contains none of them. They are declared as their
own libraries rather than as modules of `InductiveModels` for exactly that
reason; only the test binary, through the `familyadapterplan`,
`familyadaptershadow` and `familyadapterconstruction` suites, builds them. -/
lean_lib FamilyAdapterPlan where
  srcDir := "test"
  roots := #[`FamilyAdapterPlan]

lean_lib FamilyAdapterShadow where
  srcDir := "test"
  roots := #[`FamilyAdapterShadow]

lean_lib FamilyAdapterConstruction where
  srcDir := "test"
  roots := #[`FamilyAdapterConstruction]

lean_lib OneLayerProjectionPrototype where
  srcDir := "test"
  roots := #[`OneLayerProjectionPrototype]

/-- Compile-time application oracle for the embedded one-layer recursor proof. -/
lean_lib OneLayerRecursorProof where
  srcDir := "test"
  roots := #[`OneLayerRecursorProof]

-- Diagnostics: these targets are useful during development, but are not
-- correctness suites and are not part of the default build.
lean_exe envprobe where
  srcDir := "tools"
  root := `EnvProbe
  supportInterpreter := true

lean_exe levelfuzz where
  srcDir := "tools"
  root := `LevelFuzz
