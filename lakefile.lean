import Lake

open System Lake DSL

package lean_inductive_models where testDriver := "test"

lean_lib InductiveModels where
  srcDir := "src"
  globs := #[`InductiveModels.+]

@[default_target] lean_exe «lean-inductive-models» where
  srcDir := "src"
  root := `Main
  supportInterpreter := true

lean_exe test where
  srcDir := "test"
  root := `Test
  supportInterpreter := true

lean_exe clitest where
  srcDir := "test"
  root := `CliTest
  supportInterpreter := true

lean_exe supervisortest where
  srcDir := "test"
  root := `SupervisorTest
  supportInterpreter := true

lean_exe generationflagstest where
  srcDir := "test"
  root := `GenerationFlagsTest
  supportInterpreter := true

lean_exe checktest where
  srcDir := "test"
  root := `CheckTest
  supportInterpreter := true

lean_exe ordertest where
  srcDir := "test"
  root := `OrderTest
  supportInterpreter := true

lean_exe kernelchecktest where
  srcDir := "test"
  root := `KernelCheckTest
  supportInterpreter := true

lean_exe incrementalordertest where
  srcDir := "test"
  root := `IncrementalOrderTest
  supportInterpreter := true

lean_exe namingtest where
  srcDir := "test"
  root := `NamingTest
  supportInterpreter := true

lean_exe drivernamingtest where
  srcDir := "test"
  root := `DriverNamingTest
  supportInterpreter := true

lean_exe privatealiastest where
  srcDir := "test"
  root := `PrivateAliasTest
  supportInterpreter := true

lean_exe sourcereplayaliastest where
  srcDir := "test"
  root := `SourceReplayAliasTest
  supportInterpreter := true

lean_exe simplenamingtest where
  srcDir := "test"
  root := `SimpleNamingTest
  supportInterpreter := true

lean_exe rulektest where
  srcDir := "test"
  root := `RuleKTest
  supportInterpreter := true

lean_exe defaultctoriotatest where
  srcDir := "test"
  root := `DefaultCtorIotaTest
  supportInterpreter := true

lean_exe sourcestructuresyntaxtest where
  srcDir := "test"
  root := `SourceStructureSyntaxTest
  supportInterpreter := true

lean_exe composedrecursorsyntaxtest where
  srcDir := "test"
  root := `ComposedRecursorSyntaxTest
  supportInterpreter := true

lean_exe mainclitest where
  srcDir := "test"
  root := `MainCliTest

lean_exe memoryprobe where
  srcDir := "test"
  root := `MemoryProbe
  supportInterpreter := true

lean_exe sourcespooltest where
  srcDir := "test"
  root := `SourceSpoolTest
  supportInterpreter := true

lean_exe projectiontest where
  srcDir := "test"
  root := `ProjectionTest
  supportInterpreter := true

lean_exe indexedfibrediagnostictest where
  srcDir := "test"
  root := `IndexedFibreDiagnosticTest
  supportInterpreter := true

lean_exe mutualonelayerdiagnostictest where
  srcDir := "test"
  root := `MutualOneLayerDiagnosticTest
  supportInterpreter := true

lean_exe structureetatest where
  srcDir := "test"
  root := `StructureEtaTest
  supportInterpreter := true

lean_exe deepimaxboxtest where
  srcDir := "test"
  root := `DeepImaxBoxTest
  supportInterpreter := true

lean_exe psigmaprimetest where
  srcDir := "test"
  root := `PSigmaPrimeTest
  supportInterpreter := true

lean_exe exactsortlifttest where
  srcDir := "test"
  root := `ExactSortLiftTest
  supportInterpreter := true

lean_exe tightpsigmaprimeroutetest where
  srcDir := "test"
  root := `TightPSigmaPrimeRouteTest
  supportInterpreter := true

lean_exe vanishingerasuretest where
  srcDir := "test"
  root := `VanishingErasureTest
  supportInterpreter := true

lean_exe transparentowneraliasestest where
  srcDir := "test"
  root := `TransparentOwnerAliasTest
  supportInterpreter := true

lean_exe exportsyntaxnormalizationtest where
  srcDir := "test"
  root := `ExportSyntaxNormalizationTest
  supportInterpreter := true

lean_exe basisvalidationtest where
  srcDir := "test"
  root := `BasisValidationTest
  supportInterpreter := true

lean_exe familyadapterplantest where
  srcDir := "test"
  root := `FamilyAdapterPlanTest
  supportInterpreter := true

lean_exe familyadaptershadowtest where
  srcDir := "test"
  root := `FamilyAdapterShadowTest
  supportInterpreter := true

lean_exe familyadapterconstructiontest where
  srcDir := "test"
  root := `FamilyAdapterConstructionTest
  supportInterpreter := true

lean_lib FamilyAdapterGeneratedFixtures where
  srcDir := "test/fixtures/inductive-models"
  roots := #[`family_adapter_generated]

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
