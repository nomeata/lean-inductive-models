import Lake

open System Lake DSL

package «lean-inductive-models» where testDriver := "test"

/-- Native filesystem primitives used by the bounded spool copier. Kept in one
small archive so every executable importing `Modelgen.Spool` resolves the same
portable seek and secure-workspace implementation. -/
extern_lib lean_inductive_models_spool (pkg : NPackage __name__) := do
  let source ← inputFile (pkg.dir / "c/InductiveModelsSpool.c") true
  let object ← buildLeanO (pkg.buildDir / "ir/InductiveModelsSpool.c.o") source
  buildStaticLib (pkg.staticLibDir / "liblean_inductive_models_spool.a") #[object]

lean_lib Modelgen where
  srcDir := "src"
  globs := #[`Modelgen.+]

@[default_target] lean_exe «lean-inductive-models» where
  srcDir := "src"
  root := `Main
  supportInterpreter := true

lean_exe test where
  srcDir := "test"
  root := `Test
  supportInterpreter := true

lean_exe monotest where
  srcDir := "test"
  root := `MonoTest
  supportInterpreter := true

lean_exe clitest where
  srcDir := "test"
  root := `CliTest
  supportInterpreter := true

lean_exe supervisortest where
  srcDir := "test"
  root := `SupervisorTest
  supportInterpreter := true
  -- Test-only C source: linked into no production executable.
  moreLinkArgs := #["test/SupervisorSignal.c"]

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

lean_exe stagedwritertest where
  srcDir := "test"
  root := `StagedWriterTest
  supportInterpreter := true

lean_exe projectiontest where
  srcDir := "test"
  root := `ProjectionTest
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

lean_lib OneLayerProjectionPrototype where
  srcDir := "test"
  roots := #[`OneLayerProjectionPrototype]

-- Diagnostics: these targets are useful during development, but are not
-- correctness suites and are not part of the default build.
lean_exe envprobe where
  srcDir := "tools"
  root := `EnvProbe
  supportInterpreter := true

lean_exe levelfuzz where
  srcDir := "tools"
  root := `LevelFuzz
