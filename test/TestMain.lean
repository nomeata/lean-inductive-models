import Test
import CliTest
import GenerationFlagsTest
import CheckTest
import KernelCheckTest
import OrderTest
import IncrementalOrderTest
import NamingTest
import DriverNamingTest
import PrivateAliasTest
import SourceReplayAliasTest
import SimpleNamingTest
import RuleKTest
import DefaultCtorIotaTest
import SourceStructureSyntaxTest
import ComposedRecursorSyntaxTest
import MainCliTest
import ProjectionTest
import ProjectionTransportCensusTest
import EmissionOrderCensusTest
import IndexedFibreDiagnosticTest
import MutualOneLayerDiagnosticTest
import StructureEtaTest
import DeepImaxBoxTest
import PSigmaPrimeTest
import ExactSortLiftTest
import TightPSigmaPrimeRouteTest
import VanishingErasureTest
import TransparentOwnerAliasTest
import ExportSyntaxNormalizationTest
import BasisValidationTest
import ArenaFormatTest
import FamilyAdapterPlanTest
import FamilyAdapterShadowTest
import FamilyAdapterConstructionTest
import MemoryProbe

/-!
# One test binary, one suite per invocation

Every suite used to be its own `lean_exe`, and every one of those linked the
whole library into a separate ~230 MB binary: 39 targets, 8.5 GB of
`.lake/build/bin`, and the same link cost paid once per suite. The suites are
one closure of Lean modules, so they are one program; the only thing that made
them 39 programs was 39 `main`s.

They are one program now, and the suite name is its first argument:

```console
lake exe test fixtures "$PWD"
lake exe test kernelcheck "$PWD"
lake exe test cli
```

**One suite per process, still.** A suite that spawns the CLI, imports modules,
or builds an environment gets the same fresh process it always had; this
dispatcher runs exactly the one suite it is named and never a second. What it
does not do is run every suite in one process — several of them install
environments and search paths, and their independence is worth more than the
process.

Remaining arguments are passed through untouched, so the suites that read a
repository root out of `args.head?` still get it and the ones that ignore
`argv` still ignore it. `memoryprobe` is a diagnostic rather than a correctness
suite — `lake exe test memoryprobe whole INPUT.ndjson` — and is listed apart
from `correctnessSuites` for that reason: `test/scripts/run-correctness.sh`,
`.github/workflows/ci.yml` and `docs/maintainers/Testing.md` run the
correctness list, and `test/scripts/check-ci-serialized-builds.sh` asserts that
the three agree with the registry below.
-/

/-- A named suite: the name `lake exe test` dispatches on, and the suite's own
`main` under the module's namespace. -/
structure Suite where
  name : String
  run : List String → IO UInt32

/-- `suite name run` is `Suite.mk`, spelled so that one registry entry fits on
one line and a shell script can read the names back out of this file. -/
def suite (name : String) (run : List String → IO UInt32) : Suite := ⟨name, run⟩

/-- The correctness suites, in the order `run-correctness.sh` runs them. -/
def correctnessSuites : List Suite :=
  [ suite "fixtures"                   Test.main
  , suite "cli"                        (fun _ => CliTest.main)
  , suite "generationflags"            (fun _ => GenerationFlagsTest.main)
  , suite "check"                      CheckTest.main
  , suite "kernelcheck"                InductiveModels.KernelCheck.Tests.main
  , suite "order"                      InductiveModels.Order.Tests.main
  , suite "incrementalorder"           InductiveModels.IncrementalOrder.Tests.main
  , suite "naming"                     NamingTest.main
  , suite "drivernaming"               (fun _ => DriverNamingTest.main)
  , suite "privatealias"               (fun _ => PrivateAliasTest.main)
  , suite "sourcereplayalias"          (fun _ => SourceReplayAliasTest.main)
  , suite "simplenaming"               (fun _ => SimpleNamingTest.main)
  , suite "rulek"                      (fun _ => RuleKTest.main)
  , suite "defaultctoriota"            DefaultCtorIotaTest.main
  , suite "sourcestructuresyntax"      SourceStructureSyntaxTest.main
  , suite "composedrecursorsyntax"     ComposedRecursorSyntaxTest.main
  , suite "maincli"                    MainCliTest.main
  , suite "projection"                 (fun _ => ProjectionTest.main)
  , suite "projectiontransportcensus"  ProjectionTransportCensusTest.main
  , suite "emissionordercensus"        EmissionOrderCensusTest.main
  , suite "indexedfibrediagnostic"     IndexedFibreDiagnosticTest.main
  , suite "mutualonelayerdiagnostic"   MutualOneLayerDiagnosticTest.main
  , suite "structureeta"               (fun _ => StructureEtaTest.main)
  , suite "deepimaxbox"                (fun _ => DeepImaxBoxTest.main)
  , suite "psigmaprime"                (fun _ => PSigmaPrimeTest.main)
  , suite "exactsortlift"              (fun _ => ExactSortLiftTest.main)
  , suite "tightpsigmaprimeroute"      (fun _ => TightPSigmaPrimeRouteTest.main)
  , suite "vanishingerasure"           (fun _ => VanishingErasureTest.main)
  , suite "transparentowneralias"      (fun _ => TransparentOwnerAliasTest.main)
  , suite "exportsyntaxnormalization"  ExportSyntaxNormalizationTest.main
  , suite "basisvalidation"            (fun _ => BasisValidationTest.main)
  , suite "arenaformat"                ArenaFormatTest.main
  , suite "familyadapterplan"          (fun _ => FamilyAdapterPlanTest.main)
  , suite "familyadaptershadow"        (fun _ => FamilyAdapterShadowTest.main)
  , suite "familyadapterconstruction"  (fun _ => FamilyAdapterConstructionTest.main)
  ]

/-- Diagnostics. Useful during development, not correctness suites, and not run
by `run-correctness.sh` or CI. -/
def diagnosticSuites : List Suite :=
  [ suite "memoryprobe"                MemoryProbe.main
  ]

def suites : List Suite := correctnessSuites ++ diagnosticSuites

private def usage : IO Unit := do
  IO.eprintln "usage: lake exe test SUITE [ARGS...]"
  IO.eprintln "correctness suites:"
  for s in correctnessSuites do IO.eprintln s!"  {s.name}"
  IO.eprintln "diagnostics:"
  for s in diagnosticSuites do IO.eprintln s!"  {s.name}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.eprintln "test: no suite named"
    usage
    return 2
  | name :: rest =>
    match suites.find? (·.name == name) with
    | some s => s.run rest
    | none =>
      IO.eprintln s!"test: unknown suite {name}"
      usage
      return 2
