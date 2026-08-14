#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$root"

mkdir -p "$root/_tmp/build-tmp"
export TMPDIR="${TMPDIR:-$root/_tmp/build-tmp}"

build_serially() {
  local target
  for target in "$@"; do
    lake -Kjobs=1 build "$target"
  done
}

compile_only_targets=(
  OneLayerProjectionPrototype
  OneLayerRecursorProof
)
correctness_targets=(
  test monotest clitest supervisortest generationflagstest checktest kernelchecktest ordertest
  familyadapterplantest familyadaptershadowtest familyadapterconstructiontest
  incrementalordertest namingtest drivernamingtest privatealiastest sourcereplayaliastest
  simplenamingtest rulektest defaultctoriotatest sourcestructuresyntaxtest
  composedrecursorsyntaxtest mainclitest projectiontest indexedfibrediagnostictest
  mutualonelayerdiagnostictest structureetatest
  deepimaxboxtest psigmaprimetest exactsortlifttest
  tightpsigmaprimeroutetest vanishingerasuretest
  transparentowneraliasestest exportsyntaxnormalizationtest
  basisvalidationtest sourcespooltest
)

build_serially lean-inductive-models
build_serially "${compile_only_targets[@]}"
build_serially "${correctness_targets[@]}"

lake exe test "$root"
lake exe monotest "$root"
lake exe clitest
lake exe supervisortest --run-tests "$root/.lake/build/bin/supervisortest"
lake exe generationflagstest
lake exe checktest "$root"
lake exe kernelchecktest "$root"
lake exe familyadapterplantest
lake exe familyadaptershadowtest
lake exe familyadapterconstructiontest
lake exe ordertest "$root"
lake exe incrementalordertest "$root"
lake exe namingtest
lake exe drivernamingtest
lake exe privatealiastest
lake exe sourcereplayaliastest
lake exe simplenamingtest
lake exe rulektest
lake exe defaultctoriotatest "$root"
lake exe sourcestructuresyntaxtest "$root"
lake exe composedrecursorsyntaxtest "$root"
lake exe mainclitest "$root"
lake exe projectiontest
lake exe indexedfibrediagnostictest "$root"
lake exe mutualonelayerdiagnostictest "$root"
lake exe structureetatest
lake exe deepimaxboxtest
lake exe psigmaprimetest
lake exe exactsortlifttest
lake exe tightpsigmaprimeroutetest
lake exe vanishingerasuretest
lake exe transparentowneraliasestest
lake exe exportsyntaxnormalizationtest
lake exe basisvalidationtest
lake exe sourcespooltest "$root"

PYTHONDONTWRITEBYTECODE=1 python3 test/scripts/test_family_adapter_fixture_generator.py
python3 test/scripts/generate_family_adapter_fixtures.py \
  --output test/fixtures/inductive-models/family_adapter_generated.lean --check

test/scripts/check_arena_corpus.py
test/scripts/check-hard-nested-a.sh
test/scripts/check-hard-nested-c.sh
test/scripts/check-mathlib-result.sh
test/scripts/check-lean4export-patch.sh
test/scripts/check-shared-prefix-ownership.sh
test/scripts/check-ci-serialized-builds.sh
