#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$root"

mkdir -p "$root/_tmp/build-tmp"
export TMPDIR="${TMPDIR:-$root/_tmp/build-tmp}"

# Bound Lake's build parallelism. Lake 5.0.0 has no job-count flag -- `-j` is
# gone and `-K` only sets a configuration key no lakefile here reads -- so the
# `-Kjobs=1` this loop used to pass did nothing at all. Lake schedules build
# jobs as Lean tasks, so the runtime thread pool is the bound that exists.
# See docs/maintainers/Testing.md for the measurements behind the value.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"

# One root per invocation: at most one target link live, and a named target on
# failure. Not serialization; Lake still runs up to LEAN_NUM_THREADS jobs.
build_bounded() {
  local target
  for target in "$@"; do
    lake build "$target"
  done
}

compile_only_targets=(
  FamilyAdapterConstruction
  FamilyAdapterPlan
  FamilyAdapterShadow
  OneLayerProjectionPrototype
  OneLayerRecursorProof
)
correctness_targets=(
  test clitest generationflagstest checktest kernelchecktest ordertest
  familyadapterplantest familyadaptershadowtest familyadapterconstructiontest
  incrementalordertest namingtest drivernamingtest privatealiastest sourcereplayaliastest
  simplenamingtest rulektest defaultctoriotatest sourcestructuresyntaxtest
  composedrecursorsyntaxtest mainclitest projectiontest projectiontransportcensustest
  emissionordercensustest
  indexedfibrediagnostictest
  mutualonelayerdiagnostictest structureetatest
  deepimaxboxtest psigmaprimetest exactsortlifttest
  tightpsigmaprimeroutetest vanishingerasuretest
  transparentowneraliasestest exportsyntaxnormalizationtest
  basisvalidationtest arenaformattest
)

build_bounded lean-inductive-models
build_bounded "${compile_only_targets[@]}"
build_bounded "${correctness_targets[@]}"

lake exe test "$root"
lake exe clitest
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
lake exe projectiontransportcensustest "$root"
lake exe emissionordercensustest "$root"
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
lake exe arenaformattest "$root"

PYTHONDONTWRITEBYTECODE=1 python3 test/scripts/test_family_adapter_fixture_generator.py
python3 test/scripts/generate_family_adapter_fixtures.py \
  --output test/fixtures/inductive-models/family_adapter_generated.lean --check

test/scripts/check_arena_corpus.py
test/scripts/check-hard-nested-a.sh
test/scripts/check-hard-nested-c.sh
test/scripts/check-mathlib-result.sh
test/scripts/check-lean4export-patch.sh
test/scripts/check-ci-serialized-builds.sh
test/scripts/check-checker-imports.sh
