#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$root"

mkdir -p "$root/_tmp/build-tmp"
export TMPDIR="${TMPDIR:-$root/_tmp/build-tmp}"

# Bound Lake's build parallelism. Lake 5.0.0 has no job-count flag -- `-j` is
# gone and `-K` only sets a configuration key a TOML lakefile cannot read -- so the
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
  OneLayerProjectionPrototype
  OneLayerRecursorProof
)
# One binary, one suite per invocation, named by its first argument. Every
# suite takes the repository root as its optional first argument or ignores
# `argv` entirely, so passing it to all of them is exactly what each one did
# before. `test/TestMain.lean` holds the registry these names come from.
correctness_suites=(
  fixtures cli generationflags check kernelcheck order
  familyadapterplan familyadaptershadow familyadapterconstruction
  incrementalorder naming drivernaming privatealias sourcereplayalias
  simplenaming rulek defaultctoriota sourcestructuresyntax
  composedrecursorsyntax maincli projection projectiontransportcensus
  emissionordercensus
  indexedfibrediagnostic
  mutualonelayerdiagnostic structureeta
  deepimaxbox psigmaprime exactsortlift
  tightpsigmaprimeroute vanishingerasure
  transparentowneralias exportsyntaxnormalization
  basisvalidation arenaformat
)

build_bounded lean-inductive-models
build_bounded "${compile_only_targets[@]}"
build_bounded test

for suite in "${correctness_suites[@]}"; do
  lake exe test "$suite" "$root"
done

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
test/scripts/check-no-known-gap.sh
