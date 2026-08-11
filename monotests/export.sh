#!/usr/bin/env bash
# Export this directory's `.lean` sources to `.ndjson`, using the repository's
# own `scripts/export-fixture.sh` — same toolchain, same `lean4export` revision,
# same `--#export` convention — **unfiltered**, and without writing into
# `mini/tests/fixtures`.
#
#   ./modelgen/monotests/export.sh [NAME[.lean] ...]
#
# `MODELGEN_FILTER=0`: `scripts/export-fixture.sh` splices the model of every
# nested inductive into what it writes, because `mini/tests/fixtures` must
# arrive filtered. Nothing here nests, so the pass is the identity today and
# the flag changes no byte — but the monomorphiser's input is meant to be what
# `lean4export` emitted, and a monotest fixture that later grows a nested
# inductive should not silently acquire a model too. `modelgen/tests/export.sh`
# carries the same flag for a reason that is not hypothetical.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
declare -a NAMES=()
if (($#)); then
  for a in "$@"; do NAMES+=("$(basename "$a" .lean)"); done
else
  while IFS= read -r f; do NAMES+=("$(basename "$f" .lean)"); done \
    < <(find "$HERE" -name '*.lean' | sort)
fi
for b in "${NAMES[@]}"; do
  FIXTURE_DIR="$HERE" OUT_DIR="$HERE" MODELGEN_FILTER=0 \
    bash "$ROOT/scripts/export-fixture.sh" "$b.lean"
done
