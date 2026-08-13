#!/usr/bin/env bash
# Regenerate raw monomorphization fixtures from their adjacent Lean sources.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
FIXTURES="$ROOT/test/fixtures/mono"

declare -a NAMES=()
if (($#)); then
  for arg in "$@"; do NAMES+=("$(basename "$arg" .lean)"); done
else
  while IFS= read -r file; do NAMES+=("$(basename "$file" .lean)"); done \
    < <(find "$FIXTURES" -maxdepth 1 -type f -name '*.lean' | sort)
fi

for name in "${NAMES[@]}"; do
  FIXTURE_DIR="$FIXTURES" OUT_DIR="$FIXTURES" LEAN_INDUCTIVE_MODELS_FILTER=0 \
    bash "$ROOT/scripts/export-fixture.sh" "$name.lean"
done
