#!/usr/bin/env bash
# Export this directory's fixtures to `.ndjson`, using the repository's own
# `scripts/export-fixture.sh` — same toolchain, same `lean4export` revision,
# same `--#export` convention — **unfiltered**, and without writing into
# `mini/tests/fixtures`.
#
#   ./modelgen/tests/export.sh [NAME[.lean] ...]
#
# # Why unfiltered
#
# `scripts/export-fixture.sh` passes everything it writes through `modelgen`,
# because `mini/tests/fixtures` has to arrive with the model already spliced in
# so `cargo test` needs no Lean. That is exactly the wrong input *here*: the
# filter is idempotent, so on its own output the generator declines `nested
# model name taken` and axes 1–3 of `Test.lean` — the counts, the kernel, the
# statements — measure nothing. `MODELGEN_FILTER=0` is what this directory
# needs and what this script sets.
#
# # The two source directories
#
# Most fixtures here have their `.lean` beside them. **The five shared shapes
# do not**: `nested_iota`, `nested_deep`, `nested_shapes`, `nested_iota_arm`
# and `nested_keying` are `mini/tests/fixtures`' sources, and a second copy
# would be a second thing to keep in step. They are exported from there into
# here instead — one `.lean`, two `.ndjson`, one filtered and one raw — and
# `Test.lean`'s `runShared` cross-checks the pair, so a raw copy that has
# drifted from the fixture beside its source is a test failure rather than a
# silent divergence.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
FIX="$HERE"

# The shapes whose `.lean` lives in `mini/tests/fixtures`.
SHARED=(nested_iota nested_deep nested_shapes nested_iota_arm nested_keying)
is_shared() { local n; for n in "${SHARED[@]}"; do [[ "$n" == "$1" ]] && return 0; done; return 1; }

declare -a NAMES=()
if (($#)); then
  for a in "$@"; do NAMES+=("$(basename "$a" .lean)"); done
else
  while IFS= read -r f; do NAMES+=("$(basename "$f" .lean)"); done \
    < <(find "$HERE" -name '*.lean' | sort)
  NAMES+=("${SHARED[@]}")
fi

for b in "${NAMES[@]}"; do
  if [[ -f "$HERE/$b.lean" ]]; then src="$HERE"
  elif is_shared "$b" && [[ -f "$FIX/$b.lean" ]]; then src="$FIX"
  else echo "no source for $b" >&2; exit 2; fi
  FIXTURE_DIR="$src" OUT_DIR="$HERE" MODELGEN_FILTER=0 \
    bash "$ROOT/scripts/export-fixture.sh" "$b.lean"
done
