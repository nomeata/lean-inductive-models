#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/.." && pwd)"
bin="${MODELGEN_BIN:-$root/.lake/build/bin/modelgen}"

[[ -x "$bin" ]] || { echo "modelgen is not built: $bin" >&2; exit 2; }

mkdir -p "$root/_tmp"
work="$(mktemp -d "$root/_tmp/check-hard-nested-c.XXXXXX")"
trap 'rm -rf "$work"' EXIT

ulimit -Sv "${MODELGEN_MEMORY_KB:-16777216}"
TMPDIR="$work" "$bin" "$here/nested_mutual_indexed_container.ndjson" \
  -o "$work/modelled.ndjson" --check-recursors 2>"$work/report"

grep -q '^C: model of ' "$work/report"
! grep -q '^C: declined' "$work/report"
grep -q '^statements: .* 0 differ$' "$work/report"
grep -q '^recursors: .* 0 differ$' "$work/report"
