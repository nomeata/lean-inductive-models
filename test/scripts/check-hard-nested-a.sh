#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../.." && pwd)"
bin="${LEAN_INDUCTIVE_MODELS_BIN:-$root/.lake/build/bin/lean-inductive-models}"
fixture="$root/test/fixtures/lean-inductive-models/hard_nested_mutual_index.ndjson"

[[ -x "$bin" ]] || { echo "lean-inductive-models is not built: $bin" >&2; exit 2; }

mkdir -p "$root/_tmp"
work="$(mktemp -d "$root/_tmp/check-hard-nested-a.XXXXXX")"
trap 'rm -rf "$work"' EXIT

memory_limit_kib="${LEAN_INDUCTIVE_MODELS_MEMORY_KB:-16777216}"
current_memory_limit="$(ulimit -Sv)"
if [[ "$current_memory_limit" == unlimited ]] ||
    ((current_memory_limit > memory_limit_kib)); then
  ulimit -Sv "$memory_limit_kib"
fi
TMPDIR="$work" "$bin" "$fixture" \
  -o "$work/modelled.ndjson" --no-simple --no-basic 2>"$work/report"

grep -q '^C: model of ' "$work/report"
grep -q '^A: model of ' "$work/report"
! grep -Eq '^(C|A): declined' "$work/report"
grep -q '^statements: .* 0 differ$' "$work/report"
[[ -s "$work/modelled.ndjson" ]]
