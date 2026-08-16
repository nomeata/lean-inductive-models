#!/usr/bin/env bash
# Cheap parser regression test for scripts/check-mathlib-result.sh.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
mkdir -p "$ROOT/_tmp"
WORK="$(mktemp -d "$ROOT/_tmp/mathlib-result-test.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

generate="$WORK/generate.log"
output="$WORK/output.ndjson"
recheck="$WORK/check-input.log"

printf '%s\n' \
  "Owner: model of 7 declarations" \
  "Owner: prelude spliced — Eq, PSigma', PSigma'.mk, PUnit" \
  "Eq: exempt — prim model: a basis primitive" \
  "Nat: exempt — prim model: a basis primitive" \
  "PSigma: model of 9 declarations" \
  "PUnit: exempt — prim model: a basis primitive" \
  "statements: 48699 compared, 0 differ" \
  "levels: 211 planner comparisons, 0 escapes" \
  "output backend: declaration-stream" \
  "output check: 12001 model families checked" > "$generate"
printf '%s\n' "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"PSigma'\"}}" > "$output"
printf '%s\n' \
  'input kernel check: accepted' \
  'input check: 12001 model families checked' > "$recheck"

checker="$ROOT/scripts/check-mathlib-result.sh"
ci_harness="$ROOT/scripts/ci-mathlib.sh"

# The three phase budgets bound RESIDENT memory, not virtual address space:
# since the v4.33.0 toolchain a `lean` frontend reserves about 12.8 GiB of
# address space at startup against an unchanged 2.0 GiB peak RSS, so `ulimit -v`
# can no longer express either quantity. Keep all three exact budgets and their
# phase assignments explicit.
#
# Each of these is a pin on the harness, so each carries its own message. A bare
# `grep -Fq` under `set -e` fails the whole suite with no output at all, which is
# how a pin left behind by a harness change reads as an unexplained exit 1.
require_harness() {
  grep -Fq "$1" "$ci_harness" || {
    echo "mathlib CI harness no longer contains: $1" >&2
    exit 1
  }
}
require_harness 'BUILD_LIMIT_KIB=$((6 * 1024 * 1024))'
require_harness 'EXPORT_LIMIT_KIB=$((12 * 1024 * 1024))'
require_harness 'WORKER_LIMIT_KIB=$((12 * 1024 * 1024))'
# The budgets are observed and compared, not imposed: the harness reads GNU
# time's peak RSS for each phase and fails the run when it is over. This pair
# replaces a pin on `MemoryMax="${limit_kib}K"`, the cgroup ceiling the harness
# used to try to impose; what has to stay true is that every budget above is
# read against a resident-memory measurement and that exceeding one is fatal,
# not which mechanism produces the number.
require_harness 'Maximum resident set size'
grep -Eq 'fail "\$label exceeded the \$limit_label' "$ci_harness" || {
  echo "mathlib CI does not fail a phase that exceeds its budget" >&2
  exit 1
}
if grep -Eq '^[[:space:]]*ulimit[[:space:]]+.*-v' "$ci_harness"; then
  echo "mathlib CI still bounds virtual address space instead of memory" >&2
  exit 1
fi
for phase in build-generator build-exporter mathlib-cache; do
  grep -Eq "run_build_measured([[:space:]]+|.* )$phase" "$ci_harness" || {
    echo "mathlib CI does not use the 6 GiB budget for $phase" >&2
    exit 1
  }
done
grep -Eq 'run_export_measured([[:space:]]+|.* )export' "$ci_harness" || {
  echo "mathlib CI does not use the 12 GiB budget for export" >&2
  exit 1
}
for phase in generate check-input; do
  grep -Eq "run_worker_measured([[:space:]]+|.* )$phase" "$ci_harness" || {
    echo "mathlib CI does not use the 12 GiB worker budget for $phase" >&2
    exit 1
  }
done

generate_phase="$(sed -n '/run_worker_measured generate \\/,/tee "\$LOG_DIR\/generate.log"/p' \
  "$ci_harness")"
grep -Fq 'LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE=1' <<<"$generate_phase" || {
  echo "mathlib CI does not expose the generation backend" >&2
  exit 1
}
grep -Fq -- '--no-type-check-generated' <<<"$generate_phase" || {
  echo "mathlib CI generation does not defer its kernel gate" >&2
  exit 1
}

check_phase="$(sed -n '/run_worker_measured check-input \\/,/tee "\$LOG_DIR\/check-input.log"/p' \
  "$ci_harness")"
for flag in --type-check-input --no-type-check-generated --no-output; do
  grep -Fq -- "$flag" <<<"$check_phase" || {
    echo "mathlib CI serialized kernel gate is missing $flag" >&2
    exit 1
  }
done

# GitHub's stock Ubuntu runner does not provide ripgrep. Shadow any host copy
# so this regression test also proves the checker has no hidden rg dependency.
rg() {
  echo "mathlib result parser unexpectedly invoked rg" >&2
  return 127
}
export -f rg

"$checker" "$generate" "$output" "$recheck" >/dev/null

sed 's/0 differ/1 differ/' "$generate" > "$WORK/bad-statements.log"
if "$checker" "$WORK/bad-statements.log" "$output" "$recheck" >/dev/null 2>&1; then
  echo "mathlib result parser accepted a statement difference" >&2
  exit 1
fi

grep -vF 'input kernel check: accepted' "$recheck" > "$WORK/no-kernel-check.log"
if "$checker" "$generate" "$output" "$WORK/no-kernel-check.log" >/dev/null 2>&1; then
  echo "mathlib result parser accepted a missing kernel reread" >&2
  exit 1
fi

grep -vF 'output backend: declaration-stream' "$generate" > "$WORK/no-stream-backend.log"
if "$checker" "$WORK/no-stream-backend.log" "$output" "$recheck" >/dev/null 2>&1; then
  echo "mathlib result parser accepted a missing declaration-stream backend" >&2
  exit 1
fi

sed 's/output backend: declaration-stream/output backend: compact-discard/' \
  "$generate" > "$WORK/wrong-backend.log"
if "$checker" "$WORK/wrong-backend.log" "$output" "$recheck" >/dev/null 2>&1; then
  echo "mathlib result parser accepted a non-output generation backend" >&2
  exit 1
fi

sed '/output backend: declaration-stream/p' "$generate" > "$WORK/duplicate-backend.log"
if "$checker" "$WORK/duplicate-backend.log" "$output" "$recheck" >/dev/null 2>&1; then
  echo "mathlib result parser accepted duplicate backend reports" >&2
  exit 1
fi

printf '%s\n' '{"in":1,"str":{"pre":0,"str":"PULiftP"}}' >> "$output"
if "$checker" "$generate" "$output" "$recheck" >/dev/null 2>&1; then
  echo "mathlib result parser accepted legacy PULiftP output" >&2
  exit 1
fi

echo "mathlib result parser: pass"
