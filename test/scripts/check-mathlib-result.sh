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
  "output check: 12001 model families checked" > "$generate"
printf '%s\n' "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"PSigma'\"}}" > "$output"
printf '%s\n' \
  'input kernel check: accepted' \
  'input check: 12001 model families checked' > "$recheck"

checker="$ROOT/scripts/check-mathlib-result.sh"
ci_harness="$ROOT/scripts/ci-mathlib.sh"

# The native compiler needs more address space than either authoritative model
# worker. Keep both exact envelopes and their phase assignments explicit.
grep -Fq 'BUILD_LIMIT_KIB=$((12 * 1024 * 1024))' "$ci_harness"
grep -Fq 'WORKER_LIMIT_KIB=$((10 * 1024 * 1024))' "$ci_harness"
for phase in build-generator build-exporter mathlib-cache export; do
  grep -Eq "run_build_measured([[:space:]]+|.* )$phase" "$ci_harness" || {
    echo "mathlib CI does not use the 12 GiB envelope for $phase" >&2
    exit 1
  }
done
for phase in generate check-input; do
  grep -Eq "run_worker_measured([[:space:]]+|.* )$phase" "$ci_harness" || {
    echo "mathlib CI does not use the 10 GiB envelope for $phase" >&2
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

printf '%s\n' '{"in":1,"str":{"pre":0,"str":"PULiftP"}}' >> "$output"
if "$checker" "$generate" "$output" "$recheck" >/dev/null 2>&1; then
  echo "mathlib result parser accepted legacy PULiftP output" >&2
  exit 1
fi

echo "mathlib result parser: pass"
