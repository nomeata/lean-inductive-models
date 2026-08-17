#!/usr/bin/env bash
# Cheap parser regression test for scripts/check-mathlib-result.sh, plus the
# pins that keep scripts/ci-mathlib.sh a single pass with nothing turned off.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
mkdir -p "$ROOT/_tmp"
WORK="$(mktemp -d "$ROOT/_tmp/mathlib-result-test.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

generate="$WORK/generate.log"

# One pass, in the order the tool prints it: the structural input check, the
# backend trace, generation, the structural output check, the kernel verdict.
printf '%s\n' \
  "input check: 0 model families checked" \
  "output backend: compact-discard" \
  "generated kernel checks: 6882" \
  "Owner: model of 7 declarations" \
  "Owner: prelude spliced — Eq, PSigma', PSigma'.mk, PUnit" \
  "Eq: exempt — prim model: a basis primitive" \
  "Nat: exempt — prim model: a basis primitive" \
  "PSigma: model of 9 declarations" \
  "PUnit: exempt — prim model: a basis primitive" \
  "statements: 48699 compared, 0 differ" \
  "levels: 211 planner comparisons, 0 escapes" \
  "output check: 12001 model families checked" \
  "generated kernel check: accepted" > "$generate"

checker="$ROOT/scripts/check-mathlib-result.sh"
ci_harness="$ROOT/scripts/ci-mathlib.sh"

require_harness() {
  grep -Eq -- "$1" "$ci_harness" || {
    echo "mathlib CI harness no longer matches: $1${2:+ -- $2}" >&2
    exit 1
  }
}
forbid_harness() {
  if grep -Eqn -- "$1" "$ci_harness"; then
    echo "mathlib CI harness must not contain: $1${2:+ -- $2}" >&2
    exit 1
  fi
}

# Correctness, not scaffolding: the corpus and the exporter are both pinned to a
# reviewed revision, and the exporter is stock upstream at that revision.
require_harness '^MATHLIB_REV="[0-9a-f]{40}"$'
require_harness '^EXPORTER_REV="[0-9a-f]{40}"$'

# Honest exit status. `pipefail` alone would abort the script before a
# PIPESTATUS line could name the side that failed, so each large pipeline is
# guarded and reports both members. A corrupt or truncated export must never
# read as a passing gate.
require_harness '^set -euo pipefail$'
[[ "$(grep -Ec 'PIPESTATUS' "$ci_harness")" == 2 ]] || {
  echo "mathlib CI does not report PIPESTATUS for both the export and the generation pipe" >&2
  exit 1
}

# One pass with the documented flags. `--type-check-generated` is the default
# and is stated so this pin can read it; the other two are the deliberate
# reductions. Everything else -- generation and both structural checks -- stays
# at its default, so any `--no-` form of them is a weakened gate.
generator_line="$(grep -n 'lean-inductive-models" -' "$ci_harness" || true)"
[[ -n "$generator_line" ]] || {
  echo "mathlib CI does not run the generator over the export on stdin" >&2
  exit 1
}
for flag in --no-output --no-type-check-input --type-check-generated; do
  require_harness "$flag"
done
# Anchored at the end of the option, so `git clone --no-checkout` is not
# mistaken for the generator's `--no-check`.
for weakening in --no-type-check-generated --no-check-input --no-check-output \
    --no-check --no-inductives; do
  forbid_harness "$weakening([[:space:]]|\$)" "the Mathlib gate may not turn a check off"
done
# No artifact is written, so no output target may be passed either.
forbid_harness '(^|[[:space:]])-o[[:space:]]' "the gate writes no model artifact"
require_harness 'LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE=1' \
  "the backend and generated-kernel-check counts must be exposed"

# The export is serialized to a compressed file and read back, never piped live
# into the generator. That is what keeps the two peaks -- roughly 8 GiB and
# 12 GiB -- from having to coexist on a 16 GiB runner.
require_harness 'gzip -1 > "\$EXPORT_GZ"'
require_harness 'gzip -dc "\$EXPORT_GZ"'

# GitHub's stock Ubuntu runner does not provide ripgrep. Shadow any host copy
# so this regression test also proves the checker has no hidden rg dependency.
rg() {
  echo "mathlib result parser unexpectedly invoked rg" >&2
  return 127
}
export -f rg

"$checker" "$generate" >/dev/null

reject() {
  local description="$1" log="$2"
  if "$checker" "$log" >/dev/null 2>&1; then
    echo "mathlib result parser accepted $description" >&2
    exit 1
  fi
}

sed 's/0 differ/1 differ/' "$generate" > "$WORK/bad-statements.log"
reject "a statement difference" "$WORK/bad-statements.log"

# The regression this change exists to end: before it, the gate ran with
# `--no-type-check-generated` and reported exactly this line.
sed 's/^generated kernel checks: 6882$/generated kernel checks: 0/' "$generate" \
  > "$WORK/no-generated-checks.log"
reject "a run that kernel-checked no generated island" "$WORK/no-generated-checks.log"

grep -vF 'generated kernel check: accepted' "$generate" > "$WORK/no-kernel-verdict.log"
reject "a missing generated-island kernel verdict" "$WORK/no-kernel-verdict.log"

grep -vF 'output check: ' "$generate" > "$WORK/no-output-check.log"
reject "a missing generated-model structural check" "$WORK/no-output-check.log"

grep -vF 'input check: ' "$generate" > "$WORK/no-input-check.log"
reject "a missing source structural check" "$WORK/no-input-check.log"

grep -vF 'output backend: compact-discard' "$generate" > "$WORK/no-backend.log"
reject "a missing compact-discard backend" "$WORK/no-backend.log"

sed 's/output backend: compact-discard/output backend: declaration-stream/' \
  "$generate" > "$WORK/wrong-backend.log"
reject "a backend that writes output" "$WORK/wrong-backend.log"

sed '/output backend: compact-discard/p' "$generate" > "$WORK/duplicate-backend.log"
reject "duplicate backend reports" "$WORK/duplicate-backend.log"

{ cat "$generate"; printf '%s\n' 'Foo: declined — no route'; } > "$WORK/declined.log"
reject "a declined inductive" "$WORK/declined.log"

{ cat "$generate"; printf '%s\n' 'PULiftP: model of 3 declarations'; } > "$WORK/pulift.log"
reject "legacy PULiftP output" "$WORK/pulift.log"

echo "mathlib result parser: pass"
