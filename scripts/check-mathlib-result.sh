#!/usr/bin/env bash
# Validate the durable artifacts produced by the full-Mathlib modelgen run.
# Counts are deliberately required to be positive but are not pinned: the
# corpus revisions, rather than a historical observation, define their values.
set -euo pipefail

if [[ $# -ne 3 ]]; then
  echo "usage: $0 GENERATE_LOG OUTPUT_NDJSON CHECK_INPUT_LOG" >&2
  exit 2
fi

GENERATE_LOG="$1"
OUTPUT="$2"
CHECK_INPUT_LOG="$3"

fail() {
  echo "mathlib result: $*" >&2
  exit 1
}

for artifact in "$GENERATE_LOG" "$OUTPUT" "$CHECK_INPUT_LOG"; do
  [[ -s "$artifact" ]] || fail "missing or empty artifact: $artifact"
done

rg -q '^statements: [1-9][0-9]* compared, 0 differ$' "$GENERATE_LOG" ||
  fail "generated-statement comparison was absent, empty, or nonzero"
[[ "$(rg -c '^statements: ' "$GENERATE_LOG")" == 1 ]] ||
  fail "generation reported more than one statement-comparison result"

rg -q '^output check: [1-9][0-9]* model families checked$' "$GENERATE_LOG" ||
  fail "in-memory output check reported no model families"
[[ "$(rg -c '^output check: ' "$GENERATE_LOG")" == 1 ]] ||
  fail "generation reported more than one output-check result"

rg -q '^levels: [1-9][0-9]* planner comparisons, 0 escapes$' "$GENERATE_LOG" ||
  fail "universe planning was absent, empty, or escaped"
[[ "$(rg -c '^levels: ' "$GENERATE_LOG")" == 1 ]] ||
  fail "generation reported more than one universe-planning result"

# This set follows from the pinned input: it owns four of the five basis
# inductives. PSigma' is absent there and must instead be spliced below.
expected_exemptions=$'Eq\nNat\nPSigma\nPUnit'
actual_exemptions="$({
  sed -nE 's/^([^:]+): exempt — .*$/\1/p' "$GENERATE_LOG" || true
} | LC_ALL=C sort)"
[[ "$actual_exemptions" == "$expected_exemptions" ]] ||
  fail "basis exemptions differ; expected {$expected_exemptions}, found {$actual_exemptions}"

rg -q ": prelude spliced — (.*, )?PSigma'(, |$)" "$GENERATE_LOG" ||
  fail "generation did not report splicing the tight PSigma' basis"
rg -Fq "\"str\":\"PSigma'\"}" "$OUTPUT" ||
  fail "serialized output has no exact PSigma' name-table entry"

# PULiftP was replaced by the derived PSigma'/PUnit construction. Its name
# must not survive in either the emitted stream or either report.
if rg -Fn 'PULiftP' "$GENERATE_LOG" "$OUTPUT" "$CHECK_INPUT_LOG"; then
  fail "legacy PULiftP survived in a full-Mathlib artifact"
fi

rg -q '^input check: [1-9][0-9]* model families checked$' "$CHECK_INPUT_LOG" ||
  fail "serialized input recheck reported no model families"
[[ "$(rg -c '^input check: ' "$CHECK_INPUT_LOG")" == 1 ]] ||
  fail "serialized input recheck reported more than one result"

echo "mathlib result: generation, exact interfaces, levels, basis, and serialized reread pass"
