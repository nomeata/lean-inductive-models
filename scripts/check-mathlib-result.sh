#!/usr/bin/env bash
# Validate the log of the full-Mathlib single-pass run (scripts/ci-mathlib.sh).
# Counts are deliberately required to be positive but are not pinned: the
# corpus revisions, rather than a historical observation, define their values.
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 GENERATE_LOG" >&2
  exit 2
fi

GENERATE_LOG="$1"

fail() {
  echo "mathlib result: $*" >&2
  exit 1
}

[[ -s "$GENERATE_LOG" ]] || fail "missing or empty artifact: $GENERATE_LOG"

# `require_once EXACT PREFIX MESSAGE` -- a line matching EXACT is present, and
# exactly one line matches the looser PREFIX. Both halves are load-bearing: the
# exact form is the property, and the prefix count catches a second, differing
# report of the same thing, which means two passes ran where one was configured.
require_once() {
  local matches
  grep -Eq "$1" "$GENERATE_LOG" || fail "$3"
  matches="$(grep -Ec "$2" "$GENERATE_LOG" || true)"
  [[ "$matches" == 1 ]] || fail "$3: reported $matches times, expected once"
}

grep -Eq ': model of [1-9][0-9]* declarations$' "$GENERATE_LOG" ||
  fail "generation reported no models"
if grep -En ': declined' "$GENERATE_LOG" >&2; then
  fail "one or more Mathlib inductives declined"
fi

require_once '^statements: [1-9][0-9]* compared, 0 differ$' '^statements: ' \
  "generated-statement comparison was absent, empty, or nonzero"
require_once '^levels: [1-9][0-9]* planner comparisons, 0 escapes$' '^levels: ' \
  "universe planning was absent, empty, or escaped"

# The structural checks, both left at their defaults. `output check:` covers the
# model families this run generated, read off the compact certificates rather
# than off a written artifact -- it is the same verdict the discarded 5.9 GB
# output's re-read used to report as `input check:`. `input check:` now covers
# the Mathlib export itself, which carries no models of its own, so its count is
# legitimately 0 and only its presence is a property: the source stream was
# structurally validated before anything was generated from it.
require_once '^output check: [1-9][0-9]* model families checked$' '^output check: ' \
  "generated-model structural check reported no model families"
require_once '^input check: [0-9]+ model families checked$' '^input check: ' \
  "the source export was not structurally checked"

# The kernel evidence. The gate no longer writes an artifact to re-read under
# `--type-check-input`, which was the only kernel check in the run and reported
# `generated kernel checks: 0`; `--type-check-generated` checks each generated
# island against its trusted source prefix as it is produced. So the pair that
# replaces `input kernel check: accepted` is the accepting verdict *and* a
# positive count -- a verdict alone would be reported just as happily by a run
# that checked nothing, which is exactly the state this change ends.
require_once '^generated kernel check: accepted$' '^generated kernel check: ' \
  "the kernel did not accept the generated islands"
require_once '^generated kernel checks: [1-9][0-9]*$' '^generated kernel checks: ' \
  "no generated island was submitted to the kernel"

# No artifact is written, so the run must be on the no-output compact path.
# Anything else means output retention came back and with it the 5.9 GB write.
require_once '^output backend: compact-discard$' '^output backend: ' \
  "generation did not select the no-output compact backend"

# This set follows from the pinned input: it owns three of the four ordinary
# inductive members of the five-member basis. PSigma' is absent there and must
# instead be spliced below; Quot is the special kernel member and is not an
# inductive-owner exemption. Ordinary PSigma is modelled like any other source
# inductive.
expected_exemptions=$'Eq\nNat\nPUnit'
actual_exemptions="$({
  sed -nE 's/^([^:]+): exempt — .*$/\1/p' "$GENERATE_LOG" || true
} | LC_ALL=C sort)"
[[ "$actual_exemptions" == "$expected_exemptions" ]] ||
  fail "basis exemptions differ; expected {$expected_exemptions}, found {$actual_exemptions}"

grep -Eq '^PSigma: model of [1-9][0-9]* declarations$' "$GENERATE_LOG" ||
  fail "ordinary PSigma was not modelled"

# The splice report replaces a `"str":"PSigma'"` grep over the serialized output.
# It is the same claim about the same run one step earlier -- that the tight
# PSigma' basis was constructed for this corpus -- and that a spliced basis
# reaches the name table byte-for-byte is what the fixture round-trip suites
# check, on exports they actually write.
grep -Eq ": prelude spliced — (.*, )?PSigma'(, |$)" "$GENERATE_LOG" ||
  fail "generation did not report splicing the tight PSigma' basis"

# PULiftP was replaced by the derived PSigma'/PUnit construction. Its name must
# not survive anywhere in the report.
if grep -Fn 'PULiftP' "$GENERATE_LOG"; then
  fail "legacy PULiftP survived in a full-Mathlib artifact"
fi

echo "mathlib result: generation, exact interfaces, levels, basis, and generated-island kernel checks pass"
