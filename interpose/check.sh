#!/usr/bin/env bash
# Reproduce MODELGEN.md §8.6.1's claims, end to end, and fail loudly if any of
# them stops holding.  Run from anywhere:
#
#     modelgen/interpose/check.sh
#
# Checks, in order:
#   1. the library builds;
#   2. the standalone reproducer flips REJECTED -> ACCEPTED;
#   3. `modelgen --interpose-levels` takes (its own probe would abort if not);
#   4. `BoxF` is declined stock and modelled interposed;
#   5. a fuzz reports zero false accepts.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mg_root="$(dirname "$here")"
MG="$mg_root/.lake/build/bin/modelgen"
FIX="$mg_root/tests/prim_declines.ndjson"
SO="$here/levelhack.so"
fail() { echo "FAIL: $*" >&2; exit 1; }

echo "== 1. build =="
"$here/build.sh" >/dev/null
[ -f "$SO" ] || fail "no $SO"

echo "== 2. standalone reproducer =="
if [ -x "$here/demo/.lake/build/bin/leveldemo" ]; then
  # From its own directory: the demo imports `Init`, so `findSysroot` has to
  # resolve to the toolchain in demo/lean-toolchain and not to elan's default.
  out=$(cd "$here/demo" && ./.lake/build/bin/leveldemo "$SO" 2>/dev/null)
  echo "$out" | grep -q 'before loadDynlib:  REJECTED' || fail "demo: not rejected before"
  echo "$out" | grep -q 'after  loadDynlib:  ACCEPTED' || fail "demo: not accepted after"
  echo "   ok: REJECTED before loadDynlib, ACCEPTED after"
else
  echo "   skipped: (cd $here/demo && lake build) first"
fi

[ -x "$MG" ] || { echo "== modelgen not built; stopping here =="; exit 0; }

echo "== 3+4. modelgen, stock vs interposed, on $(basename "$FIX") =="
a=$("$MG" "$FIX" --prim-models -o /dev/null 2>&1)
b=$("$MG" "$FIX" --prim-models --interpose-levels "$SO" -o /dev/null 2>&1)
# The stock decline is a *kernel* refusal since MODELGEN.md §8.6.2, not the
# planner's "no pad or codomain box closes the gap" — the planner's own level
# equality is complete now, so the pad is planned and `addChecked` is what
# says no. Still a decline, still this assertion; only the message moved.
echo "$a" | grep -q "^BoxF: declined" || fail "stock modelgen did not decline BoxF"
echo "$b" | grep -q "^BoxF: model of" || fail "interposed modelgen did not model BoxF"
echo "$b" | grep -q "witness flipped reject -> accept" || fail "take-verification did not report a flip"
# 11, not the 9 this asserted until now: the count had grown with the fixture
# and the assertion had gone stale on master, failing for both the stock and
# the complete planner alike.
echo "$b" | grep -q "statements: 11 compared .* 0 differ" || fail "statement oracle disagreed"
echo "   ok: BoxF declined stock, modelled interposed, statement oracle clean"

echo "== 5. fuzz: false accepts must be zero =="
f=$(MODELGEN_LEVELHACK_FUZZ=200000 MODELGEN_LEVELHACK_FUZZ_DEPTH=4 \
    LD_PRELOAD="$SO" "$MG" "$FIX" -o /dev/null 2>&1 || true)
echo "$f" | grep 'replacement          FALSE ACCEPTS' | while read -r line; do
  n=${line##*: }
  [ "$n" = "0" ] || { echo "FAIL: $line" >&2; exit 1; }
done
echo "$f" | grep -c 'replacement          FALSE ACCEPTS *: 0' | grep -qx 2 \
  || fail "expected two zero false-accept lines (equiv and >=)"
echo "   ok: 200000 pairs, 0 false accepts for equivalence and for >="

echo
echo "ALL CHECKS PASSED"
