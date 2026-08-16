#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
ci="$root/scripts/ci-mathlib.sh"
patch="$root/vendor/lean4export/compact-expr-interner.patch"
vendor_readme="$root/vendor/lean4export/README.md"
revision="caccfbebbc99077962b3321125b2375bb3fa22db"
patch_sha="151c25f6adbfd915ce62786da33352c089653f62d5d3445cc3b38879de19deeb"

fail() {
  echo "lean4export patch check: $*" >&2
  exit 1
}

[[ -f "$patch" ]] || fail "patch is missing"
[[ "$(sha256sum "$patch" | awk '{print $1}')" == "$patch_sha" ]] ||
  fail "patch SHA-256 differs from its reviewed value"
grep -Fq "EXPORTER_REV=$revision" <(tr -d '"' < "$ci") ||
  fail "Mathlib CI no longer pins the reviewed lean4export revision"
grep -Fq "EXPORTER_PATCH_SHA=$patch_sha" <(tr -d '"' < "$ci") ||
  fail "Mathlib CI no longer pins the reviewed patch SHA-256"
grep -Fq "$revision" "$vendor_readme" || fail "vendor README omits revision"
grep -Fq "$patch_sha" "$vendor_readme" || fail "vendor README omits patch SHA"
grep -Fq 'git -C "$EXPORTER_DIR" apply --check "$EXPORTER_PATCH"' "$ci" ||
  fail "Mathlib CI no longer checks patch applicability"
grep -Fq 'git -C "$EXPORTER_DIR" apply "$EXPORTER_PATCH"' "$ci" ||
  fail "Mathlib CI no longer applies the patch"
if grep -Eq '^\+.*(@\[extern|moreLinkArgs|extern .C.)' "$patch"; then
  fail "lean4export patch introduces a native-language boundary"
fi

if [[ "${LEAN4EXPORT_DIFFERENTIAL:-0}" != 1 ]]; then
  echo "lean4export patch: pin, SHA-256, pure-Lean and harness gates passed"
  exit 0
fi

scratch="$root/_tmp/lean4export-differential"
stock="$scratch/stock"
patched="$scratch/patched"
output="$scratch/output"
mkdir -p "$scratch" "$output"

checkout_pinned() {
  local directory="$1"
  if [[ ! -d "$directory/.git" ]]; then
    git clone --filter=blob:none --no-checkout \
      https://github.com/leanprover/lean4export.git "$directory"
  fi
  git -C "$directory" fetch --depth=1 origin "$revision"
  git -C "$directory" checkout --detach --force FETCH_HEAD
  git -C "$directory" clean -ffd
  # Deliberately a literal, not a copy of `$root/lean-toolchain`. This check
  # builds the pinned exporter revision the Mathlib gate builds, and that
  # revision's Lean version is independent of ours -- see the matching comment
  # in `scripts/ci-mathlib.sh`. Keep it in step with that file and with
  # `scripts/export-fixture.sh`, which pins the same literal.
  echo "leanprover/lean4:v4.29.1" > "$directory/lean-toolchain"
}

checkout_pinned "$stock"
checkout_pinned "$patched"
git -C "$patched" apply --check "$patch"
git -C "$patched" apply "$patch"

memory_kib=$((4 * 1024 * 1024))
run_capped() (
  ulimit -S -v "$memory_kib"
  ulimit -H -v "$memory_kib"
  exec "$@"
)

(cd "$stock" && run_capped lake -Kjobs=1 build lean4export)
(cd "$patched" && run_capped lake -Kjobs=1 build lean4export)

mapfile -t fixture_args < "$root/test/fixtures/lean4export/compact_interner.args"
(cd "$stock" && run_capped lake env .lake/build/bin/lean4export \
  "${fixture_args[@]}" > "$output/stock.ndjson")
(cd "$patched" && run_capped lake env .lake/build/bin/lean4export \
  --compact-expr-test-table "${fixture_args[@]}" \
  > "$output/patched.ndjson")
cmp "$output/stock.ndjson" "$output/patched.ndjson" ||
  fail "patched exporter bytes differ from stock"

set +e
(cd "$patched" && run_capped lake env .lake/build/bin/lean4export \
  --compact-expr-test-tiny Init -- Nat.add \
  > "$output/tiny.ndjson" 2> "$output/tiny.err")
tiny_status=$?
set -e
(( tiny_status != 0 )) || fail "one-entry table did not fail closed"
grep -Fq 'compact expression interner exhausted its 1 entry capacity' \
  "$output/tiny.err" || fail "one-entry table failed for an unexpected reason"

echo "lean4export differential: $(wc -l < "$output/stock.ndjson") identical lines; overflow rejected"
