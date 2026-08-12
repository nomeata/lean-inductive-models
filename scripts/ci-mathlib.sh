#!/usr/bin/env bash
# Exercise the default inductive-model pipeline over a pinned full Mathlib
# export, then check the serialized models as input in a second pass.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORK="$ROOT/_tmp"
MATHLIB_DIR="$WORK/mathlib"
EXPORTER_DIR="$WORK/lean4export"
LOG_DIR="$WORK/logs"
PERF_DIR="$WORK/perf"
TMP_DIR="$WORK/tmp"
INPUT="$WORK/mathlib.ndjson"
OUTPUT="$WORK/mathlib.model.ndjson"

MATHLIB_REV="5e932f97dd25535344f80f9dd8da3aab83df0fe6"
EXPORTER_REV="caccfbebbc99077962b3321125b2375bb3fa22db"
MEMORY_LIMIT_BYTES=$((40 * 1024 * 1024 * 1024))
MIN_DISK_KIB=$((30 * 1024 * 1024))

mkdir -p "$LOG_DIR" "$PERF_DIR" "$TMP_DIR"
export TMPDIR="$TMP_DIR"
exec > >(tee "$LOG_DIR/mathlib-ci.log") 2>&1

fail() {
  echo "mathlib CI: $*" >&2
  exit 1
}

for tool in git lake perf rg; do
  command -v "$tool" >/dev/null || fail "required command not found: $tool"
done

# Fail closed unless the whole script is inside the requested cgroup-v2
# limits. Per-process ulimits are insufficient for a compiler process tree.
cgroup_rel="$(awk -F: '$1 == "0" { print $3 }' /proc/self/cgroup)"
[[ -n "$cgroup_rel" ]] || fail "not running in a unified cgroup-v2 hierarchy"
cgroup_dir="/sys/fs/cgroup$cgroup_rel"
[[ -r "$cgroup_dir/memory.max" ]] || fail "cannot read the cgroup memory limit"
memory_max="$(<"$cgroup_dir/memory.max")"
swap_max="$(<"$cgroup_dir/memory.swap.max")"
[[ "$memory_max" != "max" ]] || fail "cgroup memory is unlimited"
[[ "$memory_max" =~ ^[0-9]+$ ]] || fail "invalid cgroup memory limit: $memory_max"
(( memory_max <= MEMORY_LIMIT_BYTES )) ||
  fail "cgroup memory limit exceeds 40 GiB: $memory_max bytes"
[[ "$swap_max" == "0" ]] || fail "cgroup swap limit is not zero: $swap_max"

available_kib="$(df -Pk "$WORK" | awk 'NR == 2 { print $4 }')"
[[ "$available_kib" =~ ^[0-9]+$ ]] || fail "could not determine available disk space"
(( available_kib >= MIN_DISK_KIB )) ||
  fail "at least 30 GiB free under _tmp/ is required; found $available_kib KiB"

# Verify instruction counting before downloading or generating the corpus.
perf stat -e instructions -o "$PERF_DIR/preflight.perf" -- true

checkout_pinned() {
  local url="$1" revision="$2" directory="$3"
  if [[ -e "$directory" && ! -d "$directory/.git" ]]; then
    fail "$directory exists and is not a Git checkout"
  fi
  if [[ ! -d "$directory/.git" ]]; then
    git clone --filter=blob:none --no-checkout "$url" "$directory"
  fi
  git -C "$directory" fetch --depth=1 origin "$revision"
  git -C "$directory" checkout --detach FETCH_HEAD
}

checkout_pinned \
  https://github.com/leanprover-community/mathlib4.git \
  "$MATHLIB_REV" "$MATHLIB_DIR"
(cd "$MATHLIB_DIR" && lake exe cache get)

checkout_pinned \
  https://github.com/leanprover/lean4export.git \
  "$EXPORTER_REV" "$EXPORTER_DIR"
cp "$ROOT/lean-toolchain" "$EXPORTER_DIR/lean-toolchain"
(cd "$EXPORTER_DIR" && lake build)

(cd "$ROOT" && lake build modelgen)
EXPORTER_BIN="$EXPORTER_DIR/.lake/build/bin/lean4export"
MODELGEN_BIN="$ROOT/.lake/build/bin/modelgen"
[[ -x "$EXPORTER_BIN" ]] || fail "exporter binary was not built"
[[ -x "$MODELGEN_BIN" ]] || fail "model generator binary was not built"

rm -f "$INPUT" "$OUTPUT"
(cd "$MATHLIB_DIR" &&
  perf stat -e instructions -o "$PERF_DIR/export.perf" -- \
    lake env "$EXPORTER_BIN" Mathlib > "$INPUT")
[[ -s "$INPUT" ]] || fail "Mathlib export is missing or empty"

# No selection flags: this deliberately exercises the documented default,
# including inductive generation and input/output checking. Universe-level
# monomorphization remains off.
perf stat -e instructions -o "$PERF_DIR/generate.perf" -- \
  "$MODELGEN_BIN" "$INPUT" -o "$OUTPUT" \
  2> >(tee "$LOG_DIR/generate.log" >&2)

[[ -s "$OUTPUT" ]] || fail "generated export is missing or empty"
if rg -n ': declined' "$LOG_DIR/generate.log"; then
  fail "one or more Mathlib inductives declined"
fi
rg -q ': model of [1-9][0-9]* declarations' "$LOG_DIR/generate.log" ||
  fail "generation reported no models"

# Re-read the bytes that were actually written. The positive diagnostic guard
# prevents a silently inert input checker from turning this into a green run.
perf stat -e instructions -o "$PERF_DIR/check-input.perf" -- \
  "$MODELGEN_BIN" "$OUTPUT" \
    --no-inductives --check-input --no-check-output --no-output \
  2> >(tee "$LOG_DIR/check-input.log" >&2)

"$ROOT/scripts/check-mathlib-result.sh" \
  "$LOG_DIR/generate.log" "$OUTPUT" "$LOG_DIR/check-input.log"

echo "mathlib CI: full export generated and serialized models checked"
