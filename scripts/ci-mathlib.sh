#!/usr/bin/env bash
# Exercise the default inductive-model pipeline over a pinned full Mathlib
# export, then kernel-check the serialized models as input in a second pass.
#
# This harness is intentionally shaped for a standard GitHub-hosted runner:
# it never materializes the uncompressed source export, and it removes build
# and checkout phases before the staged generator needs their disk space.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORK="$ROOT/_tmp"
MATHLIB_DIR="$WORK/mathlib"
EXPORTER_DIR="$WORK/lean4export"
MATHLIB_CACHE_DIR="$WORK/mathlib-cache"
BIN_DIR="$WORK/bin"
LOG_DIR="$WORK/logs"
PERF_DIR="$WORK/perf"
TMP_DIR="$WORK/tmp"
INPUT_GZ="$WORK/mathlib.ndjson.gz"
INPUT_FIFO="$WORK/mathlib.ndjson.pipe"
OUTPUT="$WORK/mathlib.model.ndjson"

MATHLIB_REV="5e932f97dd25535344f80f9dd8da3aab83df0fe6"
EXPORTER_REV="caccfbebbc99077962b3321125b2375bb3fa22db"
WORKER_LIMIT_KIB=$((10 * 1024 * 1024))
# The measured staged spool and output are each about 6 GB. This is a
# generation-phase guard, after all disposable builds and checkouts are gone;
# it is not a runner-size preflight.
GENERATION_FREE_KIB=$((12 * 1024 * 1024))

mkdir -p "$BIN_DIR" "$LOG_DIR" "$PERF_DIR" "$TMP_DIR"
export TMPDIR="$TMP_DIR"
export MATHLIB_CACHE_DIR
exec > >(tee "$LOG_DIR/mathlib-ci.log") 2>&1
trap 'rm -f "$INPUT_FIFO"' EXIT

fail() {
  echo "mathlib CI: $*" >&2
  exit 1
}

for tool in awk df du git grep gzip lake mkfifo stat; do
  command -v "$tool" >/dev/null || fail "required command not found: $tool"
done
[[ -x /usr/bin/time ]] || fail "required command not found: /usr/bin/time"

disk_census() {
  local phase="$1"
  {
    echo "disk census: $phase"
    df -Pk "$WORK"
    du -sk "$WORK" "$ROOT/.lake/build" 2>/dev/null || true
  } | tee -a "$LOG_DIR/disk.log"
}

available_kib() {
  df -Pk "$WORK" | awk 'NR == 2 { print $4 }'
}

cleanup_tree() {
  local path="$1"
  case "$path" in
    "$MATHLIB_DIR"|"$EXPORTER_DIR"|"$MATHLIB_CACHE_DIR"|"$ROOT/.lake/build") ;;
    *) fail "refusing to remove unexpected cleanup path: $path" ;;
  esac
  if [[ -e "$path" ]]; then
    rm -rf -- "$path"
  fi
}

# Each potentially large process tree inherits an exact 10 GiB address-space
# limit. The public generator's supervised worker inherits this limit too.
run_capped() (
  ulimit -S -v "$WORKER_LIMIT_KIB"
  ulimit -H -v "$WORKER_LIMIT_KIB"
  [[ "$(ulimit -S -v)" == "$WORKER_LIMIT_KIB" ]] ||
    fail "could not set the 10 GiB soft RLIMIT_AS"
  [[ "$(ulimit -H -v)" == "$WORKER_LIMIT_KIB" ]] ||
    fail "could not set the 10 GiB hard RLIMIT_AS"
  exec "$@"
)

PERF_AVAILABLE=false
if command -v perf >/dev/null &&
    perf stat -e instructions -o "$PERF_DIR/preflight.perf" -- true \
      >/dev/null 2>"$PERF_DIR/preflight.err"; then
  PERF_AVAILABLE=true
  echo "instruction counting: available"
else
  {
    echo "instruction counting: unavailable on this runner"
    if [[ -s "$PERF_DIR/preflight.err" ]]; then
      sed -n '1,20p' "$PERF_DIR/preflight.err"
    fi
  } | tee "$PERF_DIR/preflight.perf"
fi

run_measured() {
  local label="$1"
  shift
  if [[ "$PERF_AVAILABLE" == true ]]; then
    run_capped /usr/bin/time -v -o "$PERF_DIR/$label.time" \
      perf stat -e instructions -o "$PERF_DIR/$label.perf" -- "$@"
  else
    echo "instructions: unavailable" > "$PERF_DIR/$label.perf"
    run_capped /usr/bin/time -v -o "$PERF_DIR/$label.time" "$@"
  fi
}

# Hosted runners normally have no configured swap. Try the standard
# passwordless-sudo escape hatch if one does, then fail closed unless the
# resulting state can be verified as zero swap.
if awk 'NR > 1 { found = 1 } END { exit !found }' /proc/swaps; then
  echo "swap: configured; attempting sudo swapoff -a"
  sudo -n swapoff -a || true
fi
if awk 'NR > 1 { found = 1 } END { exit !found }' /proc/swaps; then
  fail "active swap remains after the hosted-runner swapoff attempt"
fi
echo "swap: verified zero"
if [[ -r /sys/fs/cgroup/memory.current ]]; then
  echo "host cgroup memory.current: $(< /sys/fs/cgroup/memory.current)"
fi
if [[ -r /sys/fs/cgroup/memory.max ]]; then
  echo "host cgroup memory.max: $(< /sys/fs/cgroup/memory.max)"
fi
disk_census start

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

# Build one root per Lake invocation. Copy the standalone executables out of
# their build trees so every build artifact can be reclaimed before generation.
(cd "$ROOT" && run_measured build-generator \
  lake -Kjobs=1 build lean-inductive-models)
cp "$ROOT/.lake/build/bin/lean-inductive-models" \
  "$BIN_DIR/lean-inductive-models"
[[ -x "$BIN_DIR/lean-inductive-models" ]] || fail "model generator was not built"
cleanup_tree "$ROOT/.lake/build"
disk_census generator-built

checkout_pinned \
  https://github.com/leanprover/lean4export.git \
  "$EXPORTER_REV" "$EXPORTER_DIR"
cp "$ROOT/lean-toolchain" "$EXPORTER_DIR/lean-toolchain"
(cd "$EXPORTER_DIR" && run_measured build-exporter lake -Kjobs=1 build)
cp "$EXPORTER_DIR/.lake/build/bin/lean4export" "$BIN_DIR/lean4export"
[[ -x "$BIN_DIR/lean4export" ]] || fail "exporter binary was not built"
cleanup_tree "$EXPORTER_DIR"
disk_census exporter-built

checkout_pinned \
  https://github.com/leanprover-community/mathlib4.git \
  "$MATHLIB_REV" "$MATHLIB_DIR"
(cd "$MATHLIB_DIR" && run_measured mathlib-cache lake -Kjobs=1 exe cache get)
cleanup_tree "$MATHLIB_CACHE_DIR"
disk_census mathlib-cached

rm -f "$INPUT_GZ" "$INPUT_FIFO" "$OUTPUT"
set +e
(cd "$MATHLIB_DIR" &&
  run_measured export lake env "$BIN_DIR/lean4export" Mathlib) |
  gzip -1 > "$INPUT_GZ"
export_status=("${PIPESTATUS[@]}")
set -e
(( export_status[0] == 0 )) || fail "Mathlib exporter failed: ${export_status[0]}"
(( export_status[1] == 0 )) || fail "Mathlib export compression failed: ${export_status[1]}"
[[ -s "$INPUT_GZ" ]] || fail "compressed Mathlib export is missing or empty"
echo "compressed Mathlib export bytes: $(stat -c '%s' "$INPUT_GZ")"

# The export is self-contained. Remove both checkouts and every cache/build
# artifact before the staged spool and final output begin to coexist.
cleanup_tree "$MATHLIB_DIR"
cleanup_tree "$ROOT/.lake/build"
disk_census pre-generation-cleanup
free_kib="$(available_kib)"
[[ "$free_kib" =~ ^[0-9]+$ ]] || fail "could not determine free generation disk"
(( free_kib >= GENERATION_FREE_KIB )) ||
  fail "generation needs 12 GiB free after cleanup; found $free_kib KiB"

# Feed the compressed export through a FIFO. The structural checker sees the
# exact original byte stream, while the uncompressed 5.6 GB source never
# occupies the hosted runner's disk. Once the feeder reaches EOF the compressed
# source can also be reclaimed before final output serialization.
mkfifo "$INPUT_FIFO"
gzip -dc "$INPUT_GZ" > "$INPUT_FIFO" &
feeder_pid=$!

# No selection flags: this deliberately exercises the documented default,
# including inductive generation and structural input/output checking.
set +e
(
  set -o pipefail
  run_measured generate \
    env -u LEAN_INDUCTIVE_MODELS_INTERNAL_WORKER \
    "$BIN_DIR/lean-inductive-models" "$INPUT_FIFO" -o "$OUTPUT" \
    2>&1 | tee "$LOG_DIR/generate.log" >&2
) &
generator_pid=$!
wait "$feeder_pid"
feeder_status=$?
if (( feeder_status == 0 )); then
  rm -f "$INPUT_GZ" "$INPUT_FIFO"
  disk_census source-reclaimed
fi
wait "$generator_pid"
generator_status=$?
set -e
(( feeder_status == 0 )) ||
  fail "compressed Mathlib input feeder failed: $feeder_status"
(( generator_status == 0 )) || fail "model generator failed: $generator_status"

[[ -s "$OUTPUT" ]] || fail "generated export is missing or empty"
disk_census generated
if grep -En ': declined' "$LOG_DIR/generate.log"; then
  fail "one or more Mathlib inductives declined"
fi
grep -Eq ': model of [1-9][0-9]* declarations' "$LOG_DIR/generate.log" ||
  fail "generation reported no models"

# Re-read the bytes that were actually written. Keep structural input checking
# enabled and additionally ask Lean's kernel to validate every declaration.
# This pass is serialized after the first process and its private spool exit.
(
  set -o pipefail
  run_measured check-input \
    env -u LEAN_INDUCTIVE_MODELS_INTERNAL_WORKER \
    "$BIN_DIR/lean-inductive-models" "$OUTPUT" \
      --no-inductives --check-input --no-check-output \
      --type-check-input --no-type-check-output --no-output \
    2>&1 | tee "$LOG_DIR/check-input.log" >&2
)

"$ROOT/scripts/check-mathlib-result.sh" \
  "$LOG_DIR/generate.log" "$OUTPUT" "$LOG_DIR/check-input.log"
rm -f "$OUTPUT"
disk_census complete

echo "mathlib CI: full export generated, structurally checked, and kernel-reread"
