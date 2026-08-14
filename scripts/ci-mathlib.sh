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
EXPORTER_PATCH="$ROOT/vendor/lean4export/compact-expr-interner.patch"
EXPORTER_PATCH_SHA="151c25f6adbfd915ce62786da33352c089653f62d5d3445cc3b38879de19deeb"
WORKER_LIMIT_KIB=$((10 * 1024 * 1024))
BUILD_LIMIT_KIB=$((12 * 1024 * 1024))
EXPORT_LIMIT_KIB=$((12 * 1024 * 1024))
# The measured staged spool and output are each about 6 GB. This is a
# generation-phase guard, after all disposable builds and checkouts are gone;
# it is not a runner-size preflight.
GENERATION_FREE_KIB=$((12 * 1024 * 1024))

mkdir -p "$BIN_DIR" "$LOG_DIR" "$PERF_DIR" "$TMP_DIR"
export TMPDIR="$TMP_DIR"
export MATHLIB_CACHE_DIR
exec > >(tee "$LOG_DIR/mathlib-ci.log") 2>&1
feeder_pid=""

cleanup_input_stream() {
  if [[ -n "$feeder_pid" ]]; then
    kill "$feeder_pid" 2>/dev/null || true
    wait "$feeder_pid" 2>/dev/null || true
    feeder_pid=""
  fi
  rm -f "$INPUT_FIFO" "$INPUT_GZ"
}
trap cleanup_input_stream EXIT

fail() {
  echo "mathlib CI: $*" >&2
  exit 1
}

for tool in awk df du git grep gzip lake mkfifo sha256sum stat; do
  command -v "$tool" >/dev/null || fail "required command not found: $tool"
done
[[ -x /usr/bin/time ]] || fail "required command not found: /usr/bin/time"
(( BASH_VERSINFO[0] >= 5 )) || fail "Bash 5 or newer is required for wait -n -p"

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

# Every large process tree has an exact address-space ceiling. Serialized Lake
# builds and cache extraction need 12 GiB (Simple.c exceeds 10 GiB). The pinned
# exporter patch shrinks its retained global expression index enough to restore
# that same 12 GiB ceiling, leaving 4 GiB of the standard runner's 16 GiB for
# gzip and runner services. The public generator and serialized kernel reread
# retain the authoritative 10 GiB worker ceiling; the supervised child inherits
# its parent's limit.
run_capped() (
  limit_kib="$1"
  limit_label="$2"
  shift 2
  ulimit -S -v "$limit_kib"
  ulimit -H -v "$limit_kib"
  [[ "$(ulimit -S -v)" == "$limit_kib" ]] ||
    fail "could not set the $limit_label soft RLIMIT_AS"
  [[ "$(ulimit -H -v)" == "$limit_kib" ]] ||
    fail "could not set the $limit_label hard RLIMIT_AS"
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
  local limit_kib="$1" limit_label="$2" label="$3"
  shift 3
  if [[ "$PERF_AVAILABLE" == true ]]; then
    run_capped "$limit_kib" "$limit_label" \
      /usr/bin/time -v -o "$PERF_DIR/$label.time" \
      perf stat -e instructions -o "$PERF_DIR/$label.perf" -- "$@"
  else
    echo "instructions: unavailable" > "$PERF_DIR/$label.perf"
    run_capped "$limit_kib" "$limit_label" \
      /usr/bin/time -v -o "$PERF_DIR/$label.time" "$@"
  fi
}

run_build_measured() {
  run_measured "$BUILD_LIMIT_KIB" "12 GiB build/cache" "$@"
}

run_export_measured() {
  run_measured "$EXPORT_LIMIT_KIB" "12 GiB Mathlib export" "$@"
}

run_worker_measured() {
  run_measured "$WORKER_LIMIT_KIB" "10 GiB model worker" "$@"
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
(cd "$ROOT" && run_build_measured build-generator \
  lake -Kjobs=1 build lean-inductive-models)
cp "$ROOT/.lake/build/bin/lean-inductive-models" \
  "$BIN_DIR/lean-inductive-models"
[[ -x "$BIN_DIR/lean-inductive-models" ]] || fail "model generator was not built"
cleanup_tree "$ROOT/.lake/build"
disk_census generator-built

checkout_pinned \
  https://github.com/leanprover/lean4export.git \
  "$EXPORTER_REV" "$EXPORTER_DIR"
[[ "$(sha256sum "$EXPORTER_PATCH" | awk '{print $1}')" == "$EXPORTER_PATCH_SHA" ]] ||
  fail "lean4export compact-interner patch SHA-256 mismatch"
git -C "$EXPORTER_DIR" apply --check "$EXPORTER_PATCH"
git -C "$EXPORTER_DIR" apply "$EXPORTER_PATCH"
cp "$ROOT/lean-toolchain" "$EXPORTER_DIR/lean-toolchain"
(cd "$EXPORTER_DIR" && run_build_measured build-exporter lake -Kjobs=1 build)
cp "$EXPORTER_DIR/.lake/build/bin/lean4export" "$BIN_DIR/lean4export"
[[ -x "$BIN_DIR/lean4export" ]] || fail "exporter binary was not built"
cleanup_tree "$EXPORTER_DIR"
disk_census exporter-built

checkout_pinned \
  https://github.com/leanprover-community/mathlib4.git \
  "$MATHLIB_REV" "$MATHLIB_DIR"
(cd "$MATHLIB_DIR" && run_build_measured mathlib-cache lake -Kjobs=1 exe cache get)
cleanup_tree "$MATHLIB_CACHE_DIR"
disk_census mathlib-cached

rm -f "$INPUT_GZ" "$INPUT_FIFO" "$OUTPUT"
set +e
(cd "$MATHLIB_DIR" &&
  run_export_measured export lake env "$BIN_DIR/lean4export" Mathlib) |
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
feeder_job="$feeder_pid"

# Keep the documented generation and structural-check defaults. Defer only the
# whole-output kernel gate so named output uses the bounded staged backend; the
# separate serialized input pass below is the authoritative kernel verdict.
set +e
(
  set -o pipefail
  run_worker_measured generate \
    env -u LEAN_INDUCTIVE_MODELS_INTERNAL_WORKER \
      LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE=1 \
    "$BIN_DIR/lean-inductive-models" "$INPUT_FIFO" -o "$OUTPUT" \
      --no-type-check-output \
    2>&1 | tee "$LOG_DIR/generate.log" >&2
) &
generator_pid=$!
completed_pid=""
wait -n -p completed_pid "$feeder_job" "$generator_pid"
first_status=$?
if [[ "$completed_pid" == "$feeder_job" ]]; then
  feeder_status="$first_status"
  feeder_pid=""
  rm -f "$INPUT_GZ" "$INPUT_FIFO"
  disk_census source-reclaimed
  wait "$generator_pid"
  generator_status=$?
else
  generator_status="$first_status"
  if (( generator_status != 0 )); then
    # The worker may have failed before opening the FIFO. Cancel the exact
    # blocked gzip child so the hosted job cannot hang in open(2).
    kill "$feeder_job" 2>/dev/null || true
  fi
  wait "$feeder_job"
  feeder_status=$?
  feeder_pid=""
  rm -f "$INPUT_GZ" "$INPUT_FIFO"
fi
set -e
echo "input process statuses: generator=$generator_status feeder=$feeder_status"
(( generator_status == 0 )) || fail "model generator failed: $generator_status"
(( feeder_status == 0 )) || fail "compressed Mathlib input feeder failed: $feeder_status"

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
  run_worker_measured check-input \
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
