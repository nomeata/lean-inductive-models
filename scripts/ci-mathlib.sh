#!/usr/bin/env bash
# Exercise the default inductive-model pipeline over a pinned full Mathlib
# export, then kernel-check the serialized models as input in a second pass.
#
# This harness is intentionally shaped for a standard GitHub-hosted runner:
# it never materializes the uncompressed source export, and it removes build
# and checkout phases before declaration-wise generation needs their disk space.
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
WORKER_LIMIT_KIB=$((12 * 1024 * 1024))
BUILD_LIMIT_KIB=$((6 * 1024 * 1024))
EXPORT_LIMIT_KIB=$((12 * 1024 * 1024))
# Lake's build parallelism bound; see the build phases below and
# docs/maintainers/Testing.md for the measurements.
BUILD_THREADS=4
# Keep the conservative generation-phase disk guard for the named-output
# transaction's private sibling. This is
# applied after all disposable builds and checkouts are gone; it is not a
# runner-size preflight.
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

# GNU time is a separate binary from the shell's `time` keyword, and only the
# binary accepts `-v -o`. Hosted runners ship it at /usr/bin/time; distributions
# which do not use the FHS (NixOS) place it elsewhere on PATH. Resolve it once
# rather than hardcoding a path, and verify the resolved binary really is GNU
# time so a BSD/busybox `time` cannot silently change what is measured.
TIME_BIN="${TIME_BIN:-}"
if [[ -z "$TIME_BIN" ]]; then
  if [[ -x /usr/bin/time ]]; then
    TIME_BIN=/usr/bin/time
  else
    # `command -v time` would answer with Bash's reserved word. `type -P`
    # searches PATH for an executable file only, which is what is wanted here.
    TIME_BIN="$(type -P time || true)"
  fi
fi
[[ -n "$TIME_BIN" && -x "$TIME_BIN" ]] ||
  fail "required command not found: GNU time (set TIME_BIN)"
"$TIME_BIN" -v -o /dev/null true 2>/dev/null ||
  fail "$TIME_BIN does not support GNU time's -v -o reporting"
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

# Every large process tree has an exact memory budget. Phases are serialized,
# so the runner only has to hold the largest one at a time.
#
# These budgets bound RESIDENT memory. They used to be `ulimit -v` (RLIMIT_AS)
# ceilings, which only ever proxied for that, and the v4.33.0 toolchain ended
# even the proxy: a v4.33.0 `lean` frontend reserves about 12.8 GiB of virtual
# address space at startup -- eleven-plus 1 GiB anonymous allocator arenas --
# while its peak RSS is unchanged at roughly 2.0 GiB. An RLIMIT_AS small
# enough to catch a runaway now aborts every `lean` at startup with "failed to
# create thread", and one large enough to let `lean` start says nothing about
# memory at all. `MIMALLOC_ARENA_RESERVE` does not change the reservation.
#
# A cgroup v2 `memory.max` is the honest instrument. It accounts page cache as
# well as anonymous memory, but the kernel *reclaims* cache under pressure and
# only OOM-kills on genuine anonymous growth, so the ~5.9 GB output sibling the
# generate phase streams does not trip a budget while a real leak does. It is
# also the mechanism the host itself uses to kill oversized runs, so a phase is
# tested against the real constraint rather than a proxy for it.
#
# Measured peak RSS against the pinned corpus, in phase order, from one
# end-to-end run of this harness. build-generator is quoted from a cold build
# tree, which is the only figure the budget is about; a warm tree turns that
# phase into a relink and measures Lake itself, around 0.79 GiB.
#
#   build-generator  2.91 GiB   under BUILD_LIMIT_KIB  ( 6 GiB)
#   build-exporter   1.43 GiB   under BUILD_LIMIT_KIB  ( 6 GiB)
#   mathlib-cache    0.92 GiB   under BUILD_LIMIT_KIB  ( 6 GiB)
#   export           7.79 GiB   under EXPORT_LIMIT_KIB (12 GiB)
#   generate        11.36 GiB   under WORKER_LIMIT_KIB (12 GiB)
#   check-input      8.19 GiB   under WORKER_LIMIT_KIB (12 GiB)
#
# The build budget is no longer set by any single translation unit: splitting
# the simple construction route dropped build-generator to 2.91 GiB, so 6 GiB
# leaves it a factor of two and still fails a runaway well before the runner
# does. The export budget is sized by the exporter phase, whose 7.79 GiB the
# pinned compact-interner patch already buys, leaving 4 GiB of the standard
# runner's 16 GiB for gzip and runner services.
#
# The 12 GiB worker budget is the authoritative one for the public generator
# and the serialized kernel reread, and generation now fits under it -- but by
# 0.64 GiB, 5.3%, which is not a margin to spend. Two things make it narrower
# than it looks. A 16 GiB runner has to hold this 11.36 GiB alongside the OS,
# the gzip feeder and the page cache backing the ~5.9 GB output sibling, so the
# budget is close to the runner's real ceiling and not merely to a policy
# number. And the interner's key array is a power-of-two table: at the ~99.9M
# interned nodes this corpus reaches it sits at about 75% of a 134.2M-entry
# capacity, so a corpus that pushes it over the load factor doubles the table
# and costs roughly 1.6 GB in one step -- straight through the budget. Treat
# 12 GiB as the number generation has to keep reaching, not as headroom the
# compact certificates retained across the whole stream may grow into. See the
# generate phase below for what does and does not influence them.

# Pick the strongest memory-limiting mechanism this runner actually supports,
# once, by running each candidate for real. Nothing is assumed available:
#
#   user-scope    `systemd-run --user --scope`. The payload is a child of this
#                 shell, so environment, working directory, file descriptors
#                 and namespaces are inherited unchanged. Preferred.
#   system-scope  `sudo systemd-run --scope`, dropping straight back to the
#                 calling user with setpriv and re-applying this shell's
#                 environment. Hosted runners have passwordless sudo and a
#                 system manager but often no per-user manager, so this is
#                 usually the one that applies there.
#   measure       No usable cgroup. Phases run unbudgeted and their peak RSS is
#                 compared against the budget afterwards. That cannot prevent a
#                 runaway, but it still fails the job on one.
#
# The peak-RSS comparison runs under every mechanism, so the budget is always
# reported even when the kernel is also enforcing it. `TIME_BIN -v` reports the
# largest single process in the tree rather than the tree's sum; the cgroup is
# the accurate accountant and this is the backstop.
#
# `measure` is a weak backstop and should be read as one. Two ways it passes a
# phase the cgroup would have killed:
#
#   * It measures the largest single process, not the tree. The build phases
#     fan out into many `lean` children under Lake, so a tree that sums past
#     6 GiB reports whichever child was biggest. Only the single-worker phases
#     -- export, generate, check-input -- are measured by a number that means
#     what the budget says.
#   * It is after the fact. A runaway takes the whole runner down first; the
#     comparison never runs and the job fails as an OOM kill or a lost runner,
#     not as a budget verdict.
#
# The probes above decide which one applies, so this is not a switch to flip.
# On a GitHub-hosted Ubuntu runner the expected outcome is `system-scope`: no
# per-user manager for the `runner` user, but a system manager and passwordless
# sudo, which is what `run_system_scope` needs. If a runner ever reports
# `measure` in the job log, the budgets on that run were observations and not
# limits, and the log says so on the line above.
LIMIT_MECHANISM=measure
SCOPE_ENV="$TMP_DIR/scope-env"

run_user_scope() {
  local limit_kib="$1"
  shift
  systemd-run --user --scope --quiet --collect \
    -p MemoryMax="${limit_kib}K" -p MemorySwapMax=0 -- "$@"
}

run_system_scope() {
  local limit_kib="$1"
  shift
  # `sudo` resets the environment and the scope would otherwise run as root.
  # Carry this shell's environment across in a NUL-delimited dump and hand the
  # payload back to the calling user before it starts. The dump is per-caller
  # so nothing here assumes phases never overlap.
  local scope_env="$SCOPE_ENV.$BASHPID"
  env -0 > "$scope_env"
  sudo -n systemd-run --scope --quiet --collect \
    -p MemoryMax="${limit_kib}K" -p MemorySwapMax=0 \
    -- setpriv --reuid="$(id -u)" --regid="$(id -g)" --init-groups \
      bash -c '
        dump="$1"
        shift
        while IFS= read -r -d "" assignment; do
          case "$assignment" in
            [A-Za-z_]*=*) export "$assignment" ;;
          esac
        done < "$dump"
        rm -f "$dump"
        exec "$@"' bash "$scope_env" "$@"
}

# A candidate counts as working only if the payload really ran, as the calling
# user, with this shell's environment.
scope_probe_ok() {
  local runner="$1" observed
  observed="$(
    export CI_MATHLIB_SCOPE_PROBE=marker
    "$runner" $((1024 * 1024)) \
      sh -c 'printf "%s %s\n" "$(id -u)" "${CI_MATHLIB_SCOPE_PROBE:-unset}"' \
      2>/dev/null
  )" || return 1
  [[ "$observed" == "$(id -u) marker" ]]
}

if command -v systemd-run >/dev/null; then
  if scope_probe_ok run_user_scope; then
    LIMIT_MECHANISM=user-scope
  elif command -v setpriv >/dev/null && scope_probe_ok run_system_scope; then
    LIMIT_MECHANISM=system-scope
  fi
fi
echo "memory budgets: enforced by $LIMIT_MECHANISM"
if [[ "$LIMIT_MECHANISM" == measure ]]; then
  echo "memory budgets: no cgroup available; budgets are checked after each phase"
fi

run_capped() (
  limit_kib="$1"
  limit_label="$2"
  shift 2
  case "$LIMIT_MECHANISM" in
    user-scope) run_user_scope "$limit_kib" "$@" ;;
    system-scope) run_system_scope "$limit_kib" "$@" ;;
    measure) exec "$@" ;;
    *) fail "unknown memory-limit mechanism for $limit_label: $LIMIT_MECHANISM" ;;
  esac
)

# This report goes to stderr, never to stdout. `run_measured` is called from
# inside pipelines whose stdout is *data*: the export phase pipes the exporter's
# stdout straight into `gzip`, so a line written to stdout here is compressed
# into the export itself rather than logged. That corruption is silent until
# something downstream tries to parse the artifact -- it cost one full gate run,
# whose only symptoms were a `parse error: offset 0` from the generator, an
# export 80 bytes larger than the pinned one, and a missing `memory: export`
# line in the job log. Every phase report is a diagnostic, so stderr is also
# where it belongs on its own merits.
#
# A measurement that cannot be read is not a passed budget check. Reporting
# "unavailable" and returning success made the budget satisfiable by failing to
# measure, which is strictly worse than having no budget: an unbudgeted phase at
# least looks unbudgeted. So an unreadable or non-numeric peak fails the phase.
# The one exception is a phase that already failed on its own: GNU time may
# never have written a report, and that phase's own status is the interesting
# one, so it is left to propagate unmasked.
report_peak_rss() {
  local limit_kib="$1" limit_label="$2" label="$3" command_status="$4"
  local peak_kib
  peak_kib="$(awk -F': ' '/Maximum resident set size/ { print $2 }' \
    "$PERF_DIR/$label.time" 2>/dev/null || true)"
  if [[ ! "$peak_kib" =~ ^[0-9]+$ ]]; then
    echo "memory: $label peak RSS unavailable" >&2
    if ((command_status != 0)); then
      return 0
    fi
    fail "$label reported no readable peak RSS in $PERF_DIR/$label.time;" \
      "the $limit_label was never checked"
  fi
  awk -v kib="$peak_kib" -v budget="$limit_kib" -v phase="$label" \
    -v mechanism="$LIMIT_MECHANISM" \
    'BEGIN { printf "memory: %s peak RSS %.2f GiB of %.2f GiB budget (%s)\n",
             phase, kib / 1048576, budget / 1048576, mechanism }' >&2
  if ((peak_kib > limit_kib)); then
    fail "$label exceeded the $limit_label: ${peak_kib} KiB peak RSS"
  fi
}

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
  local status=0
  if [[ "$PERF_AVAILABLE" == true ]]; then
    run_capped "$limit_kib" "$limit_label" \
      "$TIME_BIN" -v -o "$PERF_DIR/$label.time" \
      perf stat -e instructions -o "$PERF_DIR/$label.perf" -- "$@" || status=$?
  else
    echo "instructions: unavailable" > "$PERF_DIR/$label.perf"
    run_capped "$limit_kib" "$limit_label" \
      "$TIME_BIN" -v -o "$PERF_DIR/$label.time" "$@" || status=$?
  fi
  report_peak_rss "$limit_kib" "$limit_label" "$label" "$status"
  return "$status"
}

run_build_measured() {
  run_measured "$BUILD_LIMIT_KIB" "6 GiB build/cache budget" "$@"
}

run_export_measured() {
  run_measured "$EXPORT_LIMIT_KIB" "12 GiB Mathlib export budget" "$@"
}

run_worker_measured() {
  run_measured "$WORKER_LIMIT_KIB" "12 GiB model worker budget" "$@"
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

# Build one root per Lake invocation, with Lake's parallelism bounded.
#
# The bound is `LEAN_NUM_THREADS`, not a Lake flag: Lake 5.0.0 dropped `-j` and
# `-K` only sets a configuration key a lakefile may read back, which neither
# this package nor lean4export does. The `-Kjobs=1` these phases used to pass
# was inert, so this budget was previously being met by an unbounded build that
# happened to fit. Lake schedules its build jobs as Lean tasks, so sizing the
# Lean runtime's thread pool is what bounds them. Measured on a 96-core host,
# clean `lake build lean-inductive-models`: unbounded 39.4 s wall at 4.58x
# CPU/wall and 3.00 GiB peak summed PSS; at 4, 54.0 s and 2.41 GiB; at 1,
# 164.8 s and 1.92 GiB. Four keeps the ceiling the same on every machine at a
# third of the cost of serializing, and leaves the 6 GiB budget a factor of two.
#
# The bound is applied to the Lake *builds* only. The cache phase below is a
# download, peaks at 0.91 GiB, and has nothing to gain from a thread ceiling;
# the export and generation phases are single measured workers whose numbers
# above were taken without one.
#
# Copy the standalone executables out of their build trees so every build
# artifact can be reclaimed before generation.
(cd "$ROOT" && run_build_measured build-generator \
  env LEAN_NUM_THREADS="$BUILD_THREADS" lake build lean-inductive-models)
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
# Deliberately a literal, not a copy of `$ROOT/lean-toolchain`. The exporter's
# Lean version is independent of ours: the NDJSON export is the interface
# between them. `$EXPORTER_REV` (caccfbe) ships v4.29.0 and `$MATHLIB_REV`
# (5e932f97) was built by v4.29.1, so the exporter must load those oleans under
# v4.29.1. Copying our pin here would rebuild the exporter under whatever this
# repository targets and break the gate. `scripts/export-fixture.sh` pins the
# same literal for the same reason.
echo "leanprover/lean4:v4.29.1" > "$EXPORTER_DIR/lean-toolchain"
(cd "$EXPORTER_DIR" && run_build_measured build-exporter \
  env LEAN_NUM_THREADS="$BUILD_THREADS" lake build)
cp "$EXPORTER_DIR/.lake/build/bin/lean4export" "$BIN_DIR/lean4export"
[[ -x "$BIN_DIR/lean4export" ]] || fail "exporter binary was not built"
cleanup_tree "$EXPORTER_DIR"
disk_census exporter-built

checkout_pinned \
  https://github.com/leanprover-community/mathlib4.git \
  "$MATHLIB_REV" "$MATHLIB_DIR"
(cd "$MATHLIB_DIR" && run_build_measured mathlib-cache lake exe cache get)
cleanup_tree "$MATHLIB_CACHE_DIR"
disk_census mathlib-cached

rm -f "$INPUT_GZ" "$INPUT_FIFO" "$OUTPUT"
# Everything this subshell writes to stdout becomes part of the compressed
# export. Only the exporter may write there: diagnostics inside `run_measured`,
# `run_capped` and `report_peak_rss` go to stderr, `cd` is given an absolute
# path so no CDPATH echo can reach the stream, and nothing in here may call
# `disk_census`, whose `tee` writes to stdout by construction.
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
# artifact before the full transformed AST and final output coexist.
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

# Keep the documented generation and structural-check defaults. Named output
# streams declarations into a transactional sibling. The separate serialized
# input pass below remains the authoritative kernel verdict.
#
# Do not try to reclaim the generate phase's cost by adding `--no-check-output`
# here. That flag does not govern retention or work; it only governs the
# verdict. The compact certificate arrays behind the plateau
# (`FilterState.compactRecords`, whose rows each hold an `Order.DeclSummary`
# with a `referenced : HashSet Name`, plus `compactIslands`) accumulate
# whenever the retention mode is compact, which for a named output is
# unconditionally the streaming mode. `FilterState.finalize` then runs
# `Check.compactSourceReport` over all of them regardless of the flag, because
# `plan.coveredInputOwners` -- and therefore the decline exit code -- is
# derived from that report. `config.checkOutput` decides only whether the
# resulting violations are enforced and reported, so turning it off would drop
# the structural gate on the committed artifact and break
# check-mathlib-result.sh's required `output check:` line while saving nothing.
#
# Measured A/B over the pinned Mathlib export, same binary, run with the phase
# budget lifted so neither arm is cut off. The absolute numbers predate the
# reduction recorded in the phase table above -- both arms were taken at the
# then-current 13.91 GiB -- but the comparison is between two arms of one
# binary, so it is the difference that carries and it is nil:
#
#                     wall        peak RSS     output bytes
#   default          31:17.86     13.91 GiB    5937056185
#   --no-check-output 31:19.04    13.96 GiB    5937056185
#
# Identical artifacts; the flag is worth +0.06% wall and +0.35% RSS, i.e.
# nothing but noise. In both arms the output sibling was fully written roughly
# 11 minutes before exit and RSS stayed flat for that entire tail, which is the
# post-stream `compactSourceReport` pass, not output serialization.
set +e
(
  set -o pipefail
  run_worker_measured generate \
    env LEAN_INDUCTIVE_MODELS_OUTPUT_BACKEND_TRACE=1 \
    "$BIN_DIR/lean-inductive-models" "$INPUT_FIFO" -o "$OUTPUT" \
      --no-type-check-generated \
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
# This pass is serialized after declaration-wise generation exits.
(
  set -o pipefail
  run_worker_measured check-input \
    "$BIN_DIR/lean-inductive-models" "$OUTPUT" \
      --no-inductives --check-input --no-check-output \
      --type-check-input --no-type-check-generated --no-output \
    2>&1 | tee "$LOG_DIR/check-input.log" >&2
)

"$ROOT/scripts/check-mathlib-result.sh" \
  "$LOG_DIR/generate.log" "$OUTPUT" "$LOG_DIR/check-input.log"
rm -f "$OUTPUT"
disk_census complete

echo "mathlib CI: full export generated, structurally checked, and kernel-reread"
