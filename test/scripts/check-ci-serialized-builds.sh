#!/usr/bin/env bash
# CI / maintainer-guide build and correctness matrix guard.
#
# The file name is historical. Builds here are *bounded*, not serialized: the
# one-root-per-Lake-invocation loop this script pins keeps at most one target
# link live, but inside a single invocation Lake still runs several jobs at
# once. What bounds that is `LEAN_NUM_THREADS`, which this script also pins --
# Lake 5.0.0 has no job-count flag at all, and the `-Kjobs=1` that used to
# stand in for one only set an unread configuration key. The last assertion
# below keeps that inert option from coming back.
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
workflow="$root/.github/workflows/ci.yml"
maintainer_guide="$root/docs/maintainers/Testing.md"
lakefile="$root/lakefile.lean"

# Lake's build parallelism bound, asserted to be one positive number stated
# identically by the workflow and the maintainer guide. A guard that only
# checked the shape of the build loop would pass just as happily with no bound
# at all, which is exactly the state this replaces.
workflow_bound="$(
  sed -nE 's/^[[:space:]]*LEAN_NUM_THREADS:[[:space:]]*"?([0-9]+)"?[[:space:]]*$/\1/p' \
    "$workflow" | LC_ALL=C sort -u
)"
if [[ ! "$workflow_bound" =~ ^[1-9][0-9]*$ ]]; then
  echo "CI does not set a single positive LEAN_NUM_THREADS build bound" >&2
  exit 1
fi
# The bound has to stay stated per job. A workflow-level `env:` is inherited by
# every job and no job can unset one, so hoisting it would push a thread ceiling
# into the Mathlib gate's cache, export and generation phases -- which the
# harness deliberately runs without one, and whose recorded peak RSS figures in
# docs/maintainers/Testing.md were taken that way. This is the only property
# keeping that from happening silently: the symptom would be different numbers,
# not an error.
if grep -qE '^env:[[:space:]]*$' "$workflow"; then
  echo "ci.yml sets a workflow-level env:, which the Mathlib gate job inherits" >&2
  exit 1
fi
guide_bound="$(
  sed -nE 's/^export LEAN_NUM_THREADS=([0-9]+)$/\1/p' "$maintainer_guide" |
    LC_ALL=C sort -u
)"
if [[ "$guide_bound" != "$workflow_bound" ]]; then
  echo "maintainer guide LEAN_NUM_THREADS ($guide_bound) differs from CI ($workflow_bound)" >&2
  exit 1
fi
runner_bound="$(
  sed -nE 's/^export LEAN_NUM_THREADS="\$\{LEAN_NUM_THREADS:-([0-9]+)\}"$/\1/p' \
    "$root/test/scripts/run-correctness.sh" | LC_ALL=C sort -u
)"
if [[ "$runner_bound" != "$workflow_bound" ]]; then
  echo "run-correctness.sh LEAN_NUM_THREADS default ($runner_bound) differs from CI ($workflow_bound)" >&2
  exit 1
fi
mathlib_bound="$(
  sed -nE 's/^BUILD_THREADS=([0-9]+)$/\1/p' "$root/scripts/ci-mathlib.sh" |
    LC_ALL=C sort -u
)"
if [[ "$mathlib_bound" != "$workflow_bound" ]]; then
  echo "ci-mathlib.sh BUILD_THREADS ($mathlib_bound) differs from CI ($workflow_bound)" >&2
  exit 1
fi

# One workflow, not two. The full-Mathlib gate was its own workflow file, with
# a second copy of the trigger set, the runner image and the Lean setup step;
# folding it into `ci.yml` as a job is only worth something if it stays folded
# in, so assert both halves -- `ci.yml` is the only workflow file, and it is
# what invokes the gate script.
mapfile -t workflow_files < <(
  find "$root/.github/workflows" -maxdepth 1 -type f \
    \( -name '*.yml' -o -name '*.yaml' \) -printf '%f\n' | LC_ALL=C sort
)
if [[ "${#workflow_files[@]}" -ne 1 || "${workflow_files[0]}" != ci.yml ]]; then
  printf '%s\n' "expected .github/workflows to hold ci.yml alone; found:" >&2
  printf '  %s\n' "${workflow_files[@]}" >&2
  exit 1
fi
gate_invocations="$(
  grep -cE '^[[:space:]]*run:[[:space:]]+bash scripts/ci-mathlib\.sh$' "$workflow" || true
)"
if [[ "$gate_invocations" != 1 ]]; then
  echo "CI does not invoke scripts/ci-mathlib.sh exactly once (found $gate_invocations)" >&2
  exit 1
fi
if ! grep -Fq 'scripts/ci-mathlib.sh' "$maintainer_guide"; then
  echo "maintainer guide does not name the full-Mathlib gate script" >&2
  exit 1
fi

# Keep the retired project name out of both tracked text and tracked paths.
# Construct it from separate fragments so this guard does not exempt itself.
# `-a` deliberately treats tracked binary blobs as text: generated archives or
# other binary fixtures must not preserve the retired bytes either.
retired_name="$(printf '%s%s' 'model' 'gen')"
if git -C "$root" grep -ain "$retired_name" -- .; then
  echo "tracked content still contains the retired project name" >&2
  exit 1
fi
while IFS= read -r tracked_path; do
  if [[ "${tracked_path,,}" == *"$retired_name"* ]]; then
    echo "tracked path still contains the retired project name: $tracked_path" >&2
    exit 1
  fi
done < <(git -C "$root" ls-files)

mapfile -t direct_builds < <(
  sed -nE 's/^[[:space:]]*(lake .*build .*)$/\1/p' "$workflow"
)
expected_direct_builds=(
  'lake build lean-inductive-models'
  'lake build "$target"'
)

arena_script="$root/test/scripts/check_arena_corpus.py"
for arena_flag in \
    --inductives --check-input --check-output --type-check-input --type-check-generated --no-output; do
  if ! grep -Fq "\"$arena_flag\"" "$arena_script"; then
    echo "Arena corpus checker is missing $arena_flag" >&2
    exit 1
  fi
done
if grep -Fq '"--no-inductives"' "$arena_script" || grep -Fq '"--no-check"' "$arena_script"; then
  echo "Arena corpus checker disables generation or structural checks" >&2
  exit 1
fi
sorted_direct_builds="$(printf '%s\n' "${direct_builds[@]}" | LC_ALL=C sort)"
sorted_expected_builds="$(
  printf '%s\n' "${expected_direct_builds[@]}" | LC_ALL=C sort
)"
if [[ "$sorted_direct_builds" != "$sorted_expected_builds" ]]; then
  printf '%s\n' "CI contains a Lake build outside the one-target loop:" >&2
  printf '  %s\n' "${direct_builds[@]}" >&2
  printf '%s\n' "Expected only the bounded Arena build and target loop:" >&2
  printf '  %s\n' "${expected_direct_builds[@]}" >&2
  exit 1
fi

# No tracked Lake invocation may carry a `-K` configuration option. Lake 5.0.0
# reads `-K` only as a key for the configuration file to consume via
# `get_config?`, and this lakefile consumes none, so every such option here has
# been a silent no-op pretending to control the build. Prose may name the
# option; a command line may not. Case matters: an invocation is lowercase.
config_opt="$(printf '%s%s' '-' 'K')"
if git -C "$root" grep -nE "(^|[[:space:]])lake[[:space:]][^#]*$config_opt" \
    -- '*.sh' '*.yml' '*.md'; then
  echo "a Lake invocation passes a $config_opt option; it does not bound the build" >&2
  exit 1
fi

function_source="$({
  sed -n '/^          build_bounded() {$/,/^          }$/p' "$workflow"
} | sed 's/^          //')"
if [[ -z "$function_source" ]]; then
  echo "CI build_bounded function is missing" >&2
  exit 1
fi

actual="$({
  eval "$function_source"
  lake() { printf '%s\n' "$*"; }
  build_bounded alpha beta gamma
})"
expected=$'build alpha\nbuild beta\nbuild gamma'
if [[ "$actual" != "$expected" ]]; then
  printf 'CI build_bounded did not issue one Lake root per invocation:\n%s\n' "$actual" >&2
  exit 1
fi

readme_function_source="$(
  sed -n '/^build_bounded() {$/,/^}$/p' "$maintainer_guide"
)"
if [[ -z "$readme_function_source" ]]; then
  echo "maintainer guide build_bounded function is missing" >&2
  exit 1
fi
mapfile -t readme_direct_builds < <(
  sed -nE 's/^[[:space:]]*(TMPDIR="[^\"]+" )?(lake .*build .*)$/\2/p' "$maintainer_guide"
)
if [[ "${#readme_direct_builds[@]}" -ne 1 ||
      "${readme_direct_builds[0]}" != 'lake build "$target"' ]]; then
  printf '%s\n' "maintainer guide contains a Lake build outside the one-target loop:" >&2
  printf '  %s\n' "${readme_direct_builds[@]}" >&2
  exit 1
fi

readme_actual="$({
  eval "$readme_function_source"
  lake() { printf '%s\n' "$*"; }
  build_bounded alpha beta gamma
})"
if [[ "$readme_actual" != "$expected" ]]; then
  printf 'maintainer guide build_bounded did not issue one Lake root per invocation:\n%s\n' \
    "$readme_actual" >&2
  exit 1
fi

# The compile-only targets are the `lean_lib`s under `test/` that no suite
# module imports: nothing builds them as a side effect of building the test
# binary, so each has to be named in the build matrices or it is never compiled
# at all. `TestSuites` is excluded because it is the library the suite modules
# themselves live in -- `lake build test` builds exactly its imported modules.
mapfile -t lake_test_libraries < <(
  current=
  while IFS= read -r line; do
    if [[ "$line" =~ ^lean_lib[[:space:]]+([^[:space:]]+)[[:space:]]+where$ ]]; then
      current="${BASH_REMATCH[1]}"
    elif [[ "$line" =~ ^lean_exe[[:space:]]+ ]]; then
      current=
    elif [[ -n "$current" && "$line" =~ ^[[:space:]]+srcDir[[:space:]]+:=[[:space:]]+\"test\"$ ]]; then
      printf '%s\n' "$current"
      current=
    elif [[ -n "$current" && "$line" =~ ^[[:space:]]+srcDir[[:space:]]+:= ]]; then
      current=
    fi
  done < "$lakefile"
)
mapfile -t lake_compile_only_targets < <(
  for library in "${lake_test_libraries[@]}"; do
    if [[ "$library" == TestSuites ]]; then
      continue
    fi
    if ! grep -qxE "import $library" "$root"/test/*.lean; then
      printf '%s\n' "$library"
    fi
  done
)
if [[ "${#lake_compile_only_targets[@]}" -eq 0 ]]; then
  echo "no compile-only library found in $lakefile; the extraction stopped working" >&2
  exit 1
fi

readme_compile_source="$(
  sed -n '/^compile_only_targets=($/,/^)/p' "$maintainer_guide"
)"
ci_compile_source="$(
  sed -n '/^          compile_only_targets=($/,/^          )/p' "$workflow" |
    sed 's/^          //'
)"
for matrix_name in readme_compile_source ci_compile_source; do
  declare -n matrix_source="$matrix_name"
  if [[ -z "$matrix_source" ]]; then
    printf '%s\n' "$matrix_name is missing" >&2
    exit 1
  fi
  mapfile -t compile_matrix_targets < <(
    eval "$matrix_source"
    printf '%s\n' "${compile_only_targets[@]}"
  )
  sorted_matrix_targets="$(printf '%s\n' "${compile_matrix_targets[@]}" | LC_ALL=C sort)"
  sorted_compile_targets="$(
    printf '%s\n' "${lake_compile_only_targets[@]}" | LC_ALL=C sort
  )"
  if [[ "$sorted_matrix_targets" != "$sorted_compile_targets" ]]; then
    printf '%s differs from the lakefile compile-only libraries:\n' "$matrix_name" >&2
    diff -u \
      <(printf '%s\n' "$sorted_compile_targets") \
      <(printf '%s\n' "$sorted_matrix_targets") >&2 || true
    exit 1
  fi
done

# There is one test executable and the suite is its first argument, so the
# agreement this script enforces is no longer between lists of Lake targets but
# between the dispatcher's registry and the three places that name suites: the
# runner, the workflow and the maintainer guide. `test/TestMain.lean` is the
# registry, and it is the file the binary itself dispatches on -- a suite
# spelled wrong anywhere else is a name the binary rejects at run time, and a
# suite missing from a matrix is a suite nothing runs.
registry="$root/test/TestMain.lean"
mapfile -t registry_suites < <(
  sed -n '/^def correctnessSuites : List Suite :=$/,/^  \]$/p' "$registry" |
    sed -nE 's/^  [][,] suite "([a-z]+)".*$/\1/p'
)
if [[ "${#registry_suites[@]}" -lt 2 ]]; then
  echo "test/TestMain.lean correctnessSuites registry did not parse" >&2
  exit 1
fi
sorted_registry="$(printf '%s\n' "${registry_suites[@]}" | LC_ALL=C sort)"
if [[ "$sorted_registry" != "$(printf '%s\n' "${registry_suites[@]}" | LC_ALL=C sort -u)" ]]; then
  echo "test/TestMain.lean registers a suite name twice" >&2
  exit 1
fi
# The diagnostics are registered apart and must stay out of the matrices; set
# equality below is what enforces that, so assert the registry really does keep
# them in a second list rather than in the one compared.
if ! sed -n '/^def diagnosticSuites : List Suite :=$/,/^  \]$/p' "$registry" |
    grep -qE '^  \[ suite "[a-z]+"'; then
  echo "test/TestMain.lean has no diagnosticSuites registry" >&2
  exit 1
fi

# The runner and the guide state the suite list as one array each; the workflow
# runs `fixtures` and `maincli` in their own matrix jobs and the rest from an
# array, so its list is the union of the two spellings.
runner_suites_source="$(
  sed -n '/^correctness_suites=($/,/^)/p' "$root/test/scripts/run-correctness.sh"
)"
readme_suites_source="$(
  sed -n '/^correctness_suites=($/,/^)/p' "$maintainer_guide"
)"
ci_suites_source="$(
  sed -n '/^              focused_suites=($/,/^              )$/p' "$workflow" |
    sed 's/^              //'
)"
for matrix_name in runner_suites_source readme_suites_source ci_suites_source; do
  declare -n matrix_source="$matrix_name"
  if [[ -z "$matrix_source" ]]; then
    printf '%s\n' "$matrix_name is missing" >&2
    exit 1
  fi
done
mapfile -t runner_suites < <(
  eval "$runner_suites_source"
  printf '%s\n' "${correctness_suites[@]}"
)
mapfile -t readme_suites < <(
  eval "$readme_suites_source"
  printf '%s\n' "${correctness_suites[@]}"
)
mapfile -t ci_suites < <(
  eval "$ci_suites_source"
  printf '%s\n' "${focused_suites[@]}"
  sed -nE 's/^[[:space:]]*lake exe test ([a-z]+).*$/\1/p' "$workflow"
)
# The guide also spells the individual execution matrix out, one line per suite.
mapfile -t readme_run_suites < <(
  sed -nE 's/^lake exe test ([a-z]+).*$/\1/p' "$maintainer_guide"
)
for matrix_name in runner_suites readme_suites ci_suites readme_run_suites; do
  declare -n matrix_suites="$matrix_name"
  sorted_matrix_suites="$(printf '%s\n' "${matrix_suites[@]}" | LC_ALL=C sort)"
  if [[ "$sorted_matrix_suites" != "$sorted_registry" ]]; then
    printf '%s\n' "$matrix_name differs from the test/TestMain.lean suite registry:" >&2
    diff -u \
      <(printf '%s\n' "$sorted_registry") \
      <(printf '%s\n' "$sorted_matrix_suites") >&2 || true
    exit 1
  fi
done

mapfile -t check_scripts < <(
  find "$root/test/scripts" -maxdepth 1 -type f \
    \( -name 'check-*.sh' -o -name 'check_*.py' \) \
    -printf 'test/scripts/%f\n' | LC_ALL=C sort
)
mapfile -t readme_check_scripts < <(
  sed -nE \
    -e 's|^(TMPDIR="[^\"]+" )?(test/scripts/check-[^[:space:]]+\.sh).*|\2|p' \
    -e 's|^(TMPDIR="[^\"]+" )?(test/scripts/check_[^[:space:]]+\.py).*|\2|p' \
    "$maintainer_guide" | LC_ALL=C sort
)
mapfile -t ci_check_scripts < <(
  sed -nE \
    -e 's|^[[:space:]]*(test/scripts/check-[^[:space:]]+\.sh).*|\1|p' \
    -e 's|^[[:space:]]*(test/scripts/check_[^[:space:]]+\.py).*|\1|p' \
    "$workflow" | LC_ALL=C sort
)
expected_scripts="$(printf '%s\n' "${check_scripts[@]}")"
for matrix_name in readme_check_scripts ci_check_scripts; do
  declare -n matrix_scripts="$matrix_name"
  actual_scripts="$(printf '%s\n' "${matrix_scripts[@]}")"
  if [[ "$actual_scripts" != "$expected_scripts" ]]; then
    printf '%s\n' "$matrix_name differs from the repository check scripts:" >&2
    diff -u \
      <(printf '%s\n' "$expected_scripts") \
      <(printf '%s\n' "$actual_scripts") >&2 || true
    exit 1
  fi
done

echo "CI/maintainer-guide build matrix: LEAN_NUM_THREADS=$workflow_bound, \
${#registry_suites[@]} suites, ${#lake_compile_only_targets[@]} compile-only libraries, \
${#check_scripts[@]} scripts"
