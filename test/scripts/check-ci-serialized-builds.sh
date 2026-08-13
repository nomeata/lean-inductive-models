#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
workflow="$root/.github/workflows/ci.yml"
readme="$root/README.md"
lakefile="$root/lakefile.lean"

mapfile -t direct_builds < <(
  sed -nE 's/^[[:space:]]*(lake .*build .*)$/\1/p' "$workflow"
)
expected_direct_builds=(
  'lake -Kjobs=1 build modelgen'
  'lake -Kjobs=1 build "$target"'
)

arena_script="$root/test/scripts/check_arena_corpus.py"
for arena_flag in \
    --inductives --check-input --check-output --type-check-input --type-check-output --no-output; do
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
  printf '%s\n' "Expected only the serialized Arena build and target loop:" >&2
  printf '  %s\n' "${expected_direct_builds[@]}" >&2
  exit 1
fi

function_source="$({
  sed -n '/^          build_serially() {$/,/^          }$/p' "$workflow"
} | sed 's/^          //')"
if [[ -z "$function_source" ]]; then
  echo "CI build_serially function is missing" >&2
  exit 1
fi

actual="$({
  eval "$function_source"
  lake() { printf '%s\n' "$*"; }
  build_serially alpha beta gamma
})"
expected=$'-Kjobs=1 build alpha\n-Kjobs=1 build beta\n-Kjobs=1 build gamma'
if [[ "$actual" != "$expected" ]]; then
  printf 'CI build_serially did not issue one Lake root per invocation:\n%s\n' "$actual" >&2
  exit 1
fi

readme_function_source="$(
  sed -n '/^build_serially() {$/,/^}$/p' "$readme"
)"
if [[ -z "$readme_function_source" ]]; then
  echo "README build_serially function is missing" >&2
  exit 1
fi
mapfile -t readme_direct_builds < <(
  sed -nE 's/^[[:space:]]*(TMPDIR="[^\"]+" )?(lake .*build .*)$/\2/p' "$readme"
)
if [[ "${#readme_direct_builds[@]}" -ne 1 ||
      "${readme_direct_builds[0]}" != 'lake -Kjobs=1 build "$target"' ]]; then
  printf '%s\n' "README contains a Lake build outside the one-target loop:" >&2
  printf '  %s\n' "${readme_direct_builds[@]}" >&2
  exit 1
fi

readme_actual="$({
  eval "$readme_function_source"
  lake() { printf '%s\n' "$*"; }
  build_serially alpha beta gamma
})"
if [[ "$readme_actual" != "$expected" ]]; then
  printf 'README build_serially did not issue one Lake root per invocation:\n%s\n' \
    "$readme_actual" >&2
  exit 1
fi

mapfile -t lake_test_targets < <(
  current=
  while IFS= read -r line; do
    if [[ "$line" =~ ^(\[default_target\][[:space:]]+)?lean_exe[[:space:]]+([^[:space:]]+)[[:space:]]+where$ ]]; then
      current="${BASH_REMATCH[2]}"
    elif [[ -n "$current" && "$line" =~ ^[[:space:]]+srcDir[[:space:]]+:=[[:space:]]+\"test\"$ ]]; then
      if [[ "$current" != memoryprobe ]]; then
        printf '%s\n' "$current"
      fi
      current=
    fi
  done < "$lakefile"
)

readme_targets_source="$(
  sed -n '/^correctness_targets=($/,/^)/p' "$readme"
)"
if [[ -z "$readme_targets_source" ]]; then
  echo "README correctness_targets array is missing" >&2
  exit 1
fi
mapfile -t readme_targets < <(
  eval "$readme_targets_source"
  printf '%s\n' "${correctness_targets[@]}"
)

sorted_lake_targets="$(printf '%s\n' "${lake_test_targets[@]}" | LC_ALL=C sort)"
sorted_readme_targets="$(printf '%s\n' "${readme_targets[@]}" | LC_ALL=C sort)"
if [[ "$sorted_readme_targets" != "$sorted_lake_targets" ]]; then
  printf '%s\n' "README correctness targets differ from lakefile.lean:" >&2
  diff -u \
    <(printf '%s\n' "$sorted_lake_targets") \
    <(printf '%s\n' "$sorted_readme_targets") >&2 || true
  exit 1
fi

mapfile -t readme_run_targets < <(
  sed -nE 's/^TMPDIR="[^\"]+" lake exe ([^[:space:]]+).*$/\1/p' "$readme"
)
mapfile -t ci_run_targets < <(
  sed -nE 's/^[[:space:]]*lake exe ([^[:space:]]+).*$/\1/p' "$workflow"
)
for matrix_name in readme_run_targets ci_run_targets; do
  declare -n matrix_targets="$matrix_name"
  sorted_matrix_targets="$(printf '%s\n' "${matrix_targets[@]}" | LC_ALL=C sort)"
  if [[ "$sorted_matrix_targets" != "$sorted_lake_targets" ]]; then
    printf '%s\n' "$matrix_name differs from the lakefile.lean correctness targets:" >&2
    diff -u \
      <(printf '%s\n' "$sorted_lake_targets") \
      <(printf '%s\n' "$sorted_matrix_targets") >&2 || true
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
    "$readme" | LC_ALL=C sort
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

echo "CI/README serialized builds and correctness matrix: ${#lake_test_targets[@]} targets, ${#check_scripts[@]} scripts"
