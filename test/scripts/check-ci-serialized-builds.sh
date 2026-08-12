#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
workflow="$root/.github/workflows/ci.yml"

mapfile -t direct_builds < <(
  sed -nE 's/^[[:space:]]*(lake -Kjobs=1 build .*)$/\1/p' "$workflow"
)
if [[ "${#direct_builds[@]}" -ne 1 ||
      "${direct_builds[0]}" != 'lake -Kjobs=1 build "$target"' ]]; then
  printf '%s\n' "CI contains a Lake build outside the one-target loop:" >&2
  printf '  %s\n' "${direct_builds[@]}" >&2
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

echo "CI serialized builds: pass"
