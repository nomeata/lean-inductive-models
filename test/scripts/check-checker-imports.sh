#!/usr/bin/env bash
set -euo pipefail

# The independent structural checker must not import the generator it checks.
#
# `README.md` states the checker's checks "intentionally do not unfold
# definitions, use proof irrelevance, ask Lean for definitional equality, or
# inspect arbitrary declaration values", and concludes that the correspondence
# check is independent of the kernel verdict. Independence is a claim about
# *reach*: a checker that imports the nested generator can call it, and no
# amount of care inside `Check.lean` makes that unreachable for the next
# change. This guard turns the claim into something mechanical by reading the
# import graph.
#
# Two directions are enforced, because either alone rots:
#
#   * no module of the generator is in the checker's transitive closure, named
#     explicitly so that a rename is a visible edit; and
#   * the closure is exactly the checker's declared foundation, so a *new*
#     generator module under a name this script has never heard of is caught
#     the day it is imported rather than the day someone remembers to add it.
#
# Names on the forbidden list need not exist yet — `Gen` and `Nested` are the
# split the generator is expected to grow into, and listing them now costs
# nothing and closes the window later. Every forbidden name that *does* exist
# is required to be reachable from the driver, which is what keeps the list
# from silently degrading into a set of typos that forbid nothing.

root="$(cd "$(dirname "$0")/../.." && pwd)"
src="$root/src/InductiveModels"

checker_root=Check
driver_root=Driver

# The modules the structural checker is entitled to reach. `EqKit` is the
# equality plumbing carved out of `Model.lean` for exactly this reason: it is
# `Name`/`Expr` construction with no generator monad in it.
allowed_closure=(Check EqKit Format Naming Plan Projection)

# The generator. `Check` may not reach any of these, directly or transitively.
forbidden=(Gen Nested Simple Mutual Driver Model)

if [[ ! -d "$src" ]]; then
  echo "source directory is missing: $src" >&2
  exit 1
fi

# The source file a module name denotes. A dotted name is a directory path, so
# a module split into `Format/Foo.lean` is followed rather than reported lost.
file_of() {
  printf '%s/%s.lean' "$src" "${1//.//}"
}

# Direct `import InductiveModels.X` edges of one module, module names only.
imports_of() {
  local module="$1" file
  file="$(file_of "$module")"
  if [[ ! -f "$file" ]]; then
    echo "import graph names a module with no source file: $module" >&2
    exit 1
  fi
  sed -nE 's/^import[[:space:]]+InductiveModels\.([A-Za-z0-9_.]+)[[:space:]]*$/\1/p' "$file"
}

# Transitive closure including the root itself, one module per line, sorted.
closure_of() {
  local start="$1"
  local -a frontier=("$start")
  local -A seen=()
  seen["$start"]=1
  while [[ "${#frontier[@]}" -gt 0 ]]; do
    local current="${frontier[0]}"
    frontier=("${frontier[@]:1}")
    local next
    while IFS= read -r next; do
      [[ -z "$next" ]] && continue
      if [[ -z "${seen[$next]:-}" ]]; then
        seen["$next"]=1
        frontier+=("$next")
      fi
    done < <(imports_of "$current")
  done
  printf '%s\n' "${!seen[@]}" | LC_ALL=C sort
}

mapfile -t checker_closure < <(closure_of "$checker_root")
mapfile -t driver_closure < <(closure_of "$driver_root")

in_list() {
  local needle="$1"; shift
  local candidate
  for candidate in "$@"; do
    [[ "$candidate" == "$needle" ]] && return 0
  done
  return 1
}

status=0

for module in "${forbidden[@]}"; do
  if in_list "$module" "${checker_closure[@]}"; then
    printf '%s\n' \
      "the structural checker reaches the generator: InductiveModels.$checker_root imports InductiveModels.$module transitively" >&2
    status=1
  fi
  if [[ -f "$(file_of "$module")" ]] && ! in_list "$module" "${driver_closure[@]}"; then
    printf '%s\n' \
      "forbidden module InductiveModels.$module exists but is unreachable from InductiveModels.$driver_root; the forbidden list has gone stale" >&2
    status=1
  fi
done

sorted_allowed="$(printf '%s\n' "${allowed_closure[@]}" | LC_ALL=C sort)"
sorted_actual="$(printf '%s\n' "${checker_closure[@]}")"
if [[ "$sorted_actual" != "$sorted_allowed" ]]; then
  printf '%s\n' \
    "InductiveModels.$checker_root transitive imports differ from the checker's declared foundation:" >&2
  diff -u <(printf '%s\n' "$sorted_allowed") <(printf '%s\n' "$sorted_actual") >&2 || true
  status=1
fi

if [[ "$status" -ne 0 ]]; then
  exit 1
fi

echo "structural checker imports: ${#checker_closure[@]} modules, none of them the generator"
