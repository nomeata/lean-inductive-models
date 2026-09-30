#!/usr/bin/env bash
# Fail if a source file calls one of Lean's expression walks that is not
# memoized. Each of these recurses into both children of a node without a
# cache, so it costs the expression's size as a tree, which can be exponential
# in its size as a DAG; docs/maintainers/DagSafety.md has the table and the
# memoized replacement for each.
#
# The kit that provides the replacements, src/InductiveModels/ExprDag.lean, is
# the one file allowed to name them. Elsewhere even a comment has to spell them
# without the leading dot, which keeps this a plain text search.
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
src="$root/src"

# `\b` after the name keeps `containsFVarDag` and friends out of the match.
pattern='\.(containsFVar|hasAnyFVar|replaceNoCache|sizeWithoutSharing|dbgToString)\b|\b(instantiateLevelParamsNoCache|Expr\.replaceNoCache)\b'

status=0
while IFS= read -r hit; do
  file="${hit%%:*}"
  case "$file" in
    */InductiveModels/ExprDag.lean) continue ;;
  esac
  echo "unmemoized Expr walk: $hit" >&2
  status=1
done < <(grep -rnE "$pattern" --include='*.lean' "$src" || true)

if [[ "$status" -ne 0 ]]; then
  echo "use the memoized form from InductiveModels.Dag (docs/maintainers/DagSafety.md)" >&2
  exit 1
fi
echo "DAG-safe calls: no unmemoized core Expr walk in src/"
