#!/usr/bin/env bash
# Regenerate Lean sources as committed NDJSON fixtures.
#
#   scripts/export-fixture.sh [NAME[.lean] ...]
#
# `FIXTURE_DIR` selects the source directory and defaults to the modelgen
# fixtures. `OUT_DIR` defaults to the same directory. `MODELGEN_FILTER=0`
# retains the raw lean4export result; otherwise the export is passed through
# modelgen. A source line containing exactly `--#monomorph` additionally
# enables `modelgen --mono-levels`.
#
# The exporter checkout, compiler output, and intermediate exports all live
# below the repository-local `_tmp/` directory. `LEAN4EXPORT_DIR` and
# `MODELGEN_BIN` may point at existing builds.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FIXTURES="${FIXTURE_DIR:-$ROOT/test/fixtures/modelgen}"
OUT="${OUT_DIR:-$FIXTURES}"
FILTER="${MODELGEN_FILTER:-1}"
TOOLCHAIN="leanprover/lean4:v4.29.1"
EXPORT_REV="caccfbe"
EXPORT_DIR="${LEAN4EXPORT_DIR:-$ROOT/_tmp/lean4export}"

command -v elan >/dev/null || { echo "elan is not on PATH" >&2; exit 2; }
mkdir -p "$ROOT/_tmp" "$OUT"

if [[ ! -d "$EXPORT_DIR/.git" ]]; then
  git clone --quiet https://github.com/leanprover/lean4export "$EXPORT_DIR"
fi
git -C "$EXPORT_DIR" checkout --quiet "$EXPORT_REV"
printf '%s\n' "$TOOLCHAIN" > "$EXPORT_DIR/lean-toolchain"
( cd "$EXPORT_DIR" && lake build >&2 )

EXPORTER_BIN="$EXPORT_DIR/.lake/build/bin/lean4export"
MODELGEN_BIN="${MODELGEN_BIN:-$ROOT/.lake/build/bin/modelgen}"
EXPORT_LEAN_PATH="$(cd "$EXPORT_DIR" && lake env printenv LEAN_PATH)"

ensure_modelgen() {
  if [[ ! -x "$MODELGEN_BIN" ]]; then
    echo "building modelgen" >&2
    ( cd "$ROOT" && lake build modelgen >&2 )
  fi
  [[ -x "$MODELGEN_BIN" ]] || {
    echo "modelgen is not built: $MODELGEN_BIN" >&2
    exit 2
  }
}

declare -a SOURCES=()
if (($#)); then
  for arg in "$@"; do SOURCES+=("$FIXTURES/$(basename "$arg")"); done
else
  while IFS= read -r file; do SOURCES+=("$file"); done \
    < <(find "$FIXTURES" -maxdepth 1 -type f -name '*.lean' | sort)
fi

WORK="$(mktemp -d "$ROOT/_tmp/export-fixture.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

for source in "${SOURCES[@]}"; do
  [[ -f "$source" ]] || { echo "fixture source not found: $source" >&2; exit 2; }
  base="$(basename "$source" .lean)"
  module="$(printf '%s' "$base" | sed -E 's/(^|_)([a-z])/\U\2/g')"
  cp "$source" "$WORK/$module.lean"
  ( cd "$WORK" && elan run "$TOOLCHAIN" lean -o "$module.olean" "$module.lean" )

  declare -a ONLY=()
  while IFS= read -r name; do ONLY+=("$name"); done \
    < <(sed -n 's/^--#export  *//p' "$source" | tr ' ' '\n' | grep -v '^$')
  if ((${#ONLY[@]})); then
    LEAN_PATH="$WORK:$EXPORT_LEAN_PATH" "$EXPORTER_BIN" "$module" -- "${ONLY[@]}" \
      > "$OUT/$base.ndjson"
  else
    LEAN_PATH="$WORK:$EXPORT_LEAN_PATH" "$EXPORTER_BIN" "$module" > "$OUT/$base.ndjson"
  fi
  unset ONLY

  MONO=0
  grep -q '^--#monomorph *$' "$source" && MONO=1
  if ((FILTER || MONO)); then
    ensure_modelgen
    declare -a MODELGEN_ARGS=()
    ((MONO)) && MODELGEN_ARGS+=(--mono-levels)
    ((!FILTER)) && MODELGEN_ARGS+=(--no-inductives)
    "$MODELGEN_BIN" "${MODELGEN_ARGS[@]}" \
      "$OUT/$base.ndjson" -o "$WORK/$base.filtered.ndjson"
    mv "$WORK/$base.filtered.ndjson" "$OUT/$base.ndjson"
    unset MODELGEN_ARGS
  fi

  suffix=""
  ((!FILTER)) && suffix=" (unfiltered)"
  ((MONO)) && suffix="$suffix (monomorphized)"
  echo "$base.ndjson: $(wc -l < "$OUT/$base.ndjson") lines$suffix" >&2
done
