#!/usr/bin/env bash
# Regenerate Lean sources as committed NDJSON fixtures.
#
#   scripts/export-fixture.sh [NAME[.lean] ...]
#
# `FIXTURE_DIR` selects the source directory and defaults to the lean-inductive-models
# fixtures. `OUT_DIR` defaults to the same directory. `LEAN_INDUCTIVE_MODELS_FILTER=0`
# retains the raw lean4export result; otherwise the export is passed through
# lean-inductive-models. A source line containing exactly `--#monomorph` additionally
# enables `lean-inductive-models --mono-levels`.
#
# The exporter checkout, compiler output, and intermediate exports all live
# below the repository-local `_tmp/` directory. `LEAN4EXPORT_DIR` and
# `LEAN_INDUCTIVE_MODELS_BIN` may point at existing builds. Every child inherits a 16 GiB
# virtual-memory limit.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FIXTURES="${FIXTURE_DIR:-$ROOT/test/fixtures/lean-inductive-models}"
OUT="${OUT_DIR:-$FIXTURES}"
FILTER="${LEAN_INDUCTIVE_MODELS_FILTER:-1}"
TOOLCHAIN="leanprover/lean4:v4.29.1"
EXPORT_REV="caccfbe"
EXPORT_DIR="${LEAN4EXPORT_DIR:-$ROOT/_tmp/lean4export}"
MEMORY_LIMIT_KIB=16777216

current_memory_limit="$(ulimit -Sv)"
if [[ "$current_memory_limit" == unlimited ]] ||
    ((current_memory_limit > MEMORY_LIMIT_KIB)); then
  ulimit -Sv "$MEMORY_LIMIT_KIB"
fi

command -v elan >/dev/null || { echo "elan is not on PATH" >&2; exit 2; }
mkdir -p "$ROOT/_tmp" "$OUT"

if [[ ! -d "$EXPORT_DIR/.git" ]]; then
  git clone --quiet https://github.com/leanprover/lean4export "$EXPORT_DIR"
fi
git -C "$EXPORT_DIR" checkout --quiet "$EXPORT_REV"
printf '%s\n' "$TOOLCHAIN" > "$EXPORT_DIR/lean-toolchain"
( cd "$EXPORT_DIR" && lake build >&2 )

EXPORTER_BIN="$EXPORT_DIR/.lake/build/bin/lean4export"
LEAN_INDUCTIVE_MODELS_BIN="${LEAN_INDUCTIVE_MODELS_BIN:-$ROOT/.lake/build/bin/lean-inductive-models}"
EXPORT_LEAN_PATH="$(cd "$EXPORT_DIR" && lake env printenv LEAN_PATH)"

ensure_inductive_models() {
  if [[ ! -x "$LEAN_INDUCTIVE_MODELS_BIN" ]]; then
    echo "building lean-inductive-models" >&2
    ( cd "$ROOT" && lake build lean-inductive-models >&2 )
  fi
  [[ -x "$LEAN_INDUCTIVE_MODELS_BIN" ]] || {
    echo "lean-inductive-models is not built: $LEAN_INDUCTIVE_MODELS_BIN" >&2
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
    ensure_inductive_models
    declare -a LEAN_INDUCTIVE_MODELS_ARGS=()
    ((MONO)) && LEAN_INDUCTIVE_MODELS_ARGS+=(--mono-levels)
    ((!FILTER)) && LEAN_INDUCTIVE_MODELS_ARGS+=(--no-inductives)
    "$LEAN_INDUCTIVE_MODELS_BIN" "${LEAN_INDUCTIVE_MODELS_ARGS[@]}" \
      "$OUT/$base.ndjson" -o "$WORK/$base.filtered.ndjson"
    mv "$WORK/$base.filtered.ndjson" "$OUT/$base.ndjson"
    unset LEAN_INDUCTIVE_MODELS_ARGS
  fi

  suffix=""
  ((!FILTER)) && suffix=" (unfiltered)"
  ((MONO)) && suffix="$suffix (monomorphized)"
  echo "$base.ndjson: $(wc -l < "$OUT/$base.ndjson") lines$suffix" >&2
done
