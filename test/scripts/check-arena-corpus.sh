#!/usr/bin/env bash
# Run modelgen as a Lean Kernel Arena checker against the published corpus.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../.." && pwd)"
bin="${MODELGEN_BIN:-$root/.lake/build/bin/modelgen}"
url="${ARENA_TESTS_URL:-https://arena.lean-lang.org/lean-arena-tests.tar.gz}"

if (($# > 1)); then
  echo "usage: $0 [lean-arena-tests.tar.gz]" >&2
  exit 2
fi
[[ -x "$bin" ]] || { echo "modelgen is not built: $bin" >&2; exit 2; }

mkdir -p "$root/_tmp"
work="$(mktemp -d "$root/_tmp/arena-corpus.XXXXXX")"
trap 'rm -rf -- "$work"' EXIT
archive="${1:-$work/lean-arena-tests.tar.gz}"

if (($# == 0)); then
  curl --fail --location --retry 5 --retry-all-errors \
    --output "$archive" "$url"
fi
[[ -f "$archive" ]] || { echo "Arena archive not found: $archive" >&2; exit 2; }

# Reject links, special files, traversal, duplicate paths, and implausibly large
# expanded archives before invoking tar. The published archive contains only
# regular NDJSON files rooted directly below good/ and bad/.
python3 - "$archive" <<'PY'
import pathlib
import sys
import tarfile

archive = sys.argv[1]
seen = set()
total_size = 0
counts = {"good": 0, "bad": 0}
try:
    with tarfile.open(archive, "r:gz") as stream:
        members = stream.getmembers()
        for member in members:
            path = pathlib.PurePosixPath(member.name)
            canonical = path.as_posix()
            valid_path = (
                canonical == member.name
                and not path.is_absolute()
                and len(path.parts) >= 2
                and path.parts[0] in counts
                and path.suffix == ".ndjson"
                and ".." not in path.parts
            )
            if not valid_path or not member.isfile():
                raise ValueError(f"unsafe or unexpected archive member: {member.name!r}")
            if canonical in seen:
                raise ValueError(f"duplicate archive member: {member.name!r}")
            if member.size > 256 * 1024 * 1024:
                raise ValueError(f"archive member is too large: {member.name!r}")
            seen.add(canonical)
            counts[path.parts[0]] += 1
            total_size += member.size
        if not seen or not all(counts.values()):
            raise ValueError("archive must contain regular NDJSON files in good/ and bad/")
        if total_size > 2 * 1024 * 1024 * 1024:
            raise ValueError("expanded archive is larger than 2 GiB")
except (tarfile.TarError, OSError, ValueError) as error:
    print(f"invalid Arena archive: {error}", file=sys.stderr)
    raise SystemExit(2)
PY

corpus="$work/corpus"
mkdir -p "$corpus" "$work/logs" "$work/runtime"
tar --extract --gzip --file "$archive" --directory "$corpus" \
  --no-same-owner --no-same-permissions

good_passed=0
bad_passed=0
failed=0
total=0

run_group() {
  local group="$1" expected="$2" file relative stderr_log stdout_log status
  while IFS= read -r -d '' file; do
    relative="${file#"$corpus/"}"
    stderr_log="$work/logs/${relative//\//_}.stderr"
    stdout_log="$work/logs/${relative//\//_}.stdout"
    set +e
    TMPDIR="$work/runtime" "$bin" \
      --no-inductives --no-check --type-check-input --no-output "$file" \
      >"$stdout_log" 2>"$stderr_log"
    status=$?
    set -e
    ((total += 1))
    if ((status == expected)); then
      if [[ "$group" == good ]]; then
        ((good_passed += 1))
      else
        ((bad_passed += 1))
      fi
      continue
    fi

    ((failed += 1))
    printf 'FAIL %s: expected exit %d, got %d\n' "$relative" "$expected" "$status" >&2
    if [[ -s "$stderr_log" ]]; then
      sed -n '1,8{s/^/  /;p;}' "$stderr_log" >&2
    elif [[ -s "$stdout_log" ]]; then
      sed -n '1,8{s/^/  stdout: /;p;}' "$stdout_log" >&2
    fi
  done < <(find "$corpus/$group" -type f -name '*.ndjson' -print0 | LC_ALL=C sort -z)
}

run_group good 0
run_group bad 1

printf 'Arena corpus: %d good accepted, %d bad rejected, %d failed (%d total)\n' \
  "$good_passed" "$bad_passed" "$failed" "$total"
((failed == 0))
