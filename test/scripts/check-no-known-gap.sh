#!/usr/bin/env bash
set -euo pipefail

# No shape an arm ought to reach and does not: nothing in this tool declines
# with `incomplete`.
#
# The vocabulary for a gap is deliberately kept: `Decline.ShapeScope` still has
# both `incomplete` ("not as complete as it should be") and `outOfScope`
# ("intentionally does not handle"), because the day a genuine gap appears it
# must be recordable as one rather than dressed up as a boundary. What holds
# today is that *nothing produces* the first scope, and a claim about
# production is a claim about reach: a decline site added next month is a gap
# nobody wrote down.
#
# So the mechanical form of the claim is: no decline site names `.incomplete`.
# Every producer spells the scope on the same line as the constructor
# (`declineWith (.shapeUnsupported tname .outOfScope`), which is the shape this
# reads. The `outOfScope` producers are counted too, so that a refactor which
# moved the scope onto its own line would fail here rather than silently make
# this script forbid nothing.

root="$(cd "$(dirname "$0")/../.." && pwd)"
src="$root/src/InductiveModels"

if [[ ! -d "$src" ]]; then
  echo "check-no-known-gap: cannot find $src" >&2
  exit 1
fi

mapfile -t sites < <(grep -rn '\.shapeUnsupported' --include='*.lean' "$src" || true)

gaps=()
boundaries=0
for site in "${sites[@]}"; do
  text="${site#*:*:}"
  # The declaration of the constructor itself, and the two readers that match
  # on it, are the type's own definition rather than a decline site.
  if [[ "$text" == *"| shapeUnsupported"* || "$text" == *"| .shapeUnsupported"* ]]; then
    continue
  fi
  # Prose about the scopes is not a producer of one. A line comment cannot
  # decline anything, so skipping it costs no reach.
  trimmed="${text#"${text%%[![:space:]]*}"}"
  if [[ "$trimmed" == --* ]]; then
    continue
  fi
  if [[ "$text" == *".incomplete"* ]]; then
    gaps+=("$site")
  fi
  if [[ "$text" == *".outOfScope"* ]]; then
    boundaries=$((boundaries + 1))
  fi
done

if (( ${#gaps[@]} > 0 )); then
  echo "check-no-known-gap: nothing declined .incomplete before; these sites now do:" >&2
  printf '  %s\n' "${gaps[@]}" >&2
  exit 1
fi

if (( boundaries == 0 )); then
  echo "check-no-known-gap: found no .outOfScope decline site either, so this check \
is reading nothing; the decline sites must spell the scope on the constructor's own line" >&2
  exit 1
fi

echo "check-no-known-gap: no .incomplete decline site; ${boundaries} stated boundaries"
