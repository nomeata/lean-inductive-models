#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
out_dir="$root/_tmp/shared-prefix-ownership"
mkdir -p "$out_dir"

ulimit -Sv 12582912
ulimit -Hv 12582912

# This is a source-to-C ownership oracle, not a native build.  The two-phase
# route depends on the RC compiler consuming the private preparation object,
# popping snapshot roots before owner work, and not retaining a second
# FilterState reference across the mutating feed transition.
lake env lean -c "$out_dir/Driver.c" -o "$out_dir/Driver.olean" \
  "$root/src/InductiveModels/Driver.lean"

PYTHONDONTWRITEBYTECODE=1 python3 - "$out_dir/Driver.c" \
  "$root/src/InductiveModels/Driver.lean" <<'PY'
import re
import sys
from pathlib import Path

text = Path(sys.argv[1]).read_text()
source = Path(sys.argv[2]).read_text()


def function_body(name: str) -> str:
    pattern = re.compile(
        rf"LEAN_EXPORT lean_object\* [^\s\n]*{re.escape(name)}\([^;\n]*\) \{{"
    )
    match = pattern.search(text)
    if match is None:
        raise SystemExit(f"generated C is missing {name}")
    start = match.start()
    depth = 0
    opened = False
    for index in range(match.end() - 1, len(text)):
        char = text[index]
        if char == "{":
            depth += 1
            opened = True
        elif char == "}":
            depth -= 1
            if opened and depth == 0:
                return text[start : index + 1]
    raise SystemExit(f"generated C has an unterminated {name}")


def function_containing(*markers: str) -> str:
    pattern = re.compile(r"LEAN_EXPORT lean_object\* [^\s\n]+\([^;\n]*\) \{")
    for match in pattern.finditer(text):
        depth = 0
        for index in range(match.end() - 1, len(text)):
            char = text[index]
            if char == "{":
                depth += 1
            elif char == "}":
                depth -= 1
                if depth == 0:
                    body = text[match.start() : index + 1]
                    if all(marker in body for marker in markers):
                        return body
                    break
    raise SystemExit(f"generated C has no function containing {markers}")


state_match = re.search(
    r"private structure FilterState where\n(?P<body>.*?)(?=\nprivate (?:inductive|def|structure))",
    source,
    re.S,
)
if state_match is None:
    raise SystemExit("cannot parse FilterState fields")
state_fields = re.findall(r"^  ([A-Za-z][A-Za-z0-9_?]*)\s*:", state_match.group("body"), re.M)
try:
    main_env_field = state_fields.index("mainEnv")
    compact_field = state_fields.index("compactRecords")
    kernel_rows_field = state_fields.index("kernelCheckRows")
except ValueError as error:
    raise SystemExit(f"cannot locate ownership-sensitive FilterState field: {error}")


outer = function_body("InductiveModels_runSharedPrefixPhaseB")
reverse = re.search(r"l_Array_reverse___redArg\((x_\d+)\)", outer)
if reverse is None:
    raise SystemExit("shared-prefix Phase B no longer consumes a reversed snapshot stack")
snapshot = reverse.group(1)
before_reverse = outer[: reverse.start()]
capture = re.search(
    rf"{snapshot} = lean_ctor_get\(x_1, 2\);\s*lean_inc_ref\({snapshot}\);",
    before_reverse,
)
if capture is None or "lean_dec_ref(x_1);" not in before_reverse[capture.end() :]:
    raise SystemExit("prepared snapshot roots remain live when the stack is reversed")
after_prepared_drop = before_reverse.rsplit("lean_dec_ref(x_1);", 1)[1]
if re.search(rf"lean_inc(?:_ref)?\({snapshot}\);", after_prepared_drop):
    raise SystemExit("snapshot array is incremented again after consuming preparation")

loop = function_containing(
    "InductiveModels_prepareSharedPrefixOwnerState(",
    "InductiveModels_feedSharedPrefixOwner(",
    "lean_array_pop(",
)
pop_at = loop.find("lean_array_pop(")
prepare_call = re.search(
    r"InductiveModels_prepareSharedPrefixOwnerState\((x_\d+),", loop
)
owner_call = re.search(
    r"InductiveModels_feedSharedPrefixOwner\((x_\d+),", loop
)
if prepare_call is None or owner_call is None:
    raise SystemExit("shared-prefix owner loop lost pop/support/feed ownership landmarks")
if pop_at < 0 or not (pop_at < prepare_call.start() and pop_at < owner_call.start()):
    raise SystemExit("owner snapshot is not popped before preparation and feed")

accumulator = prepare_call.group(1)
accumulator_capture = re.search(
    rf"{accumulator} = lean_ctor_get\((x_\d+), 1\);\s*lean_inc\({accumulator}\);",
    loop,
)
if accumulator_capture is None:
    raise SystemExit("cannot identify the consuming loop-state transfer")
loop_state = accumulator_capture.group(1)
release = f"lean_ctor_release({loop_state}, 1);"
release_at = loop.find(release, accumulator_capture.end(), prepare_call.start())
if release_at < 0:
    raise SystemExit("loop tuple retains a FilterState sibling before owner preparation")
after_release = loop[release_at + len(release) : prepare_call.start()]
if re.search(rf"lean_inc(?:_ref)?\({accumulator}\);", after_release):
    raise SystemExit("FilterState is incremented after its loop-state transfer")
if re.search(rf"lean_ctor_get\({accumulator}, {compact_field}\)", loop):
    raise SystemExit("owner loop retains compactRecords across its consuming transition")

prepare = function_body("InductiveModels_prepareSharedPrefixOwnerState")
installs = [match.start() for match in re.finditer(
    r"InductiveModels_installSharedPrefixSupport\(", prepare
)]
set_envs = [match.start() for match in re.finditer(r"l_Lean_setEnv[^\n]*\(", prepare)]
install_at = installs[0] if installs else -1
main_capture = re.search(
    rf"(x_\d+) = lean_ctor_get\(x_1, {main_env_field}\);", prepare[:install_at]
)
if install_at < 0 or main_capture is None:
    raise SystemExit("owner preparation no longer exposes the prior mainEnv release")
old_main = main_capture.group(1)
if f"lean_dec({old_main});" not in prepare[main_capture.end() : install_at]:
    raise SystemExit("prior owner mainEnv remains live during support replay")
if len(set_envs) < len(installs) or any(
    set_at >= install_at for set_at, install_at in zip(set_envs, installs)
):
    raise SystemExit("ambient Meta environment is not reset before every support replay branch")

owner = function_body("InductiveModels_feedSharedPrefixOwner")
feed = re.search(r"InductiveModels_FilterState_feedSource\((x_\d+),", owner)
if feed is None:
    raise SystemExit("owner transition no longer reaches feedSource")
current = feed.group(1)
feed_segment = owner[: feed.start()]
if "lean_is_exclusive(x_1)" not in feed_segment:
    raise SystemExit("owner transition no longer tests exclusive FilterState ownership")
if re.search(rf"lean_inc(?:_ref)?\({current}\);", feed_segment):
    raise SystemExit("FilterState is reference-counted again before feedSource")
if not re.search(rf"lean_ctor_set\({current}, {compact_field}, (x_\d+)\);", feed_segment):
    raise SystemExit("feedSource no longer receives the consumed updated FilterState")
compact_value = re.search(
    rf"lean_ctor_set\({current}, {compact_field}, (x_\d+)\);", feed_segment
).group(1)
if f"lean_ctor_release(x_1, {compact_field});" not in feed_segment:
    raise SystemExit("compactRecords is copied rather than transferred from FilterState")
after_release = feed_segment.rsplit(f"lean_ctor_release(x_1, {compact_field});", 1)[1]
if re.search(rf"lean_inc(?:_ref)?\({compact_value}\);", after_release):
    raise SystemExit("compactRecords gains a sibling after its ownership transfer")
if f"lean_ctor_release(x_1, {kernel_rows_field});" not in feed_segment:
    raise SystemExit("kernel row state is copied rather than transferred to feedSource")

print("shared-prefix ownership: generated C consumes snapshots and FilterState")
PY
