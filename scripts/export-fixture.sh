#!/usr/bin/env bash
# Regenerate the designed end-to-end fixtures in `mini/tests/fixtures/`.
#
#   scripts/export-fixture.sh                    # every .lean in the fixture dir
#   scripts/export-fixture.sh rung_ladder.lean   # just these
#
# Each `<name>.lean` becomes `<name>.ndjson` beside it. The `.lean` source is
# checked in next to the export so the intent is readable and the export is
# reproducible; the `.ndjson` is checked in too, so neither `lean` nor the
# network is needed to run the tests.
#
# # The toolchain, and why it is pinned where it is
#
# `vendor/arena-tests` was co-developed with `lean-mini-kernel` and every file
# in it carries
#
#     "lean":{"githash":"f72c35b3f637c8c6571d353742168ab66cc22c00","version":"4.29.1"}
#
# in its meta line. This script reproduces **that exact pair** — Lean v4.29.1
# and `lean4export` at `caccfbe` (`chore: bump toolchain to v4.29.0`, the last
# commit before the v4.30 bump) — so a designed fixture and a corpus fixture
# differ in their content and in nothing else.
#
# There is no version *skew* to work around: `lean4export` has emitted export
# format `3.1.0` continuously from v4.29 through v4.33-rc1, and
# `checker/src/parser.rs`'s `check_semver` accepts `>= 3.1.0, < 3.2.0`, so a
# newer toolchain would parse too. The pin is about holding the *content*
# generator fixed, not about placating the parser — an unpinned regeneration
# that silently changed, say, how `let` binders or structure-eta flags are
# emitted would show up as a fixture diff nobody asked for.
#
# # Why the sources say `prelude`
#
# `lean4export` exports a module together with its transitive dependencies, so
# importing `Init` would emit thousands of declarations and bury the shape each
# fixture exists to exercise. Every source here is therefore `prelude` — no
# imports at all — and declares from scratch the three `unsafe axiom`s
# (`lcErased`, `lcAny`, `lcVoid`) that `Init.Prelude` declares in its first
# lines and that the code generator needs before it will accept an `inductive`.
# They are `unsafe`, so they are not exported and never reach the checker.
#
# # Why the sources carry an `--#export` line, and why they carry `def`s
#
# `mini::ledger::run` opens a `(declaration, σ)` pair for every `Axiom` and
# `Def` in the export and for **no** `Inductive`: a type former, its
# constructors and its recursor are one `Declaration::Inductive`, and nothing
# asks them for `⊢ ⟦c.{σ}⟧ ∈ ⟦ty[σ]⟧` on their own. An export that declares an
# inductive and nothing else therefore measures *nothing* — it is accepted, and
# the ledger is empty. Every fixture consequently carries `def`s that mention
# the type former, each constructor and (where it is the point) the recursor;
# those defs are the pairs the tests assert on. `042_rbTreeDef`'s `rbTreeDef` is
# the corpus doing the same thing.
#
# Lean also generates `T.recOn`, `T.below`, `T.brecOn` and friends beside every
# inductive. They are real declarations and would be checked, but they bury the
# named use sites in noise and make `--block` stop somewhere incidental. A
# source may therefore list the declarations to export on a line of the form
#
#     --#export Name1 Name2 ...
#
# (several such lines are concatenated), which becomes `lean4export`'s `--`
# filter. Transitive dependencies are pulled in automatically, so the list only
# needs the declarations the fixture is *about*. This is the shape the corpus
# has: `042_rbTreeDef.ndjson` contains `Color`, `N`, `RBTree`, their
# constructors, `rec`, and `rbTreeDef` — no `recOn`, no `below`.
#
# # The `modelgen` pass, and why the filtered output is what is committed
#
# `mini/src/nested_splice.rs` no longer *generates* the model of a nested
# inductive: `modelgen/` splices it into the export (`MODELGEN.md` §1) and mini
# recognises what is there. So a fixture with a nested inductive has to arrive
# already filtered, and every `.ndjson` this script writes is passed through
# `modelgen` before it is committed. The filter is the **identity** on a file
# with nothing to splice — measured over 73 corpus files — so the pass is
# unconditional and the diff on a non-nested fixture is empty.
#
# The alternative was to commit the raw export and filter at test time. That
# was rejected: `mini/tests/fixtures`' whole point is that "the `.ndjson` is
# checked in too, so neither `lean` nor the network is needed to run the tests"
# (above), and filtering at test time would put a pinned Lean toolchain on the
# critical path of `cargo test`. The cost of the choice is that a committed
# `.ndjson` is no longer byte-for-byte what `lean4export` emitted for the
# `.lean` beside it — for the five nested fixtures it is that export with the
# model spliced in. `modelgen` is idempotent (it declines `nested model name
# taken` on its own output and passes it through byte for byte), so
# re-running this script over an already-filtered tree is a no-op.
#
# # `MODELGEN_FILTER=0`, and the directory that must *not* be filtered
#
# Idempotence is what makes the pass safe to re-run, and it is also what makes
# an already-filtered file **useless as input to `modelgen`'s own test suite**:
# the generator declines `nested model name taken` and axes 1–3 of
# `modelgen/Test.lean` — the counts, the kernel, the statements — measure
# nothing. `modelgen/tests/` therefore holds the *unfiltered* export of every
# shape it asserts on, and `modelgen/tests/export.sh` sets `MODELGEN_FILTER=0`
# to get one. Two directories, two requirements: `mini/tests/fixtures` must be
# filtered so `cargo test` needs no Lean, `modelgen/tests` must not be so the
# generator has something to generate.
#
# `MODELGEN_FILTER=0` was also, until it existed, a **silent** hazard rather
# than a choice: `modelgen/tests/export.sh` and `monotests/export.sh` route
# through this script, so from the commit that added the pass onward,
# regenerating either directory would have filtered it — turning `modelgen`'s
# own inputs into its own output. Neither had been re-run since.
#
# # Where it reads and where it writes
#
# `FIXTURE_DIR` is the directory the `.lean` sources are read from (default
# `mini/tests/fixtures`) and `OUT_DIR` is where the `.ndjson` is written
# (default: the same). They are separate so the five nested shapes can have
# **one** `.lean` — in `mini/tests/fixtures`, where the Rust suite's fixture
# lives — and two exports, a filtered one beside the source and a raw one under
# `modelgen/tests`. A second copy of a `.lean` would be a second thing to keep
# in step, and `modelgen/Test.lean` cross-checks the two exports against each
# other instead.
#
# `MODELGEN_BIN` overrides the binary; the default is `modelgen`'s own
# `lake build` output, which this script builds if it is not there.
#
# # `--#monomorph`, and why one fixture is not `lean4export`'s output
#
# A source may carry a line
#
#     --#monomorph
#
# on which the export is additionally passed through `monomorph`
# (`MONOMORPH.md`), after the `modelgen` filter and before it is written.
# `mini/tests/fixtures/mono_prefix.lean` is the only one that does.
#
# It is there because the shape it measures **cannot be written in Lean**.
# `monomorph` names the copy of a declaration at σ by prepending
# `_at.⟨|σ|⟩.⟨σ₀⟩…` at the root, and a name whose root component is `_at`
# followed by `Name.num` components is not something a `.lean` source can
# declare. The alternative — a unit test that hands `direct::clause_for` a
# hand-built `_at.1.0.Acc` — measures the table and not the pipeline, and the
# pipeline is what `MONOMORPH.md` §4.3 found the defect in.
#
# `MONOMORPH_BIN` overrides the binary, which is built beside `modelgen` from
# the same package.
#
# Set `LEAN4EXPORT_DIR` to reuse an existing clone; the default is a scratch
# checkout under `target/`, which is gitignored.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FIXTURES="${FIXTURE_DIR:-$ROOT/tests}"
OUT="${OUT_DIR:-$FIXTURES}"
FILTER="${MODELGEN_FILTER:-1}"
TOOLCHAIN="leanprover/lean4:v4.29.1"
EXPORT_REV="caccfbe"
EXPORT_DIR="${LEAN4EXPORT_DIR:-$ROOT/_tmp/lean4export}"

command -v elan >/dev/null || { echo "elan is not on PATH" >&2; exit 2; }

if [[ ! -d "$EXPORT_DIR/.git" ]]; then
  echo "cloning lean4export into $EXPORT_DIR" >&2
  git clone --quiet https://github.com/leanprover/lean4export "$EXPORT_DIR"
fi
git -C "$EXPORT_DIR" checkout --quiet "$EXPORT_REV"
# The pinned revision asks for v4.29.0; the corpus was built at v4.29.1, which
# is the same export format and the same githash line is what we compare on.
printf '%s\n' "$TOOLCHAIN" > "$EXPORT_DIR/lean-toolchain"
( cd "$EXPORT_DIR" && lake build >&2 )
BIN="$EXPORT_DIR/.lake/build/bin/lean4export"
MODELGEN_BIN="${MODELGEN_BIN:-$ROOT/.lake/build/bin/modelgen}"
MONOMORPH_BIN="${MONOMORPH_BIN:-$ROOT/.lake/build/bin/monomorph}"
if ((FILTER)); then
  if [[ ! -x "$MODELGEN_BIN" ]]; then
    echo "building modelgen" >&2
    ( cd "$ROOT" && lake build >&2 )
  fi
  [[ -x "$MODELGEN_BIN" ]] || { echo "no modelgen at $MODELGEN_BIN" >&2; exit 2; }
fi
EXPORT_LEAN_PATH="$(cd "$EXPORT_DIR" && lake env printenv LEAN_PATH)"

declare -a SOURCES=()
if (($#)); then
  for a in "$@"; do SOURCES+=("$FIXTURES/$(basename "$a")"); done
else
  while IFS= read -r f; do SOURCES+=("$f"); done < <(find "$FIXTURES" -name '*.lean' | sort)
fi

mkdir -p "$ROOT/_tmp"
WORK="$(mktemp -d "$ROOT/_tmp/export-fixture.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

for src in "${SOURCES[@]}"; do
  base="$(basename "$src" .lean)"
  # lean4export takes a *module* name, so the source is compiled under a
  # capitalised, identifier-shaped module name in a scratch directory.
  mod="$(printf '%s' "$base" | sed -E 's/(^|_)([a-z])/\U\2/g')"
  cp "$src" "$WORK/$mod.lean"
  ( cd "$WORK" && elan run "$TOOLCHAIN" lean -o "$mod.olean" "$mod.lean" )
  declare -a ONLY=()
  while IFS= read -r name; do ONLY+=("$name"); done \
    < <(sed -n 's/^--#export  *//p' "$src" | tr ' ' '\n' | grep -v '^$')
  if ((${#ONLY[@]})); then
    LEAN_PATH="$WORK:$EXPORT_LEAN_PATH" "$BIN" "$mod" -- "${ONLY[@]}" > "$OUT/$base.ndjson"
  else
    LEAN_PATH="$WORK:$EXPORT_LEAN_PATH" "$BIN" "$mod" > "$OUT/$base.ndjson"
  fi
  unset ONLY
  # The model of every nested inductive, spliced in — see the header. The
  # filter writes to a scratch file inside `$WORK` and the result is moved into
  # place, so a failed pass leaves the previous fixture untouched rather than
  # half a file.
  # (`>&2` used to be needed here because the report was on stdout; it is on
  # stderr now — `MODELGEN.md` §1.4 — so the report arrives there by itself.)
  if ((FILTER)); then
    "$MODELGEN_BIN" "$OUT/$base.ndjson" -o "$WORK/$base.filtered.ndjson"
    mv "$WORK/$base.filtered.ndjson" "$OUT/$base.ndjson"
  fi
  # `--#monomorph`: universe levels removed, one copy per instantiation, every
  # name carrying the root prefix. After the `modelgen` filter, because that is
  # the order the pipeline runs them in and `MONOMORPH.md` §1.1's prefix is
  # shape-free precisely so it composes onto `T._model.*`. Same move-into-place
  # discipline as above.
  MONO=0
  grep -q '^--#monomorph *$' "$src" && MONO=1
  if ((MONO)); then
    if [[ ! -x "$MONOMORPH_BIN" ]]; then
      echo "building monomorph" >&2
      ( cd "$ROOT" && lake build monomorph >&2 )
    fi
    [[ -x "$MONOMORPH_BIN" ]] || { echo "no monomorph at $MONOMORPH_BIN" >&2; exit 2; }
    "$MONOMORPH_BIN" "$OUT/$base.ndjson" -o "$WORK/$base.mono.ndjson"
    mv "$WORK/$base.mono.ndjson" "$OUT/$base.ndjson"
  fi
  echo "$base.ndjson: $(wc -l < "$OUT/$base.ndjson") lines$( ((FILTER)) || echo ' (unfiltered)')$( ((MONO)) && echo ' (monomorphized)')" >&2
done
