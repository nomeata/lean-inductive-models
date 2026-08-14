#!/usr/bin/env python3
"""Generate finite-family adapter regression sources deterministically.

The command accepts arbitrary nonnegative finite arities.  Its defaults form a
small covering set around historical implementation boundaries; they are test
samples, not model eligibility limits.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence


DEFAULT_ARITIES = (0, 1, 2, 3, 5, 8)
DEFAULT_MEMBER_COUNTS = (1, 2, 3, 5)
DEFAULT_CONSTRUCTOR_COUNTS = (1, 2, 3, 5)
DEFAULT_INDEX_ARITIES = (1, 2, 3)


def parse_counts(value: str) -> tuple[int, ...]:
    counts = tuple(int(part) for part in value.split(",") if part)
    if not counts:
        raise argparse.ArgumentTypeError("a count list must not be empty")
    if any(count < 0 for count in counts):
        raise argparse.ArgumentTypeError("counts must be nonnegative")
    return counts


def grouped_binders(prefix: str, count: int, type_: str) -> str:
    if count == 0:
        return ""
    names = " ".join(f"{prefix}{index}" for index in range(count))
    return f" ({names} : {type_})"


def unique_counts(values: Sequence[int]) -> tuple[int, ...]:
    if any(value < 0 for value in values):
        raise ValueError("fixture counts must be nonnegative")
    return tuple(dict.fromkeys(values))


def emit_direct(arity: int) -> tuple[str, str]:
    name = f"GeneratedDirect{arity}"
    fields = grouped_binders("child", arity, name)
    return name, f"inductive {name} : Type where\n  | mk{fields} : {name}\n"


def emit_dependent(arity: int) -> tuple[str, str]:
    name = f"GeneratedDependent{arity}"
    fields = grouped_binders("child", arity, name)
    return name, (
        f"inductive {name} : Type where\n"
        f"  | mk (which : GeneratedKey) (payload : GeneratedPayload which)"
        f"{fields} : {name}\n"
    )


def emit_infinitary(arity: int) -> tuple[str, str]:
    name = f"GeneratedInfinitary{arity}"
    fields = "".join(
        f" (children{index} : GeneratedKey -> {name})" for index in range(arity)
    )
    return name, f"inductive {name} : Type where\n  | mk{fields} : {name}\n"


def emit_nested(arity: int) -> tuple[str, str]:
    name = f"GeneratedNested{arity}"
    fields = grouped_binders("children", arity, f"GeneratedList {name}")
    return name, f"inductive {name} : Type where\n  | mk{fields} : {name}\n"


def indexed_application(name: str, index_arity: int) -> str:
    suffix = " ".join(f"index{index}" for index in range(index_arity))
    return f"{name} {suffix}".strip()


def emit_indexed(index_arity: int, occurrences: int) -> tuple[str, str]:
    name = f"GeneratedIndexed{index_arity}x{occurrences}"
    indices = grouped_binders("index", index_arity, "GeneratedIndex")
    application = indexed_application(name, index_arity)
    fields = grouped_binders("child", occurrences, application)
    former = " -> ".join(["GeneratedIndex"] * index_arity + ["Type"])
    return name, (
        f"inductive {name} : {former} where\n"
        f"  | mk{indices}{fields} : {application}\n"
    )


def emit_constructor_family(constructors: int, occurrences: int) -> tuple[str, str]:
    name = f"GeneratedConstructors{constructors}x{occurrences}"
    if constructors == 0:
        return name, f"inductive {name} : Type\n"
    lines = [f"inductive {name} : Type where"]
    for constructor in range(constructors):
        fields = grouped_binders(f"child{constructor}_", occurrences, name)
        lines.append(f"  | c{constructor}{fields} : {name}")
    return name, "\n".join(lines) + "\n"


def emit_mutual(member_count: int, occurrences: int) -> tuple[list[str], str]:
    names = [f"GeneratedMutual{member_count}x{occurrences}_{index}"
             for index in range(member_count)]
    lines = [] if member_count == 1 else ["mutual"]
    for owner_index, owner in enumerate(names):
        lines.append(f"inductive {owner} : Type where")
        lines.append(f"  | stop : {owner}")
        fields = []
        for occurrence in range(occurrences):
            target = names[(owner_index + occurrence + 1) % member_count]
            fields.append(f"(edge{occurrence} : {target})")
        suffix = " " + " ".join(fields) if fields else ""
        lines.append(f"  | step{suffix} : {owner}")
    if member_count != 1:
        lines.append("end")
    return names, "\n".join(lines) + "\n"


@dataclass(frozen=True)
class FixtureMatrix:
    arities: Sequence[int]
    member_counts: Sequence[int]
    constructor_counts: Sequence[int]
    index_arities: Sequence[int]

    def render(self) -> str:
        sections: list[str] = []
        exported = ["GeneratedIndex", "GeneratedKey", "GeneratedPayload", "GeneratedList"]

        arities = unique_counts(self.arities)
        member_counts = unique_counts(self.member_counts)
        constructor_counts = unique_counts(self.constructor_counts)
        index_arities = unique_counts(self.index_arities)

        for arity in arities:
            for emitter in (emit_direct, emit_dependent, emit_infinitary, emit_nested):
                name, source = emitter(arity)
                exported.append(name)
                sections.append(source)

        occurrence_samples = arities
        for index_arity in index_arities:
            for occurrences in occurrence_samples:
                name, source = emit_indexed(index_arity, occurrences)
                exported.append(name)
                sections.append(source)

        constructor_occurrences = max(occurrence_samples, default=0)
        for constructors in constructor_counts:
            name, source = emit_constructor_family(constructors, constructor_occurrences)
            exported.append(name)
            sections.append(source)

        mutual_occurrences = max(occurrence_samples, default=0)
        for members in member_counts:
            if members == 0:
                continue
            names, source = emit_mutual(members, mutual_occurrences)
            exported.extend(names)
            sections.append(source)

        header = """/-
Generated by `test/scripts/generate_family_adapter_fixtures.py`.

The sampled counts straddle former unary/binary/singleton boundaries.  They
are regression inputs only: the generator accepts arbitrary finite counts.
-/
prelude

namespace FamilyAdapterGenerated

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive GeneratedIndex : Type where
  | zero
  | next (index : GeneratedIndex)

inductive GeneratedKey : Type where
  | key

inductive GeneratedPayload : GeneratedKey -> Type where
  | at (which : GeneratedKey) : GeneratedPayload which

inductive GeneratedList (alpha : Type) : Type where
  | nil : GeneratedList alpha
  | cons (head : alpha) (tail : GeneratedList alpha) : GeneratedList alpha
"""
        export_line = "--#export " + " ".join(
            f"FamilyAdapterGenerated.{name}" for name in exported
        ) + "\n"
        return header + "\n" + "\n".join(sections) + \
            "\nend FamilyAdapterGenerated\n\n" + export_line


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--output", type=Path, required=True)
    result.add_argument("--arities", type=parse_counts,
                        default=DEFAULT_ARITIES)
    result.add_argument("--member-counts", type=parse_counts,
                        default=DEFAULT_MEMBER_COUNTS)
    result.add_argument("--constructor-counts", type=parse_counts,
                        default=DEFAULT_CONSTRUCTOR_COUNTS)
    result.add_argument("--index-arities", type=parse_counts,
                        default=DEFAULT_INDEX_ARITIES)
    result.add_argument("--check", action="store_true",
                        help="fail if OUTPUT is not already the deterministic result")
    return result


def main(argv: Iterable[str] | None = None) -> int:
    args = parser().parse_args(argv)
    fixture = FixtureMatrix(
        arities=args.arities,
        member_counts=args.member_counts,
        constructor_counts=args.constructor_counts,
        index_arities=args.index_arities,
    ).render()
    if args.check:
        if not args.output.exists() or args.output.read_text() != fixture:
            raise SystemExit(f"{args.output} is not the current deterministic fixture")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(fixture)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
