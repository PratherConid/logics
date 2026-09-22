"""Where each principle holds, and how the principles are ordered by strength.

Prints a table over the named frames, then sweeps every poset up to a given
size.  Fewer algebras validating a principle means a stronger principle, so the
final listing reads as a strength order.

Usage:  python compare_principles.py [max_points]
"""

from __future__ import annotations

import sys
from itertools import product

import heyting as H

COMBINED = ["PierceOrLuk", "PierceOrLuk'", "DeMorganOrLuk",
            "DeMorganOrLuk'", "ImpOrOrLuk", "ImpOrOrLuk'",
            "PeirceOrImpOr", "PeirceOrImpOr'"]


def table_over_named_frames() -> None:
    print("validity in the named frames (T = reaches the top value everywhere)\n")
    width = max(len(n) for n in COMBINED)
    head = " " * 12 + "  ".join(n.rjust(width) for n in COMBINED)
    print(head + "   EM   WEM")
    for name, poset in H.NAMED_FRAMES.items():
        alg = H.Algebra(poset)
        cells = ["T".rjust(width) if alg.is_valid(H.PRINCIPLES[n]) else ".".rjust(width)
                 for n in COMBINED]
        em = "T" if alg.is_valid(H.excluded_middle) else "."
        wem = "T" if alg.is_valid(H.weak_excluded_middle) else "."
        print(f"{name:<12}" + "  ".join(cells) + f"   {em:<4} {wem}")


def sweep(max_points: int) -> None:
    names = COMBINED + ["ExcludedMiddle", "WeakExcludedMiddle"]
    valid_count = {n: 0 for n in names}
    strictly_weaker = {(x, y): 0 for x, y in product(names, names) if x != y}
    total = 0

    for poset in H.posets_upto(max_points):
        alg = H.Algebra(poset)
        valid = {n: alg.is_valid(H.PRINCIPLES[n]) for n in names}
        total += 1
        for x in names:
            valid_count[x] += valid[x]
        for x, y in strictly_weaker:
            if valid[x] and not valid[y]:
                strictly_weaker[(x, y)] += 1

    print(f"\n\nsweep of all {total} posets on up to {max_points} points\n")
    print("  principle             valid in")
    for n in sorted(names, key=lambda n: -valid_count[n]):
        print(f"  {n:<22}{valid_count[n]:>5}   (more algebras = weaker)")

    print("\n  strength separations (first valid where second is not):")
    found = False
    for (x, y), count in sorted(strictly_weaker.items(), key=lambda kv: -kv[1]):
        if count:
            print(f"    {x:<20} but not {y:<20}{count:>5}")
            found = True
    if not found:
        print("    (none: all of them validate exactly the same algebras)")


def main() -> None:
    max_points = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    table_over_named_frames()
    sweep(max_points)


if __name__ == "__main__":
    main()
