"""Find an algebra validating one principle but not another.

Such an algebra is exactly what shows the first principle does not derive the
second: by soundness, every substitution instance of a valid principle is
valid, so no list of them can prove something the algebra refutes.  Finding
none is evidence the two principles generate the same logic, not proof of it.

Searches the named frames, then every poset up to ``--sweep`` points, then
random posets of larger sizes.

Usage:  python separating_frames.py FIRST SECOND [--sweep 5] [--random 150]
"""

from __future__ import annotations

import argparse
import random
import sys

import heyting as H


def separates(poset: H.Poset, first: str, second: str) -> tuple[int, int] | None:
    """The first failing pair of `second`, if `first` is valid here and `second` not."""
    alg = H.Algebra(poset)
    if not alg.is_valid(H.PRINCIPLES[first]):
        return None
    bad = alg.failures(H.PRINCIPLES[second])
    if not bad:
        return None
    a, b = bad[0]
    return alg.index(a), alg.index(b)


class Reporter:
    """Prints the first separating algebra of each stage and counts the rest.

    Labelled posets come in many isomorphic copies, so printing every hit buries
    the one worth looking at.
    """

    def __init__(self, first: str, second: str) -> None:
        self.first, self.second, self.total = first, second, 0

    def stage(self, heading: str) -> None:
        print(f"\n{heading}")
        self.shown = False

    def check(self, label: str, poset: H.Poset) -> None:
        hit = separates(poset, self.first, self.second)
        if hit is None:
            return
        self.total += 1
        if not self.shown:
            self.shown = True
            alg_size = 2 ** len(poset)
            print(f"  SEPARATED by {label}: {self.second} fails at "
                  f"elements {hit[0]}, {hit[1]} of a <= {alg_size} element algebra")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("first", help="principle that should be valid")
    parser.add_argument("second", help="principle that should fail")
    parser.add_argument("--sweep", type=int, default=5)
    parser.add_argument("--random", type=int, default=150)
    parser.add_argument("--seed", type=int, default=20260922)
    args = parser.parse_args()

    for name in (args.first, args.second):
        if name not in H.PRINCIPLES:
            sys.exit(f"unknown principle {name!r}; known: {', '.join(H.PRINCIPLES)}")

    print(f"looking for an algebra where {args.first} holds "
          f"but {args.second} fails")
    reporter = Reporter(args.first, args.second)

    reporter.stage("named frames:")
    for name, poset in H.NAMED_FRAMES.items():
        reporter.check(name, poset)

    reporter.stage(f"all posets up to {args.sweep} points:")
    total = 0
    for poset in H.posets_upto(args.sweep):
        total += 1
        reporter.check(f"a {len(poset)} point poset", poset)
    print(f"  checked {total}")

    rng = random.Random(args.seed)
    for size in (6, 7):
        reporter.stage(f"{args.random} random posets on {size} points:")
        checked = 0
        for poset in H.random_posets(size, args.random, rng):
            if 2 ** len(poset) > 256:  # keep each check cheap
                continue
            checked += 1
            reporter.check(f"a {size} point poset", poset)
        print(f"  checked {checked}")

    print(f"\n{reporter.total} separating algebras found in total "
          f"(labelled posets repeat each one up to isomorphism)")
    if not reporter.total:
        print(f"{args.first} may well derive {args.second}; "
              f"try find_instantiation.py")


if __name__ == "__main__":
    main()
