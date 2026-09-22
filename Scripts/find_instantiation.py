"""Search for a substitution instance making one principle derive another.

A derivation of ``target(a, b)`` from a principle ``source`` need not use
``source(a, b)``; it may use ``source`` at shifted arguments.  This searches
for such a shift semantically: a pair of terms ``(A, B)`` with
``source(A, B) <= target(a, b)`` in every test algebra.

Two stages, because they fail differently.  A search over a handful of frames
is fast but produces false positives, so every survivor is rechecked against a
full sweep; only survivors of that are reported.  A ``source`` that is strictly
weaker than ``target`` will of course yield nothing.

Usage:  python find_instantiation.py SOURCE TARGET [--depth 2] [--sweep 5]
        python find_instantiation.py --list
"""

from __future__ import annotations

import argparse
import random
import sys

import heyting as H

# small and highly discriminating, used to cut the candidate set down fast
PRUNE_FRAMES = ["discriminating", "3-chain", "diamond", "fork(1,1)",
                "4-chain", "fork(2,2)"]


def prune(source: H.Principle, target: H.Principle, depth: int) -> set[tuple[str, str]]:
    """Terms surviving on the prune frames.  Fast, but not yet trustworthy."""
    candidates: set[tuple[str, str]] | None = None
    for name in PRUNE_FRAMES:
        alg = H.Algebra(H.NAMED_FRAMES[name])
        for a, b in alg.pairs():
            lib = H.term_library(alg, a, b, depth=depth)
            if candidates is None:
                candidates = {(x, y) for x in lib for y in lib}
            goal = target(alg, a, b)
            candidates = {(x, y) for x, y in candidates
                          if source(alg, lib[x], lib[y]) | goal == goal}
            if not candidates:
                return set()
        print(f"  after {name:<12}{len(candidates):>7} candidates", flush=True)
    return candidates or set()


def confirm(candidates: set[tuple[str, str]], source: H.Principle,
            target: H.Principle, depth: int, max_points: int,
            random_count: int = 0, seed: int = 20260922) -> set[tuple[str, str]]:
    """Recheck candidates against every poset up to ``max_points`` points, then
    against random larger ones.

    The random stage is not decoration.  A candidate can survive every poset on
    five points and still fail on six, so a search confirmed only up to five is
    not evidence for anything.
    """
    survivors = set(candidates)
    frames = list(H.posets_upto(max_points))
    if random_count:
        rng = random.Random(seed)
        for size in (6, 7):
            frames += list(H.random_posets(size, random_count, rng))
    for poset in frames:
        alg = H.Algebra(poset)
        for a, b in alg.pairs():
            lib = H.term_library(alg, a, b, depth=depth)
            goal = target(alg, a, b)
            survivors = {(x, y) for x, y in survivors
                         if source(alg, lib[x], lib[y]) | goal == goal}
            if not survivors:
                return set()
    return survivors


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?", help="principle to instantiate")
    parser.add_argument("target", nargs="?", help="principle to derive")
    parser.add_argument("--depth", type=int, default=2, help="term library depth")
    parser.add_argument("--sweep", type=int, default=4,
                        help="confirm over all posets up to this many points")
    parser.add_argument("--random", type=int, default=60,
                        help="also confirm over this many random 6 and 7 point posets")
    parser.add_argument("--list", action="store_true", help="list principle names")
    args = parser.parse_args()

    if args.list or not (args.source and args.target):
        print("principles:", ", ".join(H.PRINCIPLES))
        sys.exit(0 if args.list else 2)

    source, target = H.PRINCIPLES[args.source], H.PRINCIPLES[args.target]
    print(f"searching for (A, B) with {args.source}(A, B) -> {args.target}(a, b)\n")
    candidates = prune(source, target, args.depth)
    if not candidates:
        print("\nno candidates survive the prune frames")
        return

    print(f"\nconfirming {len(candidates)} candidates on every poset "
          f"up to {args.sweep} points", flush=True)
    survivors = confirm(candidates, source, target, args.depth, args.sweep)
    if not survivors:
        print("  none survive: the prune frames were giving false positives")
        return
    print(f"  {len(survivors)} survive, for example:")
    for x, y in sorted(survivors)[:10]:
        print(f"    {args.source}({x}, {y})")


if __name__ == "__main__":
    main()
