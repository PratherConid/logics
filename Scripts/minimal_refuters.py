"""The minimal finite rooted frames refuting a formula.

A refuting frame is minimal when no frame it reduces to refutes the formula as
well, and it is enough to look one step below it (see ``frames.py``).  Every
refuting frame up to the size searched reduces to one of the minimal ones
listed, so a list that stops growing is evidence -- not proof -- that it is
complete.

Usage:  python minimal_refuters.py "(a → b) ∨ (b → a)" --points 7
"""

from __future__ import annotations

import argparse

from evaluate import Bank
from formulas import Formula, parse, show, variables
from frames import Key, describe, one_step, rooted_frames


def minimal_refuters(p: Formula, max_points: int) -> dict[int, tuple[int, list[Key]]]:
    """For each size, how many frames refute ``p`` and which are minimal."""
    frames = rooted_frames(max_points)
    bank = Bank.complete((k for keys in frames.values() for k in keys),
                         max(variables(p), default=0) + 1)
    refuted = dict(zip(bank.frames, bank.refuted(bank.evaluate(p)).tolist()))
    return {n: (sum(refuted[k] for k in keys),
                [k for k in keys if refuted[k] and not any(refuted[s] for s in one_step(k))])
            for n, keys in frames.items()}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("formula", help="a formula in a, b, c, ...")
    parser.add_argument("--points", type=int, default=7, help="largest frame size (at most 8)")
    args = parser.parse_args()

    p = parse(args.formula)
    print(f"minimal refuters of {show(p)}")
    for n, (count, minimal) in minimal_refuters(p, args.points).items():
        print(f"  {n} points: {count} refuting, {len(minimal)} minimal")
        for key in minimal:
            print(f"      {describe(key)}")


if __name__ == "__main__":
    main()
