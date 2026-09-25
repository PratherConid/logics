"""De Jongh's characteristic formula of a finite rooted frame, in two variables.

Colour the points by which of ``a`` and ``b`` hold there, so that no two points
are alike -- no two are bisimilar -- and the coloured frame sits inside the
universal model on two variables.  Then, from the top down, each point ``w``
with immediate successors ``w₁ … wₖ`` gets

    φ_w = (atoms true at w) ∧ ((new atoms ∨ ψ_w₁ ∨ … ∨ ψ_wₖ) → φ_w₁ ∨ … ∨ φ_wₖ)
    ψ_w = φ_w → φ_w₁ ∨ … ∨ φ_wₖ

where the *new* atoms are those false at ``w`` and true at every ``wᵢ``; a
maximal point gets ``φ_w`` = its atoms and the negations of the rest, and
``ψ_w = ¬φ_w``.  In the frame, ``φ_w`` holds exactly above ``w`` and ``ψ_w``
exactly off the points below ``w``; ``ψ`` at the root is refuted on a frame
exactly when that frame reduces to the given one, which makes it the frame's
characteristic formula.

This tries every colouring, checks those two facts and the characteristic
property on every frame up to ``--verify`` points, and prints the smallest
formula that passes.

Usage:  python dejongh_formula.py uneven-kite --verify 7
"""

from __future__ import annotations

import argparse
from itertools import product

import numpy as np

from evaluate import Bank
from formulas import A, B, Formula, conjunction, disjunction, neg, show, size
from frames import Key, NAMED_FRAMES, covers, frame_arg, reductions, root, rooted_frames, upsets


def colour(va: int, vb: int, point: int) -> tuple[bool, bool]:
    return bool(va >> point & 1), bool(vb >> point & 1)


def distinguishes(key: Key, va: int, vb: int) -> bool:
    """Whether the colouring leaves no two points bisimilar."""
    n = len(key)
    alike = {(x, y) for x in range(n) for y in range(n)
             if colour(va, vb, x) == colour(va, vb, y)}
    changed = True
    while changed:
        changed = False
        for x, y in list(alike):
            forth = all(any(key[y] >> y2 & 1 and (x2, y2) in alike for y2 in range(n))
                        for x2 in range(n) if key[x] >> x2 & 1)
            back = all(any(key[x] >> x2 & 1 and (x2, y2) in alike for x2 in range(n))
                       for y2 in range(n) if key[y] >> y2 & 1)
            if not (forth and back):
                alike.discard((x, y))
                changed = True
    return all(x == y for x, y in alike)


def dejongh(key: Key, va: int, vb: int) -> tuple[dict[int, Formula], dict[int, Formula]]:
    """The formulas ``φ_w`` and ``ψ_w`` of every point, under the colouring."""
    successors: dict[int, list[int]] = {w: [] for w in range(len(key))}
    for x, y in covers(key):
        successors[x].append(y)
    atoms = (A, B)
    phi: dict[int, Formula] = {}
    psi: dict[int, Formula] = {}

    def depth(w: int) -> int:
        return 1 + max((depth(s) for s in successors[w]), default=0)

    for w in sorted(range(len(key)), key=depth):
        col = colour(va, vb, w)
        true = [atoms[i] for i in range(2) if col[i]]
        if not successors[w]:
            phi[w] = conjunction(true + [neg(atoms[i]) for i in range(2) if not col[i]])
            psi[w] = neg(phi[w])
            continue
        new = [atoms[i] for i in range(2)
               if not col[i] and all(colour(va, vb, s)[i] for s in successors[w])]
        above = disjunction(phi[s] for s in successors[w])
        guard = ("imp", disjunction(new + [psi[s] for s in successors[w]]), above)
        phi[w] = conjunction(true + [guard])
        psi[w] = ("imp", phi[w], above)
    return phi, psi


def sound_in_frame(key: Key, va: int, vb: int, phi: dict[int, Formula],
                   psi: dict[int, Formula]) -> bool:
    """``φ_w`` holds exactly above ``w`` and ``ψ_w`` exactly off the points below it."""
    bank = Bank([(key, va, vb)])
    full = (1 << len(key)) - 1
    below = [sum(1 << x for x in range(len(key)) if key[x] >> w & 1) for w in range(len(key))]
    return all(int(bank.evaluate(phi[w])[0]) == key[w]
               and int(bank.evaluate(psi[w])[0]) == full & ~below[w] for w in range(len(key)))


def characteristic(key: Key, verify_points: int) -> Formula | None:
    frames = rooted_frames(verify_points)
    bank = Bank.complete(k for keys in frames.values() for k in keys)
    wanted = np.array([key in reductions(k) for k in bank.frames])
    best = None
    for va, vb in product(upsets(key), repeat=2):
        if not distinguishes(key, va, vb):
            continue
        phi, psi = dejongh(key, va, vb)
        formula = psi[root(key)]
        if best is not None and size(formula) >= size(best):
            continue
        if sound_in_frame(key, va, vb, phi, psi) and \
                (bank.refuted(bank.evaluate(formula)) == wanted).all():
            best = formula
    return best


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("frame", help=f"one of {', '.join(NAMED_FRAMES)}, or pairs like 'r<x r<y'")
    parser.add_argument("--verify", type=int, default=7,
                        help="check on every frame up to this many points (at most 8)")
    args = parser.parse_args()

    frame = frame_arg(args.frame)
    formula = characteristic(frame.key, args.verify)
    if formula is None:
        print("no colouring passes the checks")
        return
    print(f"size {size(formula)}, verified on every frame up to {args.verify} points:")
    print(f"  {show(formula)}")


if __name__ == "__main__":
    main()
