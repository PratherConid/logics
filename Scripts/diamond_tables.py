"""Print the diamond algebra, as encoded by ``Diamond`` in Logics/Heyting.lean.

The Lean definition codes each element by the bit mask of the frame points it
contains and derives the operations from those masks, so this prints the masks
and the resulting tables.  Run it to check the Lean encoding by eye, or to
regenerate it if the frame ever changes.
"""

from __future__ import annotations

import heyting as H

LEAN_NAMES = ["bot", "e", "x", "y", "m", "top"]


def main() -> None:
    alg = H.Algebra(H.DIAMOND)
    poset = H.DIAMOND
    mask = lambda s: sum(1 << p for p in s)
    names = dict(zip(alg.elements, LEAN_NAMES))

    print("frame: root 0 below incomparable 1 and 2, both below top 3")
    print("principal upward closed sets, `upset` in Lean:")
    for p in poset.points:
        print(f"  upset {p} = {mask(poset.up[p]):>2}")

    print("\nelements, `mask` in Lean:")
    for e in alg.elements:
        print(f"  {names[e]:<4} = mask {mask(e):>2}   points {sorted(e)}")

    print("\nimplication table (row a, column b, entry a => b):")
    print("        " + "".join(f"{n:>5}" for n in LEAN_NAMES))
    for a in alg.elements:
        row = "".join(f"{names[alg.imp(a, b)]:>5}" for b in alg.elements)
        print(f"  {names[a]:<6}" + row)

    print("\nnegation:", ", ".join(
        f"~{names[a]} = {names[alg.neg(a)]}" for a in alg.elements))

    print("\nwhat holds here:")
    for name, principle in H.PRINCIPLES.items():
        bad = alg.failures(principle)
        if not bad:
            print(f"  {name:<20} valid")
        else:
            a, b = bad[0]
            print(f"  {name:<20} fails, e.g. at a = {names[a]}, b = {names[b]}")


if __name__ == "__main__":
    main()
