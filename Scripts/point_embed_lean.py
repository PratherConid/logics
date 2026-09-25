"""The derivations ``PointEmbed.sh_of_refutes`` asks for, as Lean source.

Reads a spec written by ``witness_search.py`` -- a frame, the premise ``P`` and
conclusion ``C`` of a formula, and a witness ``T_w`` for each point other than
the root -- and prints, for a refuter file in Logics/IntermediateAxioms/Refuter:

* a ``def`` for ``P``, for ``C`` and for each witness, named ``T`` and the point;
* a theorem for each condition of Logics/PointEmbed.lean's ``Images`` under
  ``P``: ``mono_w_v`` derives ``T_v`` from ``T_w`` for ``v`` below ``w``;
  ``meet_w_v`` derives, from the witnesses of two incomparable points, the join
  of those of the points above both; ``arrow_w`` is the arrow condition at
  ``w``; ``con`` derives ``C`` from the join of all the witnesses.

Each derivation is found by ``g4ip.py``.  The joins list the points in the
order of the spec's ``points``, which must be the order of ``J`` in the file's
``Points``, since ``PointEmbed.below`` keeps that order.

Usage:  python point_embed_lean.py kite.json > derivations.lean
"""

from __future__ import annotations

import argparse
import json
import sys

from formulas import BOT, Formula, disj, parse, to_lean
from frames import NamedFrame
from g4ip import derivation


def statement(p: Formula, names: dict[Formula, str]) -> str:
    """A formula in a theorem statement, by name where it has one and with joins
    of named formulas written as ``Form.disj``."""
    if p in names:
        return names[p]
    members, rest = [], p
    while rest[0] == "or" and rest[1] in names:
        members.append(names[rest[1]])
        rest = rest[2]
    if rest == BOT:
        return f"Form.disj [{', '.join(members)}]"
    if p[0] in ("and", "or", "imp"):
        args = [statement(q, names) for q in p[1:]]
        return f".{p[0]} " + " ".join(a if " " not in a else f"({a})" for a in args)
    return to_lean(p)


def conditions(frame: NamedFrame, points: list[str], witness: dict[str, Formula],
               conclusion: Formula) -> list[tuple[str, Formula, Formula]]:
    """Each condition as its name, the hypothesis beside ``P`` and the goal."""
    up = {n: frame.up(n) for n in points}
    rest = points[1:]
    joined = lambda names: disj(witness[n] for n in rest if n in names)
    result = []
    for w in rest:
        for v in rest:
            if w != v and up[w] <= up[v]:
                result.append((f"mono_{w}_{v}", witness[w], witness[v]))
    for w in rest:
        for v in rest:
            if not (up[w] <= up[v] or up[v] <= up[w]):
                above = {u for u in rest if up[u] <= up[w] & up[v]}
                result.append((f"meet_{w}_{v}", ("and", witness[w], witness[v]), joined(above)))
    for w in rest:
        outside = joined({u for u in rest if w not in up[u]})
        result.append((f"arrow_{w}", ("imp", witness[w], outside), outside))
    result.append(("con", joined(set(rest)), conclusion))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("spec", help="a JSON spec from witness_search.py")
    parser.add_argument("--width", type=int, default=100, help="line width of the terms")
    args = parser.parse_args()

    with open(args.spec, encoding="utf-8") as f:
        spec = json.load(f)
    frame = NamedFrame.parse(spec["frame"])
    points = spec["points"]
    if sorted(points) != sorted(frame.names) or points[0] != frame.root:
        sys.exit("the spec's points must be the frame's, the root first")
    premise, conclusion = parse(spec["premise"]), parse(spec["conclusion"])
    witness = {w: parse(t) for w, t in spec["witnesses"].items()}
    names = {premise: "P", conclusion: "C"} | {t: f"T{w}" for w, t in witness.items()}

    print(f"def P : Form := {to_lean(premise)}")
    print(f"def C : Form := {to_lean(conclusion)}")
    for w in points[1:]:
        print(f"def T{w} : Form := {to_lean(witness[w])}")
    for name, hyp, goal in conditions(frame, points, witness, conclusion):
        term = derivation([hyp, premise], goal, indent=2, width=args.width)
        if term is None:
            sys.exit(f"{name} has no derivation: the witnesses do not satisfy it")
        print(f"\ntheorem {name} : [{statement(hyp, names)}, P] ⊢ {statement(goal, names)} :=")
        print(f"  {term}")


if __name__ == "__main__":
    main()
