"""Witnesses for embedding a frame's algebra, in the form Logics/PointEmbed.lean
asks for them.

``PointEmbed.sh_of_refutes`` puts the algebra of a finite rooted frame below
every algebra refuting a formula ``P → C``, given a formula ``T_w`` in ``a`` and
``b`` for each point ``w`` other than the root, and derivations under ``P`` of

    mono   T_w → T_v                 for each point v below w
    meet   T_w ∧ T_v → M(w, v)       for incomparable w and v, where M(w, v) is
                                     the join of T_u over the points u above both
    arrow  (T_w → N_w) → N_w         where N_w is the join of T_u over the points
                                     u not below w
    con    (join of every T_w) → C

This looks for such formulas among the small ones.  A candidate for ``T_w``
must name the points above ``w`` at a refutation of ``P → C`` in the frame
itself, and each condition must hold under ``P`` in every frame up to
``--search`` points; a solution is then checked on every frame up to
``--verify`` points.  Only then is it worth deriving the conditions, which
``point_embed_lean.py`` does.

Several formulas can be given, for instance characteristic formulas from
``characteristic_search.py``; they are tried in turn, and the first that has
witnesses is written to ``--out`` as a JSON spec.  Its ``points`` list the
frame's points root first, in the order the frame was given in; it is the order
``point_embed_lean.py`` lists them in, and must be that of ``J`` in the Lean
file's ``Points``.

Usage:  python witness_search.py uneven-kite \\
            "((((a → b ∨ ¬b) → a) → a) → a ∨ b) → b ∨ (b → a ∨ ¬a)" --out kite.json
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from typing import Iterator

import numpy as np

from evaluate import Bank
from formulas import TOP, Formula, parse, show, variables
from frames import NAMED_FRAMES, NamedFrame, frame_arg, rooted_frames
from levels import formula_levels

Witnesses = dict[str, Formula]


def log(message: str) -> None:
    print(message, file=sys.stderr, flush=True)


def split(p: Formula) -> tuple[Formula, Formula]:
    """A formula as premise and conclusion; ``⊤`` is the premise of a formula
    that is not an implication."""
    return (p[1], p[2]) if p[0] == "imp" else (TOP, p)


class Conditions:
    """The conditions of the module docstring for one frame and one formula,
    checked on a bank of frames."""

    def __init__(self, frame: NamedFrame, premise: Formula, conclusion: Formula,
                 bank: Bank) -> None:
        self.frame, self.bank = frame, bank
        self.premise = bank.evaluate(premise)
        self.conclusion = bank.evaluate(conclusion)
        self.points = [n for n in frame.names if n != frame.root]
        self.up = {n: frame.up(n) for n in frame.names}

    def holds(self, x: np.ndarray, y: np.ndarray) -> bool:
        """Whether ``x`` lies below ``y`` wherever the premise holds."""
        return not np.any(self.premise & x & ~y)

    def join(self, names, values: dict[str, np.ndarray]) -> np.ndarray:
        result = np.zeros_like(self.premise)
        for n in names:
            result = result | values[n]
        return result

    def local(self, w: str, values: dict[str, np.ndarray]) -> bool:
        """The conditions among ``w`` and the points already given values."""
        for v in values:
            if v == w:
                continue
            if self.up[w] <= self.up[v] and not self.holds(values[w], values[v]):
                return False
            if self.up[v] <= self.up[w] and not self.holds(values[v], values[w]):
                return False
            if not (self.up[w] <= self.up[v] or self.up[v] <= self.up[w]):
                above = [u for u in self.points if self.up[u] <= self.up[w] & self.up[v]]
                if all(u in values for u in above) and \
                        not self.holds(values[w] & values[v], self.join(above, values)):
                    return False
        return True

    def complete(self, values: dict[str, np.ndarray]) -> bool:
        """The arrow conditions and ``con``, once every point has a value."""
        for w in self.points:
            outside = self.join((u for u in self.points if w not in self.up[u]), values)
            if not self.holds(self.bank.imp(values[w], outside), outside):
                return False
        return self.holds(self.join(self.points, values), self.conclusion)


def search(frame: NamedFrame, formula: Formula, term_size: int, search_points: int,
           verify_points: int) -> Iterator[Witnesses]:
    """Witnesses for the formula, checked on frames up to ``verify_points``."""
    premise, conclusion = split(formula)
    small = Bank.complete(k for keys in rooted_frames(search_points).values() for k in keys)
    own = Bank.complete([frame.ups])
    refuting = np.nonzero(own.evaluate(formula) != own.full)[0]
    if not len(refuting):
        raise ValueError(f"the frame does not refute {show(formula)}")
    at = refuting[0]
    terms = [(f, v) for forms, vs in formula_levels(small, term_size) for f, v in zip(forms, vs)]
    at_own = [own.evaluate(f)[at] for f, _ in terms]
    cond = Conditions(frame, premise, conclusion, small)
    pools = {w: [term for term, value in zip(terms, at_own)
                 if value == frame.ups[frame.names.index(w)]] for w in cond.points}
    log("  candidates per point: " + ", ".join(f"{w} {len(pools[w])}" for w in cond.points))
    verify: Conditions | None = None
    order = sorted(cond.points, key=lambda w: len(cond.up[w]))  # maximal points first
    chosen: dict[str, Formula] = {}
    values: dict[str, np.ndarray] = {}

    def extend(i: int) -> Iterator[Witnesses]:
        nonlocal verify
        if i == len(order):
            if not cond.complete(values):
                return
            if verify is None:
                frames = [k for keys in rooted_frames(verify_points).values() for k in keys]
                verify = Conditions(frame, premise, conclusion, Bank.complete(frames))
            big = {w: verify.bank.evaluate(chosen[w]) for w in order}
            if all(verify.local(w, big) for w in order) and verify.complete(big):
                yield dict(chosen)
            return
        w = order[i]
        for t, v in pools[w]:
            chosen[w], values[w] = t, v
            if cond.local(w, values):
                yield from extend(i + 1)
        chosen.pop(w, None)
        values.pop(w, None)

    yield from extend(0)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("frame", help=f"one of {', '.join(NAMED_FRAMES)}, or pairs like 'r<x r<y'")
    parser.add_argument("formulas", nargs="+", help="formulas in a and b, tried in turn")
    parser.add_argument("--term-size", type=int, default=5, help="largest witness size")
    parser.add_argument("--search", type=int, default=5,
                        help="check conditions on every frame up to this many points")
    parser.add_argument("--verify", type=int, default=7,
                        help="recheck a solution on every frame up to this many points")
    parser.add_argument("--out", help="write the spec here as JSON")
    args = parser.parse_args()

    frame = frame_arg(args.frame)
    for text in args.formulas:
        formula = parse(text)
        if not variables(formula) <= {0, 1}:
            parser.error(f"{text!r} uses variables other than a and b")
        log(f"{show(formula)}")
        start = time.time()
        solution = next(search(frame, formula, args.term_size, args.search, args.verify), None)
        log(f"  {'found' if solution else 'none'}, {time.time() - start:.0f}s")
        if solution is None:
            continue
        premise, conclusion = split(formula)
        points = [frame.root] + [n for n in frame.names if n != frame.root]
        spec = {"frame": frame.spec(), "points": points,
                "premise": show(premise), "conclusion": show(conclusion),
                "witnesses": {w: show(solution[w]) for w in points if w in solution}}
        print(json.dumps(spec, ensure_ascii=False, indent=2))
        if args.out:
            with open(args.out, "w", encoding="utf-8") as f:
                json.dump(spec, f, ensure_ascii=False, indent=2)
        return
    log("no formula has witnesses among the terms searched")


if __name__ == "__main__":
    main()
