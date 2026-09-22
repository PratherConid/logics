"""Finite Heyting algebras, built as the upward closed sets of a finite poset.

By Birkhoff's representation theorem every finite distributive lattice, and so
every finite Heyting algebra, arises this way, which makes posets a complete
source of countermodels: a propositional formula is intuitionistically
derivable exactly when it takes the top value in all of these algebras.

The vocabulary matches ``Logics/``: an element is an upward closed set of frame
points, ``imp`` is the Heyting arrow, and a *principle* is a function sending
two elements to an element, valid in an algebra when it reaches the top value
at every pair.
"""

from __future__ import annotations

import random
from itertools import product
from typing import Callable, Iterable, Iterator

Element = frozenset  # frozenset[int]: an upward closed set of frame points
Principle = Callable[["Algebra", Element, Element], Element]


class Poset:
    """A finite poset, given by the upward closed set of each of its points."""

    __slots__ = ("points", "up")

    def __init__(self, up: dict[int, Iterable[int]]) -> None:
        self.points = tuple(sorted(up))
        self.up = {p: frozenset(up[p]) for p in self.points}
        for x in self.points:
            if x not in self.up[x]:
                raise ValueError(f"order is not reflexive at {x}")
            for y in self.up[x]:
                if not self.up[y] <= self.up[x]:
                    raise ValueError(f"order is not transitive at {x} <= {y}")

    def leq(self, x: int, y: int) -> bool:
        return y in self.up[x]

    def __len__(self) -> int:
        return len(self.points)


class Algebra:
    """The Heyting algebra of upward closed subsets of a poset.

    Meet and join are intersection and union, so elements are combined with
    ``&`` and ``|`` directly; only the arrow needs to consult the frame.
    """

    __slots__ = ("poset", "top", "bot", "elements")

    def __init__(self, poset: Poset) -> None:
        self.poset = poset
        self.top = frozenset(poset.points)
        self.bot = frozenset()
        upsets = []
        for bits in product((False, True), repeat=len(poset)):
            s = frozenset(p for p, b in zip(poset.points, bits) if b)
            if all(poset.up[p] <= s for p in s):
                upsets.append(s)
        upsets.sort(key=lambda s: (len(s), sorted(s)))
        self.elements = tuple(upsets)

    def imp(self, a: Element, b: Element) -> Element:
        """The largest element whose meet with ``a`` lies below ``b``."""
        return frozenset(p for p in self.poset.points
                         if not (self.poset.up[p] & a) - b)

    def neg(self, a: Element) -> Element:
        return self.imp(a, self.bot)

    def pairs(self) -> Iterator[tuple[Element, Element]]:
        return product(self.elements, self.elements)

    def is_valid(self, principle: Principle) -> bool:
        return all(principle(self, a, b) == self.top for a, b in self.pairs())

    def failures(self, principle: Principle) -> list[tuple[Element, Element]]:
        return [(a, b) for a, b in self.pairs() if principle(self, a, b) != self.top]

    def index(self, a: Element) -> int:
        return self.elements.index(a)

    def __len__(self) -> int:
        return len(self.elements)


# --- the principles of Logics/ClassicalAxioms/AxiomDef.lean -------------------

def peirce(H: Algebra, a: Element, b: Element) -> Element:
    return H.imp(H.imp(H.imp(a, b), a), a)


def lukasiewicz(H: Algebra, a: Element, b: Element) -> Element:
    return H.imp(H.imp(H.neg(a), H.neg(b)), H.imp(b, a))


def de_morgan(H: Algebra, a: Element, b: Element) -> Element:
    return H.imp(H.neg(H.neg(a) & H.neg(b)), a | b)


def imp_or(H: Algebra, a: Element, b: Element) -> Element:
    return H.imp(H.imp(a, b), H.neg(a) | b)


def excluded_middle(H: Algebra, a: Element, b: Element) -> Element:
    return a | H.neg(a)


def weak_excluded_middle(H: Algebra, a: Element, b: Element) -> Element:
    return H.neg(a) | H.neg(H.neg(a))


def combined(left: Principle, *, swap: bool) -> Principle:
    """``left(a, b)`` joined with Lukasiewicz, swapping the latter's arguments
    when ``swap``.  This is the shape shared by all six combined principles."""

    def principle(H: Algebra, a: Element, b: Element) -> Element:
        right = lukasiewicz(H, b, a) if swap else lukasiewicz(H, a, b)
        return left(H, a, b) | right

    return principle


PRINCIPLES: dict[str, Principle] = {
    "PierceOrLuk": combined(peirce, swap=False),
    "PierceOrLuk'": combined(peirce, swap=True),
    "DeMorganOrLuk": combined(de_morgan, swap=False),
    "DeMorganOrLuk'": combined(de_morgan, swap=True),
    "ImpOrOrLuk": combined(imp_or, swap=False),
    "ImpOrOrLuk'": combined(imp_or, swap=True),
    "ExcludedMiddle": excluded_middle,
    "WeakExcludedMiddle": weak_excluded_middle,
}


# --- frames -------------------------------------------------------------------

def chain(n: int) -> Poset:
    """``n`` points in a line; its algebra is the ``n + 1`` element chain."""
    return Poset({i: range(i, n) for i in range(n)})


def fork(*branches: int) -> Poset:
    """A root with one chain of each given length hanging above it."""
    up: dict[int, Iterable[int]] = {}
    nxt, above = 1, []
    for length in branches:
        nodes = list(range(nxt, nxt + length))
        nxt += length
        for i, p in enumerate(nodes):
            up[p] = nodes[i:]
        above += nodes
    up[0] = [0] + above
    return Poset(up)


#: Root, two incomparable middle points, a top: the ``Diamond`` of Heyting.lean.
DIAMOND = Poset({0: {0, 1, 2, 3}, 1: {1, 3}, 2: {2, 3}, 3: {3}})

NAMED_FRAMES: dict[str, Poset] = {
    "1-chain": chain(1),
    "2-chain": chain(2),
    "3-chain": chain(3),
    "4-chain": chain(4),
    "5-chain": chain(5),
    "fork(1,1)": fork(1, 1),
    "fork(1,1,1)": fork(1, 1, 1),
    "fork(2,2)": fork(2, 2),
    "diamond": DIAMOND,
}


# --- enumeration ---------------------------------------------------------------

def all_posets(n: int) -> Iterator[Poset]:
    """Every poset on ``n`` labelled points.

    Brute force over the ``2 ** (n * (n - 1))`` candidate relations, so this is
    seconds up to ``n = 5`` (about a million candidates) and hopeless at
    ``n = 6`` (about a billion).  Use :func:`random_posets` beyond that.
    """
    pts = range(n)
    pairs = [(i, j) for i in pts for j in pts if i != j]
    for bits in product((False, True), repeat=len(pairs)):
        rel = {(i, i) for i in pts} | {p for p, b in zip(pairs, bits) if b}
        if any((i, j) in rel and (j, i) in rel for i, j in pairs):
            continue  # antisymmetry
        if any((i, j) in rel and (j, k) in rel and (i, k) not in rel
               for i in pts for j in pts for k in pts):
            continue  # transitivity
        yield Poset({i: [j for j in pts if (i, j) in rel] for i in pts})


def posets_upto(n: int) -> Iterator[Poset]:
    """Every poset on 1 to ``n`` labelled points."""
    for k in range(1, n + 1):
        yield from all_posets(k)


def random_posets(n: int, count: int, rng: random.Random) -> Iterator[Poset]:
    """``count`` random posets on ``n`` points, from a random acyclic relation."""
    for _ in range(count):
        perm = list(range(n))
        rng.shuffle(perm)
        density = rng.choice((0.2, 0.3, 0.45, 0.6))
        rel = {(i, i) for i in range(n)}
        for i in range(n):
            for j in range(i + 1, n):
                if rng.random() < density:
                    rel.add((perm[i], perm[j]))
        changed = True
        while changed:  # transitive closure
            changed = False
            for x, y in list(rel):
                for y2, z in list(rel):
                    if y == y2 and (x, z) not in rel:
                        rel.add((x, z))
                        changed = True
        yield Poset({i: [j for j in range(n) if (i, j) in rel] for i in range(n)})


# --- terms, for searching over substitution instances --------------------------

def term_library(H: Algebra, a: Element, b: Element, *,
                 depth: int = 1) -> dict[str, Element]:
    """Candidate substitution terms over two variables, keyed by readable names.

    ``depth=1`` gives the atoms, their negations and the constants; ``depth=2``
    adds one layer of disjunction and implication over the atoms, which is what
    it takes to reach shifted instances such as ``b|b>a``.  Searching at depth 1
    alone can miss real derivations, so a candidate found on a few frames should
    always be rechecked against a full sweep.
    """
    atoms = {
        "a": a, "b": b,
        "~a": H.neg(a), "~b": H.neg(b),
        "a|b": a | b, "a&b": a & b,
        "a>b": H.imp(a, b), "b>a": H.imp(b, a),
    }
    lib = dict(atoms)
    lib.update({"~~a": H.neg(H.neg(a)), "~~b": H.neg(H.neg(b)),
                "bot": H.bot, "top": H.top})
    if depth >= 2:
        for n1, v1 in atoms.items():
            for n2, v2 in atoms.items():
                lib[f"{n1}|{n2}"] = v1 | v2
                lib[f"{n1}>{n2}"] = H.imp(v1, v2)
    return lib
