"""Finite rooted frames up to isomorphism, and how they reduce to one another.

A frame is a finite poset, stored as a tuple of bitmasks: bit ``j`` of
``ups[i]`` is set when ``i ≤ j``.  Up to isomorphism a frame has one canonical
form (``canonical``), which serves as its key.  Every rooted frame arises from a
smaller one by adding a new maximal point, which is how ``rooted_frames``
enumerates them; up to eight points that is 2451 frames.

A frame ``F`` *reduces to* ``G`` when ``G`` is a p-morphic image of a generated
subframe of ``F`` -- dually, when ``G``'s algebra lies below ``F``'s in the
order ``SH`` of Logics/Homomorphism.lean (``sh_iff_merge`` in
Logics/FiniteFrame.lean) -- and then everything refuted on ``G`` is refuted on
``F``.  Every p-morphism between finite frames is a composition of
alpha-reductions (a point merged into its only immediate successor) and
beta-reductions (two points with the same strict successors merged) --
``Merger.isChain`` in Logics/Reduction.lean -- so the frames one step below
``F`` are its proper generated subframes and its alpha and beta reductions
(``one_step``), and ``reductions`` closes that set.

Frames whose points carry names, for input and output, are ``NamedFrame``s,
read from covering pairs such as ``"r<x r<y x<t y<t"``.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from itertools import groupby, permutations, product

Key = tuple[int, ...]


def _matrix(ups: Key) -> list[list[bool]]:
    n = len(ups)
    return [[bool(ups[i] >> j & 1) for j in range(n)] for i in range(n)]


def _masks(le: list[list[bool]]) -> Key:
    return tuple(sum(1 << j for j, x in enumerate(row) if x) for row in le)


def _close(le: list[list[bool]]) -> list[list[bool]]:
    n = len(le)
    for k in range(n):
        for i in range(n):
            if le[i][k]:
                for j in range(n):
                    if le[k][j]:
                        le[i][j] = True
    return le


def canonical(ups: Key) -> Key:
    """The canonical form of a frame: its least relabelling among those that
    respect a few isomorphism invariants of the points."""
    le = _matrix(ups)
    n = len(le)
    inv: list = [(sum(le[j][i] for j in range(n)), sum(le[i])) for i in range(n)]
    for _ in range(2):
        inv = [(inv[i],
                tuple(sorted(inv[j] for j in range(n) if le[i][j] and i != j)),
                tuple(sorted(inv[j] for j in range(n) if le[j][i] and i != j)))
               for i in range(n)]
    order = sorted(range(n), key=lambda i: inv[i])
    classes = [list(g) for _, g in groupby(order, key=lambda i: inv[i])]
    best = None
    for perms in product(*(permutations(c) for c in classes)):
        p = [x for c in perms for x in c]
        relabelled = _masks([[le[p[i]][p[j]] for j in range(n)] for i in range(n)])
        if best is None or relabelled < best:
            best = relabelled
    return best


def rooted_frames(max_points: int) -> dict[int, list[Key]]:
    """Every rooted frame with at most ``max_points`` points, by size."""
    result = {1: [canonical((1,))]}
    for n in range(2, max_points + 1):
        found = set()
        for key in result[n - 1]:
            le = _matrix(key)
            m = len(le)
            for below in range(1, 1 << m):
                # the new point's strict predecessors must form a downset
                if all(not (below >> i & 1) or all(not le[j][i] or below >> j & 1 for j in range(m))
                       for i in range(m)):
                    grown = [row + [bool(below >> i & 1)] for i, row in enumerate(le)]
                    found.add(canonical(_masks(grown + [[False] * m + [True]])))
        result[n] = sorted(found)
    return result


def upsets(ups: Key) -> list[int]:
    """The upward closed sets of the frame, as bitmasks."""
    return [s for s in range(1 << len(ups))
            if all(not (s >> i & 1) or s & u == u for i, u in enumerate(ups))]


def root(ups: Key) -> int:
    full = (1 << len(ups)) - 1
    return next(i for i, u in enumerate(ups) if u == full)


def covers(ups: Key) -> list[tuple[int, int]]:
    """The covering pairs ``(i, j)``: ``i < j`` with nothing strictly between."""
    le = _matrix(ups)
    n = len(le)
    lt = [[le[i][j] and i != j for j in range(n)] for i in range(n)]
    return [(i, j) for i in range(n) for j in range(n)
            if lt[i][j] and not any(lt[i][k] and lt[k][j] for k in range(n))]


def one_step(ups: Key) -> set[Key]:
    """The frames one step below: proper generated subframes, alpha and beta
    reductions."""
    le = _matrix(ups)
    n = len(le)
    result = set()
    r = root(ups)
    for x in range(n):
        if x != r:
            pts = [j for j in range(n) if le[x][j]]
            result.add(canonical(_masks([[le[i][j] for j in pts] for i in pts])))

    def merge(x: int, y: int) -> Key:
        pts = [i for i in range(n) if i != x]
        merged = [[le[i][j] or (i == y and le[x][j]) or (j == y and le[i][x]) for j in pts]
                  for i in pts]
        return canonical(_masks(_close(merged)))

    cov = covers(ups)
    for x, y in cov:
        if sum(1 for x2, _ in cov if x2 == x) == 1:
            result.add(merge(x, y))
    strict = [ups[i] & ~(1 << i) for i in range(n)]
    for x in range(n):
        for y in range(x + 1, n):
            if strict[x] == strict[y]:
                result.add(merge(x, y))
    return result


@lru_cache(maxsize=None)
def reductions(ups: Key) -> frozenset[Key]:
    """Every frame this one reduces to, itself included."""
    result = {ups}
    for smaller in one_step(ups):
        result |= reductions(smaller)
    return frozenset(result)


def describe(ups: Key) -> str:
    """The frame by its covering pairs, points numbered as in its key."""
    return " ".join(f"{i}<{j}" for i, j in covers(ups)) or "a single point"


# --- frames with named points ---------------------------------------------------

@dataclass(frozen=True)
class NamedFrame:
    """A rooted frame whose points carry names."""

    names: tuple[str, ...]
    ups: Key

    @classmethod
    def parse(cls, spec: str) -> "NamedFrame":
        """Read covering pairs such as ``"r<x r<y x<t y<t"``."""
        names: list[str] = []
        pairs = []
        for item in spec.replace(",", " ").split():
            lo, sep, hi = item.partition("<")
            if not sep or not lo or not hi:
                raise ValueError(f"not a pair p<q: {item!r}")
            for name in (lo, hi):
                if name not in names:
                    names.append(name)
            pairs.append((names.index(lo), names.index(hi)))
        n = len(names)
        le = [[i == j for j in range(n)] for i in range(n)]
        for i, j in pairs:
            le[i][j] = True
        _close(le)
        if any(le[i][j] and le[j][i] and i != j for i in range(n) for j in range(n)):
            raise ValueError(f"the pairs contain a cycle: {spec!r}")
        if not any(all(row) for row in le):
            raise ValueError(f"the frame has no root: {spec!r}")
        return cls(tuple(names), _masks(le))

    @property
    def key(self) -> Key:
        return canonical(self.ups)

    @property
    def root(self) -> str:
        return self.names[root(self.ups)]

    def up(self, name: str) -> frozenset[str]:
        """The points at or above the named one."""
        mask = self.ups[self.names.index(name)]
        return frozenset(n for j, n in enumerate(self.names) if mask >> j & 1)

    def spec(self) -> str:
        return " ".join(f"{self.names[i]}<{self.names[j]}" for i, j in covers(self.ups))


NAMED_FRAMES: dict[str, str] = {
    "fork": "r<x r<y",
    "diamond": "r<x r<y x<t y<t",
    "tall-fork": "r<x1 r<y1 x1<x2 y1<y2",
    "uneven-fork": "r<x r<y1 y1<y2",
    "uneven-kite": "r<x r<y1 y1<y2 x<t y2<t",
    "diamond-hair": "r<u r<v v<z u<m v<m",
}


def frame_arg(text: str) -> NamedFrame:
    """A frame from the command line: one of ``NAMED_FRAMES``, or covering pairs."""
    return NamedFrame.parse(NAMED_FRAMES.get(text, text))
