"""Formulas evaluated at many frames and valuations at once.

A ``Bank`` holds *entries*, each a frame with a valuation of the variables
``a``, ``b``, ``c``, ..., and evaluates a formula at all of them in one pass of
numpy operations.  An element is an upward closed set stored as a bitmask, so
meet and join are ``&`` and ``|``; only the arrow consults the frame.  Frames
have at most eight points, so an element fits in a byte.

Requires numpy.
"""

from __future__ import annotations

import random
from itertools import product
from typing import Iterable, Sequence

import numpy as np

from formulas import BOT, TOP, VAR_NAMES, Formula
from frames import Key, upsets

MAX_POINTS = 8

Entry = tuple  # a frame, then the value of each variable: (key, a, b, ...)


def every_valuation(frames: Iterable[Key], variables: int = 2) -> list[Entry]:
    return [(k, *vs) for k in frames for vs in product(upsets(k), repeat=variables)]


def random_valuations(frames: Sequence[Key], count: int, rng: random.Random,
                      variables: int = 2) -> list[Entry]:
    """``count`` random frames from the list, each with a random valuation."""
    entries = []
    for _ in range(count):
        k = rng.choice(frames)
        us = upsets(k)
        entries.append((k, *(rng.choice(us) for _ in range(variables))))
    return entries


def arrow(x: np.ndarray, y: np.ndarray, up: np.ndarray, present: np.ndarray) -> np.ndarray:
    """``x → y`` at each entry, given the points above each point there: the
    points ``i`` present with nothing of ``x`` outside ``y`` above them."""
    outside = ~y
    result = np.zeros(np.broadcast_shapes(x.shape, y.shape), dtype=np.uint8)
    for i in range(MAX_POINTS):
        holds = ((up[i] & x & outside) == 0) & present[i]
        result |= holds.astype(np.uint8) << i
    return result


class Bank:
    """Entries grouped by frame, with the arrays needed to evaluate at them.

    ``frames`` lists the frames, ``starts`` where each one's entries begin and
    ``frame_of`` the frame of each entry; ``atoms`` holds the value of each
    variable, ``full`` the top element and ``up[i]`` the points above point
    ``i`` at each entry, ``present[i]`` whether the entry's frame has point ``i``.
    """

    def __init__(self, entries: Sequence[Entry]) -> None:
        entries = sorted(entries, key=lambda e: e[0])
        frames: list[Key] = []
        counts: list[int] = []
        for key, *_ in entries:
            if frames and frames[-1] == key:
                counts[-1] += 1
            else:
                frames.append(key)
                counts.append(1)
        variables = len(entries[0]) - 1 if entries else 0
        atoms = np.array([e[1:] for e in entries], dtype=np.uint8).reshape(len(entries), variables)
        self._setup(frames, counts, atoms.T)

    @classmethod
    def complete(cls, frames: Iterable[Key], variables: int = 2) -> "Bank":
        """Every valuation on each frame."""
        frames = sorted(set(frames))
        blocks, counts = [], []
        for key in frames:
            us = np.array(upsets(key), dtype=np.uint8)
            grid = np.meshgrid(*[us] * variables, indexing="ij")
            blocks.append(np.stack([g.ravel() for g in grid]).reshape(variables, -1))
            counts.append(len(us) ** variables)
        bank = cls.__new__(cls)
        atoms = np.concatenate(blocks, axis=1) if blocks else np.zeros((variables, 0), np.uint8)
        bank._setup(frames, counts, atoms)
        return bank

    def _setup(self, frames: list[Key], counts: list[int], atoms: np.ndarray) -> None:
        if any(len(k) > MAX_POINTS for k in frames):
            raise ValueError(f"a frame has more than {MAX_POINTS} points")
        self.frames = frames
        self.variables = atoms.shape[0]
        self.starts = np.concatenate([[0], np.cumsum(counts)[:-1]]).astype(np.intp)
        self.frame_of = np.repeat(np.arange(len(frames), dtype=np.int32), counts)
        self.atoms = np.ascontiguousarray(atoms, dtype=np.uint8)
        sizes = np.array([len(k) for k in frames], dtype=np.int64)
        self.full = ((1 << sizes) - 1).astype(np.uint8)[self.frame_of]
        ups = np.array([list(k) + [0] * (MAX_POINTS - len(k)) for k in frames],
                       dtype=np.uint8).reshape(len(frames), MAX_POINTS)
        self.up = np.ascontiguousarray(ups[self.frame_of].T)
        self.present = self.up != 0

    def __len__(self) -> int:
        return len(self.full)

    def imp(self, x: np.ndarray, y: np.ndarray) -> np.ndarray:
        """The arrow, pointwise; ``x`` and ``y`` broadcast against each other."""
        return arrow(x, y, self.up, self.present)

    def evaluate(self, p: Formula) -> np.ndarray:
        if p == BOT:
            return np.zeros_like(self.full)
        if p == TOP:
            return self.full
        if p[0] == "var":
            if p[1] >= self.variables:
                raise ValueError("a bank evaluates formulas in "
                                 f"{', '.join(VAR_NAMES[:self.variables])} only")
            return self.atoms[p[1]]
        x, y = self.evaluate(p[1]), self.evaluate(p[2])
        return x & y if p[0] == "and" else x | y if p[0] == "or" else self.imp(x, y)

    def refuted(self, values: np.ndarray) -> np.ndarray:
        """For each frame, whether the values miss the top at one of its entries.
        ``values`` may carry leading axes, one row per formula."""
        missing = (values != self.full).astype(np.uint8)
        return np.maximum.reduceat(missing, self.starts, axis=-1).astype(bool)

    def at_frame(self, key: Key) -> np.ndarray:
        """A mask of the entries on the given frame."""
        return self.frame_of == self.frames.index(key)
