"""Search for short characteristic formulas of a finite rooted frame.

A formula is characteristic for a frame ``F`` when a finite rooted frame refutes
it exactly when that frame reduces to ``F`` (see ``frames.py``); among the
frames, ``F`` is then its only minimal refuter.  ``dejongh_formula.py`` builds
one, but it is long.  This enumerates formulas in ``--variables`` variables
(``a``, ``b``, ...) by size, with ``levels.py``, and keeps the characteristic
ones, in three stages of increasing cost:

1. Formulas are enumerated on a sample -- every frame up to ``--complete``
   points, and ``F``, under every valuation, plus ``--samples`` random
   valuations on frames of up to 7 points -- and merged when they agree there.
   A formula passes when it is refuted on ``F`` and holds at every sampled
   valuation whose frame does not reduce to ``F``.  Merging on a sample can
   hide a formula behind a smaller one that agrees with it there; the random
   valuations make that rare.
2. A passing formula is checked on whole frames: every frame of up to 6 points
   not already whole in the sample, and ``--whole-frames`` random 7 point ones,
   under every valuation.
3. A survivor is verified on every frame up to ``--verify`` points, and printed.

The first stage runs on ``--workers`` worker processes, which build each level.
Every level but the last is kept, ``--memory`` permitting; a level that does not
fit is recomputed where needed, which is slow.  Each size takes about three
times as long as the one before in two variables, more in three.  Progress goes
to stderr: a line per size, and a line every ``--progress`` seconds within one.

Usage:  python characteristic_search.py uneven-kite --max-size 9
        python characteristic_search.py tall-fork --variables 3 --max-size 11 --workers 12
"""

from __future__ import annotations

import argparse
import random
import sys
import time
from typing import Iterator

import numpy as np

import levels
from evaluate import Bank, every_valuation, random_valuations
from formulas import Formula, show, size
from frames import NAMED_FRAMES, Key, frame_arg, reductions, rooted_frames
from levels import Levels, gigabytes

SAMPLE_POINTS = 7  # the largest frames in the sample and the second stage


def log(message: str) -> None:
    print(message, file=sys.stderr, flush=True)


class Checker:
    """Stages 2 and 3: whether a formula is refuted exactly on the frames that
    reduce to the target, on a set of whole frames."""

    def __init__(self, target: Key, frames: list[Key], variables: int) -> None:
        self.bank = Bank.complete(frames, variables)
        self.wanted = np.array([target in reductions(k) for k in self.bank.frames])

    def __call__(self, p: Formula) -> bool:
        return bool((self.bank.refuted(self.bank.evaluate(p)) == self.wanted).all())


def _sample_stage(args: None, keys: np.ndarray, rows: np.ndarray) -> np.ndarray:
    """Stage 1, in a worker: the keys of the new formulas refuted on the target
    and holding wherever they must."""
    missing = rows != levels.array("full")
    passing = (missing[:, levels.array("target")].any(axis=1)
               & ~missing[:, levels.array("must_hold")].any(axis=1))
    return keys[passing]


def search(target: Key, max_size: int, variables: int, complete: int, samples: int,
           whole_frames: int, verify_points: int, seed: int, workers: int, memory: float,
           progress: float) -> Iterator[Formula]:
    """The characteristic formulas of ``target`` up to ``max_size``, smallest first."""
    rng = random.Random(seed)
    frames = rooted_frames(SAMPLE_POINTS)
    small = [k for n in range(1, complete + 1) for k in frames[n]]
    larger = [k for n in range(complete + 1, SAMPLE_POINTS + 1) for k in frames[n]]
    sample = Bank(every_valuation(set(small) | {target}, variables)
                  + random_valuations(larger, samples, rng, variables))
    whole = Checker(target, [k for n in range(complete + 1, SAMPLE_POINTS) for k in frames[n]]
                    + rng.sample(frames[SAMPLE_POINTS], whole_frames), variables)
    verify: Checker | None = None
    log(f"sample of {len(sample)} valuations on {len(sample.frames)} frames; "
        f"second stage {len(whole.bank)} valuations on {len(whole.bank.frames)} frames")

    def check(forms: list[Formula]) -> tuple[int, list[Formula]]:
        """Stages 2 and 3 for formulas that passed the first."""
        nonlocal verify
        survivors, found = 0, []
        for p in forms:
            if not whole(p):
                log(f"    passed the sample, not whole frames: {show(p)}")
                continue
            survivors += 1
            if verify is None:
                log(f"  building the frames up to {verify_points} points to verify on")
                verify = Checker(target, [k for keys in rooted_frames(verify_points).values()
                                          for k in keys], variables)
            if verify(p):
                found.append(p)
            else:
                log(f"    passed whole frames, not the verification: {show(p)}")
        return survivors, found

    budget = int(memory * 2**30)
    start = time.time()
    with Levels(sample, workers, log, progress) as enum:
        width = enum.width

        def padded(mask: np.ndarray) -> np.ndarray:
            return np.pad(mask, (0, width - len(mask)))

        must_hold = ~np.array([target in reductions(k) for k in sample.frames])[sample.frame_of]
        enum.shared.put("full", padded(sample.full))
        enum.shared.put("target", padded(sample.at_frame(target)))
        enum.shared.put("must_hold", padded(must_hold))

        for s in range(max_size + 1):
            if s == 0:
                keys = enum.keys(0)
                counts = {"built": len(keys), "kept": len(keys), "seconds": 0.0}
                forms = [enum.formula(0, int(n)) for n in _sample_stage(None, keys, enum.rows(0))]
            else:
                counts = enum.grow(store=False, inspect=(_sample_stage, None))
                level_keys = enum.keys(s)
                flagged = np.concatenate(counts["inspected"]) if counts["inspected"] else \
                    np.zeros(0, np.int64)
                flagged = np.sort(flagged[np.isin(flagged, level_keys)])
                forms = [enum.formula_of_key(s, int(k)) for k in flagged]
                if s < max_size:
                    if enum.shared.nbytes() + enum.sizes[s] * width <= budget:
                        enum.store(s)
                    else:
                        log(f"  size {s} does not fit in --memory; it is recomputed where needed")
            survivors, found = check(forms)
            log(f"size {s}: {counts['kept']:,} new formulas of {counts['built']:,} built, "
                f"{len(forms)} passed the sample, {survivors} whole frames, "
                f"{len(found)} characteristic; {counts['seconds']:.0f}s this size, "
                f"{time.time() - start:.0f}s in all, {enum.memory()}")
            yield from found


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("frame", help=f"one of {', '.join(NAMED_FRAMES)}, or pairs like 'r<x r<y'")
    parser.add_argument("--max-size", type=int, default=10, help="largest formula size")
    parser.add_argument("--variables", type=int, default=2, help="how many variables: a, b, c, ...")
    parser.add_argument("--complete", type=int,
                        help="frames up to this many points are in the sample under every "
                             "valuation (default 5 with two variables, 4 with more)")
    parser.add_argument("--samples", type=int, default=2000,
                        help="random valuations on larger frames in the sample")
    parser.add_argument("--whole-frames", type=int, default=60,
                        help="random 7 point frames in the second stage")
    parser.add_argument("--verify", type=int, default=7,
                        help="verify on every frame up to this many points (at most 8)")
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--workers", type=int, default=0,
                        help="worker processes for the first stage (0: none)")
    parser.add_argument("--memory", type=float, default=12.0,
                        help="gigabytes of formula values to keep between sizes")
    parser.add_argument("--progress", type=float, default=60.0,
                        help="seconds between progress lines within a size")
    args = parser.parse_args()

    complete = args.complete if args.complete is not None else 5 if args.variables <= 2 else 4
    target = frame_arg(args.frame).key
    for p in search(target, args.max_size, args.variables, complete, args.samples,
                    args.whole_frames, args.verify, args.seed, args.workers, args.memory,
                    args.progress):
        print(f"{size(p)}\t{show(p)}", flush=True)


if __name__ == "__main__":
    main()
