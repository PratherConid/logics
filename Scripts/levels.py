"""Formulas enumerated by size, one per value on a bank.

Level ``s`` holds formulas of size ``s``, built from the variables of the bank,
``⊥`` and ``⊤``.  A formula is kept when its values on the bank differ from
those of every formula kept before it, so each kept formula is a smallest one
with its values.  Within a level, formulas come in the order of their *keys*:
by the size of the left part, the left part, the connective (``∧``, ``∨``,
``→``) and the right part.  Meets and joins commute, so each is built once,
with the left part first in that order.  A part that is ``⊥`` or ``⊤`` is
skipped where the result repeats a smaller formula, which keeps the same ones.

A level is stored as its keys -- an ``int64`` packing the left size, the
connective and the positions of the two parts in their levels -- and, unless it
is *virtual*, its values, one row of bytes per formula.  A virtual level costs
eight bytes a formula and recomputes a row when asked for it; that is cheap
when the level is only combined with small ones.  Rows are padded with zeros to
a multiple of eight bytes and compared by a random linear hash, so two
different ones are merged only with negligible probability.

The work of a level can be spread over worker processes (``workers``), the
levels then living in shared memory.  Worker functions reach them through
``array`` and ``rows``; other modules can run their own functions on the same
workers with ``Levels.run``.

Requires numpy.
"""

from __future__ import annotations

import math
import multiprocessing
import sys
import time
from multiprocessing import shared_memory
from typing import Any, Callable, Iterable, Iterator

import numpy as np

from evaluate import Bank, arrow
from formulas import BOT, TOP, Formula, var

AND, OR, IMP = 0, 1, 2
OPS = ("and", "or", "imp")
_KBITS = 26  # positions within a level stay below 2**26
_KMASK = (1 << _KBITS) - 1

# --- keys ---------------------------------------------------------------------


def encode(left: Any, k: Any, op: Any, g: Any) -> Any:
    """The key of the formula ``op`` applied to part ``k`` of level ``left`` and
    part ``g`` of the level that makes up the size; arrays broadcast."""
    left, k, op, g = (np.asarray(v, dtype=np.int64) for v in (left, k, op, g))
    return (((left << _KBITS | k) << 2 | op) << _KBITS) | g


def decode(keys: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """``left, k, op, g`` of each key."""
    keys = np.asarray(keys, dtype=np.int64)
    rest = keys >> _KBITS
    return rest >> (_KBITS + 2), rest >> 2 & _KMASK, rest & 3, keys & _KMASK


# --- hashing ------------------------------------------------------------------

def row_hashes(rows: np.ndarray) -> np.ndarray:
    """A random linear hash of each row, with weights fixed by a seed."""
    return rows.astype(np.uint64) @ array("weights")


# --- arrays the workers can reach ----------------------------------------------


class Shared:
    """Named arrays: in shared memory when worker processes read them, plain
    arrays otherwise."""

    def __init__(self, processes: bool) -> None:
        self.processes = processes
        self.arrays: dict[str, np.ndarray] = {}
        self._segments: dict[str, shared_memory.SharedMemory] = {}

    def create(self, name: str, shape: tuple[int, ...], dtype: Any) -> np.ndarray:
        self.drop(name)
        dtype = np.dtype(dtype)
        if self.processes:
            size = max(1, math.prod(shape) * dtype.itemsize)
            segment = shared_memory.SharedMemory(create=True, size=size)
            self._segments[name] = segment
            array = np.ndarray(shape, dtype, buffer=segment.buf)
        else:
            array = np.empty(shape, dtype)
        self.arrays[name] = array
        return array

    def put(self, name: str, array: np.ndarray) -> np.ndarray:
        out = self.create(name, array.shape, array.dtype)
        out[...] = array
        return out

    def get(self, name: str) -> np.ndarray | None:
        return self.arrays.get(name)

    def drop(self, name: str) -> None:
        self.arrays.pop(name, None)
        segment = self._segments.pop(name, None)
        if segment is not None:
            _close(segment)
            segment.unlink()

    def close(self) -> None:
        for name in list(self.arrays):
            self.drop(name)

    def directory(self) -> dict[str, tuple[str, tuple[int, ...], str]]:
        """What a worker needs to attach to each array."""
        return {name: (seg.name, self.arrays[name].shape, self.arrays[name].dtype.str)
                for name, seg in self._segments.items()}

    def nbytes(self) -> int:
        return sum(a.nbytes for a in self.arrays.values())


class _Attached:
    """A worker's view of the main process's ``Shared`` arrays."""

    def __init__(self) -> None:
        self.arrays: dict[str, np.ndarray] = {}
        self._segments: dict[str, shared_memory.SharedMemory] = {}

    def sync(self, directory: dict[str, tuple[str, tuple[int, ...], str]]) -> None:
        for name in list(self._segments):
            if directory.get(name, ("",))[0] != self._segments[name].name:
                self.arrays.pop(name, None)
                _close(self._segments.pop(name))
        for name, (segment_name, shape, dtype) in directory.items():
            if name not in self._segments:
                segment = shared_memory.SharedMemory(name=segment_name)
                self._segments[name] = segment
                self.arrays[name] = np.ndarray(shape, np.dtype(dtype), buffer=segment.buf)

    def get(self, name: str) -> np.ndarray | None:
        return self.arrays.get(name)


def _close(segment: shared_memory.SharedMemory) -> None:
    try:
        segment.close()
    except BufferError:  # a view is still alive; the segment goes with the process
        pass


_active: Shared | _Attached | None = None


def array(name: str) -> np.ndarray:
    """A named array, in the main process or a worker."""
    found = _active.get(name)
    if found is None:
        raise KeyError(name)
    return found


def has(name: str) -> bool:
    return _active.get(name) is not None


def _init_worker() -> None:
    global _active
    _active = _Attached()


def _call(job: tuple[Callable, dict, Any]) -> Any:
    function, directory, args = job
    _active.sync(directory)
    return function(args)


# --- values of formulas, in the main process or a worker ----------------------


def combine(op: int, x: np.ndarray, y: np.ndarray) -> np.ndarray:
    """``x op y`` on padded rows; ``x`` and ``y`` broadcast."""
    if op == AND:
        return x & y
    if op == OR:
        return x | y
    return arrow(x, y, array("up"), array("present"))


def rows(s: int, index: slice | np.ndarray) -> np.ndarray:
    """The values of the formulas at ``index`` in level ``s``."""
    if has(f"values/{s}"):
        return array(f"values/{s}")[index]
    return compute(s, array(f"keys/{s}")[index])


def compute(s: int, keys: np.ndarray) -> np.ndarray:
    """The values of the formulas of size ``s`` with these keys."""
    left, k, op, g = decode(keys)
    out = np.empty((len(left), array("weights").shape[0]), dtype=np.uint8)
    for i in np.unique(left).tolist():
        at = np.flatnonzero(left == i)
        x, y = rows(i, k[at]), rows(s - 1 - i, g[at])
        for code in np.unique(op[at]).tolist():
            same = op[at] == code
            out[at[same]] = combine(code, x[same], y[same])
    return out


def seen_before(hashes: np.ndarray, seen: np.ndarray) -> np.ndarray:
    """Which hashes occur in the sorted array ``seen``."""
    if not len(seen):
        return np.zeros(len(hashes), dtype=bool)
    at = np.minimum(np.searchsorted(seen, hashes), len(seen) - 1)
    return seen[at] == hashes


def first_per_hash(hashes: np.ndarray, keys: np.ndarray) -> np.ndarray:
    """The positions holding the smallest key for each distinct hash."""
    order = np.lexsort((keys, hashes))
    h = hashes[order]
    first = np.ones(len(h), dtype=bool)
    first[1:] = h[1:] != h[:-1]
    return order[first]


Inspect = tuple[Callable[[Any, np.ndarray, np.ndarray], Any], Any]


def _generate(task: tuple) -> tuple[int, np.ndarray, np.ndarray, Any]:
    """Phase one of a level: the new formulas of one block of pairs, as hashes
    and keys, the smallest key for each hash in the block.  An ``inspect`` hook
    ``(function, args)`` is shown their keys and rows as well."""
    s, i, (k0, k1), (g0, g1), variables, inspect = task
    j = s - 1 - i
    x, y = rows(i, slice(k0, k1)), rows(j, slice(g0, g1))
    kk, gg = np.arange(k0, k1)[:, None], np.arange(g0, g1)[None, :]
    everywhere = np.ones((k1 - k0, g1 - g0), dtype=bool)
    parts = []
    if i <= j:
        keep = everywhere & (gg > kk) if i == j else everywhere
        if j == 0:
            keep = keep & (gg < variables)  # x ∧ ⊥, x ∨ ⊥ ... repeat smaller formulas
        parts += [(AND, keep), (OR, keep)]
    keep = everywhere & (gg != kk) if i == j else everywhere
    if j == 0:
        keep = keep & (gg != variables + 1)  # x → ⊤ is ⊤
    parts.append((IMP, keep))

    seen = array("seen")
    width = x.shape[1]
    built = 0
    hashes, keys, values = [], [], []
    for op, keep in parts:
        chosen = np.flatnonzero(keep)
        if not len(chosen):
            continue
        built += len(chosen)
        block = combine(op, x[:, None, :], y[None, :, :]).reshape(-1, width)
        if len(chosen) < len(block):
            block = block[chosen]
        h = row_hashes(block)
        new = ~seen_before(h, seen)
        hashes.append(h[new])
        keys.append(encode(i, kk, op, gg).ravel()[chosen[new]])
        if inspect is not None:
            values.append(block[new])
    if not hashes:
        return built, np.zeros(0, np.uint64), np.zeros(0, np.int64), None
    hashes, keys = np.concatenate(hashes), np.concatenate(keys)
    first = first_per_hash(hashes, keys)
    extra = None
    if inspect is not None:
        function, args = inspect
        extra = function(args, keys[first], np.concatenate(values)[first])
    return built, hashes[first], keys[first], extra


def _fill(task: tuple[int, int, int]) -> None:
    """Phase two: the values of a stretch of a new level, from its keys."""
    s, p0, p1 = task
    array(f"values/{s}")[p0:p1] = compute(s, array(f"keys/{s}")[p0:p1])


def blocks(nk: int, nj: int, pairs: int) -> Iterator[tuple[tuple[int, int], tuple[int, int]]]:
    """Blocks of about ``pairs`` pairs covering ``range(nk) × range(nj)``,
    taking a small side whole."""
    kb = min(nk, max(1, math.isqrt(pairs)))
    gb = min(nj, max(1, pairs // kb))
    kb = min(nk, max(1, pairs // gb))
    for k0 in range(0, nk, kb):
        for g0 in range(0, nj, gb):
            yield (k0, min(nk, k0 + kb)), (g0, min(nj, g0 + gb))


class _Merge:
    """Hashes and keys from many blocks, reduced to the smallest key per hash."""

    def __init__(self, limit: int = 20_000_000) -> None:
        self.limit = limit
        self.hashes = np.zeros(0, np.uint64)
        self.keys = np.zeros(0, np.int64)
        self._pending: list[tuple[np.ndarray, np.ndarray]] = []
        self._count = 0

    def add(self, hashes: np.ndarray, keys: np.ndarray) -> None:
        self._pending.append((hashes, keys))
        self._count += len(hashes)
        if self._count > self.limit:
            self._compact()

    def _compact(self) -> None:
        hashes = np.concatenate([self.hashes] + [h for h, _ in self._pending])
        keys = np.concatenate([self.keys] + [k for _, k in self._pending])
        first = first_per_hash(hashes, keys)
        self.hashes, self.keys = hashes[first], keys[first]
        self._pending, self._count = [], 0
        self.limit = max(self.limit, 2 * len(self.hashes))

    def result(self) -> tuple[np.ndarray, np.ndarray]:
        """The hashes and keys, in the order of the keys."""
        self._compact()
        order = np.argsort(self.keys, kind="stable")
        return self.hashes[order], self.keys[order]


def memory_in_use() -> int:
    """The peak memory of this process in bytes, or 0 if unknown."""
    try:
        if sys.platform == "win32":
            import ctypes
            from ctypes import wintypes

            class Counters(ctypes.Structure):
                _fields_ = [("cb", wintypes.DWORD), ("PageFaultCount", wintypes.DWORD)] + [
                    (name, ctypes.c_size_t) for name in (
                        "PeakWorkingSetSize", "WorkingSetSize", "QuotaPeakPagedPoolUsage",
                        "QuotaPagedPoolUsage", "QuotaPeakNonPagedPoolUsage",
                        "QuotaNonPagedPoolUsage", "PagefileUsage", "PeakPagefileUsage")]

            counters = Counters()
            counters.cb = ctypes.sizeof(Counters)
            current = ctypes.windll.kernel32.GetCurrentProcess
            current.restype = wintypes.HANDLE
            query = ctypes.windll.psapi.GetProcessMemoryInfo
            query.argtypes = [wintypes.HANDLE, ctypes.POINTER(Counters), wintypes.DWORD]
            query(current(), ctypes.byref(counters), counters.cb)
            return int(counters.PeakPagefileUsage)
        import resource
        return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024
    except Exception:
        return 0


def gigabytes(n: int) -> str:
    return f"{n / 2**30:.1f} GB"


class Levels:
    """The levels of formulas on a bank, grown one at a time.

    ``workers`` worker processes share the work of each level; with none, all
    runs in this process.  ``log`` receives progress lines, at most every
    ``progress`` seconds within a long stretch of work.
    """

    def __init__(self, bank: Bank, workers: int = 0, log: Callable[[str], None] | None = None,
                 progress: float = 60.0, pairs_per_task: int | None = None) -> None:
        global _active
        self.bank = bank
        self.variables = bank.variables
        self.width = -(-len(bank) // 8) * 8
        self.workers = workers
        self.log = log or (lambda message: None)
        self.progress = progress
        self.pairs_per_task = pairs_per_task or max(64, (4 << 20) // self.width)
        self.shared = Shared(processes=workers > 0)
        _active = self.shared
        padding = self.width - len(bank)
        self.shared.put("up", np.pad(bank.up, ((0, 0), (0, padding))))
        self.shared.put("present", np.pad(bank.present, ((0, 0), (0, padding))))
        weights = np.random.default_rng(0).integers(1, 2**63, size=len(bank), dtype=np.uint64)
        self.shared.put("weights", np.pad(weights, (0, padding)))

        self.base_formulas = [var(i) for i in range(self.variables)] + [BOT, TOP]
        values = np.zeros((len(self.base_formulas), self.width), dtype=np.uint8)
        for n, p in enumerate(self.base_formulas):
            values[n, :len(bank)] = bank.evaluate(p)
        hashes = row_hashes(values)
        if len(set(hashes.tolist())) < len(hashes):
            raise ValueError("the bank does not tell the variables and constants apart")
        self.shared.put("values/0", values)
        self.shared.put("keys/0", np.arange(len(values), dtype=np.int64))
        self.shared.put("seen", np.sort(hashes))
        self.sizes = [len(values)]
        self._formulas: dict[tuple[int, int], Formula] = {}
        self._pool = None
        if workers:
            self._pool = multiprocessing.get_context("spawn").Pool(
                workers, initializer=_init_worker)

    def close(self) -> None:
        if self._pool is not None:
            self._pool.terminate()
            self._pool.join()
            self._pool = None
        self.shared.close()

    def __enter__(self) -> "Levels":
        return self

    def __exit__(self, *exc: object) -> None:
        self.close()

    # --- running work -------------------------------------------------------

    def run(self, function: Callable[[Any], Any], tasks: list, label: str = "",
            status: Callable[[], str] | None = None) -> Iterator[Any]:
        """The results of ``function`` on each task, in any order, from the
        workers or from this process.  Logs progress every ``progress`` seconds."""
        global _active
        _active = self.shared
        start = last = time.time()
        if self._pool is None:
            results: Iterable[Any] = map(function, tasks)
        else:
            directory = self.shared.directory()
            chunk = max(1, min(64, len(tasks) // (8 * self.workers)))
            results = self._pool.imap_unordered(
                _call, [(function, directory, t) for t in tasks], chunksize=chunk)
        for done, result in enumerate(results, 1):
            yield result
            now = time.time()
            if now - last >= self.progress and done < len(tasks):
                last = now
                extra = f", {status()}" if status else ""
                self.log(f"    {label}: {done}/{len(tasks)} tasks{extra}, "
                         f"{now - start:.0f}s, {self.memory()}")

    def memory(self) -> str:
        return (f"shared {gigabytes(self.shared.nbytes())}, "
                f"main peak {gigabytes(memory_in_use())}")

    # --- growing ------------------------------------------------------------

    def grow(self, store: bool = True, inspect: Inspect | None = None) -> dict[str, Any]:
        """Build the next level; keep its values unless ``store`` is false.
        Returns counts, and the results of the ``inspect`` hook on each block."""
        s = len(self.sizes)
        start = time.time()
        tasks = []
        for i in range(s):
            j = s - 1 - i
            nk = self.variables if i == 0 else self.sizes[i]  # ⊥ and ⊤ on the left repeat
            for kr, gr in blocks(nk, self.sizes[j], self.pairs_per_task):
                tasks.append((s, i, kr, gr, self.variables, inspect))
        merge = _Merge()
        inspected = []
        built = 0

        def status() -> str:
            return f"{built:,} formulas built"

        for count, hashes, keys, extra in self.run(_generate, tasks, f"size {s}", status):
            built += count
            merge.add(hashes, keys)
            if extra is not None:
                inspected.append(extra)
        hashes, keys = merge.result()
        self.shared.put(f"keys/{s}", keys)
        self.sizes.append(len(keys))
        self.shared.put("seen", np.sort(np.concatenate([self.shared.arrays["seen"], hashes])))
        if store:
            self.shared.create(f"values/{s}", (len(keys), self.width), np.uint8)
            step = max(1, min(65536, (64 << 20) // self.width))
            fill = [(s, p, min(len(keys), p + step)) for p in range(0, len(keys), step)]
            for _ in self.run(_fill, fill, f"size {s} values"):
                pass
        return {"built": built, "kept": len(keys), "seconds": time.time() - start,
                "inspected": inspected}

    def store(self, s: int) -> None:
        """Keep the values of a virtual level."""
        if not self.stored(s):
            n = self.sizes[s]
            self.shared.create(f"values/{s}", (n, self.width), np.uint8)
            step = max(1, min(65536, (64 << 20) // self.width))
            fill = [(s, p, min(n, p + step)) for p in range(0, n, step)]
            for _ in self.run(_fill, fill, f"size {s} values"):
                pass

    def stored(self, s: int) -> bool:
        return f"values/{s}" in self.shared.arrays

    # --- reading ------------------------------------------------------------

    def keys(self, s: int) -> np.ndarray:
        return self.shared.arrays[f"keys/{s}"]

    def rows(self, s: int, index: slice | np.ndarray = slice(None)) -> np.ndarray:
        """Padded values of formulas of level ``s``, in this process."""
        global _active
        _active = self.shared
        return rows(s, index)

    def compute(self, s: int, keys: np.ndarray) -> np.ndarray:
        """Padded values of formulas of size ``s`` given by keys, in this process."""
        global _active
        _active = self.shared
        return compute(s, keys)

    def values(self, s: int) -> np.ndarray:
        """The values of level ``s`` on the bank, one row per formula."""
        return self.rows(s)[:, :len(self.bank)]

    def formula(self, s: int, n: int) -> Formula:
        """Formula ``n`` of level ``s``."""
        if s == 0:
            return self.base_formulas[n]
        found = self._formulas.get((s, n))
        if found is None:
            found = self.formula_of_key(s, int(self.keys(s)[n]))
            self._formulas[(s, n)] = found
        return found

    def formula_of_key(self, s: int, key: int) -> Formula:
        """The formula of size ``s`` with this key."""
        left, k, op, g = (int(v[0]) for v in decode(np.array([key])))
        return (OPS[op], self.formula(left, k), self.formula(s - 1 - left, g))

    def formulas(self, s: int) -> list[Formula]:
        return [self.formula(s, n) for n in range(self.sizes[s])]


def formula_levels(bank: Bank, max_size: int) -> Iterator[tuple[list[Formula], np.ndarray]]:
    """The formulas of each size up to ``max_size``, one per value on the bank,
    with their values; from size 0 up."""
    with Levels(bank) as levels:
        yield levels.formulas(0), levels.values(0)
        for s in range(1, max_size + 1):
            levels.grow()
            yield levels.formulas(s), levels.values(s)
