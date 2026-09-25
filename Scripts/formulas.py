"""Propositional formulas, as nested tuples mirroring ``Form`` in Logics/Heyting.lean.

    ("var", n)                 the variable ``.var n``
    ("bot",)                   falsum, ``.fls``
    ("and" | "or" | "imp", p, q)

Negation and truth are abbreviations, as in Lean: ``¬p`` is ``p → ⊥`` and ``⊤``
is ``⊥ → ⊥``.  Formulas are read and printed in the notation of the Lean
comments -- variables ``a``, ``b``, ``c``, ... for ``.var 0``, ``.var 1``, ...,
and ``⊥ ⊤ ¬ ∧ ∨ →`` -- with ASCII ``bot top ~ & | ->`` accepted when reading.
``→`` groups to the right and binds loosest, then ``∨``, ``∧`` and ``¬``.
"""

from __future__ import annotations

import re
from typing import Iterable

from lean_terms import App, Doc, Leaf, flat

Formula = tuple

BOT: Formula = ("bot",)
TOP: Formula = ("imp", BOT, BOT)
VAR_NAMES = "abcdefgh"


def var(n: int) -> Formula:
    return ("var", n)


A, B = var(0), var(1)


def neg(p: Formula) -> Formula:
    return ("imp", p, BOT)


def em(p: Formula) -> Formula:
    """Excluded middle at ``p``: ``p ∨ ¬p``, ``excludedMiddleForm p`` in Lean."""
    return ("or", p, neg(p))


def peirce(p: Formula, q: Formula) -> Formula:
    """Peirce's law at ``p, q``: ``((p → q) → p) → p``, ``peirceForm p q`` in Lean."""
    return ("imp", ("imp", ("imp", p, q), p), p)


def conjunction(ps: Iterable[Formula]) -> Formula:
    """The conjunction of a list, grouped to the left; ``⊤`` for the empty one."""
    ps = list(ps)
    result = ps[0] if ps else TOP
    for p in ps[1:]:
        result = ("and", result, p)
    return result


def disjunction(ps: Iterable[Formula]) -> Formula:
    """The disjunction of a list, grouped to the left; ``⊥`` for the empty one."""
    ps = list(ps)
    result = ps[0] if ps else BOT
    for p in ps[1:]:
        result = ("or", result, p)
    return result


def disj(ps: Iterable[Formula]) -> Formula:
    """The disjunction of a list as ``Form.disj`` builds it: grouped to the right
    and closed off by ``⊥``, so that it evaluates to the join of the list."""
    result = BOT
    for p in reversed(list(ps)):
        result = ("or", p, result)
    return result


def size(p: Formula) -> int:
    """The number of binary connectives, negations included."""
    return 1 + size(p[1]) + size(p[2]) if len(p) == 3 else 0


def variables(p: Formula) -> set[int]:
    if p[0] == "var":
        return {p[1]}
    if p == BOT:
        return set()
    return variables(p[1]) | variables(p[2])


# --- printing -----------------------------------------------------------------

_SYMBOLS = {"and": "∧", "or": "∨", "imp": "→"}


def show(p: Formula, outer: bool = True) -> str:
    """The formula in Lean-comment notation, compound subformulas parenthesised."""
    if p == TOP:
        return "⊤"
    if p[0] == "var":
        return VAR_NAMES[p[1]]
    if p == BOT:
        return "⊥"
    if p[0] == "imp" and p[2] == BOT:
        return "¬" + show(p[1], outer=False)
    text = f"{show(p[1], False)} {_SYMBOLS[p[0]]} {show(p[2], False)}"
    return text if outer else f"({text})"


def lean_doc(p: Formula) -> Doc:
    """The formula as a Lean term of type ``Form``."""
    if p == TOP:
        return Leaf("Form.tru")
    if p[0] == "var":
        return App(".var", (Leaf(str(p[1])),))
    if p == BOT:
        return Leaf(".fls")
    if p[0] == "imp" and p[2] == BOT:
        return App("Form.neg", (lean_doc(p[1]),))
    return App("." + p[0], (lean_doc(p[1]), lean_doc(p[2])))


def to_lean(p: Formula) -> str:
    return flat(lean_doc(p), outer=True)


# --- reading ------------------------------------------------------------------

_TOKEN = re.compile(r"\s*(->|→|¬|~|∧|&|∨|\||⊥|⊤|bot|top|\(|\)|[a-h])")
_ALIASES = {"->": "→", "~": "¬", "&": "∧", "|": "∨", "bot": "⊥", "top": "⊤"}


def parse(text: str) -> Formula:
    """Read a formula written as ``show`` prints it, or in ASCII."""
    tokens, pos = [], 0
    text = text.strip()
    while pos < len(text):
        m = _TOKEN.match(text, pos)
        if not m:
            raise ValueError(f"cannot read {text[pos:]!r}")
        tokens.append(_ALIASES.get(m.group(1), m.group(1)))
        pos = m.end()
    tokens.append(None)
    i = 0

    def peek() -> str | None:
        return tokens[i]

    def take(expected: str | None = None) -> str | None:
        nonlocal i
        tok = tokens[i]
        if expected is not None and tok != expected:
            raise ValueError(f"expected {expected!r}, found {tok!r} in {text!r}")
        i += 1
        return tok

    def implication() -> Formula:
        left = disjunction()
        if peek() == "→":
            take()
            return ("imp", left, implication())
        return left

    def disjunction() -> Formula:
        left = conjunction()
        while peek() == "∨":
            take()
            left = ("or", left, conjunction())
        return left

    def conjunction() -> Formula:
        left = unary()
        while peek() == "∧":
            take()
            left = ("and", left, unary())
        return left

    def unary() -> Formula:
        tok = take()
        if tok == "¬":
            return neg(unary())
        if tok == "(":
            inner = implication()
            take(")")
            return inner
        if tok == "⊥":
            return BOT
        if tok == "⊤":
            return TOP
        if tok is not None and tok in VAR_NAMES:
            return var(VAR_NAMES.index(tok))
        raise ValueError(f"unexpected {tok!r} in {text!r}")

    result = implication()
    take(None)
    return result
