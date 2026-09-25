"""A prover for intuitionistic propositional logic that writes its proofs as
natural deduction derivations in the ``Derives`` calculus of Logics/Heyting.lean.

The search is Dyckhoff's contraction-free sequent calculus G4ip, which
terminates and is complete.  Each of its rules is read back as natural
deduction:

* an implication right rule is ``impI``, a conjunction right rule ``andI``, a
  disjunction right rule ``orI₁`` or ``orI₂``;
* a disjunction left rule is ``orE``;
* the other left rules derive the hypotheses they introduce from the one they
  replace, and add them with ``cut``: the halves of a conjunction, ``B`` from
  ``A → B`` and ``A``, ``C → (D → B)`` from ``(C ∧ D) → B``, both ``C → B`` and
  ``D → B`` from ``(C ∨ D) → B``;
* the rule for ``(C → D) → B`` derives ``D → B``, proves ``C → D`` with it, and
  cuts in ``B``.

The natural deduction context only grows -- a hypothesis G4ip consumes stays
there -- so hypotheses are referred to by position: ``h₀`` to ``h₅`` for the six
most recent, ``Derives.nth`` further down.  The search visits hypotheses in a
fixed order, so its output is reproducible.

A proof is a tuple: ``("hyp", p)``, ``("flsE", d)``, ``("andI", d, e)``,
``("andE1", d)``, ``("andE2", d)``, ``("orI1", d)``, ``("orI2", d)``,
``("orE", d, p, e, q, f)`` (``e`` and ``f`` under the new hypotheses ``p`` and
``q``), ``("impI", p, d)``, ``("impE", d, e)`` and ``("cut", p, d, e)``.
"""

from __future__ import annotations

from functools import lru_cache
from typing import Iterable

from formulas import BOT, Formula, lean_doc, show, size
from lean_terms import App, Doc, Leaf, Named, layout

Proof = tuple


def _order(p: Formula) -> tuple[int, str]:
    return size(p), show(p)


@lru_cache(maxsize=None)
def _prove(hyps: frozenset, goal: Formula) -> Proof | None:
    if goal in hyps:
        return ("hyp", goal)
    if BOT in hyps:
        return ("flsE", ("hyp", BOT))
    if goal[0] == "imp":
        d = _prove(hyps | {goal[1]}, goal[2])
        return d and ("impI", goal[1], d)
    if goal[0] == "and":
        d = _prove(hyps, goal[1])
        e = d and _prove(hyps, goal[2])
        return e and ("andI", d, e)

    ordered = sorted(hyps, key=_order)
    for h in ordered:  # the rules that lose nothing
        rest = hyps - {h}
        if h[0] == "and":
            d = _prove(rest | {h[1], h[2]}, goal)
            return d and ("cut", h[1], ("andE1", ("hyp", h)),
                          ("cut", h[2], ("andE2", ("hyp", h)), d))
        if h[0] == "or":
            d = _prove(rest | {h[1]}, goal)
            e = d and _prove(rest | {h[2]}, goal)
            return e and ("orE", ("hyp", h), h[1], d, h[2], e)
        if h[0] != "imp":
            continue
        premise, b = h[1], h[2]
        if premise == BOT:
            return _prove(rest, goal)
        if premise in hyps:
            d = _prove(rest | {b}, goal)
            return d and ("cut", b, ("impE", ("hyp", h), ("hyp", premise)), d)
        if premise[0] == "and":
            c, e = premise[1], premise[2]
            curried = ("imp", c, ("imp", e, b))
            d = _prove(rest | {curried}, goal)
            proof = ("impI", c, ("impI", e, ("impE", ("hyp", h), ("andI", ("hyp", c), ("hyp", e)))))
            return d and ("cut", curried, proof, d)
        if premise[0] == "or":
            c, e = premise[1], premise[2]
            left, right = ("imp", c, b), ("imp", e, b)
            d = _prove(rest | {left, right}, goal)
            proof_left = ("impI", c, ("impE", ("hyp", h), ("orI1", ("hyp", c))))
            proof_right = ("impI", e, ("impE", ("hyp", h), ("orI2", ("hyp", e))))
            return d and ("cut", left, proof_left, ("cut", right, proof_right, d))

    if goal[0] == "or":  # the rules that may lose, tried in turn
        d = _prove(hyps, goal[1])
        if d:
            return ("orI1", d)
        d = _prove(hyps, goal[2])
        if d:
            return ("orI2", d)
    for h in ordered:
        if h[0] == "imp" and h[1][0] == "imp":
            c, e, b = h[1][1], h[1][2], h[2]
            rest = hyps - {h}
            weaker = ("imp", e, b)
            d = _prove(rest | {weaker}, ("imp", c, e))
            f = d and _prove(rest | {b}, goal)
            if f:
                proof = ("impI", e, ("impE", ("hyp", h), ("impI", c, ("hyp", e))))
                return ("cut", weaker, proof, ("cut", b, ("impE", ("hyp", h), d), f))
    return None


def prove(hyps: Iterable[Formula], goal: Formula) -> Proof | None:
    """A proof of ``goal`` from ``hyps``, or ``None`` when there is none."""
    return _prove(frozenset(hyps), goal)


_RULES = {"flsE": ".flsE", "andE1": ".andE₁", "andE2": ".andE₂", "orI1": ".orI₁",
          "orI2": ".orI₂", "andI": ".andI", "impE": ".impE"}


def proof_doc(proof: Proof, context: list[Formula]) -> Doc:
    """The proof as a ``Derives`` term, in a context listed most recent first."""
    rule = proof[0]
    if rule == "hyp":
        i = context.index(proof[1])
        return Leaf(".h" + "₀₁₂₃₄₅"[i]) if i <= 5 else App(".nth", (Leaf(str(i)), Leaf("rfl")))
    if rule in _RULES:
        return App(_RULES[rule], tuple(proof_doc(d, context) for d in proof[1:]))
    if rule == "impI":
        return App(".impI", (proof_doc(proof[2], [proof[1]] + context),))
    if rule == "orE":
        _, d, p, e, q, f = proof
        return App(".orE", (proof_doc(d, context), proof_doc(e, [p] + context),
                            proof_doc(f, [q] + context)))
    if rule == "cut":
        _, p, d, e = proof
        return App(".cut", (Named("p", lean_doc(p)), proof_doc(d, context),
                            proof_doc(e, [p] + context)))
    raise ValueError(f"unknown rule {rule!r}")


def derivation(hyps: list[Formula], goal: Formula, indent: int = 2,
               width: int = 100) -> str | None:
    """A ``Derives`` term for ``hyps ⊢ goal``, the hypotheses listed most recent
    first as in Lean, laid out within ``width`` columns; ``None`` if there is no
    derivation."""
    proof = prove(hyps, goal)
    return None if proof is None else layout(proof_doc(proof, list(hyps)), indent, width)
