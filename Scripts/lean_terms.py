"""Lean terms as trees, printed on one line or laid out within a width.

A term is a leaf (``.h₀``), an application of a head to arguments
(``.impE d e``), or a named argument (``(p := f)``).  ``flat`` prints it on
one line; ``layout`` keeps a subterm on one line when it fits and otherwise
puts each argument on its own line, indented under its head.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Leaf:
    text: str


@dataclass(frozen=True)
class App:
    head: str
    args: tuple["Doc", ...]


@dataclass(frozen=True)
class Named:
    name: str
    value: "Doc"


Doc = Leaf | App | Named


def flat(doc: Doc, outer: bool = False) -> str:
    """The term on one line.  An application is parenthesised unless ``outer``."""
    if isinstance(doc, Leaf):
        return doc.text
    if isinstance(doc, Named):
        return f"({doc.name} := {flat(doc.value, outer=True)})"
    text = " ".join([doc.head] + [flat(a) for a in doc.args])
    return text if outer else f"({text})"


def layout(doc: Doc, indent: int = 0, width: int = 100) -> str:
    """The term within ``width`` columns, starting at column ``indent``."""
    text = flat(doc)
    if indent + len(text) <= width or isinstance(doc, Leaf):
        return text
    pad = "\n" + " " * (indent + 2)
    if isinstance(doc, Named):
        return f"({doc.name} :={pad}{layout(doc.value, indent + 2, width)})"
    return "(" + doc.head + "".join(pad + layout(a, indent + 2, width) for a in doc.args) + ")"
