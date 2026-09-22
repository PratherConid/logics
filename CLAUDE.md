# Project conventions

## Do not refer to downstream code unless necessary

A file, definition or comment should not mention code that depends on it.
`Logics/Lattice.lean` must not talk about `Logics/Heyting.lean`, and
`Logics/Heyting.lean` must not talk about `Logics/Basic.lean`.  References in
the other direction, towards what a file is built on, are fine.

Why: an upstream file that names its consumers stops being readable on its own
terms, and the reference rots as soon as the downstream file is renamed, split
or dropped.  The dependency graph should be legible from the imports alone.

How to apply: state what a definition *is* and what it is built from, not what
it will later be used for.  If motivation genuinely needs a downstream example,
describe it in general terms ("a concrete finite algebra", "a propositional
calculus") rather than naming the file or its theorems.  Put the cross-reference
in the downstream file, which is allowed to point upstream.
