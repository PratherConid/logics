# Scripts

Model-theoretic scratch work behind `Logics/`. Nothing here is checked by Lean;
these find the facts, and Lean proves them. Python 3.10+. The principle scripts
need nothing else; the frame scripts need numpy.

## The principle scripts

`heyting.py` builds finite Heyting algebras as the upward closed sets of a
finite poset. By Birkhoff's representation theorem every finite Heyting algebra
arises this way, so these algebras are a complete source of countermodels: a
formula is intuitionistically derivable exactly when it reaches the top value in
all of them.

It provides `Poset` and `Algebra`, the principles of
`Logics/IntermediateAxioms/AxiomDef.lean` as functions on two elements, the named
frames (chains, forks, the diamond), poset enumeration, and a library of
substitution terms.

| script | question it answers |
| --- | --- |
| `compare_principles.py` | Where does each principle hold, and how do they order by strength? |
| `find_instantiation.py` | At which arguments does one principle derive another? |
| `separating_frames.py` | Is there an algebra validating one principle but not another? |
| `diamond_tables.py` | What are the diamond's tables, as `Diamond` in `Logics/Heyting.lean` encodes them? |

```
python compare_principles.py 5
python find_instantiation.py "ImpOrOrLuk'" PierceOrLuk --depth 1 --sweep 4
python separating_frames.py PierceOrLuk "ImpOrOrLuk'" --sweep 4
python diamond_tables.py
```

## The frame scripts

These work with formulas rather than named principles, and with rooted frames up
to isomorphism rather than labelled posets, which takes the enumeration to eight
points (2451 frames). Formulas are read in the notation of the Lean comments,
`((a → b) → a) → a` or `((a -> b) -> a) -> a`; frames by name or by covering
pairs, `"r<x r<y x<t y<t"`.

| module | what it provides |
| --- | --- |
| `formulas.py` | formulas as nested tuples mirroring `Form`, with a reader, a printer and Lean output |
| `frames.py` | rooted frames up to isomorphism, the reductions between them, named frames |
| `evaluate.py` | a formula at many frames and valuations at once (numpy); formulas enumerated by size |
| `g4ip.py` | a prover writing its proofs as `Derives` terms of `Logics/Heyting.lean` |
| `lean_terms.py` | Lean terms laid out within a width |

| script | question it answers |
| --- | --- |
| `minimal_refuters.py` | Which finite rooted frames refute a formula minimally? |
| `dejongh_formula.py` | What is a frame's characteristic formula, by de Jongh's construction? |
| `characteristic_search.py` | Is there a short characteristic formula? |
| `witness_search.py` | What witnesses does `Logics/PointEmbed.lean` need to embed a frame's algebra? |
| `point_embed_lean.py` | What are the derivations those witnesses need, as Lean source? |

The last three are the route to a refuter file such as
`Logics/IntermediateAxioms/Refuter/NoKiteUp1x2Refuter.lean`: find a
characteristic formula, witnesses for it, and the derivations.

```
python minimal_refuters.py "(a → b) ∨ (b → a)" --points 7
python dejongh_formula.py uneven-kite
python characteristic_search.py uneven-kite --max-size 10
python witness_search.py uneven-kite \
    "((((a → b ∨ ¬b) → a) → a) → a ∨ b) → b ∨ (b → a ∨ ¬a)" --out kite.json
python point_embed_lean.py kite.json > derivations.lean
```

## Traps

**Enumeration is exponential.** `all_posets(n)` filters all `2 ** (n * (n - 1))`
relations: a second at `n = 5`, about a billion candidates at `n = 6`. Use
`random_posets` above five points, or the frame scripts, which enumerate up to
isomorphism.

**A search over a few frames produces false positives.** An instantiation that
works on five hand-picked frames can still fail on the full sweep — that has
happened here, on a candidate whose hand proof then would not close. This is why
`find_instantiation.py` confirms every survivor against a full sweep before
reporting it, why the frame scripts verify on every frame up to seven points,
and why a candidate should be proved in Lean, not trusted.

Finding no separating algebra is likewise evidence, not proof: it says the two
principles generate the same logic as far as the search looked. The same goes
for a list of minimal refuters that stops growing.

**Merging on a sample can hide a formula.** `characteristic_search.py`
enumerates formulas on a sample of valuations, and a formula agreeing there with
a smaller one is dropped, even if it is the characteristic one and the smaller
one is not. Random valuations on larger frames make that rare, not impossible.

**Point order matters to Lean.** The joins in the statements
`point_embed_lean.py` writes list the points in the spec's order, which must be
the order of `J` in the refuter file's `Points`.
