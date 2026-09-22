# Scripts

Model-theoretic scratch work behind `Logics/`. Nothing here is checked by Lean;
these find the facts, and Lean proves them. Python 3.10+, no dependencies.

## The library

`heyting.py` builds finite Heyting algebras as the upward closed sets of a
finite poset. By Birkhoff's representation theorem every finite Heyting algebra
arises this way, so these algebras are a complete source of countermodels: a
formula is intuitionistically derivable exactly when it reaches the top value in
all of them.

It provides `Poset` and `Algebra`, the principles of
`Logics/ClassicalAxioms/AxiomDef.lean` as functions on two elements, the named
frames (chains, forks, the diamond), poset enumeration, and a library of
substitution terms.

## The scripts

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

## Two traps

**Enumeration is exponential.** `all_posets(n)` filters all `2 ** (n * (n - 1))`
relations: a second at `n = 5`, about a billion candidates at `n = 6`. Use
`random_posets` above five points.

**A search over a few frames produces false positives.** An instantiation that
works on five hand-picked frames can still fail on the full sweep — that has
happened here, on a candidate whose hand proof then would not close. This is why
`find_instantiation.py` confirms every survivor against a full sweep before
reporting it, and why a candidate should be proved in Lean, not trusted.

Finding no separating algebra is likewise evidence, not proof: it says the two
principles generate the same logic as far as the search looked.
