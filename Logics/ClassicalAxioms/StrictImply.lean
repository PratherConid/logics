import Logics.ClassicalAxioms.Model

/-!
# What the principles do not prove

Soundness, read backwards, turns the measurements of the previous file into
underivability: anything with a proof takes the top value under every
valuation, so a formula that misses the top value somewhere has no proof.

The first theorem applies this to bare intuitionistic logic, where the tall
fork refutes `PierceOrPierceF'` outright.  One such statement covers the whole
development, because every other principle here derives that one.

The rest say something stronger, about a principle assumed as an *axiom
schema*.  `DerivesFromSchema X p` holds when some finite list of substitution
instances of `X` derives `p`, and `DerivesFromSchema.valid` says an algebra
validating `X` validates everything the schema derives.  So a single algebra
validating `X` but refuting `p` rules out every instantiation of `X` at once,
which is what "strictly weaker" needs.

## The hierarchy

Writing `⊋` for "derives, but is not derived by", the derivations in
`Logics/ClassicalAxioms/Implication.lean` and the non-derivations here place
every combined principle of this development in a chain of four strict steps:

```
  ExcludedMiddleF ≡ PierceOrDeMorganF ≡ DeMorganOrImpOrF ≡ ImpOrOrImpOrF'
    ⊋  PeirceOrImpOrF'
    ⊋  DeMorganOrLukasiewiczF ≡ ImpOrOrLukasiewiczF ≡ PierceOrLukasiewiczF'
    ⊋  ImpOrOrLukasiewiczF' ≡ LukasiewiczOrLukasiewiczF'
    ⊋  PierceOrLukasiewiczF   ≡ PeirceOrImpOrF
    ⊋  PierceOrPierceF'
```

Not every such disjunction is intermediate.  `PierceOrDeMorganF` and
`DeMorganOrImpOrF` avoid Lukasiewicz, and both land back on excluded middle: at
arguments built from `a ∨ ¬ a` each of their disjuncts collapses to it on its
own.  Every principle that stays below the top has `LukasiewiczF` as one
disjunct, or else pairs Peirce with `ImpOrF`, the two weakest of the four.

Each `≡` is a pair of derivations at shifted instances, not an identity: the
principles so related are different formulas that prove each other.  Swapping
Lukasiewicz's arguments in the Peirce principle lands inside a class; doing it
in the `ImpOrF` principle drops a level; swapping `ImpOrF`'s own arguments in
`PeirceOrImpOrF` climbs three.

## The separating algebras

Each step is witnessed by one algebra, which validates every instance of the
weaker principle and refutes one instance of the stronger.  All four are built
in `Logics/Heyting.lean`.

| step                                         | algebra   | theorem                             |
| -------------------------------------------- | --------- | ----------------------------------- |
| `ExcludedMiddleF` over `PeirceOrImpOrF'`     | `Fin 3`   | `em_nderiv_peirceOrImpOr'`          |
| `PeirceOrImpOrF'` over `DeMorganOrLukasiewiczF` | `ForkUp 1 1` | `peirceOrImpOr'_nderiv_demorganOrLuk` |
| `DeMorganOrLukasiewiczF` over `ImpOrOrLukasiewiczF'` | `Fin 4` | `demorganOrLuk_nderiv_impOrOrLuk'` |
| `ImpOrOrLukasiewiczF'` over `PierceOrLukasiewiczF` | `KiteUp 1 1` | `impOrOrLuk'_nderiv_pierceOrLuk` |
| `PierceOrLukasiewiczF` over `PierceOrPierceF'` | `KiteUp 1 2` | `pierceOrLuk_nderiv_pierceOrPierce'` |

The shape of each algebra is what it contributes.  The chains `Fin 3` and
`Fin 4` are linear, and length is what tells the middle principles apart: the
lower classes survive every chain, while the De Morgan class dies once a chain
has two intermediate values.  The other three are not linear, and each differs
from the next in one parameter.  All three are `ForkUp m n` or `KiteUp m n`: a
root with two branches of the given lengths, the kite closing them off with a
tip.  `KiteUp 1 1` has that tip above its two incomparable middles, so the join
of those middles reaches the top; `ForkUp 1 1` has no tip, so it does not, and
that is why the fork separates the step the kite cannot.  `KiteUp 1 2` has a
tip again but reaches it by paths of different lengths, and that unevenness is
what the bottom step needs.
-/

/-- Nothing in this development is a theorem of bare intuitionistic logic.  It
is enough to say so for `PierceOrPierceF'`, since every other principle here
derives it: the fork with two long branches refutes it, so no derivation from no hypotheses
exists. -/
theorem pierceOrPierceF'_nderiv : ¬ ([] ⊢ pierceOrPierceForm') := by
  intro d
  exact pierceOrPierceForm'_nvalid_tallFork
    (Derives.valid_of_derives d (ForkUp 2 2)
      (fun n => if n = 0 then (ForkUp.tails 1 2 : ForkUp 2 2) else ForkUp.tails 2 1))

/-- Strictness below: no instantiation of `PierceOrLukasiewiczF` derives
`ImpOrOrLukasiewiczF'`. -/
theorem impOrOrLuk'_nderiv_pierceOrLuk :
    ¬ DerivesFromSchema pierceOrLukForm impOrOrLukForm' := fun h =>
  impOrOrLukForm'_nvalid_diamond (DerivesFromSchema.valid pierceOrLukForm_valid h _)

/-- Strictness above: no instantiation of `ImpOrOrLukasiewiczF'` derives
`DeMorganOrLukasiewiczF`. -/
theorem demorganOrLuk_nderiv_impOrOrLuk' :
    ¬ DerivesFromSchema impOrOrLukForm' demorganOrLukForm := fun h =>
  demorganOrLukForm_nvalid_four (DerivesFromSchema.valid impOrOrLukForm'_valid_chain h _)

/-- Strong as it is, `PeirceOrImpOrF'` still does not reach excluded middle: it
holds throughout `Fin 3`, where excluded middle does not. -/
theorem em_nderiv_peirceOrImpOr' :
    ¬ DerivesFromSchema peirceOrImpOrForm' (excludedMiddleForm (.var 0)) := fun h =>
  excludedMiddleForm_nvalid_three (DerivesFromSchema.valid peirceOrImpOrForm'_valid_three h _)

/-- The step from `DeMorganOrLukasiewiczF` up to `PeirceOrImpOrF'` is strict: no
instantiation of the former derives the latter, since the fork validates every
instance of the former and refutes one of the latter. -/
theorem peirceOrImpOr'_nderiv_demorganOrLuk :
    ¬ DerivesFromSchema demorganOrLukForm peirceOrImpOrForm' := fun h =>
  peirceOrImpOrForm'_nvalid_fork (DerivesFromSchema.valid demorganOrLukForm_valid_fork h _)

/-- The bottom step is strict too: no instantiation of `PierceOrPierceF'`
derives `PierceOrLukasiewiczF`, since the kite validates every instance of the
former and refutes one of the latter. -/
theorem pierceOrLuk_nderiv_pierceOrPierce' :
    ¬ DerivesFromSchema pierceOrPierceForm' pierceOrLukForm := fun h =>
  pierceOrLukForm_nvalid_kite (DerivesFromSchema.valid pierceOrPierceForm'_valid_kite h _)

