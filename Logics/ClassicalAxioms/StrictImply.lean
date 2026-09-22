import Logics.ClassicalAxioms.Model

/-!
# What the principles do not prove

Soundness, read backwards, turns the measurements of the previous file into
underivability: anything with a proof takes the top value under every
valuation, so a formula that misses the top value somewhere has no proof.

The first three theorems apply this to bare intuitionistic logic, where the
three element chain refutes excluded middle, double negation elimination and
Peirce's law outright.

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
| `PeirceOrImpOrF'` over `DeMorganOrLukasiewiczF` | `Fork` | `peirceOrImpOr'_nderiv_demorganOrLuk` |
| `DeMorganOrLukasiewiczF` over `ImpOrOrLukasiewiczF'` | `Fin 4` | `demorganOrLuk_nderiv_impOrOrLuk'` |
| `ImpOrOrLukasiewiczF'` over `PierceOrLukasiewiczF` | `Diamond` | `impOrOrLuk'_nderiv_pierceOrLuk` |

The shape of each algebra is what it contributes.  The chains `Fin 3` and
`Fin 4` are linear, and length is what tells the lower principles apart:
everything in the bottom two classes survives every chain, while the De Morgan
class dies once a chain has two intermediate values.  The `Diamond` and the
`Fork` are not linear, and they differ from each other in one respect: the
diamond has a top point above its two incomparable middles, so there the join
of those middles reaches the top, and in the fork it does not.  That single
difference is why the fork separates the step the diamond cannot.

`em_nderiv_peirceOrImpOr` records the bottom of the chain against the top
directly, rather than by composing the four steps.
-/

/-- Excluded middle is not derivable in intuitionistic propositional logic. -/
theorem em_nderiv : ¬ ([] ⊢ .or (.var 0) (Form.neg (.var 0))) := by
  intro d
  have h := Derives.valid_of_derives d (Fin 3) (fun _ => (1 : Fin 3))
  exact absurd h (by decide)

/-- Double negation elimination is not derivable either. -/
theorem dne_nderiv : ¬ ([] ⊢ .imp (Form.neg (Form.neg (.var 0))) (.var 0)) := by
  intro d
  have h := Derives.valid_of_derives d (Fin 3) (fun _ => (1 : Fin 3))
  exact absurd h (by decide)

/-- Nor is Peirce's law, the `PeirceF` of this file. -/
theorem peirce_nderiv :
    ¬ ([] ⊢ .imp (.imp (.imp (.var 0) (.var 1)) (.var 0)) (.var 0)) := by
  intro d
  have h := Derives.valid_of_derives d (Fin 3) (fun n => if n = 0 then 1 else 0)
  exact absurd h (by decide)

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

/-- No instantiation of `PeirceOrImpOrF` derives excluded middle: it reaches the
top value throughout `Fin 3`, where excluded middle does not. -/
theorem em_nderiv_peirceOrImpOr :
    ¬ DerivesFromSchema peirceOrImpOrForm (excludedMiddleForm (.var 0)) := fun h =>
  excludedMiddleForm_nvalid_three (DerivesFromSchema.valid peirceOrImpOrForm_valid_chain h _)

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

