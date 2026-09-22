import Logics.ClassicalAxioms.Model

/-!
# What the principles do not prove

Soundness, read backwards, turns the measurements of the previous file into
underivability: anything with a proof takes the top value under every
valuation, so a formula that misses the top value somewhere has no proof.

The first three theorems apply this to bare intuitionistic logic, where the
three element chain refutes excluded middle, double negation elimination and
Peirce's law outright.

The last two say something stronger, about a principle assumed as an *axiom
schema*.  `DerivesFromSchema X p` holds when some finite list of substitution
instances of `X` derives `p`, and `DerivesFromSchema.valid` says an algebra
validating `X` validates everything the schema derives.  So a single algebra
validating `X` but not `p` rules out every instantiation of `X` at once, which
is what "strictly weaker" needs.  Together with the derivations in
`Logics/ClassicalAxioms/Implication.lean`, they place the combined principles in
a strict chain:

`DeMorganOrLukasiewiczF ⊋ ImpOrOrLukasiewiczF' ⊋ PierceOrLukasiewiczF`

with the diamond separating the lower step and the four value chain the upper.
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

