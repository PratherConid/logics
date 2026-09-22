import Logics.ClassicalAxioms.Implication

/-!
# The principles in concrete Heyting algebras

A Heyting algebra is a set of truth values richer than `{false, true}`, and
measuring a principle against one says how classical it is: a principle reaches
the top value at every pair of truth values exactly when nothing about that
algebra refutes it.

Two families of algebra are enough for everything below.  The chains `Fin k`
order their values `0 ⊏ 1 ⊏ ⋯`, with the middle values meaning "neither
established nor refuted"; negating any of them lands on the bottom, since
nothing refutes them, which is why excluded middle already misses the top in
`Fin 3`.  The `Diamond` is the smallest algebra that is *not* a chain: its two
middle values `x` and `y` are incomparable.

The pattern that emerges is that the four combined principles fall into three
strengths.  `PierceOrLukasiewiczF` reaches the top in every chain and in the
diamond.  `ImpOrOrLukasiewiczF'` reaches it in every chain but not in the
diamond.  `DeMorganOrLukasiewiczF` already misses it in the four value chain.
Excluded middle misses it in every chain past `Fin 2`.

The last four theorems restate some of this for `Form`, evaluating a whole
schema under a valuation rather than an expression under two arguments.
-/

open HeytingAlgebra in
/-- `PierceOrLukasiewiczF` reaches the top value at every instance in *every*
chain, whatever its length.  The two cases are exactly the two disjuncts: when
`a ⊑ b` the Peirce disjunct reaches the top, and otherwise `b ⊑ a`, which sends
Lukasiewicz's conclusion `b ⇨ a` to the top. -/
theorem pierceOrLuk_top_chain {n : Nat} (a b : Fin (n + 1)) :
    (((a ⇨ b) ⇨ a) ⇨ a) ⊔ ((neg a ⇨ neg b) ⇨ (b ⇨ a)) = ⊤ := by
  by_cases hab : a.val ≤ b.val
  · have h1 : (a ⇨ b) = ⊤ := (Chain.himp_eq_top_iff a b).mpr hab
    have h2 : (((a ⇨ b) ⇨ a) ⇨ a) = ⊤ := by
      rw [h1]
      exact (Chain.himp_eq_top_iff _ _).mpr (Chain.himp_top_left_le a)
    rw [h2, BoundedLattice.top_sup]
  · have h1 : (b ⇨ a) = ⊤ := (Chain.himp_eq_top_iff b a).mpr (by omega)
    have h2 : ((neg a ⇨ neg b) ⇨ (b ⇨ a)) = ⊤ := by
      rw [h1]; exact Chain.himp_top_right _
    rw [h2, BoundedLattice.sup_top]

open HeytingAlgebra in
/-- `DeMorganOrLukasiewiczF`, every instance. -/
theorem demorganOrLuk_top (a b : Fin 3) :
    (neg (neg a ⊓ neg b) ⇨ (a ⊔ b)) ⊔ ((neg a ⇨ neg b) ⇨ (b ⇨ a)) = ⊤ := by
  revert a b; decide

open HeytingAlgebra in
/-- `ExcludedMiddleF`, by contrast, is not `⊤` throughout: it drops to `m`. -/
theorem em_not_top : ∃ a : Fin 3, a ⊔ neg a ≠ ⊤ :=
  ⟨1, Chain.em_fails (by decide) (by decide)⟩

open HeytingAlgebra in
/-- Excluded middle fails in every chain with more than two values. -/
theorem em_not_top_chain {n : Nat} (hn : 2 ≤ n) : ∃ a : Fin (n + 1), a ⊔ neg a ≠ ⊤ :=
  ⟨⟨1, by omega⟩, Chain.em_fails Nat.zero_lt_one (by omega : 1 < n)⟩

open HeytingAlgebra in
/-- `ImpOrOrLukasiewiczF'` reaches the top value in every chain, exactly as
`PierceOrLukasiewiczF` does, and unlike `DeMorganOrLukasiewiczF`, which already
fails in the four value chain.  So it cannot derive `DeMorganOrLukasiewiczF`. -/
theorem impOrOrLuk'_top_chain {n : Nat} (a b : Fin (n + 1)) :
    ((a ⇨ b) ⇨ (neg a ⊔ b)) ⊔ ((neg b ⇨ neg a) ⇨ (a ⇨ b)) = ⊤ := by
  by_cases hab : a.val ≤ b.val
  · have h1 : (a ⇨ b) = ⊤ := (Chain.himp_eq_top_iff a b).mpr hab
    have h2 : ((neg b ⇨ neg a) ⇨ (a ⇨ b)) = ⊤ := by rw [h1]; exact Chain.himp_top_right _
    rw [h2, BoundedLattice.sup_top]
  · have hne : (a ⇨ b) = b := Chain.himp_eq_of_not_le hab
    have h1 : ((a ⇨ b) ⇨ (neg a ⊔ b)) = ⊤ := by
      rw [hne]; exact (Chain.himp_eq_top_iff _ _).mpr (Lattice.le_sup_right (neg a) b)
    rw [h1, BoundedLattice.top_sup]

open HeytingAlgebra in
/-- `PierceOrLukasiewiczF'` is not `PierceOrLukasiewiczF`: swapping Lukasiewicz's
arguments costs it the four value chain, at `a = 2`, `b = 1`. -/
theorem pierceOrLukF'_not_top_four :
    ((((2 : Fin 4) ⇨ 1) ⇨ 2) ⇨ 2) ⊔ ((neg 1 ⇨ neg 2) ⇨ ((2 : Fin 4) ⇨ 1)) ≠ ⊤ := by
  decide

open HeytingAlgebra in
/-- `DeMorganOrLukasiewiczF`, by contrast, drops to `q` at `a = p`, `b = q`. -/
theorem demorganOrLuk_not_top_four :
    (neg (neg (1 : Fin 4) ⊓ neg 2) ⇨ ((1 : Fin 4) ⊔ 2))
      ⊔ ((neg 1 ⇨ neg 2) ⇨ ((2 : Fin 4) ⇨ 1)) ≠ ⊤ := by
  decide

open HeytingAlgebra in
/-- `PierceOrLukasiewiczF` holds throughout the diamond, which is not a chain. -/
theorem pierceOrLuk_top_diamond : ∀ a b : Diamond,
    (((a ⇨ b) ⇨ a) ⇨ a) ⊔ ((neg a ⇨ neg b) ⇨ (b ⇨ a)) = ⊤ := by decide

theorem pierceOrLukForm_valid (v : Nat → Diamond) : pierceOrLukForm.eval v = ⊤ :=
  pierceOrLuk_top_diamond (v 0) (v 1)

/-- `ImpOrOrLukasiewiczF'` does not: it drops below the top at `a = x`, `b = e`. -/
theorem impOrOrLukForm'_nvalid_diamond :
    impOrOrLukForm'.eval (fun n => if n = 0 then Diamond.x else Diamond.e) ≠ ⊤ := by decide

theorem impOrOrLukForm'_valid_chain (v : Nat → Fin 4) : impOrOrLukForm'.eval v = ⊤ :=
  impOrOrLuk'_top_chain (v 0) (v 1)

/-- `DeMorganOrLukasiewiczF` already fails in the four value chain. -/
theorem demorganOrLukForm_nvalid_four :
    demorganOrLukForm.eval (fun n => if n = 0 then (1 : Fin 4) else 2) ≠ ⊤ := by decide

open HeytingAlgebra in
/-- `PeirceOrImpOrF` reaches the top value in every chain, by the two cases that
serve the other chain results: `a ⊑ b` sends Peirce to the top, and `b ⊑ a`
sends `ImpOrF` there, since then `a ⇨ b` is `b` and `b ⊑ ¬a ⊔ b`. -/
theorem peirceOrImpOr_top_chain {n : Nat} (a b : Fin (n + 1)) :
    (((a ⇨ b) ⇨ a) ⇨ a) ⊔ ((a ⇨ b) ⇨ (neg a ⊔ b)) = ⊤ := by
  by_cases hab : a.val ≤ b.val
  · have h1 : (a ⇨ b) = ⊤ := (Chain.himp_eq_top_iff a b).mpr hab
    have h2 : (((a ⇨ b) ⇨ a) ⇨ a) = ⊤ := by
      rw [h1]; exact (Chain.himp_eq_top_iff _ _).mpr (Chain.himp_top_left_le a)
    rw [h2, BoundedLattice.top_sup]
  · have hne : (a ⇨ b) = b := Chain.himp_eq_of_not_le hab
    have h1 : ((a ⇨ b) ⇨ (neg a ⊔ b)) = ⊤ := by
      rw [hne]; exact (Chain.himp_eq_top_iff _ _).mpr (Lattice.le_sup_right (neg a) b)
    rw [h1, BoundedLattice.sup_top]

theorem peirceOrImpOrForm_valid_chain (v : Nat → Fin 3) : peirceOrImpOrForm.eval v = ⊤ :=
  peirceOrImpOr_top_chain (v 0) (v 1)

/-- Excluded middle, by contrast, misses the top value already in `Fin 3`. -/
theorem excludedMiddleForm_nvalid_three :
    (excludedMiddleForm (.var 0)).eval (fun _ => (1 : Fin 3)) ≠ ⊤ := by decide

