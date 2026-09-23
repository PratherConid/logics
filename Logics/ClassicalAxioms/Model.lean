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
`Fin 3`.  `KiteUp 1 1`, the diamond, is the smallest algebra that is *not* a
chain: its two
middle values `x` and `y` are incomparable.

The pattern that emerges is that the four combined principles fall into three
strengths.  `Pierce₁₂OrLukasiewicz₁₂F` reaches the top in every chain and in the
diamond.  `ImpOr₁₂OrLukasiewicz₂₁F` reaches it in every chain but not in the
diamond.  `DeMorgan₁₂OrLukasiewicz₁₂F` already misses it in the four value chain.
Excluded middle misses it in every chain past `Fin 2`.

The last four theorems restate some of this for `Form`, evaluating a whole
schema under a valuation rather than an expression under two arguments.
-/

open HeytingAlgebra in
/-- `Pierce₁₂OrLukasiewicz₁₂F` reaches the top value at every instance in *every*
chain, whatever its length.  The two cases are exactly the two disjuncts: when
`a ⊑ b` the Peirce disjunct reaches the top, and otherwise `b ⊑ a`, which sends
Lukasiewicz's conclusion `b ⇨ a` to the top. -/
theorem pierce₁₂OrLuk₁₂_top_chain {n : Nat} (a b : Fin (n + 1)) :
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
/-- `DeMorgan₁₂OrLukasiewicz₁₂F`, every instance. -/
theorem demorgan₁₂OrLuk₁₂_top (a b : Fin 3) :
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
/-- `ImpOr₁₂OrLukasiewicz₂₁F` reaches the top value in every chain, exactly as
`Pierce₁₂OrLukasiewicz₁₂F` does, and unlike `DeMorgan₁₂OrLukasiewicz₁₂F`, which already
fails in the four value chain.  So it cannot derive `DeMorgan₁₂OrLukasiewicz₁₂F`. -/
theorem impOr₁₂OrLuk₂₁_top_chain {n : Nat} (a b : Fin (n + 1)) :
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
/-- `Pierce₁₂OrLukasiewicz₂₁F` is not `Pierce₁₂OrLukasiewicz₁₂F`: swapping Lukasiewicz's
arguments costs it the four value chain, at `a = 2`, `b = 1`. -/
theorem pierce₁₂OrLuk₂₁F_not_top_four :
    ((((2 : Fin 4) ⇨ 1) ⇨ 2) ⇨ 2) ⊔ ((neg 1 ⇨ neg 2) ⇨ ((2 : Fin 4) ⇨ 1)) ≠ ⊤ := by
  decide

open HeytingAlgebra in
/-- `DeMorgan₁₂OrLukasiewicz₁₂F`, by contrast, drops to `q` at `a = p`, `b = q`. -/
theorem demorgan₁₂OrLuk₁₂_not_top_four :
    (neg (neg (1 : Fin 4) ⊓ neg 2) ⇨ ((1 : Fin 4) ⊔ 2))
      ⊔ ((neg 1 ⇨ neg 2) ⇨ ((2 : Fin 4) ⇨ 1)) ≠ ⊤ := by
  decide

open HeytingAlgebra in
/-- `Pierce₁₂OrLukasiewicz₁₂F` holds throughout the diamond, which is not a chain. -/
theorem pierce₁₂OrLuk₁₂_top_diamond : ∀ a b : KiteUp 1 1,
    (((a ⇨ b) ⇨ a) ⇨ a) ⊔ ((neg a ⇨ neg b) ⇨ (b ⇨ a)) = ⊤ := by decide

theorem pierce₁₂OrLuk₁₂Form_valid (v : Nat → KiteUp 1 1) : pierce₁₂OrLuk₁₂Form.eval v = ⊤ :=
  pierce₁₂OrLuk₁₂_top_diamond (v 0) (v 1)

/-- `ImpOr₁₂OrLukasiewicz₂₁F` does not: it drops below the top at `a = x`, `b = e`. -/
theorem impOr₁₂OrLuk₂₁Form_nvalid_diamond :
    impOr₁₂OrLuk₂₁Form.eval (fun n => if n = 0 then (KiteUp.tails 0 1 : KiteUp 1 1) else KiteUp.tails 1 1) ≠ ⊤ := by decide

theorem impOr₁₂OrLuk₂₁Form_valid_chain (v : Nat → Fin 4) : impOr₁₂OrLuk₂₁Form.eval v = ⊤ :=
  impOr₁₂OrLuk₂₁_top_chain (v 0) (v 1)

/-- `DeMorgan₁₂OrLukasiewicz₁₂F` already fails in the four value chain. -/
theorem demorgan₁₂OrLuk₁₂Form_nvalid_four :
    demorgan₁₂OrLuk₁₂Form.eval (fun n => if n = 0 then (1 : Fin 4) else 2) ≠ ⊤ := by decide

open HeytingAlgebra in
/-- `Peirce₁₂OrImpOr₁₂F` reaches the top value in every chain, by the two cases that
serve the other chain results: `a ⊑ b` sends Peirce to the top, and `b ⊑ a`
sends `ImpOrF` there, since then `a ⇨ b` is `b` and `b ⊑ ¬a ⊔ b`. -/
theorem peirce₁₂OrImpOr₁₂_top_chain {n : Nat} (a b : Fin (n + 1)) :
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

/-- Excluded middle, by contrast, misses the top value already in `Fin 3`. -/
theorem excludedMiddleForm_nvalid_three :
    (excludedMiddleForm (.var 0)).eval (fun _ => (1 : Fin 3)) ≠ ⊤ := by decide

open HeytingAlgebra in
/-- `Peirce₁₂OrImpOr₂₁F` still reaches the top value in the three value chain. -/
theorem peirce₁₂OrImpOr₂₁_top_three : ∀ a b : Fin 3,
    (((a ⇨ b) ⇨ a) ⇨ a) ⊔ ((b ⇨ a) ⇨ (neg b ⊔ a)) = ⊤ := by decide

theorem peirce₁₂OrImpOr₂₁Form_valid_three (v : Nat → Fin 3) :
    peirce₁₂OrImpOr₂₁Form.eval v = ⊤ := peirce₁₂OrImpOr₂₁_top_three (v 0) (v 1)

open HeytingAlgebra in
/-- But it already misses it in the four value chain, at `a = 2`, `b = 1`, where
every unswapped combined principle of this file still reaches the top. -/
theorem peirce₁₂OrImpOr₂₁_not_top_four :
    ((((2 : Fin 4) ⇨ 1) ⇨ 2) ⇨ 2) ⊔ (((1 : Fin 4) ⇨ 2) ⇨ (neg 1 ⊔ 2)) ≠ ⊤ := by decide

theorem peirce₁₂OrImpOr₂₁Form_nvalid_four :
    peirce₁₂OrImpOr₂₁Form.eval (fun n => if n = 0 then (2 : Fin 4) else 1) ≠ ⊤ := by decide

open HeytingAlgebra in
/-- `DeMorgan₁₂OrLukasiewicz₁₂F` reaches the top value throughout the fork. -/
theorem demorgan₁₂OrLuk₁₂_top_fork : ∀ a b : ForkUp 1 1,
    (neg (neg a ⊓ neg b) ⇨ (a ⊔ b)) ⊔ ((neg a ⇨ neg b) ⇨ (b ⇨ a)) = ⊤ := by decide

theorem demorgan₁₂OrLuk₁₂Form_valid_fork (v : Nat → ForkUp 1 1) : demorgan₁₂OrLuk₁₂Form.eval v = ⊤ :=
  demorgan₁₂OrLuk₁₂_top_fork (v 0) (v 1)

/-- `Peirce₁₂OrImpOr₂₁F` does not: it drops short at `a = tails 0 0`,
`b = tails 0 1`, where the two incomparable elements fail to join to the top. -/
theorem peirce₁₂OrImpOr₂₁Form_nvalid_fork :
    peirce₁₂OrImpOr₂₁Form.eval (fun n => if n = 0 then (ForkUp.tails 0 0 : ForkUp 1 1) else ForkUp.tails 0 1) ≠ ⊤ := by decide

open HeytingAlgebra in
/-- `Pierce₁₂OrPierce₂₁F` reaches the top value throughout the kite. -/
theorem pierce₁₂OrPierce₂₁_top_kite : ∀ a b : KiteUp 1 2,
    (((a ⇨ b) ⇨ a) ⇨ a) ⊔ (((b ⇨ a) ⇨ b) ⇨ b) = ⊤ := by decide

theorem pierce₁₂OrPierce₂₁Form_valid_kite (v : Nat → KiteUp 1 2) :
    pierce₁₂OrPierce₂₁Form.eval v = ⊤ := pierce₁₂OrPierce₂₁_top_kite (v 0) (v 1)

/-- `Pierce₁₂OrLukasiewicz₁₂F` does not: it drops below the top at `a = m5`,
`b = m3`, the two elements the uneven paths pull apart. -/
theorem pierce₁₂OrLuk₁₂Form_nvalid_kite :
    pierce₁₂OrLuk₁₂Form.eval (fun n => if n = 0 then (KiteUp.tails 1 1 : KiteUp 1 2) else KiteUp.tails 0 2) ≠ ⊤ := by decide

/-- Even `Pierce₁₂OrPierce₂₁F`, the weakest principle of this development, misses
the top value in the tall fork, at `a = m1`, `b = m2` -- the two branch tips. -/
theorem pierce₁₂OrPierce₂₁Form_nvalid_tallFork :
    pierce₁₂OrPierce₂₁Form.eval (fun n => if n = 0 then (ForkUp.tails 1 2 : ForkUp 2 2) else ForkUp.tails 2 1) ≠ ⊤ := by
  decide

