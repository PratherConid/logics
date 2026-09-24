import Logics.IntermediateAxioms.Implication

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

The pattern that emerges is that the principles fall into three strengths.
`Pierce₁₂OrLukasiewicz₁₂F` reaches the top in every chain and in the diamond.
`NoDiamondF` reaches it in every chain but not in the diamond, which is what
its level is.  `DeMorgan₁₂OrLukasiewicz₁₂F` already misses it in the four value
chain, and excluded middle already in `Fin 3`.

Most measurements come in two shapes: an equation between elements, and the
same fact for `Form`, evaluating a whole schema under a valuation rather than
an expression under two arguments.  Every one of them has a consumer, in the
separation proofs of `StrictImply` or in the `Refuter` files; a measurement
worth keeping is one some argument rests on.
-/

open HeytingAlgebra in
/-- `Pierce₁₂OrLukasiewicz₁₂F` holds throughout the diamond, which is not a chain. -/
theorem pierce₁₂OrLuk₁₂_top_diamond : ∀ a b : KiteUp 1 1,
    (((a ⇨ b) ⇨ a) ⇨ a) ⊔ ((neg a ⇨ neg b) ⇨ (b ⇨ a)) = ⊤ := by decide

theorem pierce₁₂OrLuk₁₂Form_valid (v : Nat → KiteUp 1 1) : pierce₁₂OrLuk₁₂Form.eval v = ⊤ :=
  pierce₁₂OrLuk₁₂_top_diamond (v 0) (v 1)

open HeytingAlgebra in
/-- `NoDiamondF` reaches the top value in every chain, and for the plainest of
reasons: one argument lies below the other, so it lies below the other's join
with its negation, which sends that disjunct to the top. -/
theorem noDiamond_top_chain {n : Nat} (a b : Fin (n + 1)) :
    (a ⇨ (b ⊔ neg b)) ⊔ (b ⇨ (a ⊔ neg a)) = ⊤ := by
  by_cases hab : a.val ≤ b.val
  · have h : (a ⇨ (b ⊔ neg b)) = ⊤ :=
      himp_eq_top_of_le (PartialOrder.le_trans hab (Lattice.le_sup_left b (neg b)))
    rw [h, BoundedLattice.top_sup]
  · have h : (b ⇨ (a ⊔ neg a)) = ⊤ :=
      himp_eq_top_of_le (PartialOrder.le_trans (show b.val ≤ a.val by omega)
        (Lattice.le_sup_left a (neg a)))
    rw [h, BoundedLattice.sup_top]

theorem noDiamondForm_valid_chain (v : Nat → Fin 4) : noDiamondForm.eval v = ⊤ :=
  noDiamond_top_chain (v 0) (v 1)

/-- It misses the top in the diamond, at the two incomparable middle values.
There each disjunct's negation is the bottom, so each is the arrow between the
two values, and the two arrows join to the largest value below the top. -/
theorem noDiamondForm_nvalid_diamond :
    noDiamondForm.eval (fun n => if n = 0 then (KiteUp.tails 0 1 : KiteUp 1 1)
      else KiteUp.tails 1 0) ≠ ⊤ := by decide

/-! ### Linearity and weak excluded middle

Neither is a combination of two principles, and neither is classical; both are
measured here because they separate the same algebras the combined principles
do. -/

theorem linearity_chain {n : Nat} : ∀ a b : Fin (n + 1), (a ⇨ b) ⊔ (b ⇨ a) = ⊤ := by
  intro a b
  by_cases hab : a.val ≤ b.val
  · rw [(Chain.himp_eq_top_iff a b).mpr hab, BoundedLattice.top_sup]
  · rw [(Chain.himp_eq_top_iff b a).mpr (by omega), BoundedLattice.sup_top]

theorem linearityForm_valid_chain {n : Nat} (v : Nat → Fin (n + 1)) :
    linearityForm.eval v = ⊤ := linearity_chain (v 0) (v 1)

/-- Linearity fails in the fork, at its two incomparable middles. -/
theorem linearityForm_nvalid_fork :
    linearityForm.eval (fun n => if n = 0 then (ForkUp.tails 0 1 : ForkUp 1 1)
      else ForkUp.tails 1 0) ≠ ⊤ := by decide

/-- And in the diamond, at its two incomparable middles. -/
theorem linearityForm_nvalid_kite :
    linearityForm.eval (fun n => if n = 0 then (KiteUp.tails 0 1 : KiteUp 1 1)
      else KiteUp.tails 1 0) ≠ ⊤ := by decide

open HeytingAlgebra in
/-- It holds in the diamond too: the tip makes every nonempty value dense. -/
theorem weakEm_kite : ∀ a : KiteUp 1 1, neg a ⊔ neg (neg a) = ⊤ := by decide

theorem weakEmForm_valid_kite (v : Nat → KiteUp 1 1) : weakEmForm.eval v = ⊤ :=
  weakEm_kite (v 0)

/-- But it fails in the fork, which is what the fork is for. -/
theorem weakEmForm_nvalid_fork :
    weakEmForm.eval (fun _ => (ForkUp.tails 0 1 : ForkUp 1 1)) ≠ ⊤ := by decide

/-! ### Bounded depth and the diamond -/

open HeytingAlgebra in
theorem depthTwo_fork : ∀ a b : ForkUp 1 1, a ⊔ (a ⇨ (b ⊔ neg b)) = ⊤ := by decide

theorem bd2Form_valid_fork (v : Nat → ForkUp 1 1) : bd2Form.eval v = ⊤ :=
  depthTwo_fork (v 0) (v 1)

theorem bd2Form_nvalid_four :
    bd2Form.eval (fun n => if n = 0 then (2 : Fin 4) else 1) ≠ ⊤ := by decide

open HeytingAlgebra in
/-- `NoDiamondF` holds throughout the fork, bounded depth two being stronger. -/
theorem noDiamond_fork : ∀ a b : ForkUp 1 1,
    (a ⇨ (b ⊔ neg b)) ⊔ (b ⇨ (a ⊔ neg a)) = ⊤ := by decide

theorem noDiamondForm_valid_fork (v : Nat → ForkUp 1 1) :
    noDiamondForm.eval v = ⊤ := noDiamond_fork (v 0) (v 1)

/-! ### What the even kite sees

Weak excluded middle holds in every kite, the tip making the frame directed,
which is how the kite tells it apart from the levels of the chain. -/

open HeytingAlgebra in
theorem weakEm_kite22 : ∀ a : KiteUp 2 2, neg a ⊔ neg (neg a) = ⊤ := by decide

theorem weakEmForm_valid_kite22 (v : Nat → KiteUp 2 2) : weakEmForm.eval v = ⊤ :=
  weakEm_kite22 (v 0)

/-- The even kite with two step branches refutes even the weakest principle of
the chain. -/
theorem pierce₁₂OrPierce₂₁Form_nvalid_kite22 :
    pierce₁₂OrPierce₂₁Form.eval (fun n => if n = 0 then (KiteUp.tails 1 2 : KiteUp 2 2)
      else KiteUp.tails 2 1) ≠ ⊤ := by decide

/-- Smetanich's axiom fails in the four value chain, at `a = 2`, `b = 1`. -/
theorem smetanichForm_nvalid_four :
    smetanichForm.eval (fun n => if n = 0 then (2 : Fin 4) else 1) ≠ ⊤ := by decide

/-- And in the fork and the diamond, both of which it therefore separates. -/
theorem smetanichForm_nvalid_fork :
    smetanichForm.eval (fun n => if n = 0 then (ForkUp.tails 0 0 : ForkUp 1 1)
      else ForkUp.tails 0 1) ≠ ⊤ := by decide

theorem smetanichForm_nvalid_kite :
    smetanichForm.eval (fun n => if n = 0 then (KiteUp.tails 0 0 : KiteUp 1 1)
      else KiteUp.tails 0 1) ≠ ⊤ := by decide

/-- `DeMorgan₁₂OrLukasiewicz₁₂F` already fails in the four value chain. -/
theorem demorgan₁₂OrLuk₁₂Form_nvalid_four :
    demorgan₁₂OrLuk₁₂Form.eval (fun n => if n = 0 then (1 : Fin 4) else 2) ≠ ⊤ := by decide

/-- Excluded middle, by contrast, misses the top value already in `Fin 3`. -/
theorem excludedMiddleForm_nvalid_three :
    (excludedMiddleForm (.var 0)).eval (fun _ => (1 : Fin 3)) ≠ ⊤ := by decide

open HeytingAlgebra in
/-- `Peirce₁₂OrImpOr₂₁F` still reaches the top value in the three value chain. -/
theorem peirce₁₂OrImpOr₂₁_top_three : ∀ a b : Fin 3,
    (((a ⇨ b) ⇨ a) ⇨ a) ⊔ ((b ⇨ a) ⇨ (neg b ⊔ a)) = ⊤ := by decide

theorem peirce₁₂OrImpOr₂₁Form_valid_three (v : Nat → Fin 3) :
    peirce₁₂OrImpOr₂₁Form.eval v = ⊤ := peirce₁₂OrImpOr₂₁_top_three (v 0) (v 1)

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

/-! ### Scott's axiom

It survives the chains, the fork with two single step branches, and the kites,
and falls only when a branch is longer than a step: the uneven fork is what
separates it. -/

open HeytingAlgebra in
theorem scott_four : ∀ a : Fin 4,
    (((neg (neg a) ⇨ a) ⇨ (a ⊔ neg a)) ⇨ (neg a ⊔ neg (neg a))) = ⊤ := by decide

theorem scottForm_valid_four (v : Nat → Fin 4) : scottForm.eval v = ⊤ :=
  scott_four (v 0)

open HeytingAlgebra in
theorem scott_fork : ∀ a : ForkUp 1 1,
    (((neg (neg a) ⇨ a) ⇨ (a ⊔ neg a)) ⇨ (neg a ⊔ neg (neg a))) = ⊤ := by decide

theorem scottForm_valid_fork (v : Nat → ForkUp 1 1) : scottForm.eval v = ⊤ :=
  scott_fork (v 0)

open HeytingAlgebra in
theorem scott_kite22 : ∀ a : KiteUp 2 2,
    (((neg (neg a) ⇨ a) ⇨ (a ⊔ neg a)) ⇨ (neg a ⊔ neg (neg a))) = ⊤ := by decide

theorem scottForm_valid_kite22 (v : Nat → KiteUp 2 2) : scottForm.eval v = ⊤ :=
  scott_kite22 (v 0)

/-- But it fails in the uneven fork, at the tip of the longer branch. -/
theorem scottForm_nvalid_fork12 :
    scottForm.eval (fun _ => (ForkUp.tails 1 1 : ForkUp 1 2)) ≠ ⊤ := by decide

open HeytingAlgebra in
/-- `NoDiamondF` survives the uneven fork, which is how the two are told
apart. -/
theorem noDiamond_fork12 : ∀ a b : ForkUp 1 2,
    (a ⇨ (b ⊔ neg b)) ⊔ (b ⇨ (a ⊔ neg a)) = ⊤ := by decide

theorem noDiamondForm_valid_fork12 (v : Nat → ForkUp 1 2) :
    noDiamondForm.eval v = ⊤ := noDiamond_fork12 (v 0) (v 1)

/-! ### Kreisel and Putnam's axiom

Two branches never refute it, so the algebras of the rest of this file all
validate it; the three branch fork is what it takes.  There the negation of one
branch tip is the join of the other two, so a disjunction proved from that
negation need not have either disjunct proved from it. -/

open HeytingAlgebra in
theorem kreiselPutnam_four : ∀ a b c : Fin 4,
    ((neg a ⇨ (b ⊔ c)) ⇨ ((neg a ⇨ b) ⊔ (neg a ⇨ c))) = ⊤ := by decide

theorem kreiselPutnamForm_valid_four (v : Nat → Fin 4) :
    kreiselPutnamForm.eval v = ⊤ := kreiselPutnam_four (v 0) (v 1) (v 2)

open HeytingAlgebra in
theorem kreiselPutnam_fork : ∀ a b c : ForkUp 1 1,
    ((neg a ⇨ (b ⊔ c)) ⇨ ((neg a ⇨ b) ⊔ (neg a ⇨ c))) = ⊤ := by decide

theorem kreiselPutnamForm_valid_fork (v : Nat → ForkUp 1 1) :
    kreiselPutnamForm.eval v = ⊤ := kreiselPutnam_fork (v 0) (v 1) (v 2)

open HeytingAlgebra in
theorem kreiselPutnam_kite22 : ∀ a b c : KiteUp 2 2,
    ((neg a ⇨ (b ⊔ c)) ⇨ ((neg a ⇨ b) ⊔ (neg a ⇨ c))) = ⊤ := by decide

theorem kreiselPutnamForm_valid_kite22 (v : Nat → KiteUp 2 2) :
    kreiselPutnamForm.eval v = ⊤ := kreiselPutnam_kite22 (v 0) (v 1) (v 2)

/-- It fails in the three branch fork, at the three branch tips. -/
theorem kreiselPutnamForm_nvalid_fork3 :
    kreiselPutnamForm.eval (fun n =>
      if n = 0 then (ForkUp3.tails 0 1 1 : ForkUp3 1 1 1)
      else if n = 1 then ForkUp3.tails 1 0 1
      else ForkUp3.tails 1 1 0) ≠ ⊤ := by decide

open HeytingAlgebra in
/-- Bounded depth two survives there, the fork having depth two however many
branches it has. -/
theorem bd2_fork3 : ∀ a b : ForkUp3 1 1 1, a ⊔ (a ⇨ (b ⊔ neg b)) = ⊤ := by decide

theorem bd2Form_valid_fork3 (v : Nat → ForkUp3 1 1 1) : bd2Form.eval v = ⊤ :=
  bd2_fork3 (v 0) (v 1)
