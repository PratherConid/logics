import Logics.IntermediateAxioms.Refuter.KCRefuter
import Logics.IntermediateAxioms.Refuter.NoDiamondRefuter

/-!
# Where `linearityForm` sits, exactly

Linearity, `(a → b) ∨ (b → a)`, is settled here the way `SmetanichRefuter`
settles its axiom, and for the same reason: it has *two* minimal refuters rather
than one.

**Which algebras separate it, and can they be shrunk?**  `ForkUp 1 1` and
`KiteUp 1 1` both refute it, neither is below the other, and nothing below
either one refutes it: `refuterLB_fork_linearity` and
`refuterLB_kite_linearity`.  The two are incomparable because each validates
what the other refutes -- weak excluded middle holds in the diamond and fails in
the fork, while `noDiamondForm` holds in the fork and fails in the diamond.

**Which schemas derive it?**  Exactly those missing the top value in both.  The
hard half is `sh_fork_or_kite_of_refutes_linearity`, and it needs no new
embedding: both constructions are already available, so the whole content is
the algebraic fact that

    weak excluded middle  +  `noDiamondForm`  =  linearity.

`linearity_of_weakEm_noDiamond` proves it in three cuts.  Each argument is
either refutable, and then one of the two implications holds vacuously, or
doubly negated; and once both are doubly negated, whichever disjunct of
`noDiamondForm` holds turns an excluded middle into the comparison itself,
because the unwanted half of that excluded middle is exactly what the double
negation rules out.  -/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

/-! # Part one: linearity is weak excluded middle with `noDiamondForm` -/

section Core

variable {α : Type} [HeytingAlgebra α]

/-- **Where the double negation does its work.**  An arrow into an excluded
middle, cut down by the double negation of its subject, is an arrow into the
subject: the other half of the excluded middle is ruled out. -/
theorem himp_sup_neg_inf_neg_neg (a b : α) :
    (a ⇨ (b ⊔ neg b)) ⊓ neg (neg b) ⊑ (a ⇨ b) := by
  refine le_himp_of_inf_le ?_
  refine sup_cases (le_trans (inf_le_inf (inf_le_left _ _) le_rfl)
    (himp_inf_le a (b ⊔ neg b))) (inf_le_left b _) ?_
  refine le_trans (inf_le_inf le_rfl (le_trans (inf_le_left _ _) (inf_le_right _ _))) ?_
  exact le_trans (le_of_eq (inf_neg_eq_bot (neg b))) (bot_le b)

/-- **Linearity is the conjunction of the two.**  Three cuts: on `a`, on `b`,
and then on `noDiamondForm`. -/
theorem linearity_of_weakEm_noDiamond
    (hkc : ∀ x : α, neg x ⊔ neg (neg x) = ⊤)
    (hnd : ∀ x y : α, (x ⇨ (y ⊔ neg y)) ⊔ (y ⇨ (x ⊔ neg x)) = ⊤)
    (a b : α) : (a ⇨ b) ⊔ (b ⇨ a) = ⊤ := by
  refine (eq_top_iff _).mpr ?_
  refine sup_cases (le_of_eq (hkc a).symm) ?_ ?_
  · exact le_trans (inf_le_left _ _) (le_trans (neg_le_himp a b) (le_sup_left _ _))
  refine sup_cases (le_trans (le_top _) (le_of_eq (hkc b).symm)) ?_ ?_
  · exact le_trans (inf_le_left _ _) (le_trans (neg_le_himp b a) (le_sup_right _ _))
  refine sup_cases (le_trans (le_top _) (le_of_eq (hnd a b).symm)) ?_ ?_
  · refine le_trans ?_ (le_sup_left (a ⇨ b) (b ⇨ a))
    exact le_trans (inf_le_inf le_rfl (inf_le_left _ _))
      (himp_sup_neg_inf_neg_neg a b)
  · refine le_trans ?_ (le_sup_right (a ⇨ b) (b ⇨ a))
    exact le_trans (inf_le_inf le_rfl
        (le_trans (inf_le_right _ _) (inf_le_left _ _)))
      (himp_sup_neg_inf_neg_neg b a)

end Core

/-- **Every algebra refuting linearity carries the fork or the diamond below
it.**  If weak excluded middle fails, the fork; otherwise, if `noDiamondForm`
fails, the diamond; and if neither fails, linearity held after all. -/
theorem sh_fork_or_kite_of_refutes_linearity (α : Type) (iα : HeytingAlgebra α)
    (h : ¬ ∀ v : Nat → α, (linearityForm (.var 0) (.var 1)).eval v = ⊤) :
    @SH (ForkUp 1 1) α _ iα ∨ @SH (KiteUp 1 1) α _ iα := by
  by_cases hkc : ∀ w : Nat → α, (weakEmForm (.var 0)).eval w = ⊤
  · by_cases hnd : ∀ w : Nat → α, (noDiamondForm (.var 0) (.var 1)).eval w = ⊤
    · refine absurd (fun v => ?_) h
      exact @linearity_of_weakEm_noDiamond α iα (fun x => hkc (fun _ => x))
        (fun x y => hnd (fun n => if n = 0 then x else y)) (v 0) (v 1)
    · exact Or.inr (sh_kite_of_refutes_noDiamond α iα hnd)
  · exact Or.inl (sh_forkUp_of_refutes_weakEm α iα hkc)

/-- **The criterion.**  A schema derives linearity exactly when it misses the
top value in both the fork and the diamond. -/
theorem derivesFromSchema_linearity_iff (X : Form) :
    DerivesFromSchema X (linearityForm (.var 0) (.var 1)) ↔
      (¬ ∀ w : Nat → ForkUp 1 1, X.eval w = ⊤) ∧
        (¬ ∀ w : Nat → KiteUp 1 1, X.eval w = ⊤) := by
  constructor
  · intro h
    exact ⟨fun hv => linearityForm_nvalid_fork (DerivesFromSchema.valid hv h _),
      fun hv => linearityForm_nvalid_kite (DerivesFromSchema.valid hv h _)⟩
  · exact fun hX => DerivesFromSchema.of_sh fun α iα hnv =>
      (sh_fork_or_kite_of_refutes_linearity α iα hnv).elim
        (fun hs => ⟨ForkUp 1 1, inferInstance, hs, hX.1⟩)
        (fun hs => ⟨KiteUp 1 1, inferInstance, hs, hX.2⟩)

/-! # Part two: neither refuter can be shrunk, and neither can be dropped -/

theorem linearity_fork_ge_coatom : ∀ a b : ForkUp 1 1,
    ((ForkUp.tails 0 0 : ForkUp 1 1) ⊓ ((a ⇨ b) ⊔ (b ⇨ a))) = ForkUp.tails 0 0 := by
  decide

theorem linearityForm_fork_eval_ge (v : Nat → ForkUp 1 1) :
    (ForkUp.tails 0 0 : ForkUp 1 1) ⊑ (linearityForm (.var 0) (.var 1)).eval v :=
  inf_eq_left_iff.mp (linearity_fork_ge_coatom (v 0) (v 1))

theorem linearity_fork_fail : ∀ a b : ForkUp 1 1, ((a ⇨ b) ⊔ (b ⇨ a)) ≠ ⊤ →
    ∀ z : ForkUp 1 1, z = ⊥ ∨ z = ⊤ ∨ z = a ∨ z = b ∨ z = a ⊔ b := by decide

/-- **Nothing below the fork refutes linearity.** -/
theorem refuterLB_fork_linearity : RefuterLB (ForkUp 1 1) (linearityForm (.var 0) (.var 1)) :=
  refuterLB_of_coatom fork_coatom' linearityForm_fork_eval_ge fun _ _ h _ v hv z => by
    have hfail := linearity_fork_fail _ _ hv
    rcases hfail z with hz | hz | hz | hz | hz
    · exact ⟨⊥, by rw [h.map_bot, hz]⟩
    · exact ⟨⊤, by rw [h.map_top, hz]⟩
    · exact ⟨v 0, hz.symm⟩
    · exact ⟨v 1, hz.symm⟩
    · exact ⟨v 0 ⊔ v 1, by rw [h.map_sup]; exact hz.symm⟩

theorem linearity_kite_ge_coatom : ∀ a b : KiteUp 1 1,
    ((KiteUp.tails 0 0 : KiteUp 1 1) ⊓ ((a ⇨ b) ⊔ (b ⇨ a))) = KiteUp.tails 0 0 := by
  decide

theorem linearityForm_kite_eval_ge (v : Nat → KiteUp 1 1) :
    (KiteUp.tails 0 0 : KiteUp 1 1) ⊑ (linearityForm (.var 0) (.var 1)).eval v :=
  inf_eq_left_iff.mp (linearity_kite_ge_coatom (v 0) (v 1))

theorem linearity_kite_fail : ∀ a b : KiteUp 1 1, ((a ⇨ b) ⊔ (b ⇨ a)) ≠ ⊤ →
    ∀ z : KiteUp 1 1, z = ⊥ ∨ z = ⊤ ∨ z = a ∨ z = b ∨ z = a ⊓ b ∨ z = a ⊔ b := by
  decide

/-- **Nothing below the diamond refutes linearity either.** -/
theorem refuterLB_kite_linearity : RefuterLB (KiteUp 1 1) (linearityForm (.var 0) (.var 1)) :=
  refuterLB_of_coatom kite_coatom' linearityForm_kite_eval_ge fun _ _ h _ v hv z => by
    have hfail := linearity_kite_fail _ _ hv
    rcases hfail z with hz | hz | hz | hz | hz | hz
    · exact ⟨⊥, by rw [h.map_bot, hz]⟩
    · exact ⟨⊤, by rw [h.map_top, hz]⟩
    · exact ⟨v 0, hz.symm⟩
    · exact ⟨v 1, hz.symm⟩
    · exact ⟨v 0 ⊓ v 1, by rw [h.map_inf]; exact hz.symm⟩
    · exact ⟨v 0 ⊔ v 1, by rw [h.map_sup]; exact hz.symm⟩

/-- The fork is not below the diamond: weak excluded middle holds in the
diamond and fails in the fork. -/
theorem not_sh_fork_kite : ¬ SH (ForkUp 1 1) (KiteUp 1 1) := fun h =>
  weakEmForm_nvalid_fork (valid_of_sh h weakEmForm_valid_kite _)

/-- The diamond is not below the fork: `noDiamondForm` holds in the fork and
fails in the diamond. -/
theorem not_sh_kite_fork : ¬ SH (KiteUp 1 1) (ForkUp 1 1) := fun h =>
  noDiamondForm_nvalid_diamond (valid_of_sh h noDiamondForm_valid_fork _)
