import Logics.IntermediateAxioms.StrictImply
import Logics.Lindenbaum
import Logics.ConcreteEmbed

/-!
# Where `weakEmForm` sits, exactly

Weak excluded middle, `¬ a ∨ ¬ ¬ a`, is not one of the combined principles and
does not belong to their chain of levels; it sits beside it.  This file settles
it the way the other refuter files settle their axioms.

**Which algebra separates it, and can it be shrunk?**  `ForkUp 1 1` refutes it,
and nothing below the fork does: `refuterLB_fork_weakEm`.  A failing element `t`
generates the whole fork, since the five values are `⊥`, `⊤`, `neg t`,
`neg (neg t)` and their join, and a homomorphism reaches all of them from `t`
alone.

**Which schemas derive it?**  Exactly those missing the top value in the fork.
The hard half is already available: `forkUp_embeds` reads the fork off a single
element at which weak excluded middle fails, which is precisely a refutation of
this axiom.  So no new construction is needed here, only the two halves of the
criterion assembled.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

/-! # Part one: the fork cannot be shrunk -/

open HeytingAlgebra in
theorem weakEm_fork_ge_coatom : ∀ a : ForkUp 1 1,
    ((ForkUp.tails 0 0 : ForkUp 1 1) ⊓ (neg a ⊔ neg (neg a))) = ForkUp.tails 0 0 := by
  decide

theorem weakEmForm_eval_ge (v : Nat → ForkUp 1 1) :
    (ForkUp.tails 0 0 : ForkUp 1 1) ⊑ weakEmForm.eval v :=
  inf_eq_left_iff.mp (weakEm_fork_ge_coatom (v 0))

open HeytingAlgebra in
/-- A failing element generates the whole fork. -/
theorem weakEm_fork_fail : ∀ a : ForkUp 1 1, (neg a ⊔ neg (neg a)) ≠ ⊤ →
    ∀ z : ForkUp 1 1, z = ⊥ ∨ z = ⊤ ∨ z = neg a ∨ z = neg (neg a) ∨
      z = neg a ⊔ neg (neg a) := by decide

/-- **Nothing below the fork refutes `weakEmForm`.** -/
theorem refuterLB_fork_weakEm : RefuterLB (ForkUp 1 1) weakEmForm :=
  refuterLB_of_coatom fork_coatom' weakEmForm_eval_ge fun _ _ h _ v hv z => by
    have hfail := weakEm_fork_fail _ hv
    rcases hfail z with hz | hz | hz | hz | hz
    · exact ⟨⊥, by rw [h.map_bot, hz]⟩
    · exact ⟨⊤, by rw [h.map_top, hz]⟩
    · exact ⟨neg (v 0), by rw [h.map_neg]; exact hz.symm⟩
    · exact ⟨neg (neg (v 0)), by rw [h.map_neg, h.map_neg]; exact hz.symm⟩
    · exact ⟨neg (v 0) ⊔ neg (neg (v 0)),
        by rw [h.map_sup, h.map_neg, h.map_neg, h.map_neg]; exact hz.symm⟩

/-! # Part two: which schemas derive the axiom -/

/-- **Every algebra refuting `weakEmForm` carries the fork below it.**  This is
`forkUp_embeds` read through the axiom: a valuation refuting the schema is an
element at which weak excluded middle fails. -/
theorem sh_forkUp_of_refutes_weakEm (α : Type) (iα : HeytingAlgebra α)
    (h : ¬ ∀ v : Nat → α, weakEmForm.eval v = ⊤) : @SH (ForkUp 1 1) α _ iα := by
  obtain ⟨v, hv⟩ := @exists_ne_top α iα _ h
  exact @sh_forkUp α iα (v 0) hv

/-- **The criterion.**  A schema derives `weakEmForm` exactly when it misses the
top value in the fork. -/
theorem derivesFromSchema_weakEm_iff (X : Form) :
    DerivesFromSchema X weakEmForm ↔ ¬ ∀ w : Nat → ForkUp 1 1, X.eval w = ⊤ := by
  constructor
  · intro h hv
    exact weakEmForm_nvalid_fork (DerivesFromSchema.valid hv h _)
  · exact fun hX => DerivesFromSchema.of_sh fun α iα hnv =>
      ⟨ForkUp 1 1, inferInstance, sh_forkUp_of_refutes_weakEm α iα hnv, hX⟩
