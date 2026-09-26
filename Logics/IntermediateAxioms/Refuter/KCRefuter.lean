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

/-- **Nothing below the fork refutes `weakEmForm`.** -/
theorem refuterLB_fork_weakEm : RefuterLB (ForkUp 1 1) (weakEmForm (.var 0)) :=
  PointEmbed.refuterLB_of_generates (c := .tails 0 0)
    [.fls, Form.tru, Form.neg (.var 0), Form.neg (Form.neg (.var 0)),
      .or (Form.neg (.var 0)) (Form.neg (Form.neg (.var 0)))]
    (by decide) (by decide) fork_coatom' (by decide) (by decide)

/-! # Part two: which schemas derive the axiom -/

/-- **Every algebra refuting `weakEmForm` carries the fork below it.**  This is
`forkUp_embeds` read through the axiom: a valuation refuting the schema is an
element at which weak excluded middle fails. -/
theorem sh_forkUp_of_refutes_weakEm (α : Type) (iα : HeytingAlgebra α)
    (h : ¬ ∀ v : Nat → α, (weakEmForm (.var 0)).eval v = ⊤) : @SH (ForkUp 1 1) α _ iα := by
  obtain ⟨v, hv⟩ := @exists_ne_top α iα _ h
  exact @sh_forkUp α iα (v 0) hv

/-- **The criterion.**  A schema derives `weakEmForm` exactly when it misses the
top value in the fork. -/
theorem derivesFromSchema_weakEm_iff (X : Form) :
    DerivesFromSchema X (weakEmForm (.var 0)) ↔ ¬ ∀ w : Nat → ForkUp 1 1, X.eval w = ⊤ :=
  DerivesFromSchema.iff_of_refuter (fun hv => weakEmForm_nvalid_fork (hv _))
    sh_forkUp_of_refutes_weakEm X
