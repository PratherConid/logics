import Logics.IntermediateAxioms.StrictImply
import Logics.Lindenbaum
import Logics.ConcreteEmbed
import Logics.Filter

/-!
# How far `ScottF` can be shrunk

Scott's axiom is refuted by `ForkUp 1 2`, the fork with one branch a single
step and the other two steps, and this file shows that nothing below the uneven
fork refutes it: `refuterLB_fork12_scott`.  A failing element `t` generates the
whole seven value algebra, the values being `⊥`, `⊤`, and

    `neg t`,  `t`,  `t ⊔ neg t`,  `neg (neg t)`,  `neg t ⊔ neg (neg t)`,

so a homomorphism reaches all of them from `t` alone.  The short branch
contributes `neg t` and the long one `t` under `neg (neg t)`, which is what
makes the branch lengths uneven.

**Which schemas derive it?**  Exactly those missing the top value in the uneven
fork.  That rests on `sh_fork12_of_scott_fails`, and the route there is worth
spelling out, because reading the seven values straight off the refuting
element does *not* work: what the embedding needs is

    `neg (neg t) ⇨ t  =  t ⊔ neg t`,

and a refutation of `ScottF` only says that this arrow's value does not lie
below `neg t ⊔ neg (neg t)`, not that it is the top.  In a product of two
algebras it need not be, and then the seven values are not closed under the
arrow.

The fix is to stop insisting on the algebra one started in.  The order on
algebras allows a homomorphic image, so quotient by the filter above that
arrow's value: there it becomes the top by construction, the identity above
holds, and the refutation survives, since the value that the arrow fails to
reach is exactly the one the filter cannot raise to the top either.  So the
fork embeds in the quotient, and `SH` asks for no more than that.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

/-- The uneven fork's largest value below the top. -/
theorem fork12_coatom : ∀ x : ForkUp 1 2,
    x ≠ ⊤ → x ⊓ (ForkUp.tails 0 0 : ForkUp 1 2) = x := by decide

theorem fork12_coatom' (x : ForkUp 1 2) (h : x ≠ ⊤) :
    x ⊑ (ForkUp.tails 0 0 : ForkUp 1 2) := inf_eq_left_iff.mp (fork12_coatom x h)

open HeytingAlgebra in
theorem scott_fork12_ge_coatom : ∀ a : ForkUp 1 2,
    ((ForkUp.tails 0 0 : ForkUp 1 2) ⊓
      (((neg (neg a) ⇨ a) ⇨ (a ⊔ neg a)) ⇨ (neg a ⊔ neg (neg a))))
      = ForkUp.tails 0 0 := by decide

theorem scottForm_fork12_eval_ge (v : Nat → ForkUp 1 2) :
    (ForkUp.tails 0 0 : ForkUp 1 2) ⊑ scottForm.eval v :=
  inf_eq_left_iff.mp (scott_fork12_ge_coatom (v 0))

open HeytingAlgebra in
/-- A failing element generates the whole uneven fork. -/
theorem scott_fork12_fail : ∀ a : ForkUp 1 2,
    (((neg (neg a) ⇨ a) ⇨ (a ⊔ neg a)) ⇨ (neg a ⊔ neg (neg a))) ≠ ⊤ →
      ∀ z : ForkUp 1 2, z = ⊥ ∨ z = ⊤ ∨ z = neg a ∨ z = a ∨ z = a ⊔ neg a ∨
        z = neg (neg a) ∨ z = neg a ⊔ neg (neg a) := by decide

/-- **Nothing below the uneven fork refutes `ScottF`.** -/
theorem refuterLB_fork12_scott : RefuterLB (ForkUp 1 2) scottForm :=
  refuterLB_of_coatom fork12_coatom' scottForm_fork12_eval_ge fun _ _ h _ v hv z => by
    have hfail := scott_fork12_fail _ hv
    rcases hfail z with hz | hz | hz | hz | hz | hz | hz
    · exact ⟨⊥, by rw [h.map_bot, hz]⟩
    · exact ⟨⊤, by rw [h.map_top, hz]⟩
    · exact ⟨neg (v 0), by rw [h.map_neg]; exact hz.symm⟩
    · exact ⟨v 0, hz.symm⟩
    · exact ⟨v 0 ⊔ neg (v 0), by rw [h.map_sup, h.map_neg]; exact hz.symm⟩
    · exact ⟨neg (neg (v 0)), by rw [h.map_neg, h.map_neg]; exact hz.symm⟩
    · exact ⟨neg (v 0) ⊔ neg (neg (v 0)),
        by rw [h.map_sup, h.map_neg, h.map_neg, h.map_neg]; exact hz.symm⟩

/-! # Part two: which schemas derive the axiom -/

/-- **Every algebra refuting `ScottF` carries the uneven fork below it.**

The quotient by the filter above `A`, the value of Scott's antecedent, sends
`A` to the top, which is exactly the identity the embedding needs; and it does
not send the consequent there, since that would say `A` lies below it, which is
what the refutation denies. -/
theorem sh_fork12_of_scott_fails {α : Type} [HeytingAlgebra α] (t : α)
    (hv : (((neg (neg t) ⇨ t) ⇨ (t ⊔ neg t)) ⇨ (neg t ⊔ neg (neg t))) ≠ ⊤) :
    SH (ForkUp 1 2) α := by
  refine ⟨FilterQuot (Filter.up ((neg (neg t) ⇨ t) ⇨ (t ⊔ neg t))), inferInstance,
    FilterQuot.onto _, ?_⟩
  refine fork12_embeds (s := FilterQuot.mk _ t) ?_ ?_
  · have htop : FilterQuot.mk (Filter.up ((neg (neg t) ⇨ t) ⇨ (t ⊔ neg t)))
        ((neg (neg t) ⇨ t) ⇨ (t ⊔ neg t)) = ⊤ :=
      (FilterQuot.mk_eq_top_iff _ _).mpr le_rfl
    refine le_antisymm (le_trans (le_of_himp_eq_top htop) (le_of_eq (sup_comm _ _))) ?_
    refine sup_le ?_ (le_himp_self _ _)
    exact le_himp_of_inf_le (le_trans (le_of_eq (inf_neg_eq_bot _)) (bot_le _))
  · intro he
    exact hv (himp_eq_top_of_le
      (Filter.up_mem.mp ((FilterQuot.mk_eq_top_iff _ _).mp he)))

theorem sh_fork12_of_refutes_scott (α : Type) (iα : HeytingAlgebra α)
    (h : ¬ ∀ v : Nat → α, scottForm.eval v = ⊤) : @SH (ForkUp 1 2) α _ iα := by
  obtain ⟨v, hv⟩ := @exists_ne_top α iα _ h
  exact @sh_fork12_of_scott_fails α iα (v 0) hv

/-- **The criterion.**  A schema derives `ScottF` exactly when it misses the top
value in the uneven fork. -/
theorem derivesFromSchema_scott_iff (X : Form) :
    DerivesFromSchema X scottForm ↔ ¬ ∀ w : Nat → ForkUp 1 2, X.eval w = ⊤ := by
  constructor
  · intro h hv
    exact scottForm_nvalid_fork12 (DerivesFromSchema.valid hv h _)
  · exact fun hX => DerivesFromSchema.of_sh fun α iα hnv =>
      ⟨ForkUp 1 2, inferInstance, sh_fork12_of_refutes_scott α iα hnv, hX⟩
