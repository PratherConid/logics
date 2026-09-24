import Logics.IntermediateAxioms.StrictImply
import Logics.Lindenbaum
import Logics.ConcreteEmbed

/-!
# Where `bd2Form` sits, exactly

Bounded depth two, `a ∨ (a → (b ∨ ¬ b))`, axiomatises the level below
Smetanich's.  This file answers for it the two questions `SmetanichRefuter`
answers for that one, and both answers are simpler, because `bd2Form` has a
single minimal refuter where Smetanich's axiom has two.

**Which algebra separates it, and can it be shrunk?**  `Fin 4` refutes it, and
nothing below `Fin 4` in the order does: `refuterLB_four_bd2`.

**Which schemas derive it?**  Exactly those missing the top value in `Fin 4`.
That rests on `sh_four_of_refutes_bd2`: every algebra refuting `bd2Form` carries
`Fin 4` below it.  With one refuter instead of two there is no case split —
the four element chain comes straight out of the refutation, with

* `lower = a ⇨ (b ⊔ neg b)`, and
* `upper = a ⊔ lower`, the axiom's own value.

Every condition making `{⊥, lower, upper, ⊤}` a copy of `Fin 4` is then
immediate.  `neg lower = ⊥` because `lower` sits above `b ⊔ neg b`, whose
negation is absurd.  And `upper ⇨ lower = lower` is pure currying: the arrow
out of `a ⊔ lower` is at most the arrow out of `a`, and `a ⇨ (a ⇨ c)` is
`a ⇨ c`.  No analogue of Smetanich's `core_le_a` is needed.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

/-! # Part one: `Fin 4` cannot be shrunk -/

open HeytingAlgebra in
theorem bd2_four_ge_two : ∀ a b : Fin 4,
    ((2 : Fin 4) ⊓ (a ⊔ (a ⇨ (b ⊔ neg b)))) = 2 := by decide

open HeytingAlgebra in
theorem bd2_four_fail : ∀ a b : Fin 4,
    (a ⊔ (a ⇨ (b ⊔ neg b))) ≠ ⊤ → a = 2 ∧ b = 1 := by decide

theorem bd2_four_eval_ge (v : Nat → Fin 4) : (2 : Fin 4) ⊑ bd2Form.eval v :=
  inf_eq_left_iff.mp (bd2_four_ge_two (v 0) (v 1))

/-- **Nothing below `Fin 4` refutes `bd2Form`.** -/
theorem refuterLB_four_bd2 : RefuterLB (Fin 4) bd2Form :=
  refuterLB_of_coatom four_coatom' bd2_four_eval_ge fun _ _ h _ v hv y => by
    have hfail := bd2_four_fail _ _ hv
    rcases four_cases y with rfl | rfl | rfl | rfl
    · exact ⟨⊥, h.map_bot⟩
    · exact ⟨v 1, hfail.2⟩
    · exact ⟨v 0, hfail.1⟩
    · exact ⟨⊤, h.map_top⟩

/-! # Part two: which schemas derive the axiom -/

namespace BD2Witness

variable {α : Type} [HeytingAlgebra α] (a b : α)

/-- The lower element of the chain. -/
def lower : α := a ⇨ (b ⊔ neg b)

/-- The axiom's own value, and the upper element. -/
def upper : α := a ⊔ lower a b

theorem lower_le_upper : lower a b ⊑ upper a b := le_sup_right _ _

/-- `lower` is dense: it sits above `b ⊔ neg b`, whose negation is `⊥`. -/
theorem neg_lower : neg (lower a b) = ⊥ := neg_himp_sup_neg_eq_bot a b

/-- **Pure currying.**  The arrow out of `a ⊔ lower` is at most the arrow out
of `a`, and `a ⇨ (a ⇨ c)` collapses to `a ⇨ c`. -/
theorem upper_himp_lower : (upper a b ⇨ lower a b) = lower a b := by
  refine le_antisymm ?_ (le_himp_self _ _)
  refine le_trans (himp_le_himp_left (le_sup_left a (lower a b))) ?_
  show (a ⇨ (a ⇨ (b ⊔ neg b))) ⊑ lower a b
  rw [← himp_curry, inf_idem]
  exact le_rfl

end BD2Witness

open BD2Witness in
/-- **Every algebra refuting `bd2Form` carries `Fin 4` below it.** -/
theorem sh_four_of_refutes_bd2 (α : Type) (iα : HeytingAlgebra α)
    (h : ¬ ∀ v : Nat → α, bd2Form.eval v = ⊤) : @SH (Fin 4) α _ iα := by
  obtain ⟨v, hv⟩ := @exists_ne_top α iα _ h
  refine @sh_of_embeds (Fin 4) α _ iα ?_
  have hT : @upper α iα (v 0) (v 1) ≠ ⊤ := hv
  exact @four_embeds α iα (lower (v 0) (v 1)) (upper (v 0) (v 1))
    (lower_le_upper (v 0) (v 1)) (neg_lower (v 0) (v 1))
    (upper_himp_lower (v 0) (v 1)) hT

/-- **The criterion.**  A schema derives `bd2Form` exactly when it misses the
top value in `Fin 4` — one algebra, no conjunction. -/
theorem derivesFromSchema_bd2_iff (X : Form) :
    DerivesFromSchema X bd2Form ↔ ¬ ∀ w : Nat → Fin 4, X.eval w = ⊤ := by
  constructor
  · intro h hv
    exact bd2Form_nvalid_four (DerivesFromSchema.valid hv h _)
  · exact fun hX => DerivesFromSchema.of_sh fun α iα hnv =>
      ⟨Fin 4, inferInstance, sh_four_of_refutes_bd2 α iα hnv, hX⟩
