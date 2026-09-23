import Logics.ClassicalAxioms.StrictImply
import Logics.Lindenbaum
import Logics.ConcreteEmbed

/-!
# Where `BD2F` sits, exactly

Bounded depth two, `a ∨ (a → (b ∨ ¬ b))`, axiomatises the level below
Smetanich's.  This file answers for it the two questions `SmetanichRefuter`
answers for that one, and both answers are simpler, because `BD2F` has a single
minimal refuter where Smetanich's axiom has two.

**Which algebra separates it, and can it be shrunk?**  `Fin 4` refutes it, and
nothing below `Fin 4` in the order does: `refuterLB_four_bd2`.

**Which schemas derive it?**  Exactly those missing the top value in `Fin 4`.
That rests on `sh_four_of_refutes_bd2`: every algebra refuting `BD2F` carries
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

/-- **Nothing below `Fin 4` refutes `BD2F`.** -/
theorem refuterLB_four_bd2 : RefuterLB (Fin 4) bd2Form := by
  intro γ iγ hsh hnv
  obtain ⟨Q, iQ, ⟨f, hfs⟩, ⟨g, hgi⟩⟩ := hsh
  by_cases hinj : Function.Injective f.toFun
  · obtain ⟨h, hhi⟩ := embeds_of_iso f hinj hfs g hgi
    obtain ⟨v, hvne⟩ := @exists_ne_top γ iγ _ hnv
    have hfail := bd2_four_fail _ _ (ne_top_of_embeds h hhi hvne)
    have hsurj : Function.Surjective h.toFun := by
      intro y
      rcases four_cases y with rfl | rfl | rfl | rfl
      · exact ⟨⊥, h.map_bot⟩
      · exact ⟨v 1, hfail.2⟩
      · exact ⟨v 0, hfail.1⟩
      · exact ⟨⊤, h.map_top⟩
    exact @sh_of_bijective γ (Fin 4) iγ _ h ⟨hhi, hsurj⟩
  · obtain ⟨a, b, hab, hne⟩ := exists_collapse f hinj
    exact absurd (@valid_of_embeds γ Q iγ iQ ⟨g, hgi⟩ _
      (valid_of_collapse f hfs hab hne four_coatom' bd2_four_eval_ge)) hnv

/-! # Part two: which schemas derive the axiom -/

namespace BD2Witness

variable {α : Type} [HeytingAlgebra α] (a b : α)

/-- The lower element of the chain. -/
def lower : α := a ⇨ (b ⊔ neg b)

/-- The axiom's own value, and the upper element. -/
def upper : α := a ⊔ lower a b

theorem lower_le_upper : lower a b ⊑ upper a b := le_sup_right _ _

/-- Implication reverses in its hypothesis. -/
theorem himp_le_himp_left {x y z : α} (h : x ⊑ y) : (y ⇨ z) ⊑ (x ⇨ z) :=
  le_himp_of_inf_le (le_trans (inf_le_inf le_rfl h) (himp_inf_le y z))

/-- `lower` is dense: it sits above `b ⊔ neg b`, whose negation is `⊥`. -/
theorem neg_lower : neg (lower a b) = ⊥ :=
  (eq_bot_iff _).mpr (le_trans (neg_antitone (le_himp_self (b ⊔ neg b) a))
    (le_of_eq (neg_sup_neg_eq_bot b)))

/-- And it is not `⊥`, given that the axiom fails. -/
theorem lower_ne_bot (hT : upper a b ≠ ⊤) : lower a b ≠ ⊥ := by
  intro hb
  apply hT
  have htop : (⊤ : α) = ⊥ := by
    have h := neg_lower a b
    rw [hb] at h
    rw [← h]
    exact (neg_bot (α := α)).symm
  exact le_antisymm (le_top _) (le_trans (le_of_eq htop) (bot_le _))

/-- **Pure currying.**  The arrow out of `a ⊔ lower` is at most the arrow out
of `a`, and `a ⇨ (a ⇨ c)` collapses to `a ⇨ c`. -/
theorem upper_himp_lower : (upper a b ⇨ lower a b) = lower a b := by
  refine le_antisymm ?_ (le_himp_self _ _)
  refine le_trans (himp_le_himp_left (le_sup_left a (lower a b))) ?_
  show (a ⇨ (a ⇨ (b ⊔ neg b))) ⊑ lower a b
  rw [← himp_curry, inf_idem]
  exact le_rfl

/-- So the two are distinct, and the chain has four elements. -/
theorem lower_ne_upper (hT : upper a b ≠ ⊤) : lower a b ≠ upper a b := by
  intro he
  apply hT
  have h := upper_himp_lower a b
  rw [← he] at h
  rw [← he, ← h]
  exact himp_eq_top_of_le le_rfl

end BD2Witness

open BD2Witness in
/-- **Every algebra refuting `BD2F` carries `Fin 4` below it.** -/
theorem sh_four_of_refutes_bd2 (α : Type) (iα : HeytingAlgebra α)
    (h : ¬ ∀ v : Nat → α, bd2Form.eval v = ⊤) : @SH (Fin 4) α _ iα := by
  obtain ⟨v, hv⟩ := @exists_ne_top α iα _ h
  refine @sh_of_embeds (Fin 4) α _ iα ?_
  have hT : @upper α iα (v 0) (v 1) ≠ ⊤ := hv
  exact @four_embeds α iα (lower (v 0) (v 1)) (upper (v 0) (v 1))
    (lower_le_upper (v 0) (v 1)) (neg_lower (v 0) (v 1))
    (upper_himp_lower (v 0) (v 1)) (lower_ne_bot (v 0) (v 1) hT)
    (lower_ne_upper (v 0) (v 1) hT) hT

theorem bd2Form_nvalid_four :
    bd2Form.eval (fun n => if n = 0 then (2 : Fin 4) else 1) ≠ ⊤ := by decide

/-- **The criterion.**  A schema derives `BD2F` exactly when it misses the top
value in `Fin 4` — one algebra, no conjunction. -/
theorem derivesFromSchema_bd2_iff (X : Form) :
    DerivesFromSchema X bd2Form ↔ ¬ ∀ w : Nat → Fin 4, X.eval w = ⊤ := by
  constructor
  · intro h hv
    exact bd2Form_nvalid_four (DerivesFromSchema.valid hv h _)
  · intro hX
    refine Lindenbaum.derivesFromSchema_iff.mpr ?_
    intro α iα hv v
    refine Classical.byContradiction fun hne => ?_
    have hnv : ¬ ∀ u : Nat → α, bd2Form.eval u = ⊤ := fun hall => hne (hall v)
    exact hX (@valid_of_sh (Fin 4) α _ iα (sh_four_of_refutes_bd2 α iα hnv) _ hv)
