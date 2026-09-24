import Logics.IntermediateAxioms.StrictImply
import Logics.Lindenbaum
import Logics.ConcreteEmbed

/-!
# Where `NoDiamondF` sits, exactly

`(a → (b ∨ ¬ b)) ∨ (b → (a ∨ ¬ a))` axiomatises the level below bounded depth
two.  This file answers for it the two questions `BD2Refuter` answers for that
one, and the answers have the same shape, with the diamond in place of the four
element chain.

**Which algebra separates it, and can it be shrunk?**  `KiteUp 1 1` refutes it,
and nothing below `KiteUp 1 1` in the order does: `refuterLB_kite_noDiamond`.
Where the chain was recovered from a failing pair by reading off two values,
the diamond needs four, but the extra two are the pair's own meet and join, so
a homomorphism reaches them for free.

**Which schemas derive it?**  Exactly those missing the top value in the
diamond.  That rests on `sh_kite_of_refutes_noDiamond`: every algebra refuting
the axiom carries `KiteUp 1 1` below it, the six values being `⊥`, `⊤`, the two
disjuncts

* `left = a ⇨ (b ⊔ neg b)`, and
* `right = b ⇨ (a ⊔ neg a)`,

and their meet and join.  Both disjuncts are dense, each lying above an
excluded middle, which is what kills every negation but `⊥`'s.  The one
condition with content is that each disjunct is the value of the arrow into the
other, and it holds because the second argument already lies below the first
disjunct: modus ponens twice brings `left ⇨ right` down to the excluded middle
that `right` concludes.  The axiom's own value is the join, so the refutation
says precisely that the join misses the top, which is what makes the six values
distinct.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

/-! # Part one: the diamond cannot be shrunk -/

/-- The diamond's largest value below the top is the join of its two
incomparable middles. -/
theorem kite_coatom : ∀ z : KiteUp 1 1,
    z ≠ ⊤ → z ⊓ (KiteUp.tails 0 0 : KiteUp 1 1) = z := by decide

theorem kite_coatom' (z : KiteUp 1 1) (h : z ≠ ⊤) :
    z ⊑ (KiteUp.tails 0 0 : KiteUp 1 1) := inf_eq_left_iff.mp (kite_coatom z h)

theorem noDiamond_kite_ge_coatom : ∀ a b : KiteUp 1 1,
    ((KiteUp.tails 0 0 : KiteUp 1 1) ⊓ ((a ⇨ (b ⊔ neg b)) ⊔ (b ⇨ (a ⊔ neg a))))
      = KiteUp.tails 0 0 := by decide

theorem noDiamondForm_eval_ge (v : Nat → KiteUp 1 1) :
    (KiteUp.tails 0 0 : KiteUp 1 1) ⊑ noDiamondForm.eval v :=
  inf_eq_left_iff.mp (noDiamond_kite_ge_coatom (v 0) (v 1))

/-- A failing pair generates the whole diamond: every value is one of the
bounds, one of the pair, or the pair's meet or join. -/
theorem noDiamond_kite_fail : ∀ a b : KiteUp 1 1,
    ((a ⇨ (b ⊔ neg b)) ⊔ (b ⇨ (a ⊔ neg a))) ≠ ⊤ →
      ∀ z : KiteUp 1 1,
        z = ⊥ ∨ z = ⊤ ∨ z = a ∨ z = b ∨ z = a ⊓ b ∨ z = a ⊔ b := by decide

/-- **Nothing below the diamond refutes `NoDiamondF`.** -/
theorem refuterLB_kite_noDiamond : RefuterLB (KiteUp 1 1) noDiamondForm := by
  intro γ iγ hsh hnv
  obtain ⟨Q, iQ, ⟨f, hfs⟩, ⟨g, hgi⟩⟩ := hsh
  by_cases hinj : Function.Injective f.toFun
  · obtain ⟨h, hhi⟩ := embeds_of_iso f hinj hfs g hgi
    obtain ⟨v, hvne⟩ := @exists_ne_top γ iγ _ hnv
    have hfail := noDiamond_kite_fail _ _ (ne_top_of_embeds h hhi hvne)
    have hsurj : Function.Surjective h.toFun := by
      intro z
      rcases hfail z with hz | hz | hz | hz | hz | hz
      · exact ⟨⊥, by rw [h.map_bot, hz]⟩
      · exact ⟨⊤, by rw [h.map_top, hz]⟩
      · exact ⟨v 0, hz.symm⟩
      · exact ⟨v 1, hz.symm⟩
      · exact ⟨v 0 ⊓ v 1, by rw [h.map_inf]; exact hz.symm⟩
      · exact ⟨v 0 ⊔ v 1, by rw [h.map_sup]; exact hz.symm⟩
    exact @sh_of_bijective γ (KiteUp 1 1) iγ _ h ⟨hhi, hsurj⟩
  · obtain ⟨a, b, hab, hne⟩ := exists_collapse f hinj
    exact absurd (@valid_of_embeds γ Q iγ iQ ⟨g, hgi⟩ _
      (valid_of_collapse f hfs hab hne kite_coatom' noDiamondForm_eval_ge)) hnv

/-! # Part two: which schemas derive the axiom -/

namespace NoDiamondWitness

variable {α : Type} [HeytingAlgebra α] (a b : α)

/-- The value of the left disjunct, and one of the two incomparable middles. -/
def left : α := a ⇨ (b ⊔ neg b)

/-- The value of the right disjunct, and the other middle. -/
def right : α := b ⇨ (a ⊔ neg a)

/-- Each disjunct lies above the excluded middle it concludes, hence above that
excluded middle's own argument. -/
theorem le_left : b ⊑ left a b :=
  le_trans (le_sup_left b (neg b)) (le_himp_self (b ⊔ neg b) a)

theorem le_right : a ⊑ right a b :=
  le_trans (le_sup_left a (neg a)) (le_himp_self (a ⊔ neg a) b)

/-- Both disjuncts are dense, lying above an excluded middle whose negation is
absurd. -/
theorem neg_left : neg (left a b) = ⊥ :=
  (eq_bot_iff _).mpr (le_trans (neg_antitone (le_himp_self (b ⊔ neg b) a))
    (le_of_eq (neg_sup_neg_eq_bot b)))

theorem neg_right : neg (right a b) = ⊥ :=
  (eq_bot_iff _).mpr (le_trans (neg_antitone (le_himp_self (a ⊔ neg a) b))
    (le_of_eq (neg_sup_neg_eq_bot a)))

/-- **Each disjunct is the value of the arrow into the other.**  One direction
is free.  For the other, the second argument lies below `left`, so a meet with
it is a meet with `left`, and modus ponens twice carries `left ⇨ right` down to
the excluded middle that `right` concludes. -/
theorem left_himp_right : (left a b ⇨ right a b) = right a b := by
  refine le_antisymm ?_ (le_himp_self _ _)
  show (left a b ⇨ right a b) ⊑ (b ⇨ (a ⊔ neg a))
  refine le_himp_of_inf_le (le_trans (le_inf ?_ (inf_le_right _ _))
    (himp_inf_le b (a ⊔ neg a)))
  exact le_trans (inf_le_inf le_rfl (le_left a b))
    (himp_inf_le (left a b) (right a b))

theorem right_himp_left : (right a b ⇨ left a b) = left a b := by
  refine le_antisymm ?_ (le_himp_self _ _)
  show (right a b ⇨ left a b) ⊑ (a ⇨ (b ⊔ neg b))
  refine le_himp_of_inf_le (le_trans (le_inf ?_ (inf_le_right _ _))
    (himp_inf_le a (b ⊔ neg b)))
  exact le_trans (inf_le_inf le_rfl (le_right a b))
    (himp_inf_le (right a b) (left a b))

end NoDiamondWitness

open NoDiamondWitness in
/-- **Every algebra refuting `NoDiamondF` carries the diamond below it.**  The
axiom's own value is the join of the two disjuncts, so the refutation is
exactly the hypothesis the embedding needs. -/
theorem sh_kite_of_refutes_noDiamond (α : Type) (iα : HeytingAlgebra α)
    (h : ¬ ∀ v : Nat → α, noDiamondForm.eval v = ⊤) : @SH (KiteUp 1 1) α _ iα := by
  obtain ⟨v, hv⟩ := @exists_ne_top α iα _ h
  exact @sh_kite α iα (left (v 0) (v 1)) (right (v 0) (v 1))
    (left_himp_right (v 0) (v 1)) (right_himp_left (v 0) (v 1))
    (neg_left (v 0) (v 1)) (neg_right (v 0) (v 1)) hv

/-- **The criterion.**  A schema derives `NoDiamondF` exactly when it misses the
top value in the diamond. -/
theorem derivesFromSchema_noDiamond_iff (X : Form) :
    DerivesFromSchema X noDiamondForm ↔ ¬ ∀ w : Nat → KiteUp 1 1, X.eval w = ⊤ := by
  constructor
  · intro h hv
    exact noDiamondForm_nvalid_diamond (DerivesFromSchema.valid hv h _)
  · intro hX
    refine Lindenbaum.derivesFromSchema_iff.mpr ?_
    intro α iα hv v
    refine Classical.byContradiction fun hne => ?_
    have hnv : ¬ ∀ u : Nat → α, noDiamondForm.eval u = ⊤ := fun hall => hne (hall v)
    exact hX (@valid_of_sh (KiteUp 1 1) α _ iα
      (sh_kite_of_refutes_noDiamond α iα hnv) _ hv)
