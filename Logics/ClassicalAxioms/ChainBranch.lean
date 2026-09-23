import Logics.ClassicalAxioms.Minimal

/-!
# The chain branch of the key lemma

`KeyLemma` splits on whether weak excluded middle holds at `b`.  When it fails,
`sh_forkUp` supplies the fork and the branch is closed.  This file is the other
branch: when it holds, the four element chain should embed, by way of

* `lo = (a ⇨ b) ⊔ neg b`, and
* `hi = ((a ⇨ b) ⇨ a) ⇨ a  ⊔  (b ⇨ a) ⇨ (neg b ⊔ a)`, the principle's own value.

All the conditions that make `{⊥, lo, hi, ⊤}` a copy of `Fin 4` are proved
here.  Three need no hypothesis at all: `lo ⊑ hi`, `neg lo = ⊥`, and hence
`lo ≠ ⊥`.  The other two follow from `hi ⇨ lo = lo`, which needs weak excluded
middle at `b`, and which turns on one inequality, `gg_le_a`: the element
`neg (neg b) ⊓ (hi ⇨ lo) ⊓ ((a ⇨ b) ⇨ a)` lies below `a` in every Heyting
algebra.  That holds because it meets `a` below `lo`, hence below `b`, so it
lies below `a ⇨ b`, while lying below `(a ⇨ b) ⇨ a` by construction.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

namespace ChainBranch

variable {α : Type} [HeytingAlgebra α] (a b : α)


def pv : α := ((a ⇨ b) ⇨ a) ⇨ a          -- Peirce value
def iv : α := (b ⇨ a) ⇨ (neg b ⊔ a)      -- ImpOr value
def hi : α := pv a b ⊔ iv a b            -- y
def lo : α := (a ⇨ b) ⊔ neg b            -- x
def ee : α := (a ⇨ b) ⇨ a                -- e

theorem le_himp_self (z w : α) : z ⊑ (w ⇨ z) := le_himp_of_inf_le (inf_le_left z w)

theorem himp_le_pv : (a ⇨ b) ⊑ pv a b :=
  le_himp_of_inf_le (le_trans (le_of_eq (inf_comm _ _)) (himp_inf_le _ _))

theorem b_le_hi : b ⊑ hi a b :=
  le_trans (le_trans (le_himp_self b a) (himp_le_pv a b)) (le_sup_left _ _)

theorem a_le_hi : a ⊑ hi a b :=
  le_trans (le_trans (le_sup_right (neg b) a) (le_himp_self _ _)) (le_sup_right _ _)

theorem lo_inf_b_le : lo a b ⊓ b ⊑ (a ⇨ b) := by
  refine sup_cases (inf_le_left _ _) ?_ ?_
  · exact inf_le_left _ _
  · refine le_trans (le_trans (le_inf (le_trans (inf_le_right _ _) (inf_le_right _ _))
      (inf_le_left _ _)) (le_of_eq (inf_neg_eq_bot b))) (bot_le _)

/-- KEY STEP 1: the arrow meets `b` below `a ⇨ b`. -/
theorem d_inf_b_le : (hi a b ⇨ lo a b) ⊓ b ⊑ (a ⇨ b) := by
  refine le_trans (le_inf ?_ (inf_le_right _ _)) (lo_inf_b_le a b)
  exact le_trans (inf_le_inf le_rfl (b_le_hi a b)) (himp_inf_le _ _)

/-- KEY STEP 2: so it meets `e` below `b ⇨ a`. -/
theorem d_inf_e_le : (hi a b ⇨ lo a b) ⊓ ee a b ⊑ (b ⇨ a) := by
  refine le_himp_of_inf_le ?_
  refine le_trans (le_inf (le_trans (inf_le_left _ _) (inf_le_right _ _)) ?_)
    (himp_inf_le (a ⇨ b) a)
  exact le_trans (le_inf (le_trans (inf_le_left _ _) (inf_le_left _ _)) (inf_le_right _ _))
    (d_inf_b_le a b)

def gg : α := neg (neg b) ⊓ (hi a b ⇨ lo a b) ⊓ ee a b

theorem gg_le_ee : gg a b ⊑ ee a b := inf_le_right _ _
theorem gg_le_nnb : gg a b ⊑ neg (neg b) :=
  le_trans (inf_le_left _ _) (inf_le_left _ _)
theorem gg_le_bha : gg a b ⊑ (b ⇨ a) :=
  le_trans (le_inf (le_trans (inf_le_left _ _) (inf_le_right _ _)) (inf_le_right _ _))
    (d_inf_e_le a b)

/-- KEY STEP 3: `g` meets the lower element below `a`. -/
theorem gg_inf_lo : gg a b ⊓ lo a b ⊑ a := by
  refine sup_cases (inf_le_right _ _) ?_ ?_
  · exact le_trans (le_inf (le_trans (inf_le_right _ _)
      (le_trans (inf_le_left _ _) (gg_le_ee a b))) (inf_le_left _ _)) (himp_inf_le (a ⇨ b) a)
  · refine le_trans (le_trans (le_inf (inf_le_left _ _) (le_trans (inf_le_right _ _)
      (le_trans (inf_le_left _ _) (gg_le_nnb a b))))
      (le_of_eq (inf_neg_eq_bot (neg b)))) (bot_le _)

/-- KEY STEP 4: `g` meets the upper element below `a`. -/
theorem gg_inf_hi : gg a b ⊓ hi a b ⊑ a := by
  refine sup_cases (inf_le_right _ _) ?_ ?_
  · exact le_trans (le_inf (inf_le_left _ _) (le_trans (inf_le_right _ _)
      (le_trans (inf_le_left _ _) (gg_le_ee a b))))
      (himp_inf_le (ee a b) a)
  · have h1 : iv a b ⊓ (gg a b ⊓ hi a b) ⊑ (neg b ⊔ a) :=
      le_trans (le_inf (inf_le_left _ _) (le_trans (inf_le_right _ _)
        (le_trans (inf_le_left _ _) (gg_le_bha a b)))) (himp_inf_le (b ⇨ a) (neg b ⊔ a))
    refine sup_cases h1 ?_ ?_
    · refine le_trans (le_trans (le_inf (inf_le_left _ _)
        (le_trans (inf_le_right _ _) (le_trans (inf_le_right _ _)
        (le_trans (inf_le_left _ _) (gg_le_nnb a b)))))
        (le_of_eq (inf_neg_eq_bot (neg b)))) (bot_le _)
    · exact inf_le_left _ _

/-! ## What the pieces give -/

/-- CONDITION 1, no hypothesis. -/
theorem lo_le_hi : lo a b ⊑ hi a b :=
  sup_le (le_trans (himp_le_pv a b) (le_sup_left _ _))
    (le_trans (le_trans (le_sup_left (neg b) a) (le_himp_self _ _)) (le_sup_right _ _))

theorem neg_antitone {u v : α} (h : u ⊑ v) : neg v ⊑ neg u :=
  le_himp_of_inf_le (le_trans (inf_le_inf le_rfl h) (himp_inf_le v ⊥))

/-- CONDITION 2, no hypothesis. -/
theorem neg_lo : neg (lo a b) = ⊥ := by
  refine (eq_bot_iff _).mpr ?_
  have h1 : neg (lo a b) ⊑ neg b :=
    le_trans (neg_antitone (le_sup_left (a ⇨ b) (neg b)))
      (neg_antitone (le_himp_self b a))
  have h2 : neg (lo a b) ⊑ neg (neg b) := neg_antitone (le_sup_right (a ⇨ b) (neg b))
  exact le_trans (le_inf h1 h2) (le_of_eq (inf_neg_eq_bot (neg b)))

/-- CONDITION 3: from condition 2, given that the principle fails. -/
theorem lo_ne_bot (hT : hi a b ≠ ⊤) : lo a b ≠ ⊥ := by
  intro hb
  apply hT
  have htop : (⊤ : α) = ⊥ := by
    have := neg_lo a b
    rw [hb] at this
    rw [← this]
    exact (neg_bot (α := α)).symm
  exact le_antisymm (le_top _) (le_trans (le_of_eq htop) (bot_le _))

/-- The inequality the branch turns on. -/
def ChainGap : Prop := gg a b ⊑ hi a b

theorem gg_le_d : gg a b ⊑ (hi a b ⇨ lo a b) :=
  le_trans (inf_le_left _ _) (inf_le_right _ _)

/-- `g` meets `a` below `lo`, because `a` lies below `hi`. -/
theorem gg_inf_a_le_lo : gg a b ⊓ a ⊑ lo a b :=
  le_trans (le_inf (le_trans (inf_le_left _ _) (gg_le_d a b))
    (le_trans (inf_le_right _ _) (a_le_hi a b))) (himp_inf_le (hi a b) (lo a b))

/-- Hence `g` meets `a` below `b`: the `a ⇨ b` disjunct of `lo` gives `b`
outright, and the `neg b` disjunct is killed by `g ⊑ neg (neg b)`. -/
theorem gg_inf_a_le_b : gg a b ⊓ a ⊑ b := by
  refine sup_cases (gg_inf_a_le_lo a b) ?_ ?_
  · exact le_trans (le_inf (inf_le_left _ _)
      (le_trans (inf_le_right _ _) (inf_le_right _ _))) (himp_inf_le a b)
  · refine le_trans (le_trans (le_inf (inf_le_left _ _)
      (le_trans (inf_le_right _ _) (le_trans (inf_le_left _ _) (gg_le_nnb a b))))
      (le_of_eq (inf_neg_eq_bot (neg b)))) (bot_le _)

/-- **THE GAP, CLOSED.**  `g ⊑ a ⇨ b` by the step above, and `g ⊑ (a ⇨ b) ⇨ a`
by construction, so `g` lies below `a`. -/
theorem gg_le_a : gg a b ⊑ a :=
  le_trans (le_inf (gg_le_ee a b) (le_himp_of_inf_le (gg_inf_a_le_b a b)))
    (himp_inf_le (a ⇨ b) a)

/-- So `ChainGap` holds in every Heyting algebra, with no hypothesis. -/
theorem chainGap (a b : α) : ChainGap a b :=
  le_trans (gg_le_a a b) (a_le_hi a b)


/-- CONDITION 5, granted the gap: the upper element implies down to the lower. -/
theorem hi_himp_lo (hW : neg b ⊔ neg (neg b) = ⊤) :
    (hi a b ⇨ lo a b) = lo a b := by
  refine le_antisymm ?_ (le_himp_self _ _)
  have hga : gg a b ⊑ a := gg_le_a a b
  have hpv : neg (neg b) ⊓ (hi a b ⇨ lo a b) ⊑ pv a b := le_himp_of_inf_le hga
  have hx : neg (neg b) ⊓ (hi a b ⇨ lo a b) ⊑ lo a b :=
    le_trans (le_inf (inf_le_right _ _)
      (le_trans hpv (le_sup_left _ _))) (himp_inf_le (hi a b) (lo a b))
  refine sup_cases (le_trans (le_top _) (le_of_eq hW.symm)) ?_ ?_
  · exact le_trans (inf_le_left _ _) (le_sup_right (a ⇨ b) (neg b))
  · exact hx

/-- CONDITION 4, granted the gap: the two elements are distinct. -/
theorem lo_ne_hi (hT : hi a b ≠ ⊤) (hW : neg b ⊔ neg (neg b) = ⊤) :
    lo a b ≠ hi a b := by
  intro he
  apply hT
  have h := hi_himp_lo a b hW
  rw [← he] at h
  rw [← he, ← h]
  exact himp_eq_top_of_le le_rfl

/-! ## The key lemma

Split on weak excluded middle at `b`.  When it fails the fork embeds, with no
reference to the refutation at all.  When it holds, the two elements above span
a four element chain. -/

theorem keyLemma_proof : KeyLemma := by
  intro α iα hnv
  obtain ⟨v, hv⟩ := @exists_refuting α iα _ hnv
  by_cases hW : @HeytingAlgebra.neg α iα (v 1) ⊔ neg (neg (v 1)) = ⊤
  · refine Or.inl (@sh_of_embeds (Fin 4) α _ iα ?_)
    have hT : @hi α iα (v 0) (v 1) ≠ ⊤ := hv
    exact @four_embeds α iα (lo (v 0) (v 1)) (hi (v 0) (v 1))
      (lo_le_hi (v 0) (v 1)) (neg_lo (v 0) (v 1)) (hi_himp_lo (v 0) (v 1) hW)
      (lo_ne_bot (v 0) (v 1) hT) (lo_ne_hi (v 0) (v 1) hT hW) hT
  · exact Or.inr (@sh_forkUp α iα (v 1) hW)

/-- **The criterion, unconditionally.**  A schema derives `Peirce₁₂OrImpOr₂₁F`
exactly when it misses the top value in both separating algebras. -/
theorem derivesFromSchema_peirce₁₂OrImpOr₂₁_iff' (X : Form) :
    DerivesFromSchema X peirce₁₂OrImpOr₂₁Form ↔
      (¬ ∀ w : Nat → Fin 4, X.eval w = ⊤) ∧
        (¬ ∀ w : Nat → ForkUp 1 1, X.eval w = ⊤) :=
  derivesFromSchema_peirce₁₂OrImpOr₂₁_iff keyLemma_proof X

end ChainBranch
