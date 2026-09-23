import Logics.ClassicalAxioms.ClassicalRefuter
import Logics.Lindenbaum
import Logics.Homomorphism

/-!
# Where Smetanich's axiom sits, exactly

The other files of this directory are organised by technique and cover every
principle at once.  This one is about a single axiom, and answers two questions
about it that the general machinery makes askable.  The axiom is Smetanich's,
`(¬ b → a) → (((a → b) → a) → a)`, which axiomatises the level of the
hierarchy that `Peirce₁₂OrImpOr₂₁F` occupies.

**Which algebras separate it, and can they be shrunk?**  `Fin 4` and
`ForkUp 1 1` both refute the axiom, and neither can be replaced by
anything smaller: every algebra below one of them that still refutes it is
back above it.  Nor can either be dropped in favour of the other, since they
are incomparable.  `RefuterLB` records the minimality; the refutations
themselves are in `Model`.

Both minimality proofs run the same way.  An algebra below `A` is a subalgebra
of a quotient of `A`, so there are two cases.

*The quotient collapses something.*  Then some element other than the top is
sent to the top, hence so is the largest non-top element, and hence so is every
value the principle takes — because in both algebras those values all lie above
that element.  The principle becomes valid in the quotient and so in anything
inside it, contradicting the assumption that it fails.

*The quotient collapses nothing.*  Then the algebra embeds into `A` itself, and
the refutation, pushed along the embedding, must land on one of the finitely
many pairs where the principle fails in `A`.  Those pairs pin down enough
elements of the image to force the embedding to be onto, so the algebra is
isomorphic to `A`.

**Which schemas derive it?**  Exactly those missing the top value in both of
those algebras.  That rests on `sh_four_or_fork_of_refutes`: every algebra
refuting the axiom carries one of the two below it, so the two are not merely
minimal but exhaustive.

That splits on weak excluded middle at `b`.  When it fails, `sh_forkUp` hands
back the fork without looking at the refutation at all.  When it holds, the
two elements

* `lower = (a ⇨ b) ⊔ neg b`, and
* `upper = (neg b ⇨ a) ⇨ peirceVal a b`, the axiom's own value,

span a copy of `Fin 4`.  Three of the conditions for that need no hypothesis:
`lower ⊑ upper`, `neg lower = ⊥`, and hence `lower ≠ ⊥`.  The other two follow
from `upper ⇨ lower = lower`, which in turn reduces to `core_le_a`, an
inequality that again holds in every Heyting algebra.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

/-! # Part one: the two algebras cannot be shrunk -/

/-! ## Lower bounds among refuters -/

/-- `A` is a lower bound for the algebras refuting `p`: anything below it in
the order that still refutes `p` is back above it.  Note this does not itself
say that `A` refutes `p`; that is a separate fact, and without it the property
holds vacuously. -/
def RefuterLB (A : Type) [iA : HeytingAlgebra A] (p : Form) : Prop :=
  ∀ (γ : Type) (iγ : HeytingAlgebra γ),
    @SH γ A iγ iA → (¬ ∀ v : Nat → γ, p.eval v = ⊤) → @SH A γ iA iγ

/-! ## `Fin 4`

The principle takes only the values `2` and `⊤` in the four element chain, and
misses the top only at `a = 2`, `b = 1`. -/

open HeytingAlgebra in
theorem smetanich_four_ge_two : ∀ a b : Fin 4,
    ((2 : Fin 4) ⊓ ((neg b ⇨ a) ⇨ (((a ⇨ b) ⇨ a) ⇨ a))) = 2 := by decide

theorem four_coatom : ∀ x : Fin 4, x ≠ ⊤ → x ⊓ (2 : Fin 4) = x := by decide

open HeytingAlgebra in
theorem smetanich_four_fail : ∀ a b : Fin 4,
    ((neg b ⇨ a) ⇨ (((a ⇨ b) ⇨ a) ⇨ a)) ≠ ⊤ → a = 2 ∧ b = 1 := by decide

theorem four_cases : ∀ y : Fin 4, y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 := by decide

theorem four_coatom' (x : Fin 4) (h : x ≠ ⊤) : x ⊑ (2 : Fin 4) :=
  inf_eq_left_iff.mp (four_coatom x h)

theorem smetanich_four_eval_ge (v : Nat → Fin 4) :
    (2 : Fin 4) ⊑ smetanichForm.eval v :=
  inf_eq_left_iff.mp (smetanich_four_ge_two (v 0) (v 1))

/-- **No algebra strictly below `Fin 4` refutes `Peirce₁₂OrImpOr₂₁F`.** -/
theorem refuterLB_four : RefuterLB (Fin 4) smetanichForm := by
  intro γ iγ hsh hnv
  obtain ⟨Q, iQ, ⟨f, hfs⟩, ⟨g, hgi⟩⟩ := hsh
  by_cases hinj : Function.Injective f.toFun
  · -- the quotient is an isomorphism: pull `γ` back into `Fin 4`
    obtain ⟨h, hhi⟩ := embeds_of_iso f hinj hfs g hgi
    obtain ⟨v, hvne⟩ := @exists_ne_top γ iγ _ hnv
    have hfail := smetanich_four_fail _ _ (ne_top_of_embeds h hhi hvne)
    have hsurj : Function.Surjective h.toFun := by
      intro y
      rcases four_cases y with rfl | rfl | rfl | rfl
      · exact ⟨⊥, h.map_bot⟩
      · exact ⟨v 1, hfail.2⟩
      · exact ⟨v 0, hfail.1⟩
      · exact ⟨⊤, h.map_top⟩
    exact @sh_of_bijective γ (Fin 4) iγ _ h ⟨hhi, hsurj⟩
  · -- the quotient collapses: the principle becomes valid below it
    obtain ⟨a, b, hab, hne⟩ := exists_collapse f hinj
    exact absurd (@valid_of_embeds γ Q iγ iQ ⟨g, hgi⟩ _
      (valid_of_collapse f hfs hab hne four_coatom' smetanich_four_eval_ge)) hnv

/-! ## `ForkUp 1 1`

The principle takes only the coatom `tails 0 0` and `⊤` in the fork, and misses
the top only at `a = tails 0 0` with `b` one of the two branch tails. -/

open HeytingAlgebra in
theorem smetanich_fork_ge_coatom : ∀ a b : ForkUp 1 1,
    ((ForkUp.tails 0 0 : ForkUp 1 1) ⊓
      ((neg b ⇨ a) ⇨ (((a ⇨ b) ⇨ a) ⇨ a))) = ForkUp.tails 0 0 := by decide

theorem fork_coatom : ∀ x : ForkUp 1 1, x ≠ ⊤ →
    x ⊓ (ForkUp.tails 0 0 : ForkUp 1 1) = x := by decide

open HeytingAlgebra in
theorem smetanich_fork_fail : ∀ a b : ForkUp 1 1,
    ((neg b ⇨ a) ⇨ (((a ⇨ b) ⇨ a) ⇨ a)) ≠ ⊤ →
      a = ForkUp.tails 0 0 ∧ (b = ForkUp.tails 0 1 ∨ b = ForkUp.tails 1 0) := by decide

theorem fork_cases : ∀ y : ForkUp 1 1, y = ⊤ ∨ y = ForkUp.tails 0 0 ∨
    y = ForkUp.tails 0 1 ∨ y = ForkUp.tails 1 0 ∨ y = ⊥ := by decide

open HeytingAlgebra in
theorem fork_neg_tails : neg (ForkUp.tails 0 1 : ForkUp 1 1) = ForkUp.tails 1 0 ∧
    neg (ForkUp.tails 1 0 : ForkUp 1 1) = ForkUp.tails 0 1 := by decide

theorem fork_coatom' (x : ForkUp 1 1) (h : x ≠ ⊤) : x ⊑ (ForkUp.tails 0 0 : ForkUp 1 1) :=
  inf_eq_left_iff.mp (fork_coatom x h)

theorem smetanich_fork_eval_ge (v : Nat → ForkUp 1 1) :
    (ForkUp.tails 0 0 : ForkUp 1 1) ⊑ smetanichForm.eval v :=
  inf_eq_left_iff.mp (smetanich_fork_ge_coatom (v 0) (v 1))

/-- **No algebra strictly below `ForkUp 1 1` refutes `Peirce₁₂OrImpOr₂₁F`.** -/
theorem refuterLB_fork : RefuterLB (ForkUp 1 1) smetanichForm := by
  intro γ iγ hsh hnv
  obtain ⟨Q, iQ, ⟨f, hfs⟩, ⟨g, hgi⟩⟩ := hsh
  by_cases hinj : Function.Injective f.toFun
  · obtain ⟨h, hhi⟩ := embeds_of_iso f hinj hfs g hgi
    obtain ⟨v, hvne⟩ := @exists_ne_top γ iγ _ hnv
    have hfail := smetanich_fork_fail _ _ (ne_top_of_embeds h hhi hvne)
    have h0 : h.toFun (v 0) = ForkUp.tails 0 0 := hfail.1
    have h1 : h.toFun (v 1) = ForkUp.tails 0 1 ∨ h.toFun (v 1) = ForkUp.tails 1 0 := hfail.2
    have hsurj : Function.Surjective h.toFun := by
      intro y
      rcases fork_cases y with rfl | rfl | rfl | rfl | rfl
      · exact ⟨⊤, h.map_top⟩
      · exact ⟨v 0, h0⟩
      · rcases h1 with he | he
        · exact ⟨v 1, he⟩
        · exact ⟨neg (v 1), by rw [h.map_neg, he, fork_neg_tails.2]⟩
      · rcases h1 with he | he
        · exact ⟨neg (v 1), by rw [h.map_neg, he, fork_neg_tails.1]⟩
        · exact ⟨v 1, he⟩
      · exact ⟨⊥, h.map_bot⟩
    exact @sh_of_bijective γ (ForkUp 1 1) iγ _ h ⟨hhi, hsurj⟩
  · obtain ⟨a, b, hab, hne⟩ := exists_collapse f hinj
    exact absurd (@valid_of_embeds γ Q iγ iQ ⟨g, hgi⟩ _
      (valid_of_collapse f hfs hab hne fork_coatom' smetanich_fork_eval_ge)) hnv

/-! ## The two are incomparable

Linearity separates them one way and bounded depth the other, so neither of the
two separating algebras can be dropped in favour of the other. -/

def linearityForm : Form := .or (.imp (.var 0) (.var 1)) (.imp (.var 1) (.var 0))

def depthTwoForm : Form :=
  .or (.var 0) (.imp (.var 0) (.or (.var 1) (Form.neg (.var 1))))

theorem linearity_four : ∀ a b : Fin 4, (a ⇨ b) ⊔ (b ⇨ a) = ⊤ := by decide

theorem linearityForm_valid_four (v : Nat → Fin 4) : linearityForm.eval v = ⊤ :=
  linearity_four (v 0) (v 1)

theorem linearityForm_nvalid_fork :
    linearityForm.eval (fun n => if n = 0 then (ForkUp.tails 0 1 : ForkUp 1 1)
      else ForkUp.tails 1 0) ≠ ⊤ := by decide

open HeytingAlgebra in
theorem depthTwo_fork : ∀ a b : ForkUp 1 1, a ⊔ (a ⇨ (b ⊔ neg b)) = ⊤ := by decide

theorem depthTwoForm_valid_fork (v : Nat → ForkUp 1 1) : depthTwoForm.eval v = ⊤ :=
  depthTwo_fork (v 0) (v 1)

theorem depthTwoForm_nvalid_four :
    depthTwoForm.eval (fun n => if n = 0 then (2 : Fin 4) else 1) ≠ ⊤ := by decide

/-- The fork is not below the chain: linearity holds in `Fin 4` and fails in it. -/
theorem not_sh_fork_four : ¬ SH (ForkUp 1 1) (Fin 4) := fun h =>
  linearityForm_nvalid_fork (valid_of_sh h linearityForm_valid_four _)

/-- The chain is not below the fork: bounded depth holds in the fork and fails
in `Fin 4`. -/
theorem not_sh_four_fork : ¬ SH (Fin 4) (ForkUp 1 1) := fun h =>
  depthTwoForm_nvalid_four (valid_of_sh h depthTwoForm_valid_fork _)

/-! # Part two: which schemas derive the axiom -/

namespace ChainWitness

variable {α : Type} [HeytingAlgebra α] (a b : α)

/-! ## The two elements -/

/-- The value Peirce's law takes at `a, b`. -/
def peirceVal : α := ((a ⇨ b) ⇨ a) ⇨ a

/-- Smetanich's own value, and the upper element of the chain. -/
def upper : α := (neg b ⇨ a) ⇨ peirceVal a b

/-- The lower element of the chain. -/
def lower : α := (a ⇨ b) ⊔ neg b

/-- The antecedent of Peirce's law. -/
def peirceAnte : α := (a ⇨ b) ⇨ a

theorem himp_le_peirceVal : (a ⇨ b) ⊑ peirceVal a b :=
  le_himp_of_inf_le (le_trans (le_of_eq (inf_comm _ _)) (himp_inf_le _ _))

theorem peirceVal_le_upper : peirceVal a b ⊑ upper a b := le_himp_self _ _

theorem a_le_upper : a ⊑ upper a b :=
  le_trans (le_himp_self a _) (peirceVal_le_upper a b)

/-! ## The three conditions that need no hypothesis -/

/-- The lower element lies below the upper one. -/
theorem lower_le_upper : lower a b ⊑ upper a b := by
  refine sup_le (le_trans (himp_le_peirceVal a b) (peirceVal_le_upper a b)) ?_
  refine le_himp_of_inf_le ?_
  exact le_trans (le_trans (le_of_eq (inf_comm _ _)) (himp_inf_le (neg b) a))
    (le_himp_self a _)

/-- The lower element is dense: `b ⊑ a ⇨ b` puts its negation below `neg b`,
and the `neg b` disjunct puts it below `neg (neg b)`. -/
theorem neg_lower : neg (lower a b) = ⊥ := by
  refine (eq_bot_iff _).mpr ?_
  have h1 : neg (lower a b) ⊑ neg b :=
    le_trans (neg_antitone (le_sup_left (a ⇨ b) (neg b)))
      (neg_antitone (le_himp_self b a))
  have h2 : neg (lower a b) ⊑ neg (neg b) := neg_antitone (le_sup_right (a ⇨ b) (neg b))
  exact le_trans (le_inf h1 h2) (le_of_eq (inf_neg_eq_bot (neg b)))

/-- And it is not `⊥`, given that the principle fails: otherwise the algebra
would be degenerate and the principle would hold. -/
theorem lower_ne_bot (hT : upper a b ≠ ⊤) : lower a b ≠ ⊥ := by
  intro hb
  apply hT
  have htop : (⊤ : α) = ⊥ := by
    have h := neg_lower a b
    rw [hb] at h
    rw [← h]
    exact (neg_bot (α := α)).symm
  exact le_antisymm (le_top _) (le_trans (le_of_eq htop) (bot_le _))

/-! ## The inequality the branch turns on -/

/-- The element everything reduces to. -/
def core : α := neg (neg b) ⊓ (upper a b ⇨ lower a b) ⊓ peirceAnte a b

theorem core_le_ante : core a b ⊑ peirceAnte a b := inf_le_right _ _

theorem core_le_negneg_b : core a b ⊑ neg (neg b) :=
  le_trans (inf_le_left _ _) (inf_le_left _ _)

theorem core_le_arrow : core a b ⊑ (upper a b ⇨ lower a b) :=
  le_trans (inf_le_left _ _) (inf_le_right _ _)

/-- `core` meets `a` below `lower`, because `a` lies below `upper`. -/
theorem core_inf_a_le_lower : core a b ⊓ a ⊑ lower a b :=
  le_trans (le_inf (le_trans (inf_le_left _ _) (core_le_arrow a b))
    (le_trans (inf_le_right _ _) (a_le_upper a b))) (himp_inf_le (upper a b) (lower a b))

/-- Hence `core` meets `a` below `b`: the `a ⇨ b` disjunct of `lower` gives `b`
outright, and the `neg b` disjunct is killed by `core ⊑ neg (neg b)`. -/
theorem core_inf_a_le_b : core a b ⊓ a ⊑ b := by
  refine sup_cases (core_inf_a_le_lower a b) ?_ ?_
  · exact le_trans (le_inf (inf_le_left _ _)
      (le_trans (inf_le_right _ _) (inf_le_right _ _))) (himp_inf_le a b)
  · refine le_trans (le_trans (le_inf (inf_le_left _ _)
      (le_trans (inf_le_right _ _) (le_trans (inf_le_left _ _) (core_le_negneg_b a b))))
      (le_of_eq (inf_neg_eq_bot (neg b)))) (bot_le _)

/-- **The inequality the branch turns on.**  The step above gives
`core ⊑ a ⇨ b`, and `core ⊑ (a ⇨ b) ⇨ a` holds by construction, so `core` lies
below `a`.  No hypothesis is needed: this is true in every Heyting algebra. -/
theorem core_le_a : core a b ⊑ a :=
  le_trans (le_inf (core_le_ante a b) (le_himp_of_inf_le (core_inf_a_le_b a b)))
    (himp_inf_le (a ⇨ b) a)

/-! ## The two remaining conditions -/

/-- The upper element implies down to the lower one.  This is the only place
weak excluded middle is used: it splits the arrow into a `neg b` part, which
sits inside `lower` already, and a `neg (neg b)` part, which `core_le_a`
places below the Peirce value and so below `upper`. -/
theorem upper_himp_lower (hW : neg b ⊔ neg (neg b) = ⊤) :
    (upper a b ⇨ lower a b) = lower a b := by
  refine le_antisymm ?_ (le_himp_self _ _)
  have hpv : neg (neg b) ⊓ (upper a b ⇨ lower a b) ⊑ peirceVal a b :=
    le_himp_of_inf_le (core_le_a a b)
  have hx : neg (neg b) ⊓ (upper a b ⇨ lower a b) ⊑ lower a b :=
    le_trans (le_inf (inf_le_right _ _) (le_trans hpv (peirceVal_le_upper a b)))
      (himp_inf_le (upper a b) (lower a b))
  refine sup_cases (le_trans (le_top _) (le_of_eq hW.symm)) ?_ ?_
  · exact le_trans (inf_le_left _ _) (le_sup_right (a ⇨ b) (neg b))
  · exact hx

/-- And the two are distinct, so the chain really has four elements: if they
agreed, the arrow between them would be `⊤`, and so would `upper`. -/
theorem lower_ne_upper (hT : upper a b ≠ ⊤) (hW : neg b ⊔ neg (neg b) = ⊤) :
    lower a b ≠ upper a b := by
  intro he
  apply hT
  have h := upper_himp_lower a b hW
  rw [← he] at h
  rw [← he, ← h]
  exact himp_eq_top_of_le le_rfl

end ChainWitness

/-! ## The two algebras exhaust the refuters -/

open ChainWitness in
/-- **Every algebra refuting `Peirce₁₂OrImpOr₂₁F` carries `Fin 4` or
`ForkUp 1 1` below it.**  Weak excluded middle at `b` decides which. -/
theorem sh_four_or_fork_of_refutes (α : Type) (iα : HeytingAlgebra α)
    (h : ¬ ∀ v : Nat → α, smetanichForm.eval v = ⊤) :
    @SH (Fin 4) α _ iα ∨ @SH (ForkUp 1 1) α _ iα := by
  obtain ⟨v, hv⟩ := @exists_ne_top α iα _ h
  by_cases hW : @HeytingAlgebra.neg α iα (v 1) ⊔ neg (neg (v 1)) = ⊤
  · refine Or.inl (@sh_of_embeds (Fin 4) α _ iα ?_)
    have hT : @upper α iα (v 0) (v 1) ≠ ⊤ := hv
    exact @four_embeds α iα (lower (v 0) (v 1)) (upper (v 0) (v 1))
      (lower_le_upper (v 0) (v 1)) (neg_lower (v 0) (v 1))
      (upper_himp_lower (v 0) (v 1) hW) (lower_ne_bot (v 0) (v 1) hT)
      (lower_ne_upper (v 0) (v 1) hT hW) hT
  · exact Or.inr (@sh_forkUp α iα (v 1) hW)

/-- Smetanich's axiom misses the top value in the four element chain, at
`a = 2`, `b = 1`. -/
theorem smetanichForm_nvalid_four :
    smetanichForm.eval (fun n => if n = 0 then (2 : Fin 4) else 1) ≠ ⊤ := by decide

/-- And in the fork, at the coatom against a branch tail. -/
theorem smetanichForm_nvalid_fork :
    smetanichForm.eval (fun n => if n = 0 then (ForkUp.tails 0 0 : ForkUp 1 1)
      else ForkUp.tails 0 1) ≠ ⊤ := by decide

/-- **The criterion.**  A schema derives `Peirce₁₂OrImpOr₂₁F` exactly when it
misses the top value in both separating algebras.

Forward is soundness.  Backward goes through completeness for a schema: an
algebra validating the schema and refuting the principle would carry one of the
two algebras below it, and validity travels down, so the schema would hold
there too, against assumption. -/
theorem derivesFromSchema_smetanich_iff (X : Form) :
    DerivesFromSchema X smetanichForm ↔
      (¬ ∀ w : Nat → Fin 4, X.eval w = ⊤) ∧
        (¬ ∀ w : Nat → ForkUp 1 1, X.eval w = ⊤) := by
  constructor
  · intro h
    exact ⟨fun hv => smetanichForm_nvalid_four (DerivesFromSchema.valid hv h _),
      fun hv => smetanichForm_nvalid_fork (DerivesFromSchema.valid hv h _)⟩
  · intro hX
    refine Lindenbaum.derivesFromSchema_iff.mpr ?_
    intro α iα hv v
    refine Classical.byContradiction fun hne => ?_
    have hnv : ¬ ∀ u : Nat → α, smetanichForm.eval u = ⊤ := fun hall => hne (hall v)
    rcases sh_four_or_fork_of_refutes α iα hnv with hsh | hsh
    · exact hX.1 (@valid_of_sh (Fin 4) α _ iα hsh _ hv)
    · exact hX.2 (@valid_of_sh (ForkUp 1 1) α _ iα hsh _ hv)
