import Logics.ClassicalAxioms.ThreeChain
import Logics.Lindenbaum
import Logics.Homomorphism

/-!
# The minimal refuters of `Peirce₁₂OrImpOr₂₁F`

`Fin 4` and `ForkUp 1 1` both refute `Peirce₁₂OrImpOr₂₁F`.  This file proves
that neither can be replaced by anything smaller: every algebra below one of
them that still refutes the principle is back above it.  It also proves that
the two are incomparable, so neither is redundant.

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

What is *not* proved here is that these two are the only minimal refuters.
That is Jankov's theorem together with an identification of the principle with
a conjunction of characteristic formulas, and neither is formalised.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

/-! ## Minimality -/

/-- `A` is minimal among the algebras refuting `p`: anything below it in the
order that still refutes `p` is back above it. -/
def MinimalRefuter (A : Type) [iA : HeytingAlgebra A] (p : Form) : Prop :=
  ∀ (γ : Type) (iγ : HeytingAlgebra γ),
    @SH γ A iγ iA → (¬ ∀ v : Nat → γ, p.eval v = ⊤) → @SH A γ iA iγ

/-- A quotient that identifies two elements validates every formula whose
values all lie above the largest non-top element. -/
theorem valid_of_collapse {A Q : Type} [HeytingAlgebra A] [HeytingAlgebra Q]
    (f : Hom A Q) (hsurj : Function.Surjective f.toFun)
    {a b : A} (hab : f.toFun a = f.toFun b) (hne : a ≠ b)
    {c : A} (hc : ∀ x : A, x ≠ ⊤ → x ⊑ c)
    {p : Form} (hp : ∀ v : Nat → A, c ⊑ p.eval v) :
    ∀ w : Nat → Q, p.eval w = ⊤ := by
  have hx : f.toFun ((a ⇨ b) ⊓ (b ⇨ a)) = ⊤ := by
    rw [f.map_inf, f.map_himp, f.map_himp, hab, himp_eq_top_of_le le_rfl, inf_top]
  have hxne : (a ⇨ b) ⊓ (b ⇨ a) ≠ ⊤ := by
    intro h
    have h1 : (a ⇨ b) = ⊤ := (eq_top_iff _).mpr (h ▸ inf_le_left (a ⇨ b) (b ⇨ a))
    have h2 : (b ⇨ a) = ⊤ := (eq_top_iff _).mpr (h ▸ inf_le_right (a ⇨ b) (b ⇨ a))
    exact hne (le_antisymm (le_of_himp_eq_top h1) (le_of_himp_eq_top h2))
  have hfc : f.toFun c = ⊤ :=
    (eq_top_iff _).mpr (le_trans (le_of_eq hx.symm) (f.mono (hc _ hxne)))
  intro w
  have hrep : ∀ n, ∃ x, f.toFun x = w n := fun n => hsurj (w n)
  have hw : w = fun n => f.toFun (Classical.choose (hrep n)) :=
    funext (fun n => (Classical.choose_spec (hrep n)).symm)
  rw [hw, f.eval]
  exact (eq_top_iff _).mpr (le_trans (le_of_eq hfc.symm) (f.mono (hp _)))

/-- Extracting a pair of distinct elements with the same image. -/
theorem exists_collapse {A Q : Type} [HeytingAlgebra A] [HeytingAlgebra Q]
    (f : Hom A Q) (h : ¬ Function.Injective f.toFun) :
    ∃ a b : A, f.toFun a = f.toFun b ∧ a ≠ b := by
  refine Classical.byContradiction fun hne => h ?_
  intro a b hab
  exact Classical.byContradiction fun hab' => hne ⟨a, b, hab, hab'⟩

/-- Extracting a refuting valuation. -/
theorem exists_refuting {γ : Type} [HeytingAlgebra γ] {p : Form}
    (h : ¬ ∀ v : Nat → γ, p.eval v = ⊤) : ∃ v : Nat → γ, p.eval v ≠ ⊤ := by
  refine Classical.byContradiction fun hne => h ?_
  intro v
  exact Classical.byContradiction fun hw => hne ⟨v, hw⟩

/-- Pushing a refutation along an embedding. -/
theorem ne_top_of_embeds {γ A : Type} [HeytingAlgebra γ] [HeytingAlgebra A]
    (h : Hom γ A) (hi : Function.Injective h.toFun) {p : Form} {v : Nat → γ}
    (hv : p.eval v ≠ ⊤) : p.eval (fun n => h.toFun (v n)) ≠ ⊤ := by
  rw [h.eval v]
  intro hc
  exact hv (hi (by rw [hc, h.map_top]))

/-- When the quotient is an isomorphism, the algebra embeds into `A` itself. -/
theorem embeds_of_iso {γ A Q : Type} [HeytingAlgebra γ] [HeytingAlgebra A] [HeytingAlgebra Q]
    (f : Hom A Q) (hinj : Function.Injective f.toFun) (hfs : Function.Surjective f.toFun)
    (g : Hom γ Q) (hgi : Function.Injective g.toFun) :
    ∃ h : Hom γ A, Function.Injective h.toFun :=
  ⟨Hom.comp (f.inv ⟨hinj, hfs⟩) g,
   fun _ _ hxy => hgi (Hom.inv_injective f ⟨hinj, hfs⟩ hxy)⟩

/-! ## `Fin 4`

The principle takes only the values `2` and `⊤` in the four element chain, and
misses the top only at `a = 2`, `b = 1`. -/

open HeytingAlgebra in
theorem peirce₁₂OrImpOr₂₁_four_ge_two : ∀ a b : Fin 4,
    ((2 : Fin 4) ⊓ ((((a ⇨ b) ⇨ a) ⇨ a) ⊔ ((b ⇨ a) ⇨ (neg b ⊔ a)))) = 2 := by decide

theorem four_coatom : ∀ x : Fin 4, x ≠ ⊤ → x ⊓ (2 : Fin 4) = x := by decide

open HeytingAlgebra in
theorem peirce₁₂OrImpOr₂₁_four_fail : ∀ a b : Fin 4,
    ((((a ⇨ b) ⇨ a) ⇨ a) ⊔ ((b ⇨ a) ⇨ (neg b ⊔ a))) ≠ ⊤ → a = 2 ∧ b = 1 := by decide

theorem four_cases : ∀ y : Fin 4, y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 := by decide

theorem four_coatom' (x : Fin 4) (h : x ≠ ⊤) : x ⊑ (2 : Fin 4) :=
  inf_eq_left_iff.mp (four_coatom x h)

theorem peirce₁₂OrImpOr₂₁_four_eval_ge (v : Nat → Fin 4) :
    (2 : Fin 4) ⊑ peirce₁₂OrImpOr₂₁Form.eval v :=
  inf_eq_left_iff.mp (peirce₁₂OrImpOr₂₁_four_ge_two (v 0) (v 1))

/-- **`Fin 4` is a minimal refuter of `Peirce₁₂OrImpOr₂₁F`.** -/
theorem minimalRefuter_four : MinimalRefuter (Fin 4) peirce₁₂OrImpOr₂₁Form := by
  intro γ iγ hsh hnv
  obtain ⟨Q, iQ, ⟨f, hfs⟩, ⟨g, hgi⟩⟩ := hsh
  by_cases hinj : Function.Injective f.toFun
  · -- the quotient is an isomorphism: pull `γ` back into `Fin 4`
    obtain ⟨h, hhi⟩ := embeds_of_iso f hinj hfs g hgi
    obtain ⟨v, hvne⟩ := @exists_refuting γ iγ _ hnv
    have hfail := peirce₁₂OrImpOr₂₁_four_fail _ _ (ne_top_of_embeds h hhi hvne)
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
      (valid_of_collapse f hfs hab hne four_coatom' peirce₁₂OrImpOr₂₁_four_eval_ge)) hnv

/-! ## `ForkUp 1 1`

The principle takes only the coatom `tails 0 0` and `⊤` in the fork, and misses
the top only at `a = tails 0 0` with `b` one of the two branch tails. -/

open HeytingAlgebra in
theorem peirce₁₂OrImpOr₂₁_fork_ge_coatom : ∀ a b : ForkUp 1 1,
    ((ForkUp.tails 0 0 : ForkUp 1 1) ⊓
      ((((a ⇨ b) ⇨ a) ⇨ a) ⊔ ((b ⇨ a) ⇨ (neg b ⊔ a)))) = ForkUp.tails 0 0 := by decide

theorem fork_coatom : ∀ x : ForkUp 1 1, x ≠ ⊤ →
    x ⊓ (ForkUp.tails 0 0 : ForkUp 1 1) = x := by decide

open HeytingAlgebra in
theorem peirce₁₂OrImpOr₂₁_fork_fail : ∀ a b : ForkUp 1 1,
    ((((a ⇨ b) ⇨ a) ⇨ a) ⊔ ((b ⇨ a) ⇨ (neg b ⊔ a))) ≠ ⊤ →
      a = ForkUp.tails 0 0 ∧ (b = ForkUp.tails 0 1 ∨ b = ForkUp.tails 1 0) := by decide

theorem fork_cases : ∀ y : ForkUp 1 1, y = ⊤ ∨ y = ForkUp.tails 0 0 ∨
    y = ForkUp.tails 0 1 ∨ y = ForkUp.tails 1 0 ∨ y = ⊥ := by decide

open HeytingAlgebra in
theorem fork_neg_tails : neg (ForkUp.tails 0 1 : ForkUp 1 1) = ForkUp.tails 1 0 ∧
    neg (ForkUp.tails 1 0 : ForkUp 1 1) = ForkUp.tails 0 1 := by decide

theorem fork_coatom' (x : ForkUp 1 1) (h : x ≠ ⊤) : x ⊑ (ForkUp.tails 0 0 : ForkUp 1 1) :=
  inf_eq_left_iff.mp (fork_coatom x h)

theorem peirce₁₂OrImpOr₂₁_fork_eval_ge (v : Nat → ForkUp 1 1) :
    (ForkUp.tails 0 0 : ForkUp 1 1) ⊑ peirce₁₂OrImpOr₂₁Form.eval v :=
  inf_eq_left_iff.mp (peirce₁₂OrImpOr₂₁_fork_ge_coatom (v 0) (v 1))

/-- **`ForkUp 1 1` is a minimal refuter of `Peirce₁₂OrImpOr₂₁F`.** -/
theorem minimalRefuter_fork : MinimalRefuter (ForkUp 1 1) peirce₁₂OrImpOr₂₁Form := by
  intro γ iγ hsh hnv
  obtain ⟨Q, iQ, ⟨f, hfs⟩, ⟨g, hgi⟩⟩ := hsh
  by_cases hinj : Function.Injective f.toFun
  · obtain ⟨h, hhi⟩ := embeds_of_iso f hinj hfs g hgi
    obtain ⟨v, hvne⟩ := @exists_refuting γ iγ _ hnv
    have hfail := peirce₁₂OrImpOr₂₁_fork_fail _ _ (ne_top_of_embeds h hhi hvne)
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
      (valid_of_collapse f hfs hab hne fork_coatom' peirce₁₂OrImpOr₂₁_fork_eval_ge)) hnv

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

/-! ## The criterion, reduced to one open lemma

A schema derives the principle exactly when it fails in both separating
algebras.  The forward direction is soundness and is proved above.  The
backward direction needs exactly one fact beyond what is formalised: that a
refutation of the principle forces one of the two algebras to appear below the
refuting algebra.  That fact is stated here as `KeyLemma` and assumed; the rest
of the criterion is proved from it.

Note that Jankov's theorem is *not* on this path.  It would restate `KeyLemma`
as an interderivability with a conjunction of characteristic formulas, but the
derivation below never mentions them. -/

/-- An embedding already puts an algebra below, with no quotient needed. -/
theorem sh_of_embeds {A α : Type} [HeytingAlgebra A] [HeytingAlgebra α]
    (h : Embeds A α) : SH A α :=
  ⟨α, inferInstance, onto_refl α, h⟩

/-- The one fact left open: refuting the principle forces one of the two
separating algebras below. -/
def KeyLemma : Prop :=
  ∀ (α : Type) (iα : HeytingAlgebra α),
    (¬ ∀ v : Nat → α, peirce₁₂OrImpOr₂₁Form.eval v = ⊤) →
      @SH (Fin 4) α _ iα ∨ @SH (ForkUp 1 1) α _ iα

/-- **The criterion**, granted `KeyLemma`: a schema derives
`Peirce₁₂OrImpOr₂₁F` exactly when it fails in both separating algebras. -/
theorem derivesFromSchema_peirce₁₂OrImpOr₂₁_iff (key : KeyLemma) (X : Form) :
    DerivesFromSchema X peirce₁₂OrImpOr₂₁Form ↔
      (¬ ∀ w : Nat → Fin 4, X.eval w = ⊤) ∧
        (¬ ∀ w : Nat → ForkUp 1 1, X.eval w = ⊤) := by
  constructor
  · intro h
    exact ⟨nvalid_four_of_derives_peirce₁₂OrImpOr₂₁ h,
      nvalid_fork_of_derives_peirce₁₂OrImpOr₂₁ h⟩
  · intro hX
    refine Lindenbaum.derivesFromSchema_iff.mpr ?_
    intro α iα hv v
    refine Classical.byContradiction fun hne => ?_
    have hnv : ¬ ∀ u : Nat → α, peirce₁₂OrImpOr₂₁Form.eval u = ⊤ := fun hall => hne (hall v)
    rcases key α iα hnv with hsh | hsh
    · exact hX.1 (@valid_of_sh (Fin 4) α _ iα hsh _ hv)
    · exact hX.2 (@valid_of_sh (ForkUp 1 1) α _ iα hsh _ hv)
