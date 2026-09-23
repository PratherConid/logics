import Logics.Homomorphism

/-!
# Concrete embeddings

`Logics/Homomorphism.lean` says what it means for one algebra to sit below
another and how validity travels along that order, but exhibits no example.
This file supplies them: the small algebras that turn up as separating
witnesses, each embedded into every algebra where a corresponding principle
fails.

* the three element chain, into every algebra where excluded middle fails;
* the five element fork, into every algebra where its weak form fails;
* the four element chain, wherever two elements sit strictly between the
  bounds with `neg x = ⊥` and `y ⇨ x = x`.

The first two are proved from a single offending element, the third from the
two elements themselves.  Each is the algebraic counterpart of a syntactic
construction that reads a refuting valuation back as a derivation.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

/-! Facts about `Fin 4` that any argument of this shape needs. -/

theorem four_coatom : ∀ x : Fin 4, x ≠ ⊤ → x ⊓ (2 : Fin 4) = x := by decide

theorem four_cases : ∀ y : Fin 4, y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 := by decide

theorem four_coatom' (x : Fin 4) (h : x ≠ ⊤) : x ⊑ (2 : Fin 4) :=
  inf_eq_left_iff.mp (four_coatom x h)

/-! ## The three element chain sits inside every non-classical algebra

Given an element `a` at which excluded middle fails, the three elements `⊥`,
`a ⊔ neg a` and `⊤` are distinct and closed under the operations.  The only
case with content is that the middle element has absurd negation, which is
`neg_sup_neg_eq_bot`. -/

namespace ThreeEmbed

variable {α : Type} [HeytingAlgebra α] (a : α)

/-- The candidate embedding: `⊥`, the excluded middle at `a`, and `⊤`. -/
def map (i : Fin 3) : α :=
  match i.val with
  | 0 => ⊥
  | 1 => a ⊔ neg a
  | _ => ⊤

theorem map_zero {i : Fin 3} (h : i.val = 0) : map a i = ⊥ := by simp [map, h]
theorem map_one {i : Fin 3} (h : i.val = 1) : map a i = a ⊔ neg a := by simp [map, h]
theorem map_two {i : Fin 3} (h : i.val = 2) : map a i = ⊤ := by simp [map, h]

theorem mono {i j : Fin 3} (h : i.val ≤ j.val) : map a i ⊑ map a j := by
  have hi := i.isLt
  have hj := j.isLt
  by_cases h0 : i.val = 0
  · rw [map_zero a h0]; exact bot_le _
  by_cases h2 : j.val = 2
  · rw [map_two a h2]; exact le_top _
  rw [map_one a (by omega : i.val = 1), map_one a (by omega : j.val = 1)]
  exact le_rfl

theorem map_inf' (i j : Fin 3) : map a (i ⊓ j) = map a i ⊓ map a j := by
  by_cases h : i.val ≤ j.val
  · rw [Chain.inf_eq_left h]
    exact (inf_eq_left_iff.mpr (mono a h)).symm
  · rw [Chain.inf_eq_right h, inf_comm]
    exact (inf_eq_left_iff.mpr (mono a (by omega))).symm

theorem map_sup' (i j : Fin 3) : map a (i ⊔ j) = map a i ⊔ map a j := by
  by_cases h : i.val ≤ j.val
  · rw [Chain.sup_eq_right h]
    exact (sup_eq_right_iff.mpr (mono a h)).symm
  · rw [Chain.sup_eq_left h, sup_comm]
    exact (sup_eq_right_iff.mpr (mono a (by omega))).symm

theorem map_himp' (i j : Fin 3) : map a (i ⇨ j) = map a i ⇨ map a j := by
  by_cases h : i.val ≤ j.val
  · rw [(Chain.himp_eq_top_iff i j).mpr h, map_two a (by decide),
      himp_eq_top_of_le (mono a h)]
  · rw [Chain.himp_eq_of_not_le h]
    have hi := i.isLt
    by_cases h2 : i.val = 2
    · rw [map_two a h2, himp_top_left]
    · rw [map_one a (by omega : i.val = 1), map_zero a (by omega : j.val = 0)]
      exact (neg_sup_neg_eq_bot a).symm

theorem val_cases (i : Fin 3) : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
  have := i.isLt; omega

/-- The three values are distinct exactly when excluded middle fails at `a`. -/
theorem injective (h : a ⊔ neg a ≠ ⊤) : Function.Injective (map a) := by
  have hbot : (⊥ : α) ≠ ⊤ := by
    intro hb
    exact h (le_antisymm (le_top _) (hb ▸ bot_le _))
  have hmid : a ⊔ neg a ≠ ⊥ := by
    intro hc
    have ha : a = ⊥ := (eq_bot_iff a).mpr (hc ▸ le_sup_left a (neg a))
    have h1 : neg a ⊑ (⊥ : α) := by rw [← hc]; exact le_sup_right a (neg a)
    rw [ha, neg_bot] at h1
    exact hbot (le_antisymm (bot_le _) h1)
  intro i j hij
  refine Fin.ext ?_
  rcases val_cases i with hi | hi | hi <;> rcases val_cases j with hj | hj | hj
  · rw [hi, hj]
  · exfalso; rw [map_zero a hi, map_one a hj] at hij; exact hmid hij.symm
  · exfalso; rw [map_zero a hi, map_two a hj] at hij; exact hbot hij
  · exfalso; rw [map_one a hi, map_zero a hj] at hij; exact hmid hij
  · rw [hi, hj]
  · exfalso; rw [map_one a hi, map_two a hj] at hij; exact h hij
  · exfalso; rw [map_two a hi, map_zero a hj] at hij; exact hbot hij.symm
  · exfalso; rw [map_two a hi, map_one a hj] at hij; exact h hij.symm
  · rw [hi, hj]

end ThreeEmbed

/-- **The three element chain embeds into every algebra where excluded middle
fails.**  So `Fin 3` lies at the bottom of the Jankov order among the
non-classical algebras. -/
theorem three_embeds {α : Type} [HeytingAlgebra α] {a : α} (h : a ⊔ neg a ≠ ⊤) :
    Embeds (Fin 3) α :=
  ⟨{ toFun := ThreeEmbed.map a
     map_bot := ThreeEmbed.map_zero a (by decide)
     map_top := ThreeEmbed.map_two a (by decide)
     map_inf := ThreeEmbed.map_inf' a
     map_sup := ThreeEmbed.map_sup' a
     map_himp := ThreeEmbed.map_himp' a },
   ThreeEmbed.injective a h⟩

/-- Hence `Fin 3` is below every non-classical algebra in the Jankov order. -/
theorem sh_three {α : Type} [HeytingAlgebra α] {a : α} (h : a ⊔ neg a ≠ ⊤) :
    SH (Fin 3) α :=
  ⟨α, inferInstance, onto_refl α, three_embeds h⟩

/-- **A schema failing in `Fin 3` is valid only in Boolean algebras.**

If excluded middle failed anywhere in `α`, the three element chain would embed
there, so `α` would inherit the schema's validity and pass it down to `Fin 3`,
where it fails.  This is the semantic half of the fact that nothing strictly
weaker than excluded middle can refute the three element chain. -/
theorem sup_neg_eq_top_of_nvalid_three {α : Type} [HeytingAlgebra α] {X : Form}
    (hX : ∀ v : Nat → α, X.eval v = ⊤)
    (h3 : ¬ ∀ w : Nat → Fin 3, X.eval w = ⊤) (a : α) : a ⊔ neg a = ⊤ :=
  Classical.byContradiction (fun hne => h3 (valid_of_sh (sh_three hne) hX))

/-! ## The fork sits inside every algebra where weak excluded middle fails

`neg t` and `neg (neg t)` always meet at `⊥` and negate to each other, and the
identities above make the five elements `⊥`, `neg t`, `neg (neg t)`, their join
and `⊤` closed under all the operations.  So they span a copy of `ForkUp 1 1`
as soon as they are distinct, which happens exactly when their join misses the
top — that is, when weak excluded middle fails at `t`. -/

theorem forkUp_cases : ∀ y : ForkUp 1 1,
    y = .all ∨ y = .tails 0 0 ∨ y = .tails 0 1 ∨ y = .tails 1 0 ∨ y = .tails 1 1 := by
  decide

namespace ForkEmbed

variable {α : Type} [HeytingAlgebra α] (t : α)

/-- `⊥`, `neg t`, `neg (neg t)`, their join, and `⊤`. -/
def map (t : α) : ForkUp 1 1 → α
  | .all => ⊤
  | .tails i j =>
      match i.val, j.val with
      | 0, 0 => neg t ⊔ neg (neg t)
      | 0, _ => neg t
      | _, 0 => neg (neg t)
      | _, _ => ⊥

@[simp] theorem map_all : map t .all = ⊤ := rfl
@[simp] theorem map_join : map t (.tails 0 0) = neg t ⊔ neg (neg t) := rfl
@[simp] theorem map_left : map t (.tails 0 1) = neg t := rfl
@[simp] theorem map_right : map t (.tails 1 0) = neg (neg t) := rfl
@[simp] theorem map_bot' : map t (.tails 1 1) = ⊥ := rfl

/-! The lattice facts, in the form the case analysis needs. -/

theorem left_inf_right : neg t ⊓ neg (neg t) = ⊥ := inf_neg_eq_bot (neg t)

theorem right_inf_left : neg (neg t) ⊓ neg t = ⊥ := by
  rw [inf_comm]; exact left_inf_right t

theorem left_le_join : neg t ⊑ neg t ⊔ neg (neg t) := le_sup_left _ _
theorem right_le_join : neg (neg t) ⊑ neg t ⊔ neg (neg t) := le_sup_right _ _

theorem neg_join : neg (neg t ⊔ neg (neg t)) = ⊥ := by
  refine (eq_bot_iff _).mpr ?_
  have h1 : neg (neg t ⊔ neg (neg t)) ⊓ neg t ⊑ ⊥ :=
    le_trans (inf_le_inf le_rfl (left_le_join t)) (himp_inf_le _ ⊥)
  have h2 : neg (neg t ⊔ neg (neg t)) ⊑ neg (neg t) := le_himp_of_inf_le h1
  have h3 : neg (neg t ⊔ neg (neg t)) ⊓ neg (neg t) ⊑ ⊥ :=
    le_trans (inf_le_inf le_rfl (right_le_join t)) (himp_inf_le _ ⊥)
  exact le_trans (le_inf le_rfl h2) h3

theorem neg_left : neg (neg t) = neg (neg t) := rfl
theorem neg_right : neg (neg (neg t)) = neg t := neg_neg_neg t

theorem bot_inf' (a : α) : (⊥ : α) ⊓ a = ⊥ := by rw [inf_comm]; exact inf_bot a

theorem left_inf_join : neg t ⊓ (neg t ⊔ neg (neg t)) = neg t :=
  inf_eq_left_iff.mpr (left_le_join t)
theorem join_inf_left : (neg t ⊔ neg (neg t)) ⊓ neg t = neg t := by
  rw [inf_comm]; exact left_inf_join t
theorem right_inf_join : neg (neg t) ⊓ (neg t ⊔ neg (neg t)) = neg (neg t) :=
  inf_eq_left_iff.mpr (right_le_join t)
theorem join_inf_right : (neg t ⊔ neg (neg t)) ⊓ neg (neg t) = neg (neg t) := by
  rw [inf_comm]; exact right_inf_join t

theorem left_sup_join : neg t ⊔ (neg t ⊔ neg (neg t)) = neg t ⊔ neg (neg t) :=
  sup_eq_right_iff.mpr (left_le_join t)
theorem join_sup_left : (neg t ⊔ neg (neg t)) ⊔ neg t = neg t ⊔ neg (neg t) := by
  rw [sup_comm]; exact left_sup_join t
theorem right_sup_join : neg (neg t) ⊔ (neg t ⊔ neg (neg t)) = neg t ⊔ neg (neg t) :=
  sup_eq_right_iff.mpr (right_le_join t)
theorem join_sup_right : (neg t ⊔ neg (neg t)) ⊔ neg (neg t) = neg t ⊔ neg (neg t) := by
  rw [sup_comm]; exact right_sup_join t


/-! Forms the case analysis leaves behind. -/

@[simp] theorem map_top' : map t (⊤ : ForkUp 1 1) = ⊤ := rfl
@[simp] theorem map_bot'' : map t (⊥ : ForkUp 1 1) = ⊥ := rfl
@[simp] theorem himp_top_gen (a : α) : (a ⇨ (⊤ : α)) = ⊤ := himp_eq_top_of_le (le_top a)
@[simp] theorem self_himp (a : α) : (a ⇨ a) = ⊤ := himp_eq_top_of_le le_rfl
@[simp] theorem bot_himp_gen (a : α) : ((⊥ : α) ⇨ a) = ⊤ := himp_eq_top_of_le (bot_le a)
@[simp] theorem left_himp_bot : (neg t ⇨ (⊥ : α)) = neg (neg t) := rfl
@[simp] theorem right_himp_bot : (neg (neg t) ⇨ (⊥ : α)) = neg t := neg_neg_neg t
@[simp] theorem join_himp_bot : ((neg t ⊔ neg (neg t)) ⇨ (⊥ : α)) = ⊥ := neg_join t
@[simp] theorem left_himp_join : (neg t ⇨ (neg t ⊔ neg (neg t))) = ⊤ :=
  himp_eq_top_of_le (left_le_join t)
@[simp] theorem right_himp_join : (neg (neg t) ⇨ (neg t ⊔ neg (neg t))) = ⊤ :=
  himp_eq_top_of_le (right_le_join t)

/-! The 75 composite reductions, each definitional. -/


/-! The 75 composite reductions, each definitional. -/

@[simp] theorem mi_a_a : map t (ForkUp.all ⊓ ForkUp.all) = ⊤ := rfl
@[simp] theorem mi_a_00 : map t (ForkUp.all ⊓ ForkUp.tails 0 0) = (neg t ⊔ neg (neg t)) := rfl
@[simp] theorem mi_a_01 : map t (ForkUp.all ⊓ ForkUp.tails 0 1) = neg t := rfl
@[simp] theorem mi_a_10 : map t (ForkUp.all ⊓ ForkUp.tails 1 0) = neg (neg t) := rfl
@[simp] theorem mi_a_11 : map t (ForkUp.all ⊓ ForkUp.tails 1 1) = ⊥ := rfl
@[simp] theorem mi_00_a : map t (ForkUp.tails 0 0 ⊓ ForkUp.all) = (neg t ⊔ neg (neg t)) := rfl
@[simp] theorem mi_00_00 : map t (ForkUp.tails 0 0 ⊓ ForkUp.tails 0 0) = (neg t ⊔ neg (neg t)) := rfl
@[simp] theorem mi_00_01 : map t (ForkUp.tails 0 0 ⊓ ForkUp.tails 0 1) = neg t := rfl
@[simp] theorem mi_00_10 : map t (ForkUp.tails 0 0 ⊓ ForkUp.tails 1 0) = neg (neg t) := rfl
@[simp] theorem mi_00_11 : map t (ForkUp.tails 0 0 ⊓ ForkUp.tails 1 1) = ⊥ := rfl
@[simp] theorem mi_01_a : map t (ForkUp.tails 0 1 ⊓ ForkUp.all) = neg t := rfl
@[simp] theorem mi_01_00 : map t (ForkUp.tails 0 1 ⊓ ForkUp.tails 0 0) = neg t := rfl
@[simp] theorem mi_01_01 : map t (ForkUp.tails 0 1 ⊓ ForkUp.tails 0 1) = neg t := rfl
@[simp] theorem mi_01_10 : map t (ForkUp.tails 0 1 ⊓ ForkUp.tails 1 0) = ⊥ := rfl
@[simp] theorem mi_01_11 : map t (ForkUp.tails 0 1 ⊓ ForkUp.tails 1 1) = ⊥ := rfl
@[simp] theorem mi_10_a : map t (ForkUp.tails 1 0 ⊓ ForkUp.all) = neg (neg t) := rfl
@[simp] theorem mi_10_00 : map t (ForkUp.tails 1 0 ⊓ ForkUp.tails 0 0) = neg (neg t) := rfl
@[simp] theorem mi_10_01 : map t (ForkUp.tails 1 0 ⊓ ForkUp.tails 0 1) = ⊥ := rfl
@[simp] theorem mi_10_10 : map t (ForkUp.tails 1 0 ⊓ ForkUp.tails 1 0) = neg (neg t) := rfl
@[simp] theorem mi_10_11 : map t (ForkUp.tails 1 0 ⊓ ForkUp.tails 1 1) = ⊥ := rfl
@[simp] theorem mi_11_a : map t (ForkUp.tails 1 1 ⊓ ForkUp.all) = ⊥ := rfl
@[simp] theorem mi_11_00 : map t (ForkUp.tails 1 1 ⊓ ForkUp.tails 0 0) = ⊥ := rfl
@[simp] theorem mi_11_01 : map t (ForkUp.tails 1 1 ⊓ ForkUp.tails 0 1) = ⊥ := rfl
@[simp] theorem mi_11_10 : map t (ForkUp.tails 1 1 ⊓ ForkUp.tails 1 0) = ⊥ := rfl
@[simp] theorem mi_11_11 : map t (ForkUp.tails 1 1 ⊓ ForkUp.tails 1 1) = ⊥ := rfl

@[simp] theorem ms_a_a : map t (ForkUp.all ⊔ ForkUp.all) = ⊤ := rfl
@[simp] theorem ms_a_00 : map t (ForkUp.all ⊔ ForkUp.tails 0 0) = ⊤ := rfl
@[simp] theorem ms_a_01 : map t (ForkUp.all ⊔ ForkUp.tails 0 1) = ⊤ := rfl
@[simp] theorem ms_a_10 : map t (ForkUp.all ⊔ ForkUp.tails 1 0) = ⊤ := rfl
@[simp] theorem ms_a_11 : map t (ForkUp.all ⊔ ForkUp.tails 1 1) = ⊤ := rfl
@[simp] theorem ms_00_a : map t (ForkUp.tails 0 0 ⊔ ForkUp.all) = ⊤ := rfl
@[simp] theorem ms_00_00 : map t (ForkUp.tails 0 0 ⊔ ForkUp.tails 0 0) = (neg t ⊔ neg (neg t)) := rfl
@[simp] theorem ms_00_01 : map t (ForkUp.tails 0 0 ⊔ ForkUp.tails 0 1) = (neg t ⊔ neg (neg t)) := rfl
@[simp] theorem ms_00_10 : map t (ForkUp.tails 0 0 ⊔ ForkUp.tails 1 0) = (neg t ⊔ neg (neg t)) := rfl
@[simp] theorem ms_00_11 : map t (ForkUp.tails 0 0 ⊔ ForkUp.tails 1 1) = (neg t ⊔ neg (neg t)) := rfl
@[simp] theorem ms_01_a : map t (ForkUp.tails 0 1 ⊔ ForkUp.all) = ⊤ := rfl
@[simp] theorem ms_01_00 : map t (ForkUp.tails 0 1 ⊔ ForkUp.tails 0 0) = (neg t ⊔ neg (neg t)) := rfl
@[simp] theorem ms_01_01 : map t (ForkUp.tails 0 1 ⊔ ForkUp.tails 0 1) = neg t := rfl
@[simp] theorem ms_01_10 : map t (ForkUp.tails 0 1 ⊔ ForkUp.tails 1 0) = (neg t ⊔ neg (neg t)) := rfl
@[simp] theorem ms_01_11 : map t (ForkUp.tails 0 1 ⊔ ForkUp.tails 1 1) = neg t := rfl
@[simp] theorem ms_10_a : map t (ForkUp.tails 1 0 ⊔ ForkUp.all) = ⊤ := rfl
@[simp] theorem ms_10_00 : map t (ForkUp.tails 1 0 ⊔ ForkUp.tails 0 0) = (neg t ⊔ neg (neg t)) := rfl
@[simp] theorem ms_10_01 : map t (ForkUp.tails 1 0 ⊔ ForkUp.tails 0 1) = (neg t ⊔ neg (neg t)) := rfl
@[simp] theorem ms_10_10 : map t (ForkUp.tails 1 0 ⊔ ForkUp.tails 1 0) = neg (neg t) := rfl
@[simp] theorem ms_10_11 : map t (ForkUp.tails 1 0 ⊔ ForkUp.tails 1 1) = neg (neg t) := rfl
@[simp] theorem ms_11_a : map t (ForkUp.tails 1 1 ⊔ ForkUp.all) = ⊤ := rfl
@[simp] theorem ms_11_00 : map t (ForkUp.tails 1 1 ⊔ ForkUp.tails 0 0) = (neg t ⊔ neg (neg t)) := rfl
@[simp] theorem ms_11_01 : map t (ForkUp.tails 1 1 ⊔ ForkUp.tails 0 1) = neg t := rfl
@[simp] theorem ms_11_10 : map t (ForkUp.tails 1 1 ⊔ ForkUp.tails 1 0) = neg (neg t) := rfl
@[simp] theorem ms_11_11 : map t (ForkUp.tails 1 1 ⊔ ForkUp.tails 1 1) = ⊥ := rfl

@[simp] theorem mh_a_a : map t (ForkUp.all ⇨ ForkUp.all) = ⊤ := rfl
@[simp] theorem mh_a_00 : map t (ForkUp.all ⇨ ForkUp.tails 0 0) = (neg t ⊔ neg (neg t)) := rfl
@[simp] theorem mh_a_01 : map t (ForkUp.all ⇨ ForkUp.tails 0 1) = neg t := rfl
@[simp] theorem mh_a_10 : map t (ForkUp.all ⇨ ForkUp.tails 1 0) = neg (neg t) := rfl
@[simp] theorem mh_a_11 : map t (ForkUp.all ⇨ ForkUp.tails 1 1) = ⊥ := rfl
@[simp] theorem mh_00_a : map t (ForkUp.tails 0 0 ⇨ ForkUp.all) = ⊤ := rfl
@[simp] theorem mh_00_00 : map t (ForkUp.tails 0 0 ⇨ ForkUp.tails 0 0) = ⊤ := rfl
@[simp] theorem mh_00_01 : map t (ForkUp.tails 0 0 ⇨ ForkUp.tails 0 1) = neg t := rfl
@[simp] theorem mh_00_10 : map t (ForkUp.tails 0 0 ⇨ ForkUp.tails 1 0) = neg (neg t) := rfl
@[simp] theorem mh_00_11 : map t (ForkUp.tails 0 0 ⇨ ForkUp.tails 1 1) = ⊥ := rfl
@[simp] theorem mh_01_a : map t (ForkUp.tails 0 1 ⇨ ForkUp.all) = ⊤ := rfl
@[simp] theorem mh_01_00 : map t (ForkUp.tails 0 1 ⇨ ForkUp.tails 0 0) = ⊤ := rfl
@[simp] theorem mh_01_01 : map t (ForkUp.tails 0 1 ⇨ ForkUp.tails 0 1) = ⊤ := rfl
@[simp] theorem mh_01_10 : map t (ForkUp.tails 0 1 ⇨ ForkUp.tails 1 0) = neg (neg t) := rfl
@[simp] theorem mh_01_11 : map t (ForkUp.tails 0 1 ⇨ ForkUp.tails 1 1) = neg (neg t) := rfl
@[simp] theorem mh_10_a : map t (ForkUp.tails 1 0 ⇨ ForkUp.all) = ⊤ := rfl
@[simp] theorem mh_10_00 : map t (ForkUp.tails 1 0 ⇨ ForkUp.tails 0 0) = ⊤ := rfl
@[simp] theorem mh_10_01 : map t (ForkUp.tails 1 0 ⇨ ForkUp.tails 0 1) = neg t := rfl
@[simp] theorem mh_10_10 : map t (ForkUp.tails 1 0 ⇨ ForkUp.tails 1 0) = ⊤ := rfl
@[simp] theorem mh_10_11 : map t (ForkUp.tails 1 0 ⇨ ForkUp.tails 1 1) = neg t := rfl
@[simp] theorem mh_11_a : map t (ForkUp.tails 1 1 ⇨ ForkUp.all) = ⊤ := rfl
@[simp] theorem mh_11_00 : map t (ForkUp.tails 1 1 ⇨ ForkUp.tails 0 0) = ⊤ := rfl
@[simp] theorem mh_11_01 : map t (ForkUp.tails 1 1 ⇨ ForkUp.tails 0 1) = ⊤ := rfl
@[simp] theorem mh_11_10 : map t (ForkUp.tails 1 1 ⇨ ForkUp.tails 1 0) = ⊤ := rfl
@[simp] theorem mh_11_11 : map t (ForkUp.tails 1 1 ⇨ ForkUp.tails 1 1) = ⊤ := rfl


theorem map_inf' (x y : ForkUp 1 1) : map t (x ⊓ y) = map t x ⊓ map t y := by
  rcases forkUp_cases x with rfl|rfl|rfl|rfl|rfl <;>
    rcases forkUp_cases y with rfl|rfl|rfl|rfl|rfl <;>
    simp [left_inf_right, right_inf_left, left_inf_join, join_inf_left,
      right_inf_join, join_inf_right, inf_idem, inf_top, top_inf, inf_bot, bot_inf']

theorem map_sup' (x y : ForkUp 1 1) : map t (x ⊔ y) = map t x ⊔ map t y := by
  rcases forkUp_cases x with rfl|rfl|rfl|rfl|rfl <;>
    rcases forkUp_cases y with rfl|rfl|rfl|rfl|rfl <;>
    simp [left_sup_join, right_sup_join, sup_idem, sup_top, top_sup, bot_sup,
      sup_comm]

theorem map_himp' (x y : ForkUp 1 1) : map t (x ⇨ y) = map t x ⇨ map t y := by
  rcases forkUp_cases x with rfl|rfl|rfl|rfl|rfl <;>
    rcases forkUp_cases y with rfl|rfl|rfl|rfl|rfl <;>
    simp [himp_top_left, neg_neg_neg, neg_himp_neg_neg, neg_neg_himp_neg,
      sup_neg_himp_left, sup_neg_himp_right]

/-- The five values are distinct exactly when weak excluded middle fails. -/
theorem injective (h : neg t ⊔ neg (neg t) ≠ ⊤) : Function.Injective (map t) := by
  have hu : neg t ≠ ⊥ := by
    intro hb; apply h; rw [hb, neg_bot, bot_sup]
  have hv : neg (neg t) ≠ ⊥ := by
    intro hb
    apply h
    have hnt : neg t = ⊤ := by rw [← neg_neg_neg t, hb, neg_bot]
    rw [hnt, top_sup]
  have huv : neg t ≠ neg (neg t) := by
    intro he
    apply hu
    have hii := left_inf_right t
    rw [← he, inf_idem] at hii
    exact hii
  have hwb : neg t ⊔ neg (neg t) ≠ ⊥ := by
    intro hb
    exact hu ((eq_bot_iff _).mpr (hb ▸ left_le_join t))
  have hut : neg t ≠ ⊤ := by
    intro he
    exact h ((eq_top_iff _).mpr (le_trans (le_of_eq he.symm) (left_le_join t)))
  have hvt : neg (neg t) ≠ ⊤ := by
    intro he
    exact h ((eq_top_iff _).mpr (le_trans (le_of_eq he.symm) (right_le_join t)))
  have hbt : (⊥ : α) ≠ ⊤ := by
    intro he
    exact h ((eq_top_iff _).mpr (le_trans (le_of_eq he.symm) (bot_le _)))
  have huw : neg t ≠ neg t ⊔ neg (neg t) := by
    intro he
    apply hv
    have h1 : neg (neg t) ⊑ neg t := le_trans (right_le_join t) (le_of_eq he.symm)
    have h2 : neg (neg t) ⊓ neg t = neg (neg t) := inf_eq_left_iff.mpr h1
    rw [right_inf_left] at h2
    exact h2.symm
  have hvw : neg (neg t) ≠ neg t ⊔ neg (neg t) := by
    intro he
    apply hu
    have h1 : neg t ⊑ neg (neg t) := le_trans (left_le_join t) (le_of_eq he.symm)
    have h2 : neg t ⊓ neg (neg t) = neg t := inf_eq_left_iff.mpr h1
    rw [left_inf_right] at h2
    exact h2.symm
  intro x y hxy
  rcases forkUp_cases x with rfl|rfl|rfl|rfl|rfl <;>
    rcases forkUp_cases y with rfl|rfl|rfl|rfl|rfl <;>
    simp_all

end ForkEmbed

/-- **The five element fork embeds into every algebra in which weak excluded
middle fails.**  Unlike the three element chain, which needs excluded middle to
fail, this needs only its weak form to fail, and the witnesses are `neg t` and
`neg (neg t)` for the offending `t`. -/
theorem forkUp_embeds {α : Type} [HeytingAlgebra α] {t : α}
    (h : neg t ⊔ neg (neg t) ≠ ⊤) : Embeds (ForkUp 1 1) α :=
  ⟨{ toFun := ForkEmbed.map t
     map_bot := rfl
     map_top := rfl
     map_inf := ForkEmbed.map_inf' t
     map_sup := ForkEmbed.map_sup' t
     map_himp := ForkEmbed.map_himp' t },
   ForkEmbed.injective t h⟩

/-- Hence the fork lies below any such algebra in the order. -/
theorem sh_forkUp {α : Type} [HeytingAlgebra α] {t : α}
    (h : neg t ⊔ neg (neg t) ≠ ⊤) : SH (ForkUp 1 1) α :=
  ⟨α, inferInstance, onto_refl α, forkUp_embeds h⟩

/-! ## A four element chain inside an algebra

Two elements `x ⊏ y` strictly between the bounds span a copy of `Fin 4` as soon
as `neg x = ⊥` and `y ⇨ x = x`: those are exactly the two arrows of the four
element chain that are not forced by the order. -/

theorem four_val_cases : ∀ i : Fin 4, i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by
  decide

namespace FourEmbed

variable {α : Type} [HeytingAlgebra α] (x y : α)

def map (i : Fin 4) : α :=
  match i.val with
  | 0 => ⊥
  | 1 => x
  | 2 => y
  | _ => ⊤

theorem map_zero {i : Fin 4} (h : i.val = 0) : map x y i = ⊥ := by simp [map, h]
theorem map_one {i : Fin 4} (h : i.val = 1) : map x y i = x := by simp [map, h]
theorem map_two {i : Fin 4} (h : i.val = 2) : map x y i = y := by simp [map, h]
theorem map_three {i : Fin 4} (h : i.val = 3) : map x y i = ⊤ := by simp [map, h]

theorem neg_y (hxy : x ⊑ y) (hnx : neg x = ⊥) : neg y = ⊥ :=
  (eq_bot_iff _).mpr (le_trans (le_himp_of_inf_le
    (le_trans (inf_le_inf le_rfl hxy) (himp_inf_le y ⊥))) (le_of_eq hnx))

theorem mono (hxy : x ⊑ y) {i j : Fin 4} (h : i.val ≤ j.val) :
    map x y i ⊑ map x y j := by
  have hi := i.isLt
  have hj := j.isLt
  by_cases h0 : i.val = 0
  · rw [map_zero x y h0]; exact bot_le _
  by_cases h3 : j.val = 3
  · rw [map_three x y h3]; exact le_top _
  by_cases h1 : i.val = 1
  · by_cases h1' : j.val = 1
    · rw [map_one x y h1, map_one x y h1']; exact le_rfl
    · rw [map_one x y h1, map_two x y (by omega)]; exact hxy
  · rw [map_two x y (by omega : i.val = 2), map_two x y (by omega : j.val = 2)]
    exact le_rfl

theorem map_inf' (hxy : x ⊑ y) (i j : Fin 4) : map x y (i ⊓ j) = map x y i ⊓ map x y j := by
  by_cases h : i.val ≤ j.val
  · rw [Chain.inf_eq_left h]
    exact (inf_eq_left_iff.mpr (mono x y hxy h)).symm
  · rw [Chain.inf_eq_right h, inf_comm]
    exact (inf_eq_left_iff.mpr (mono x y hxy (by omega))).symm

theorem map_sup' (hxy : x ⊑ y) (i j : Fin 4) : map x y (i ⊔ j) = map x y i ⊔ map x y j := by
  by_cases h : i.val ≤ j.val
  · rw [Chain.sup_eq_right h]
    exact (sup_eq_right_iff.mpr (mono x y hxy h)).symm
  · rw [Chain.sup_eq_left h, sup_comm]
    exact (sup_eq_right_iff.mpr (mono x y hxy (by omega))).symm

theorem map_himp' (hxy : x ⊑ y) (hnx : neg x = ⊥) (hyx : (y ⇨ x) = x) (i j : Fin 4) : map x y (i ⇨ j) = map x y i ⇨ map x y j := by
  by_cases h : i.val ≤ j.val
  · rw [(Chain.himp_eq_top_iff i j).mpr h, map_three x y (by decide),
      himp_eq_top_of_le (mono x y hxy h)]
  · rw [Chain.himp_eq_of_not_le h]
    have hi := i.isLt
    by_cases h3 : i.val = 3
    · rw [map_three x y h3, himp_top_left]
    by_cases h2 : i.val = 2
    · by_cases hj : j.val = 0
      · rw [map_two x y h2, map_zero x y hj]
        exact (neg_y x y hxy hnx).symm
      · rw [map_two x y h2, map_one x y (by omega)]
        exact hyx.symm
    · rw [map_one x y (by omega : i.val = 1), map_zero x y (by omega : j.val = 0)]
      exact hnx.symm

theorem injective (hxy : x ⊑ y) (hxb : x ≠ ⊥) (hxy' : x ≠ y) (hyt : y ≠ ⊤) :
    Function.Injective (map x y) := by
  have hbt : (⊥ : α) ≠ ⊤ := fun he =>
    hyt (le_antisymm (le_top _) (le_trans (le_of_eq he.symm) (bot_le _)))
  have hxt : x ≠ ⊤ := fun he =>
    hyt (le_antisymm (le_top _) (le_trans (le_of_eq he.symm) hxy))
  have hyb : y ≠ ⊥ := fun he => hxb ((eq_bot_iff _).mpr (le_trans hxy (le_of_eq he)))
  intro i j hij
  refine Fin.ext ?_
  rcases four_val_cases i with h1|h1|h1|h1 <;> rcases four_val_cases j with h2|h2|h2|h2
  · rw [h1, h2]
  · exfalso; rw [map_zero x y h1, map_one x y h2] at hij; exact hxb hij.symm
  · exfalso; rw [map_zero x y h1, map_two x y h2] at hij; exact hyb hij.symm
  · exfalso; rw [map_zero x y h1, map_three x y h2] at hij; exact hbt hij
  · exfalso; rw [map_one x y h1, map_zero x y h2] at hij; exact hxb hij
  · rw [h1, h2]
  · exfalso; rw [map_one x y h1, map_two x y h2] at hij; exact hxy' hij
  · exfalso; rw [map_one x y h1, map_three x y h2] at hij; exact hxt hij
  · exfalso; rw [map_two x y h1, map_zero x y h2] at hij; exact hyb hij
  · exfalso; rw [map_two x y h1, map_one x y h2] at hij; exact hxy' hij.symm
  · rw [h1, h2]
  · exfalso; rw [map_two x y h1, map_three x y h2] at hij; exact hyt hij
  · exfalso; rw [map_three x y h1, map_zero x y h2] at hij; exact hbt hij.symm
  · exfalso; rw [map_three x y h1, map_one x y h2] at hij; exact hxt hij.symm
  · exfalso; rw [map_three x y h1, map_two x y h2] at hij; exact hyt hij.symm
  · rw [h1, h2]

end FourEmbed

/-- **A four element chain embeds** whenever two elements sit strictly between
the bounds with `neg x = ⊥` and `y ⇨ x = x`. -/
theorem four_embeds {α : Type} [HeytingAlgebra α] {x y : α}
    (hxy : x ⊑ y) (hnx : neg x = ⊥) (hyx : (y ⇨ x) = x)
    (hxb : x ≠ ⊥) (hxy' : x ≠ y) (hyt : y ≠ ⊤) : Embeds (Fin 4) α :=
  ⟨{ toFun := FourEmbed.map x y
     map_bot := FourEmbed.map_zero x y (by decide)
     map_top := FourEmbed.map_three x y (by decide)
     map_inf := FourEmbed.map_inf' x y hxy
     map_sup := FourEmbed.map_sup' x y hxy
     map_himp := FourEmbed.map_himp' x y hxy hnx hyx },
   FourEmbed.injective x y hxy hxb hxy' hyt⟩
