import Logics.Lattice

/-!
# Heyting algebras and their models

A Heyting algebra is a bounded lattice carrying an operation `⇨` right adjoint
to `⊓`.  Built on `Logics/Lattice.lean`, this file defines the class, the
language of propositional formulas, the interpretation of a formula in an
algebra under a valuation, a natural deduction calculus for intuitionistic
propositional logic, and the soundness theorem connecting the two.

Soundness is what makes these algebras useful as models: a formula that fails to
reach `⊤` somewhere has no derivation.  The three element chain is built at the
end as the smallest algebra where that failure can occur.

Nothing here depends on Mathlib.
-/

universe u

open PartialOrder Lattice BoundedLattice

/-! ## Heyting algebras -/

/-- A Heyting algebra: a bounded lattice in which every `b ⇨ c` is the largest
element whose meet with `b` lies below `c`. -/
class HeytingAlgebra (α : Type u) extends BoundedLattice α where
  himp : α → α → α
  /-- The defining adjunction, also called residuation. -/
  himp_adj (a b c : α) : le (inf a b) c ↔ le a (himp b c)

infixr:60 " ⇨ " => HeytingAlgebra.himp

namespace HeytingAlgebra

variable {α : Type u} [HeytingAlgebra α] (a b c : α)

/-- Negation is implication into `⊥`, exactly as in the object language. -/
def neg : α := a ⇨ ⊥

/-- Modus ponens, in algebraic form. -/
theorem himp_inf_le : (a ⇨ b) ⊓ a ⊑ b :=
  (himp_adj (a ⇨ b) a b).mpr le_rfl

theorem le_himp_of_inf_le {a b c : α} (h : a ⊓ b ⊑ c) : a ⊑ b ⇨ c :=
  (himp_adj a b c).mp h

theorem inf_le_of_le_himp {a b c : α} (h : a ⊑ b ⇨ c) : a ⊓ b ⊑ c :=
  (himp_adj a b c).mpr h

/-- Case analysis on a join.  In a Heyting algebra this follows from the
adjunction; in a bare lattice it would have to be assumed. -/
theorem sup_cases {a b c d : α} (h : c ⊑ a ⊔ b) (ha : a ⊓ c ⊑ d) (hb : b ⊓ c ⊑ d) :
    c ⊑ d :=
  have h' : a ⊔ b ⊑ c ⇨ d := sup_le (le_himp_of_inf_le ha) (le_himp_of_inf_le hb)
  have hc : c ⊓ c ⊑ d := inf_le_of_le_himp (le_trans h h')
  le_trans (le_of_eq (inf_idem c).symm) hc

/-- Implication between comparable elements is the top. -/
theorem himp_eq_top_of_le {a b : α} (h : a ⊑ b) : (a ⇨ b) = ⊤ :=
  (eq_top_iff _).mpr (le_himp_of_inf_le (by rw [top_inf]; exact h))

/-- Implying out of the top is the conclusion itself. -/
theorem himp_top_left : ((⊤ : α) ⇨ a) = a :=
  le_antisymm (by have h := himp_inf_le (⊤ : α) a; rwa [inf_top] at h)
    (le_himp_of_inf_le (inf_le_left a ⊤))

/-- The negation of an excluded middle is absurd: it lies below both `a` and
`neg a`, hence below their meet, which is `⊥`. -/
theorem neg_sup_neg_eq_bot (a : α) : neg (a ⊔ neg a) = ⊥ := by
  have h1 : neg (a ⊔ neg a) ⊓ (a ⊔ neg a) ⊑ ⊥ := himp_inf_le (a ⊔ neg a) ⊥
  have h2 : neg (a ⊔ neg a) ⊓ a ⊑ ⊥ :=
    le_trans (inf_le_inf le_rfl (le_sup_left a (neg a))) h1
  have h3 : neg (a ⊔ neg a) ⊑ neg a := le_himp_of_inf_le h2
  have h4 : neg (a ⊔ neg a) ⊑ a ⊔ neg a := le_trans h3 (le_sup_right a (neg a))
  have h5 : neg (a ⊔ neg a) ⊓ neg (a ⊔ neg a) ⊑ ⊥ :=
    le_trans (inf_le_inf le_rfl h4) h1
  exact (eq_bot_iff _).mpr (le_trans (le_of_eq (inf_idem _).symm) h5)

/-- `neg ⊥` is the top. -/
theorem neg_bot : neg (⊥ : α) = ⊤ := himp_eq_top_of_le le_rfl


/-! ### Implication and the lattice operations

The identities a congruence needs: implication composes, and it is monotone in
its conclusion and antitone in its hypothesis, uniformly enough that a pair of
implications bounds the implication between the combinations. -/

theorem himp_trans (x y z : α) : (x ⇨ y) ⊓ (y ⇨ z) ⊑ (x ⇨ z) := by
  refine le_himp_of_inf_le ?_
  have h1 : ((x ⇨ y) ⊓ (y ⇨ z)) ⊓ x ⊑ (y ⇨ z) ⊓ y := by
    refine le_inf (le_trans (inf_le_left _ _) (inf_le_right _ _)) ?_
    exact le_trans (inf_le_inf (inf_le_left _ _) le_rfl) (himp_inf_le x y)
  exact le_trans h1 (himp_inf_le y z)

theorem himp_le_inf (x y z : α) : (x ⇨ y) ⊓ (x ⇨ z) ⊑ (x ⇨ y ⊓ z) := by
  refine le_himp_of_inf_le (le_inf ?_ ?_)
  · exact le_trans (inf_le_inf (inf_le_left _ _) le_rfl) (himp_inf_le x y)
  · exact le_trans (inf_le_inf (inf_le_right _ _) le_rfl) (himp_inf_le x z)

theorem sup_himp_le (x y z : α) : (x ⇨ z) ⊓ (y ⇨ z) ⊑ ((x ⊔ y) ⇨ z) := by
  refine le_himp_of_inf_le (sup_cases (inf_le_right _ _) ?_ ?_)
  · exact le_trans (le_inf (le_trans (inf_le_right _ _)
      (le_trans (inf_le_left _ _) (inf_le_left _ _))) (inf_le_left _ _)) (himp_inf_le x z)
  · exact le_trans (le_inf (le_trans (inf_le_right _ _)
      (le_trans (inf_le_left _ _) (inf_le_right _ _))) (inf_le_left _ _)) (himp_inf_le y z)

theorem himp_inf_congr (x y x' y' : α) :
    (x ⇨ x') ⊓ (y ⇨ y') ⊑ ((x ⊓ y) ⇨ (x' ⊓ y')) := by
  refine le_himp_of_inf_le (le_inf ?_ ?_)
  · exact le_trans (inf_le_inf (inf_le_left _ _) (inf_le_left _ _)) (himp_inf_le x x')
  · exact le_trans (inf_le_inf (inf_le_right _ _) (inf_le_right _ _)) (himp_inf_le y y')

theorem himp_sup_congr (x y x' y' : α) :
    (x ⇨ x') ⊓ (y ⇨ y') ⊑ ((x ⊔ y) ⇨ (x' ⊔ y')) := by
  refine le_himp_of_inf_le (sup_cases (inf_le_right _ _) ?_ ?_)
  · refine le_trans ?_ (le_sup_left x' y')
    refine le_trans (le_inf (le_trans (inf_le_right _ _)
      (le_trans (inf_le_left _ _) (inf_le_left _ _))) (inf_le_left _ _)) ?_
    exact himp_inf_le x x'
  · refine le_trans ?_ (le_sup_right x' y')
    refine le_trans (le_inf (le_trans (inf_le_right _ _)
      (le_trans (inf_le_left _ _) (inf_le_right _ _))) (inf_le_left _ _)) ?_
    exact himp_inf_le y y'

theorem himp_himp_congr (x y x' y' : α) :
    (x' ⇨ x) ⊓ (y ⇨ y') ⊑ ((x ⇨ y) ⇨ (x' ⇨ y')) := by
  refine le_himp_of_inf_le (le_himp_of_inf_le ?_)
  have h1 : (((x' ⇨ x) ⊓ (y ⇨ y')) ⊓ (x ⇨ y)) ⊓ x' ⊑ (y ⇨ y') ⊓ y := by
    refine le_inf ?_ ?_
    · exact le_trans (inf_le_left _ _) (le_trans (inf_le_left _ _) (inf_le_right _ _))
    · have ha : (((x' ⇨ x) ⊓ (y ⇨ y')) ⊓ (x ⇨ y)) ⊓ x' ⊑ x :=
        le_trans (inf_le_inf (le_trans (inf_le_left _ _) (inf_le_left _ _)) le_rfl)
          (himp_inf_le x' x)
      exact le_trans (le_inf (le_trans (inf_le_left _ _) (inf_le_right _ _)) ha) (himp_inf_le x y)
  exact le_trans h1 (himp_inf_le y y')

/-- Currying, as an equality of elements. -/
theorem himp_curry (x y z : α) : ((x ⊓ y) ⇨ z) = (x ⇨ (y ⇨ z)) := by
  refine le_antisymm (le_himp_of_inf_le (le_himp_of_inf_le ?_)) (le_himp_of_inf_le ?_)
  · exact le_trans (le_of_eq (inf_assoc _ _ _)) (himp_inf_le (x ⊓ y) z)
  · refine le_trans (le_of_eq (inf_assoc _ _ _).symm) ?_
    exact le_trans (inf_le_inf (himp_inf_le x (y ⇨ z)) le_rfl) (himp_inf_le y z)

/-- An implication reaching the top means the hypothesis lies below the
conclusion: the converse of `himp_eq_top_of_le`. -/
theorem le_of_himp_eq_top {a b : α} (h : (a ⇨ b) = ⊤) : a ⊑ b := by
  have h1 : (a ⇨ b) ⊓ a ⊑ b := himp_inf_le a b
  rw [h, top_inf] at h1
  exact h1

/-- Two elements are equal as soon as each implies the other. -/
theorem eq_of_himp_inf_eq_top {a b : α} (h : ((a ⇨ b) ⊓ (b ⇨ a)) = ⊤) : a = b :=
  le_antisymm
    (le_of_himp_eq_top ((eq_top_iff _).mpr (h ▸ inf_le_left (a ⇨ b) (b ⇨ a))))
    (le_of_himp_eq_top ((eq_top_iff _).mpr (h ▸ inf_le_right (a ⇨ b) (b ⇨ a))))

/-! ### Negation

The facts a pair of complementary regular elements needs.  In any Heyting
algebra `neg t` and `neg (neg t)` meet at `⊥`, negate to each other, and each
is what the other implies it to be — so they always span a copy of the five
element fork, as soon as their join misses the top. -/

theorem inf_neg_eq_bot (a : α) : a ⊓ neg a = ⊥ :=
  (eq_bot_iff _).mpr (le_trans (le_of_eq (inf_comm a (neg a))) (himp_inf_le a ⊥))

theorem le_neg_neg (a : α) : a ⊑ neg (neg a) :=
  le_himp_of_inf_le (le_of_eq (inf_neg_eq_bot a))

theorem neg_neg_neg (a : α) : neg (neg (neg a)) = neg a := by
  refine le_antisymm ?_ ?_
  · refine le_himp_of_inf_le ?_
    exact le_trans (inf_le_inf le_rfl (le_neg_neg a)) (himp_inf_le _ ⊥)
  · exact le_himp_of_inf_le (le_trans (le_of_eq (inf_comm _ _)) (himp_inf_le (neg a) ⊥))

/-- `neg a ⇨ neg (neg a)` is `neg (neg a)`. -/
theorem neg_himp_neg_neg (a : α) : (neg a ⇨ neg (neg a)) = neg (neg a) := by
  refine le_antisymm (le_himp_of_inf_le ?_) (le_himp_of_inf_le (inf_le_left _ _))
  exact le_trans (le_inf (himp_inf_le _ _) (inf_le_right _ _))
    (le_trans (le_of_eq (inf_comm _ _)) (le_of_eq (inf_neg_eq_bot (neg a))))

/-- `neg (neg a) ⇨ neg a` is `neg a`. -/
theorem neg_neg_himp_neg (a : α) : (neg (neg a) ⇨ neg a) = neg a := by
  refine le_antisymm (le_himp_of_inf_le ?_) (le_himp_of_inf_le (inf_le_left _ _))
  have h1 : (neg (neg a) ⇨ neg a) ⊓ a ⊑ neg a :=
    le_trans (inf_le_inf le_rfl (le_neg_neg a)) (himp_inf_le _ _)
  exact le_trans (le_inf (inf_le_right _ _) h1) (le_of_eq (inf_neg_eq_bot a))

/-- The join of the two implies back to each of them. -/
theorem sup_neg_himp_left (a : α) : ((neg a ⊔ neg (neg a)) ⇨ neg a) = neg a := by
  refine le_antisymm ?_ (le_himp_of_inf_le (inf_le_left _ _))
  have h1 : ((neg a ⊔ neg (neg a)) ⇨ neg a) ⊓ neg (neg a) ⊑ neg a :=
    le_trans (inf_le_inf le_rfl (le_sup_right _ _)) (himp_inf_le _ _)
  have h3 : ((neg a ⊔ neg (neg a)) ⇨ neg a) ⊓ neg (neg a) ⊑ ⊥ :=
    le_trans (le_inf h1 (inf_le_right _ _)) (le_of_eq (inf_neg_eq_bot (neg a)))
  have h4 : ((neg a ⊔ neg (neg a)) ⇨ neg a) ⊑ neg (neg (neg a)) := le_himp_of_inf_le h3
  rwa [neg_neg_neg] at h4

theorem sup_neg_himp_right (a : α) :
    ((neg a ⊔ neg (neg a)) ⇨ neg (neg a)) = neg (neg a) := by
  refine le_antisymm ?_ (le_himp_of_inf_le (inf_le_left _ _))
  have h1 : ((neg a ⊔ neg (neg a)) ⇨ neg (neg a)) ⊓ neg a ⊑ neg (neg a) :=
    le_trans (inf_le_inf le_rfl (le_sup_left _ _)) (himp_inf_le _ _)
  have h3 : ((neg a ⊔ neg (neg a)) ⇨ neg (neg a)) ⊓ neg a ⊑ ⊥ :=
    le_trans (le_inf (inf_le_right _ _) h1) (le_of_eq (inf_neg_eq_bot (neg a)))
  exact le_himp_of_inf_le h3

/-- Weakening: a value lies below anything implying it. -/
theorem le_himp_self (a b : α) : a ⊑ (b ⇨ a) := le_himp_of_inf_le (inf_le_left a b)

/-- Negation is antitone. -/
theorem neg_antitone {a b : α} (h : a ⊑ b) : neg b ⊑ neg a :=
  le_himp_of_inf_le (le_trans (inf_le_inf le_rfl h) (himp_inf_le b ⊥))

/-- Implication is antitone in its hypothesis. -/
theorem himp_le_himp_left {x y z : α} (h : x ⊑ y) : (y ⇨ z) ⊑ (x ⇨ z) :=
  le_himp_of_inf_le (le_trans (inf_le_inf le_rfl h) (himp_inf_le y z))

/-- A negation lies below every arrow out of what it negates. -/
theorem neg_le_himp (a b : α) : neg a ⊑ (a ⇨ b) :=
  le_himp_of_inf_le (le_trans (himp_inf_le a ⊥) (bot_le b))

/-- An arrow into an excluded middle is dense: it lies above that excluded
middle, whose negation is absurd. -/
theorem neg_himp_sup_neg_eq_bot (a b : α) : neg (a ⇨ (b ⊔ neg b)) = ⊥ :=
  (eq_bot_iff _).mpr (le_trans (neg_antitone (le_himp_self (b ⊔ neg b) a))
    (le_of_eq (neg_sup_neg_eq_bot b)))

end HeytingAlgebra

/-- **A Heyting algebra is distributive**: split `a ⊓ (b ⊔ c)` by `sup_cases`
along `b ⊔ c`. -/
instance HeytingAlgebra.distrib {α : Type u} [HeytingAlgebra α] : Distrib α where
  inf_sup_le a b c := by
    refine HeytingAlgebra.sup_cases (Lattice.inf_le_right a (b ⊔ c)) ?_ ?_
    · exact PartialOrder.le_trans (Lattice.le_inf
        (PartialOrder.le_trans (Lattice.inf_le_right _ _) (Lattice.inf_le_left _ _))
        (Lattice.inf_le_left _ _)) (Lattice.le_sup_left _ _)
    · exact PartialOrder.le_trans (Lattice.le_inf
        (PartialOrder.le_trans (Lattice.inf_le_right _ _) (Lattice.inf_le_left _ _))
        (Lattice.inf_le_left _ _)) (Lattice.le_sup_right _ _)

/-- The arrow of a product is taken componentwise too, the adjunction holding
in each component separately. -/
instance HProd.instHeytingAlgebra {α β : Type u}
    [HeytingAlgebra α] [HeytingAlgebra β] : HeytingAlgebra (α × β) where
  himp p q := (p.1 ⇨ q.1, p.2 ⇨ q.2)
  himp_adj a b c := by
    constructor
    · exact fun h => ⟨HeytingAlgebra.le_himp_of_inf_le h.1,
        HeytingAlgebra.le_himp_of_inf_le h.2⟩
    · exact fun h => ⟨HeytingAlgebra.inf_le_of_le_himp h.1,
        HeytingAlgebra.inf_le_of_le_himp h.2⟩

/-! ## Upward closed sets of a frame

Every preordered set of points gives rise to a Heyting algebra: its upward
closed subsets, ordered by inclusion.  This is the construction behind every
concrete algebra in this file, and it is also the Kripke reading of the
connectives, with points as states of knowledge and an element as the set of
states at which a proposition holds.  Only reflexivity and transitivity are
used; antisymmetry of the points plays no part.

The converse, that every finite Heyting algebra is isomorphic to the upward
closed sets of its poset of join irreducible elements, is Birkhoff's
representation theorem and is not formalised here. -/

/-- A frame: points carrying a preorder. -/
class Frame (P : Type u) where
  le : P → P → Prop
  le_refl (p : P) : le p p
  le_trans {p q r : P} : le p q → le q r → le p r

infix:50 " ≼ " => Frame.le

/-- No two distinct points lie below each other: the preorder is a partial
order. -/
def Frame.Antisymm (P : Type u) [Frame P] : Prop := ∀ p q : P, p ≼ q → q ≼ p → p = q

/-- An upward closed set of frame points: once a point is in, everything later
is in.  This is exactly persistence of truth along the order. -/
structure Upset (P : Type u) [Frame P] where
  mem : P → Prop
  upward {p q : P} : p ≼ q → mem p → mem q

namespace Upset

variable {P : Type u} [Frame P]

/-- Two upward closed sets with the same points are equal. -/
theorem ext {U V : Upset P} (h : ∀ p, U.mem p ↔ V.mem p) : U = V := by
  obtain ⟨u, hu⟩ := U
  obtain ⟨v, hv⟩ := V
  have : u = v := funext fun p => propext (h p)
  subst this
  rfl

instance : PartialOrder (Upset P) where
  le U V := ∀ p, U.mem p → V.mem p
  le_refl _ _ h := h
  le_trans h₁ h₂ p hp := h₂ p (h₁ p hp)
  le_antisymm h₁ h₂ := ext fun p => ⟨h₁ p, h₂ p⟩

instance : Lattice (Upset P) where
  inf U V := ⟨fun p => U.mem p ∧ V.mem p,
              fun h hp => ⟨U.upward h hp.1, V.upward h hp.2⟩⟩
  sup U V := ⟨fun p => U.mem p ∨ V.mem p,
              fun h hp => hp.elim (fun x => Or.inl (U.upward h x))
                                  (fun y => Or.inr (V.upward h y))⟩
  inf_le_left _ _ _ hp := hp.1
  inf_le_right _ _ _ hp := hp.2
  le_inf h₁ h₂ p hp := ⟨h₁ p hp, h₂ p hp⟩
  le_sup_left _ _ _ hp := Or.inl hp
  le_sup_right _ _ _ hp := Or.inr hp
  sup_le h₁ h₂ p hp := hp.elim (h₁ p) (h₂ p)

instance : BoundedLattice (Upset P) where
  top := ⟨fun _ => True, fun _ _ => trivial⟩
  bot := ⟨fun _ => False, fun _ h => h.elim⟩
  le_top _ _ _ := trivial
  bot_le _ _ h := h.elim

/-- `U ⇨ V` holds at `p` when every later point in `U` is also in `V`.  Looking
forward along the order is what makes this upward closed, and it is why
implication in a Kripke model quantifies over future states. -/
instance : HeytingAlgebra (Upset P) where
  himp U V := ⟨fun p => ∀ q, p ≼ q → U.mem q → V.mem q,
               fun hpq hp r hqr hu => hp r (Frame.le_trans hpq hqr) hu⟩
  himp_adj U V W := by
    constructor
    · intro h p hu q hpq hv
      exact h q ⟨U.upward hpq hu, hv⟩
    · intro h p hp
      exact h p hp.1 p (Frame.le_refl p) hp.2

/-- The upward closed set of everything above a point. -/
def up (p : P) : Upset P := ⟨fun q => p ≼ q, fun h hp => Frame.le_trans hp h⟩

/-- A point is in the join of a list exactly when it is in one of its entries. -/
theorem mem_supList : ∀ {L : List (Upset P)} {p : P},
    (supList L).mem p ↔ ∃ U ∈ L, U.mem p
  | [], _ => ⟨fun h => h.elim, fun ⟨_, hU, _⟩ => by cases hU⟩
  | U :: t, p => by
    show U.mem p ∨ (supList t).mem p ↔ _
    rw [mem_supList]
    constructor
    · rintro (h | ⟨V, hV, hp⟩)
      · exact ⟨U, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact ⟨V, List.mem_cons_of_mem U hV, hp⟩
    · rintro ⟨V, hV, hp⟩
      rcases List.mem_cons.mp hV with rfl | hV
      · exact Or.inl hp
      · exact Or.inr ⟨V, hV, hp⟩

/-! ### A worked frame

Reading `Fin n` as a linear frame recovers the chains, and shows the
construction is not vacuous: the proposition true only at the later of two
states is never refuted, so its negation is empty and excluded middle fails. -/

instance frameFin {n : Nat} : Frame (Fin n) where
  le a b := a.val ≤ b.val
  le_refl a := Nat.le_refl a.val
  le_trans h₁ h₂ := Nat.le_trans h₁ h₂

/-- The proposition holding only at the later of two states. -/
def later : Upset (Fin 2) where
  mem p := p.val = 1
  upward {p q} h hp := by
    have h' : p.val ≤ q.val := h
    have := q.isLt
    omega

theorem later_em_fails : later ⊔ HeytingAlgebra.neg later ≠ (⊤ : Upset (Fin 2)) := by
  intro h
  have h0 : (later ⊔ HeytingAlgebra.neg later).mem 0 := by rw [h]; trivial
  cases h0 with
  | inl hl => exact Nat.noConfusion hl
  | inr hn => exact hn 1 (Nat.zero_le 1) rfl

end Upset

/-! ## Minimal points

An upward closed set is entered at its minimal points, and whether it has one
entrance or several is a property of the frame rather than of any formula.  It
is what decides several of the weaker principles, so it is recorded here. -/

/-- Every inhabited set of points has a minimal one, as it does in any finite
frame (`hasMinimal_of_list`). -/
def HasMinimal (P : Type u) [Frame P] : Prop :=
  ∀ S : P → Prop, (∃ p, S p) → ∃ m, S m ∧ ∀ q, S q → q ≼ m → m ≼ q

/-- A frame whose points a list can name has minimal points: run through the
list keeping the lowest point met so far, and the one kept at the end has
nothing below it. -/
theorem hasMinimal_of_list {P : Type u} [Frame P] (l : List P) (hl : ∀ p, p ∈ l) :
    HasMinimal P := by
  have key : ∀ (l : List P) (S : P → Prop), (∃ p, p ∈ l ∧ S p) →
      ∃ m, S m ∧ ∀ q, q ∈ l → S q → q ≼ m → m ≼ q := by
    intro l S
    induction l with
    | nil => intro ⟨p, hp, _⟩; cases hp
    | cons a t ih =>
      intro hex
      by_cases ht : ∃ p, p ∈ t ∧ S p
      · obtain ⟨m, hSm, hmin⟩ := ih ht
        by_cases hlow : S a ∧ a ≼ m ∧ ¬ m ≼ a
        · refine ⟨a, hlow.1, fun q hq hSq hqa => ?_⟩
          rcases List.mem_cons.mp hq with rfl | hqt
          · exact Frame.le_refl _
          · exact Frame.le_trans hlow.2.1
              (hmin q hqt hSq (Frame.le_trans hqa hlow.2.1))
        · refine ⟨m, hSm, fun q hq hSq hqm => ?_⟩
          rcases List.mem_cons.mp hq with rfl | hqt
          · exact Classical.byContradiction fun hmq => hlow ⟨hSq, hqm, hmq⟩
          · exact hmin q hqt hSq hqm
      · obtain ⟨p, hp, hSp⟩ := hex
        have hSa : S a := by
          rcases List.mem_cons.mp hp with rfl | hpt
          · exact hSp
          · exact absurd ⟨p, hpt, hSp⟩ ht
        refine ⟨a, hSa, fun q hq hSq _ => ?_⟩
        rcases List.mem_cons.mp hq with rfl | hqt
        · exact Frame.le_refl _
        · exact absurd ⟨q, hqt, hSq⟩ ht
  intro S ⟨p, hp⟩
  obtain ⟨m, hSm, hmin⟩ := key l S ⟨p, hl p, hp⟩
  exact ⟨m, hSm, fun q hSq hqm => hmin q (hl q) hSq hqm⟩

namespace Upset

variable {P : Type u} [Frame P]

/-- `m` lies below every point of `V`. -/
def Least (V : Upset P) (m : P) : Prop := V.mem m ∧ ∀ q, V.mem q → m ≼ q

/-- Nothing in `V` lies strictly below `m`. -/
def Minimal (V : Upset P) (m : P) : Prop :=
  V.mem m ∧ ∀ q, V.mem q → q ≼ m → m ≼ q

/-- `V` is entered at a single point: inhabited only if it has a least one. -/
def Principal (V : Upset P) : Prop := ∀ p, V.mem p → ∃ m, V.Least m

/-- `V` is entered at two unrelated points. -/
def Splits (V : Upset P) : Prop :=
  ∃ m m', V.Minimal m ∧ V.Minimal m' ∧ ¬ m ≼ m' ∧ ¬ m' ≼ m

/-- Where minimal points exist the two are exact opposites. -/
theorem not_principal_iff_splits (hm : HasMinimal P) (V : Upset P) :
    ¬ V.Principal ↔ V.Splits := by
  constructor
  · intro hnp
    have hex : ∃ p, V.mem p ∧ ¬ ∃ m, V.Least m :=
      Classical.byContradiction fun hcon =>
        hnp (fun p hp => Classical.byContradiction fun hl => hcon ⟨p, hp, hl⟩)
    obtain ⟨p, hp, hnl⟩ := hex
    obtain ⟨m, hmem, hmmin⟩ := hm V.mem ⟨p, hp⟩
    have hw : ∃ w, V.mem w ∧ ¬ m ≼ w :=
      Classical.byContradiction fun hcon =>
        hnl ⟨m, hmem, fun q hq =>
          Classical.byContradiction fun hmq => hcon ⟨q, hq, hmq⟩⟩
    obtain ⟨w, hwmem, hmw⟩ := hw
    obtain ⟨m', hm'D, hm'min⟩ :=
      hm (fun q => V.mem q ∧ q ≼ w) ⟨w, hwmem, Frame.le_refl w⟩
    refine ⟨m, m', ⟨hmem, hmmin⟩, ⟨hm'D.1, fun q hq hqm' =>
      hm'min q ⟨hq, Frame.le_trans hqm' hm'D.2⟩ hqm'⟩, ?_, ?_⟩
    · exact fun hmm' => hmw (Frame.le_trans hmm' hm'D.2)
    · exact fun hm'm => hmw (Frame.le_trans (hmmin m' hm'D.1 hm'm) hm'D.2)
  · rintro ⟨m, m', hmin, hmin', hmm', _⟩ hP
    obtain ⟨l, hlmem, hlleast⟩ := hP m hmin.1
    exact hmm' (Frame.le_trans (hmin.2 l hlmem (hlleast m hmin.1))
      (hlleast m' hmin'.1))

end Upset

/-! ## The language -/

/-- Propositional formulas over variables indexed by `Nat`. -/
inductive Form where
  | var : Nat → Form
  | fls : Form
  | and : Form → Form → Form
  | or : Form → Form → Form
  | imp : Form → Form → Form
  deriving DecidableEq, Repr

namespace Form

/-- `¬ φ` abbreviates `φ → ⊥`, matching the object language. -/
def neg (p : Form) : Form := .imp p .fls

/-- `⊤` abbreviates `⊥ → ⊥`. -/
def tru : Form := .imp .fls .fls

end Form

/-! ## Models -/

open HeytingAlgebra

/-- The interpretation of a formula in a Heyting algebra under a valuation.  A
*model* is the pair of an algebra `α` and a valuation `v : Nat → α`. -/
def Form.eval {α : Type u} [HeytingAlgebra α] (v : Nat → α) : Form → α
  | .var n => v n
  | .fls => ⊥
  | .and p q => p.eval v ⊓ q.eval v
  | .or p q => p.eval v ⊔ q.eval v
  | .imp p q => p.eval v ⇨ q.eval v

/-- A formula is valid when it evaluates to `⊤` in every model. -/
def Valid (p : Form) : Prop :=
  ∀ (α : Type) [HeytingAlgebra α] (v : Nat → α), p.eval v = ⊤

/-- A formula that is not valid in an algebra misses the top value somewhere. -/
theorem exists_ne_top {α : Type} [HeytingAlgebra α] {p : Form}
    (h : ¬ ∀ v : Nat → α, p.eval v = ⊤) : ∃ v : Nat → α, p.eval v ≠ ⊤ := by
  refine Classical.byContradiction fun hne => h ?_
  intro v
  exact Classical.byContradiction fun hv => hne ⟨v, hv⟩

/-- A context is interpreted by the meet of its members. -/
def evalCtx {α : Type u} [HeytingAlgebra α] (v : Nat → α) : List Form → α
  | [] => ⊤
  | p :: Γ => p.eval v ⊓ evalCtx v Γ

/-! ## Intuitionistic natural deduction -/

/-- Derivability in intuitionistic propositional logic. -/
inductive Derives : List Form → Form → Prop where
  | ax {Γ p} : p ∈ Γ → Derives Γ p
  | flsE {Γ p} : Derives Γ .fls → Derives Γ p
  | andI {Γ p q} : Derives Γ p → Derives Γ q → Derives Γ (.and p q)
  | andE₁ {Γ p q} : Derives Γ (.and p q) → Derives Γ p
  | andE₂ {Γ p q} : Derives Γ (.and p q) → Derives Γ q
  | orI₁ {Γ p q} : Derives Γ p → Derives Γ (.or p q)
  | orI₂ {Γ p q} : Derives Γ q → Derives Γ (.or p q)
  | orE {Γ p q r} : Derives Γ (.or p q) → Derives (p :: Γ) r → Derives (q :: Γ) r →
      Derives Γ r
  | impI {Γ p q} : Derives (p :: Γ) q → Derives Γ (.imp p q)
  | impE {Γ p q} : Derives Γ (.imp p q) → Derives Γ p → Derives Γ q

notation:40 Γ " ⊢ " p => Derives Γ p

namespace Derives

/-! ### Structural rules

The rules above work in a fixed context, but a derivation stays valid in any
larger one, and a hypothesis that is itself derivable can be discharged. -/

/-- Membership transfers through a common head. -/
theorem mem_cons_of {Γ Δ : List Form} (hs : ∀ q ∈ Γ, q ∈ Δ) (r : Form) :
    ∀ q ∈ r :: Γ, q ∈ r :: Δ := by
  intro q hq
  simp only [List.mem_cons] at hq ⊢
  exact hq.imp id (hs q)

/-- Weakening: a derivation survives any enlargement of its context. -/
theorem weaken {Γ : List Form} {p : Form} (d : Γ ⊢ p) :
    ∀ Δ : List Form, (∀ q ∈ Γ, q ∈ Δ) → (Δ ⊢ p) := by
  induction d with
  | ax h => intro Δ hs; exact .ax (hs _ h)
  | flsE _ ih => intro Δ hs; exact .flsE (ih Δ hs)
  | andI _ _ ih₁ ih₂ => intro Δ hs; exact .andI (ih₁ Δ hs) (ih₂ Δ hs)
  | andE₁ _ ih => intro Δ hs; exact .andE₁ (ih Δ hs)
  | andE₂ _ ih => intro Δ hs; exact .andE₂ (ih Δ hs)
  | orI₁ _ ih => intro Δ hs; exact .orI₁ (ih Δ hs)
  | orI₂ _ ih => intro Δ hs; exact .orI₂ (ih Δ hs)
  | orE _ _ _ ih ih₁ ih₂ =>
      intro Δ hs
      exact .orE (ih Δ hs) (ih₁ _ (mem_cons_of hs _)) (ih₂ _ (mem_cons_of hs _))
  | impI _ ih => intro Δ hs; exact .impI (ih _ (mem_cons_of hs _))
  | impE _ _ ih₁ ih₂ => intro Δ hs; exact .impE (ih₁ Δ hs) (ih₂ Δ hs)

/-- Cut: a hypothesis derivable in the remaining context can be removed. -/
theorem cut {Γ : List Form} {p q : Form} (d₁ : Γ ⊢ p) (d₂ : (p :: Γ) ⊢ q) : Γ ⊢ q :=
  .impE (.impI d₂) d₁

/-- `⊤` is derivable in every context. -/
theorem tru {Γ : List Form} : Γ ⊢ Form.tru := .impI (.ax (by simp))

/-! ### Hypotheses by position

`impI` and `orE` put each new hypothesis at the front of the context, so the
most recent one is `h₀`, the one before it `h₁`, and so on. -/

section Position

variable {Γ : List Form} {p₀ p₁ p₂ p₃ p₄ p₅ : Form}

theorem h₀ : (p₀ :: Γ) ⊢ p₀ := .ax (by simp)
theorem h₁ : (p₀ :: p₁ :: Γ) ⊢ p₁ := .ax (by simp)
theorem h₂ : (p₀ :: p₁ :: p₂ :: Γ) ⊢ p₂ := .ax (by simp)
theorem h₃ : (p₀ :: p₁ :: p₂ :: p₃ :: Γ) ⊢ p₃ := .ax (by simp)
theorem h₄ : (p₀ :: p₁ :: p₂ :: p₃ :: p₄ :: Γ) ⊢ p₄ := .ax (by simp)
theorem h₅ : (p₀ :: p₁ :: p₂ :: p₃ :: p₄ :: p₅ :: Γ) ⊢ p₅ := .ax (by simp)

/-- A hypothesis further down, by its position. -/
theorem nth (i : Nat) (h : Γ[i]? = some p₀) : Γ ⊢ p₀ := .ax (List.mem_of_getElem? h)

end Position

/-- **The deduction theorem**, both ways: a hypothesis can be discharged into an
implication, and an implication taken apart into a hypothesis. -/
theorem deduction {Γ : List Form} {p q : Form} : ((p :: Γ) ⊢ q) ↔ (Γ ⊢ .imp p q) :=
  ⟨impI, fun d => .impE (d.weaken _ fun _ hr => List.mem_cons_of_mem _ hr)
    (.ax (List.mem_cons_self ..))⟩

/-- Whatever one context derives of another survives adding the same
hypothesis to both. -/
theorem derives_cons {Γ Δ : List Form} (hs : ∀ q ∈ Δ, Γ ⊢ q) (p : Form) :
    ∀ q ∈ p :: Δ, (p :: Γ) ⊢ q := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact .ax (List.mem_cons_self ..)
  · exact (hs q hq).weaken _ fun _ hr => List.mem_cons_of_mem _ hr

/-- **Cut against a whole context.**  A derivation from `Δ` gives one from `Γ` as
soon as every hypothesis in `Δ` is derivable from `Γ`: each use of a hypothesis
is replaced by its derivation. -/
theorem trans {Δ : List Form} {r : Form} (d : Δ ⊢ r) :
    ∀ {Γ : List Form}, (∀ q ∈ Δ, Γ ⊢ q) → (Γ ⊢ r) := by
  induction d with
  | ax h => intro _ hs; exact hs _ h
  | flsE _ ih => intro _ hs; exact .flsE (ih hs)
  | andI _ _ ih₁ ih₂ => intro _ hs; exact .andI (ih₁ hs) (ih₂ hs)
  | andE₁ _ ih => intro _ hs; exact .andE₁ (ih hs)
  | andE₂ _ ih => intro _ hs; exact .andE₂ (ih hs)
  | orI₁ _ ih => intro _ hs; exact .orI₁ (ih hs)
  | orI₂ _ ih => intro _ hs; exact .orI₂ (ih hs)
  | orE _ _ _ ih ih₁ ih₂ =>
      intro _ hs; exact .orE (ih hs) (ih₁ (derives_cons hs _)) (ih₂ (derives_cons hs _))
  | impI _ ih => intro _ hs; exact .impI (ih (derives_cons hs _))
  | impE _ _ ih₁ ih₂ => intro _ hs; exact .impE (ih₁ hs) (ih₂ hs)

theorem evalCtx_le_of_mem {α : Type u} [HeytingAlgebra α] (v : Nat → α) {p : Form}
    {Γ : List Form} (h : p ∈ Γ) : evalCtx v Γ ⊑ p.eval v := by
  induction h with
  | head => exact inf_le_left _ _
  | tail _ _ ih => exact le_trans (inf_le_right _ _) ih

/-- Soundness: a derivation's conclusion dominates the meet of its hypotheses in
every model. -/
theorem soundness {α : Type u} [HeytingAlgebra α] (v : Nat → α) {Γ : List Form}
    {p : Form} (d : Γ ⊢ p) : evalCtx v Γ ⊑ p.eval v := by
  induction d with
  | ax h => exact evalCtx_le_of_mem v h
  | flsE _ ih => exact le_trans ih (bot_le _)
  | andI _ _ ih₁ ih₂ => exact le_inf ih₁ ih₂
  | andE₁ _ ih => exact le_trans ih (inf_le_left _ _)
  | andE₂ _ ih => exact le_trans ih (inf_le_right _ _)
  | orI₁ _ ih => exact le_trans ih (le_sup_left _ _)
  | orI₂ _ ih => exact le_trans ih (le_sup_right _ _)
  | orE _ _ _ ih ih₁ ih₂ => exact sup_cases ih ih₁ ih₂
  | impI _ ih =>
      refine le_himp_of_inf_le ?_
      rw [inf_comm]
      exact ih
  | impE _ _ ih₁ ih₂ => exact le_trans (le_inf ih₁ ih₂) (himp_inf_le _ _)

/-- A closed derivation gives a valid formula. -/
theorem valid_of_derives {p : Form} (d : [] ⊢ p) : Valid p := by
  intro α _ v
  exact (eq_top_iff _).mpr (soundness v d)

end Derives

/-! ## Entailment between single formulas

`Ent p q` is a derivation of `q` from `p` alone.  Read as a one step
implication it gives a calculus in which a formula can be rewritten inside a
connective, which is what an induction over formula structure needs. -/

/-- `q` is derivable from the single hypothesis `p`. -/
def Ent (p q : Form) : Prop := [p] ⊢ q

namespace Ent

theorem refl (p : Form) : Ent p p := Derives.ax (by simp)

/-- An entailment applies to any derivation of its hypothesis. -/
theorem mp {Γ : List Form} {p q : Form} (h : Ent p q) (d : Γ ⊢ p) : Γ ⊢ q :=
  Derives.cut d (Derives.weaken h _ (by intro r hr; simp at hr; simp [hr]))

theorem trans {p q r : Form} (h₁ : Ent p q) (h₂ : Ent q r) : Ent p r := mp h₂ h₁

theorem fls (p : Form) : Ent .fls p := Derives.flsE (Derives.ax (by simp))
theorem tru (p : Form) : Ent p Form.tru := Derives.tru

theorem and_left (p q : Form) : Ent (.and p q) p :=
  Derives.andE₁ (q := q) (Derives.ax (by simp))
theorem and_right (p q : Form) : Ent (.and p q) q :=
  Derives.andE₂ (p := p) (Derives.ax (by simp))
theorem and_intro {r p q : Form} (h₁ : Ent r p) (h₂ : Ent r q) : Ent r (.and p q) :=
  Derives.andI h₁ h₂

theorem or_left (p q : Form) : Ent p (.or p q) := Derives.orI₁ (Derives.ax (by simp))
theorem or_right (p q : Form) : Ent q (.or p q) := Derives.orI₂ (Derives.ax (by simp))
theorem or_elim {p q r : Form} (h₁ : Ent p r) (h₂ : Ent q r) : Ent (.or p q) r :=
  Derives.orE (p := p) (q := q) (Derives.ax (by simp)) (mp h₁ (Derives.ax (by simp)))
    (mp h₂ (Derives.ax (by simp)))

/-- A provable implication is derivable from anything. -/
theorem imp_intro {r p q : Form} (h : Ent p q) : Ent r (.imp p q) :=
  Derives.impI (mp h (Derives.ax (by simp)))

/-- Weakening inside an implication. -/
theorem imp_weak (p q : Form) : Ent q (.imp p q) := Derives.impI (Derives.ax (by simp))

/-- An implication out of `⊤` is its own conclusion. -/
theorem imp_tru_left (q : Form) : Ent (.imp Form.tru q) q :=
  Derives.impE (Derives.ax (by simp)) Derives.tru

theorem and_cong {p p' q q' : Form} (h₁ : Ent p p') (h₂ : Ent q q') :
    Ent (.and p q) (.and p' q') :=
  Derives.andI (mp h₁ (Derives.andE₁ (q := q) (Derives.ax (by simp))))
    (mp h₂ (Derives.andE₂ (p := p) (Derives.ax (by simp))))

theorem or_cong {p p' q q' : Form} (h₁ : Ent p p') (h₂ : Ent q q') :
    Ent (.or p q) (.or p' q') :=
  or_elim (trans h₁ (or_left p' q')) (trans h₂ (or_right p' q'))

/-- Residuation, one way: a hypothesis can be moved out of a conjunction. -/
theorem curry {p q r : Form} (h : Ent (.and p q) r) : Ent p (.imp q r) :=
  Derives.impI (mp h (Derives.andI (Derives.ax (by simp)) (Derives.ax (by simp))))

/-- Residuation, the other way. -/
theorem uncurry {p q r : Form} (h : Ent p (.imp q r)) : Ent (.and p q) r :=
  Derives.impE (mp h (Derives.andE₁ (q := q) (Derives.ax (by simp))))
    (Derives.andE₂ (p := p) (Derives.ax (by simp)))

/-- Implication is contravariant in its hypothesis. -/
theorem imp_cong {p p' q q' : Form} (h₁ : Ent p' p) (h₂ : Ent q q') :
    Ent (.imp p q) (.imp p' q') :=
  Derives.impI (mp h₂ (Derives.impE (Derives.ax (by simp)) (mp h₁ (Derives.ax (by simp)))))

end Ent

/-! ## Substitution

A schema is a formula together with all of its substitution instances.  The
substitution lemma says that evaluating an instance is the same as evaluating
the original under a shifted valuation, which is what lets a single algebra
refute every instance of a schema at once. -/

/-- Replace each variable by a formula. -/
def Form.subst (σ : Nat → Form) : Form → Form
  | .var n => σ n
  | .fls => .fls
  | .and p q => .and (p.subst σ) (q.subst σ)
  | .or p q => .or (p.subst σ) (q.subst σ)
  | .imp p q => .imp (p.subst σ) (q.subst σ)

theorem Form.eval_subst {α : Type u} [HeytingAlgebra α] (v : Nat → α) (σ : Nat → Form) :
    ∀ p : Form, (p.subst σ).eval v = p.eval (fun n => (σ n).eval v)
  | .var _ => rfl
  | .fls => rfl
  | .and p q => by simp only [Form.subst, Form.eval, eval_subst v σ p, eval_subst v σ q]
  | .or p q => by simp only [Form.subst, Form.eval, eval_subst v σ p, eval_subst v σ q]
  | .imp p q => by simp only [Form.subst, Form.eval, eval_subst v σ p, eval_subst v σ q]

/-- The substitution applying a formula to arguments: the `n`th variable
becomes the `n`th entry of `l`, and variables past its end stay as they are. -/
def Form.args (l : List Form) : Nat → Form := fun n => l.getD n (.var n)

/-- Substituting each variable for itself changes nothing. -/
theorem Form.subst_var : ∀ p : Form, p.subst .var = p
  | .var _ => rfl
  | .fls => rfl
  | .and p q => by show Form.and _ _ = _; rw [subst_var p, subst_var q]
  | .or p q => by show Form.or _ _ = _; rw [subst_var p, subst_var q]
  | .imp p q => by show Form.imp _ _ = _; rw [subst_var p, subst_var q]

/-- Substituting twice is substituting once, by the composite. -/
theorem Form.subst_subst (σ τ : Nat → Form) :
    ∀ p : Form, (p.subst σ).subst τ = p.subst (fun n => (σ n).subst τ)
  | .var _ => rfl
  | .fls => rfl
  | .and p q => by show Form.and _ _ = Form.and _ _; rw [subst_subst σ τ p, subst_subst σ τ q]
  | .or p q => by show Form.or _ _ = Form.or _ _; rw [subst_subst σ τ p, subst_subst σ τ q]
  | .imp p q => by show Form.imp _ _ = Form.imp _ _; rw [subst_subst σ τ p, subst_subst σ τ q]

/-- **Substitution preserves derivations.**  Replacing the variables throughout
a derivation, in its hypotheses and its conclusion alike, gives a derivation
again, since every rule is schematic in the formulas it mentions. -/
theorem Derives.subst (σ : Nat → Form) {Γ : List Form} {p : Form} (d : Γ ⊢ p) :
    Γ.map (Form.subst σ) ⊢ p.subst σ := by
  induction d with
  | ax h => exact .ax (List.mem_map_of_mem h)
  | flsE _ ih => exact .flsE ih
  | andI _ _ ih₁ ih₂ => exact .andI ih₁ ih₂
  | andE₁ _ ih => exact .andE₁ ih
  | andE₂ _ ih => exact .andE₂ ih
  | orI₁ _ ih => exact .orI₁ ih
  | orI₂ _ ih => exact .orI₂ ih
  | orE _ _ _ ih ih₁ ih₂ => exact .orE ih ih₁ ih₂
  | impI _ ih => exact .impI ih
  | impE _ _ ih₁ ih₂ => exact .impE ih₁ ih₂

/-- `p` follows from the schema `X` when some finite list of substitution
instances of `X` derives it. -/
def DerivesFromSchema (X p : Form) : Prop :=
  ∃ Γ : List Form, (∀ q ∈ Γ, ∃ σ : Nat → Form, q = X.subst σ) ∧ (Γ ⊢ p)

namespace DerivesFromSchema

/-- An algebra in which every valuation makes `X` top also makes top of
everything the schema `X` derives.  Contrapositively, a single algebra that
validates `X` but not `p` shows that no instantiation of `X` proves `p`. -/
theorem valid {α : Type u} [HeytingAlgebra α] {X p : Form}
    (hX : ∀ w : Nat → α, X.eval w = ⊤) (h : DerivesFromSchema X p) (v : Nat → α) :
    p.eval v = ⊤ := by
  obtain ⟨Γ, hΓ, d⟩ := h
  have hctx : evalCtx v Γ = ⊤ := by
    clear d
    induction Γ with
    | nil => rfl
    | cons q Γ ih =>
      obtain ⟨σ, hq⟩ := hΓ q (List.mem_cons_self ..)
      have h1 : q.eval v = ⊤ := by rw [hq, Form.eval_subst]; exact hX _
      have h2 : evalCtx v Γ = ⊤ := ih (fun r hr => hΓ r (List.mem_cons_of_mem q hr))
      show q.eval v ⊓ evalCtx v Γ = ⊤
      rw [h1, h2]
      exact BoundedLattice.inf_top ⊤
  exact (BoundedLattice.eq_top_iff _).mpr (hctx ▸ Derives.soundness v d)

/-- Every schema derives itself: it is its own instance, under the identity
substitution. -/
theorem refl (X : Form) : DerivesFromSchema X X :=
  ⟨[X], fun q hq => ⟨.var, by rw [List.mem_singleton.mp hq, Form.subst_var]⟩,
    .ax (List.mem_singleton.mpr rfl)⟩

/-- **Derivability from a schema is transitive.**  Each instance of `Y` that
the derivation of `Z` uses is derived from instances of `X`, by substituting
into the derivation of `Y` (`Derives.subst`); an instance of an instance of `X`
is an instance of `X` (`Form.subst_subst`); and cutting those derivations
against the hypotheses of the derivation of `Z` (`Derives.trans`) leaves one
from instances of `X` alone. -/
theorem trans {X Y Z : Form} (h₁ : DerivesFromSchema X Y) (h₂ : DerivesFromSchema Y Z) :
    DerivesFromSchema X Z := by
  obtain ⟨Γ, hΓ, dY⟩ := h₁
  obtain ⟨Δ, hΔ, dZ⟩ := h₂
  suffices H : ∀ Δ : List Form, (∀ q ∈ Δ, ∃ τ : Nat → Form, q = Y.subst τ) →
      ∃ Θ : List Form, (∀ r ∈ Θ, ∃ ρ : Nat → Form, r = X.subst ρ) ∧ ∀ q ∈ Δ, Θ ⊢ q by
    obtain ⟨Θ, hΘ, hq⟩ := H Δ hΔ
    exact ⟨Θ, hΘ, dZ.trans hq⟩
  intro Δ hΔ
  induction Δ with
  | nil => exact ⟨[], (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | cons q Δ ih =>
    obtain ⟨τ, rfl⟩ := hΔ q (List.mem_cons_self ..)
    obtain ⟨Θ, hΘ, hd⟩ := ih fun r hr => hΔ r (List.mem_cons_of_mem _ hr)
    refine ⟨Γ.map (Form.subst τ) ++ Θ, fun r hr => ?_, fun r hr => ?_⟩
    · rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
        obtain ⟨σ, rfl⟩ := hΓ s hs
        exact ⟨_, Form.subst_subst σ τ X⟩
      · exact hΘ r hr
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact (dY.subst τ).weaken _ fun _ h => List.mem_append_left _ h
      · exact (hd r hr).weaken _ fun _ h => List.mem_append_right _ h

/-- A schema derives what one of its instances entails. -/
theorem of_ent {X A p : Form} (h : Ent A p) (hA : ∃ σ : Nat → Form, A = X.subst σ) :
    DerivesFromSchema X p :=
  ⟨[A], fun _ hq => List.mem_singleton.mp hq ▸ hA, h⟩

/-- A schema derives what two of its instances entail together. -/
theorem of_ent₂ {X A B p : Form} (h : Ent A (.imp B p)) (hA : ∃ σ : Nat → Form, A = X.subst σ)
    (hB : ∃ σ : Nat → Form, B = X.subst σ) : DerivesFromSchema X p := by
  refine ⟨[B, A], fun q hq => ?_, Derives.deduction.mpr h⟩
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hB
  · exact List.mem_singleton.mp hq ▸ hA

/-- A schema derives what it entails itself, being its own instance. -/
theorem of_ent_self {X p : Form} (h : Ent X p) : DerivesFromSchema X p :=
  of_ent h ⟨.var, (Form.subst_var X).symm⟩

end DerivesFromSchema

/-- Two schemas derive each other: they axiomatise the same logic. -/
def SchemaEquiv (X Y : Form) : Prop := DerivesFromSchema X Y ∧ DerivesFromSchema Y X

namespace SchemaEquiv

theorem refl (X : Form) : SchemaEquiv X X := ⟨DerivesFromSchema.refl X, DerivesFromSchema.refl X⟩

theorem symm {X Y : Form} (h : SchemaEquiv X Y) : SchemaEquiv Y X := ⟨h.2, h.1⟩

theorem trans {X Y Z : Form} (h₁ : SchemaEquiv X Y) (h₂ : SchemaEquiv Y Z) : SchemaEquiv X Z :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

end SchemaEquiv

/-! ## Naming the elements of an algebra by formulas

A `FormRep` picks a formula for each element of an algebra so that the
connectives track the operations, up to derivability in both directions.  That
is a Heyting algebra homomorphism into the order of formulas under entailment,
written without quotienting that order into an algebra first.

Its point is `FormRep.ent_eval`: substituting the names of a valuation's values
turns every formula into one interderivable with the name of its own value.  So
a formula refuted in the algebra becomes a formula whose named instance is
derivably below the name of a non-top element, which is how a countermodel is
read back as a derivation. -/

structure FormRep (α : Type u) [HeytingAlgebra α] where
  /-- The formula naming an element. -/
  toForm : α → Form
  /-- The name of `⊥` is absurd.  The converse holds in any case. -/
  bot : Ent (toForm ⊥) .fls
  inf_le : ∀ x y, Ent (.and (toForm x) (toForm y)) (toForm (x ⊓ y))
  le_inf : ∀ x y, Ent (toForm (x ⊓ y)) (.and (toForm x) (toForm y))
  sup_le : ∀ x y, Ent (.or (toForm x) (toForm y)) (toForm (x ⊔ y))
  le_sup : ∀ x y, Ent (toForm (x ⊔ y)) (.or (toForm x) (toForm y))
  himp_le : ∀ x y, Ent (.imp (toForm x) (toForm y)) (toForm (x ⇨ y))
  le_himp : ∀ x y, Ent (toForm (x ⇨ y)) (.imp (toForm x) (toForm y))

namespace FormRep

variable {α : Type u} [HeytingAlgebra α]

/-- The substitution naming a valuation: each variable goes to the formula
naming its value. -/
def subst (R : FormRep α) (v : Nat → α) : Nat → Form := fun n => R.toForm (v n)

/-- Every formula is interderivable with the name of its value: the
substitution lemma with derivability in place of evaluation. -/
theorem ent_eval (R : FormRep α) (v : Nat → α) : ∀ q : Form,
    Ent (q.subst (R.subst v)) (R.toForm (q.eval v)) ∧
      Ent (R.toForm (q.eval v)) (q.subst (R.subst v))
  | .var _ => ⟨Ent.refl _, Ent.refl _⟩
  | .fls => ⟨Ent.fls _, R.bot⟩
  | .and p q =>
      let hp := ent_eval R v p
      let hq := ent_eval R v q
      ⟨Ent.trans (Ent.and_cong hp.1 hq.1) (R.inf_le _ _),
       Ent.trans (R.le_inf _ _) (Ent.and_cong hp.2 hq.2)⟩
  | .or p q =>
      let hp := ent_eval R v p
      let hq := ent_eval R v q
      ⟨Ent.trans (Ent.or_cong hp.1 hq.1) (R.sup_le _ _),
       Ent.trans (R.le_sup _ _) (Ent.or_cong hp.2 hq.2)⟩
  | .imp p q =>
      let hp := ent_eval R v p
      let hq := ent_eval R v q
      ⟨Ent.trans (Ent.imp_cong hp.2 hq.1) (R.himp_le _ _),
       Ent.trans (R.le_himp _ _) (Ent.imp_cong hp.1 hq.2)⟩

end FormRep

/-! ## Chains

For every `n`, the linear order `Fin (n + 1)` carries a Heyting algebra: meet is
the smaller element, join the larger, and `a ⇨ b` is the top element when
`a ⊑ b` and `b` otherwise.  This is the algebra of upward closed subsets of the
`n` world Kripke chain `w₀ < ⋯ < w_{n-1}`.

Every element strictly between `⊥` and `⊤` refutes excluded middle, so `Fin 1`
and `Fin 2` are the Boolean cases and `Fin 3` is the smallest chain in which the
algebra is not classical. -/

namespace Chain

variable {n : Nat}

abbrev le (a b : Fin (n + 1)) : Prop := a.val ≤ b.val
abbrev inf (a b : Fin (n + 1)) : Fin (n + 1) := if a.val ≤ b.val then a else b
abbrev sup (a b : Fin (n + 1)) : Fin (n + 1) := if a.val ≤ b.val then b else a
/-- `a ⇨ b` is `⊤` when `a ⊑ b`, and `b` otherwise. -/
abbrev himp (a b : Fin (n + 1)) : Fin (n + 1) := if a.val ≤ b.val then Fin.last n else b

theorem le_refl' (a : Fin (n + 1)) : le a a := Nat.le_refl a.val
theorem le_trans' {a b c : Fin (n + 1)} : le a b → le b c → le a c := Nat.le_trans
theorem le_antisymm' {a b : Fin (n + 1)} (h₁ : le a b) (h₂ : le b a) : a = b :=
  Fin.ext (Nat.le_antisymm h₁ h₂)
theorem le_top' (a : Fin (n + 1)) : le a (Fin.last n) := Nat.lt_succ_iff.mp a.isLt
theorem bot_le' (a : Fin (n + 1)) : le 0 a := Nat.zero_le a.val
theorem inf_le_left' (a b : Fin (n + 1)) : le (inf a b) a := by
  simp only [le, inf]; split <;> omega
theorem inf_le_right' (a b : Fin (n + 1)) : le (inf a b) b := by
  simp only [le, inf]; split <;> omega
theorem le_inf' {a b c : Fin (n + 1)} (h₁ : le a b) (h₂ : le a c) : le a (inf b c) := by
  simp only [le, inf] at *; split <;> omega
theorem le_sup_left' (a b : Fin (n + 1)) : le a (sup a b) := by
  simp only [le, sup]; split <;> omega
theorem le_sup_right' (a b : Fin (n + 1)) : le b (sup a b) := by
  simp only [le, sup]; split <;> omega
theorem sup_le' {a b c : Fin (n + 1)} (h₁ : le a c) (h₂ : le b c) : le (sup a b) c := by
  simp only [le, sup] at *; split <;> omega
theorem himp_adj' (a b c : Fin (n + 1)) : le (inf a b) c ↔ le a (himp b c) := by
  have ha := Nat.lt_succ_iff.mp a.isLt
  simp only [le, inf, himp]
  split <;> split <;> first | omega | (simp only [Fin.val_last]; omega)

instance : PartialOrder (Fin (n + 1)) where
  le := le
  le_refl := le_refl'
  le_trans := le_trans'
  le_antisymm := le_antisymm'

instance : Lattice (Fin (n + 1)) where
  inf := inf
  sup := sup
  inf_le_left := inf_le_left'
  inf_le_right := inf_le_right'
  le_inf := le_inf'
  le_sup_left := le_sup_left'
  le_sup_right := le_sup_right'
  sup_le := sup_le'

instance : BoundedLattice (Fin (n + 1)) where
  top := Fin.last n
  bot := 0
  le_top := le_top'
  bot_le := bot_le'

instance : HeytingAlgebra (Fin (n + 1)) where
  himp := himp
  himp_adj := himp_adj'

/-! ### Implication in a chain -/

/-- In a chain, `a ⇨ b` is the top element exactly when `a ⊑ b`. -/
theorem himp_eq_top_iff (a b : Fin (n + 1)) : (a ⇨ b) = ⊤ ↔ a.val ≤ b.val := by
  have ha := a.isLt
  show himp a b = Fin.last n ↔ a.val ≤ b.val
  simp only [himp]
  split
  · next h => simp [h]
  · next h =>
    constructor
    · intro hb
      have hv : b.val = n := congrArg Fin.val hb
      omega
    · intro hb; exact absurd hb h

theorem himp_eq_of_not_le {a b : Fin (n + 1)} (h : ¬ a.val ≤ b.val) : (a ⇨ b) = b := by
  show himp a b = b
  simp only [himp]
  split
  · next h' => exact absurd h' h
  · rfl

theorem himp_top_right (a : Fin (n + 1)) : (a ⇨ (⊤ : Fin (n + 1))) = ⊤ :=
  (himp_eq_top_iff a ⊤).mpr (Nat.lt_succ_iff.mp a.isLt)

/-- Implying out of the top element never lands above its conclusion. -/
theorem himp_top_left_le (a : Fin (n + 1)) : (((⊤ : Fin (n + 1)) ⇨ a) : Fin (n + 1)).val ≤ a.val := by
  show (himp (Fin.last n) a).val ≤ a.val
  simp only [himp, Fin.val_last]
  split <;> first | omega | (simp only [Fin.val_last]; omega)

/-! ### Failure of excluded middle -/

theorem neg_eq_bot {a : Fin (n + 1)} (h : 0 < a.val) : HeytingAlgebra.neg a = ⊥ := by
  have hne : ¬ (a.val ≤ (0 : Fin (n + 1)).val) := by simp only [Fin.val_zero]; omega
  show himp a 0 = 0
  simp only [himp, hne, ite_false]

/-- Excluded middle fails at every element strictly between the bounds. -/
theorem em_fails {a : Fin (n + 1)} (h₀ : 0 < a.val) (hn : a.val < n) :
    a ⊔ HeytingAlgebra.neg a ≠ ⊤ := by
  rw [neg_eq_bot h₀, sup_bot]
  intro h
  have hv : a.val = n := congrArg Fin.val h
  omega


/-! ### Meet and join in a chain -/

theorem inf_eq_left {a b : Fin (n + 1)} (h : a.val ≤ b.val) : a ⊓ b = a := by
  show (if a.val ≤ b.val then a else b) = a
  simp [h]

theorem inf_eq_right {a b : Fin (n + 1)} (h : ¬ a.val ≤ b.val) : a ⊓ b = b := by
  show (if a.val ≤ b.val then a else b) = b
  simp [h]

theorem sup_eq_right {a b : Fin (n + 1)} (h : a.val ≤ b.val) : a ⊔ b = b := by
  show (if a.val ≤ b.val then b else a) = b
  simp [h]

theorem sup_eq_left {a b : Fin (n + 1)} (h : ¬ a.val ≤ b.val) : a ⊔ b = a := by
  show (if a.val ≤ b.val then b else a) = a
  simp [h]
/-- Comparison in a chain is decidable, which anything building on `⇨` needs to
know.  Resolution cannot see it through the class field. -/
instance decLe {n : Nat} (a b : Fin (n + 1)) : Decidable (a ⊑ b) :=
  Nat.decLe a.val b.val

end Chain

/-! ## Forks and kites of arbitrary shape

The concrete algebras above are particular cases of two families, each given by
the lengths of two chains.  A *fork* is a root with two branches hanging above
it; a *kite* is the same with a further point above both, closing them into two
paths from bottom to top.  Taking upward closed sets of these frames gives the
corresponding Heyting algebras, with no axioms left to check: `Upset` has
supplied them already.

These are the general constructions.  The mask based `Diamond`, `Fork`, `Kite`
and `TallFork` remain the computable presentations of four of their instances,
since membership here is `Prop` valued and so out of reach of `decide`. -/

/-- A root with two branches, of lengths `m` and `n`. -/
inductive ForkPoint (m n : Nat) where
  | root
  | left : Fin m → ForkPoint m n
  | right : Fin n → ForkPoint m n

namespace ForkPoint

def le : ForkPoint m n → ForkPoint m n → Prop
  | root, _ => True
  | left i, left j => i.val ≤ j.val
  | right i, right j => i.val ≤ j.val
  | _, _ => False

instance : Frame (ForkPoint m n) where
  le := le
  le_refl p := by cases p <;> simp [le]
  le_trans {p q r} h₁ h₂ := by
    cases p <;> cases q <;> cases r <;> simp_all [le] <;> omega

end ForkPoint

/-- A root and a tip, joined by two paths through chains of lengths `m` and `n`. -/
inductive KitePoint (m n : Nat) where
  | root
  | left : Fin m → KitePoint m n
  | right : Fin n → KitePoint m n
  | tip

namespace KitePoint

def le : KitePoint m n → KitePoint m n → Prop
  | root, _ => True
  | _, tip => True
  | left i, left j => i.val ≤ j.val
  | right i, right j => i.val ≤ j.val
  | _, _ => False

instance : Frame (KitePoint m n) where
  le := le
  le_refl p := by cases p <;> simp [le]
  le_trans {p q r} h₁ h₂ := by
    cases p <;> cases q <;> cases r <;> simp_all [le] <;> omega

end KitePoint

/-- Excluded middle fails in every fork with a branch: the proposition true
from the first left point onwards is refuted exactly on the right branch, so
the join of the two misses the root. -/
theorem forkPoint_em_fails {m n : Nat} :
    letI U : Upset (ForkPoint (m + 1) n) := Upset.up (ForkPoint.left 0)
    U ⊔ HeytingAlgebra.neg U ≠ (⊤ : Upset (ForkPoint (m + 1) n)) := by
  intro h
  have hroot : (Upset.up (ForkPoint.left (0 : Fin (m + 1)))
      ⊔ HeytingAlgebra.neg (Upset.up (ForkPoint.left (0 : Fin (m + 1))))).mem
      (ForkPoint.root : ForkPoint (m + 1) n) := by rw [h]; trivial
  cases hroot with
  | inl hu => exact hu
  | inr hn => exact hn (ForkPoint.left 0) trivial (Nat.le_refl 0)

/-! ## Forks by their upsets

The mask encodings above are hand written instances of one construction.  An
upward closed set of a fork either contains the root, and is then everything,
or omits it, and then the two branches are independent: each contributes a
tail, named by the index where it starts.  So the algebra is a pair of indices
with a top adjoined, which is decidable without any enumeration. -/

/-- An upward closed set of the fork with branches of lengths `m` and `n`.
Either everything, or -- since omitting the root frees the two branches -- a
tail of each, named by the index where it starts (`m`/`n` meaning empty). -/
inductive ForkUp (m n : Nat) where
  | all
  | tails : Fin (m + 1) → Fin (n + 1) → ForkUp m n
  deriving DecidableEq, Repr

namespace ForkUp
variable {m n : Nat}

instance (p : ForkUp m n → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  if h : p .all ∧ ∀ i j, p (.tails i j) then
    isTrue (by intro x; cases x with | all => exact h.1 | tails i j => exact h.2 i j)
  else isFalse (fun hall => h ⟨hall _, fun _ _ => hall _⟩)

/-- Index-wise maximum and minimum, staying inside `Fin (k + 1)`. -/
def mx (i j : Fin (k + 1)) : Fin (k + 1) := ⟨max i.val j.val, by omega⟩
def mn (i j : Fin (k + 1)) : Fin (k + 1) := ⟨min i.val j.val, by omega⟩

/-- Bigger index means smaller tail, so the order on indices is reversed. -/
def le : ForkUp m n → ForkUp m n → Prop
  | _, .all => True
  | .all, .tails _ _ => False
  | .tails i j, .tails i' j' => i'.val ≤ i.val ∧ j'.val ≤ j.val

def inf : ForkUp m n → ForkUp m n → ForkUp m n
  | .all, y => y
  | x, .all => x
  | .tails i j, .tails i' j' => .tails (mx i i') (mx j j')

def sup : ForkUp m n → ForkUp m n → ForkUp m n
  | .all, _ => .all
  | _, .all => .all
  | .tails i j, .tails i' j' => .tails (mn i i') (mn j j')

/-- `U ⇨ V` keeps a branch's tail only where `U`'s already lies inside `V`'s;
when that holds on both branches the root survives and the result is `all`. -/
def himp : ForkUp m n → ForkUp m n → ForkUp m n
  | _, .all => .all
  | .all, y => y
  | .tails i j, .tails i' j' =>
      if i'.val ≤ i.val ∧ j'.val ≤ j.val then .all
      else .tails (if i'.val ≤ i.val then 0 else i') (if j'.val ≤ j.val then 0 else j')

/-! Point-wise equations.  Unfolding the definitions with `simp` splits the
matches and leaves absurd side goals, so each case is recorded separately. -/

@[simp] theorem le_all (a : ForkUp m n) : le a .all := by cases a <;> trivial
@[simp] theorem le_all_tails (i : Fin (m + 1)) (j : Fin (n + 1)) :
    le (.all : ForkUp m n) (.tails i j) ↔ False := Iff.rfl
@[simp] theorem le_tails (i i' : Fin (m + 1)) (j j' : Fin (n + 1)) :
    le (.tails i j : ForkUp m n) (.tails i' j') ↔ (i'.val ≤ i.val ∧ j'.val ≤ j.val) := Iff.rfl

@[simp] theorem inf_all_left (y : ForkUp m n) : inf .all y = y := rfl
@[simp] theorem inf_all_right (x : ForkUp m n) : inf x .all = x := by cases x <;> rfl
@[simp] theorem inf_tails (i i' : Fin (m + 1)) (j j' : Fin (n + 1)) :
    inf (.tails i j : ForkUp m n) (.tails i' j') = .tails (mx i i') (mx j j') := rfl

@[simp] theorem sup_all_left (y : ForkUp m n) : sup .all y = .all := rfl
@[simp] theorem sup_all_right (x : ForkUp m n) : sup x .all = .all := by cases x <;> rfl
@[simp] theorem sup_tails (i i' : Fin (m + 1)) (j j' : Fin (n + 1)) :
    sup (.tails i j : ForkUp m n) (.tails i' j') = .tails (mn i i') (mn j j') := rfl

@[simp] theorem himp_all_right (x : ForkUp m n) : himp x .all = .all := by cases x <;> rfl
@[simp] theorem himp_all_left (y : ForkUp m n) : himp .all y = y := by cases y <;> rfl
@[simp] theorem himp_tails (i i' : Fin (m + 1)) (j j' : Fin (n + 1)) :
    himp (.tails i j : ForkUp m n) (.tails i' j')
      = if i'.val ≤ i.val ∧ j'.val ≤ j.val then .all
        else .tails (if i'.val ≤ i.val then 0 else i') (if j'.val ≤ j.val then 0 else j') := rfl

theorem le_refl' (a : ForkUp m n) : le a a := by cases a <;> simp
theorem le_trans' {a b c : ForkUp m n} : le a b → le b c → le a c := by
  cases a <;> cases b <;> cases c <;> simp_all <;> omega
theorem le_antisymm' {a b : ForkUp m n} : le a b → le b a → a = b := by
  cases a <;> cases b <;> simp_all <;> intros <;>
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
theorem inf_le_left' (a b : ForkUp m n) : le (inf a b) a := by
  cases a <;> cases b <;> simp [mx] <;> omega
theorem inf_le_right' (a b : ForkUp m n) : le (inf a b) b := by
  cases a <;> cases b <;> simp [mx] <;> omega
theorem le_inf' {a b c : ForkUp m n} : le a b → le a c → le a (inf b c) := by
  cases a <;> cases b <;> cases c <;> simp_all [mx] <;> omega
theorem le_sup_left' (a b : ForkUp m n) : le a (sup a b) := by
  cases a <;> cases b <;> simp [mn] <;> omega
theorem le_sup_right' (a b : ForkUp m n) : le b (sup a b) := by
  cases a <;> cases b <;> simp [mn] <;> omega
theorem sup_le' {a b c : ForkUp m n} : le a c → le b c → le (sup a b) c := by
  cases a <;> cases b <;> cases c <;> simp_all [mn] <;> omega
theorem himp_adj' (a b c : ForkUp m n) : le (inf a b) c ↔ le a (himp b c) := by
  cases a <;> cases b <;> cases c <;> simp [mx] <;>
    (repeat' split) <;> simp_all <;> omega

instance : PartialOrder (ForkUp m n) where
  le := le
  le_refl := le_refl'
  le_trans := le_trans'
  le_antisymm := le_antisymm'

instance : Lattice (ForkUp m n) where
  inf := inf
  sup := sup
  inf_le_left := inf_le_left'
  inf_le_right := inf_le_right'
  le_inf := le_inf'
  le_sup_left := le_sup_left'
  le_sup_right := le_sup_right'
  sup_le := sup_le'

instance : BoundedLattice (ForkUp m n) where
  top := .all
  bot := .tails (Fin.last m) (Fin.last n)
  le_top := le_all
  bot_le a := by
    cases a with
    | all => trivial
    | tails i j =>
      have h1 := i.isLt; have h2 := j.isLt
      exact ⟨by simp only [Fin.val_last]; omega, by simp only [Fin.val_last]; omega⟩

instance : HeytingAlgebra (ForkUp m n) where
  himp := himp
  himp_adj := himp_adj'

/-- The class operations *are* the raw ones.  Without this, `simp` cannot
compute a composite of two concrete values: it sees `⊓`, which is a projection
of the `Lattice` instance, and has no rule that reaches the definition
underneath.  With it, the equations above do the rest. -/
theorem inf_def (a b : ForkUp m n) : a ⊓ b = ForkUp.inf a b := rfl
theorem sup_def (a b : ForkUp m n) : a ⊔ b = ForkUp.sup a b := rfl
theorem himp_def (a b : ForkUp m n) : (a ⇨ b) = ForkUp.himp a b := rfl

end ForkUp

/-! ## Forks with three branches

The same construction with one branch more.  Two branches cannot tell a
disjunction proved from a negation apart from one of its disjuncts being so
proved; three can, so the three branch fork is worth having as a concrete
algebra of its own. -/

/-- An upward closed set of the fork with branches of lengths `m`, `n` and `k`:
everything, or -- the root once omitted -- a tail of each of the three
branches. -/
inductive ForkUp3 (m n k : Nat) where
  | all
  | tails : Fin (m + 1) → Fin (n + 1) → Fin (k + 1) → ForkUp3 m n k
  deriving DecidableEq, Repr

namespace ForkUp3
variable {m n k : Nat}

open ForkUp (mx mn)

instance (p : ForkUp3 m n k → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  if h : p .all ∧ ∀ i j l, p (.tails i j l) then
    isTrue (by
      intro x
      cases x with
      | all => exact h.1
      | tails i j l => exact h.2 i j l)
  else isFalse (fun hall => h ⟨hall _, fun _ _ _ => hall _⟩)

def le : ForkUp3 m n k → ForkUp3 m n k → Prop
  | _, .all => True
  | .all, .tails _ _ _ => False
  | .tails i j l, .tails i' j' l' =>
      i'.val ≤ i.val ∧ j'.val ≤ j.val ∧ l'.val ≤ l.val

def inf : ForkUp3 m n k → ForkUp3 m n k → ForkUp3 m n k
  | .all, y => y
  | x, .all => x
  | .tails i j l, .tails i' j' l' => .tails (mx i i') (mx j j') (mx l l')

def sup : ForkUp3 m n k → ForkUp3 m n k → ForkUp3 m n k
  | .all, _ => .all
  | _, .all => .all
  | .tails i j l, .tails i' j' l' => .tails (mn i i') (mn j j') (mn l l')

/-- As for two branches: a branch's tail survives only where the hypothesis
already lies inside the conclusion, and the root survives when all three do. -/
def himp : ForkUp3 m n k → ForkUp3 m n k → ForkUp3 m n k
  | _, .all => .all
  | .all, y => y
  | .tails i j l, .tails i' j' l' =>
      if i'.val ≤ i.val ∧ j'.val ≤ j.val ∧ l'.val ≤ l.val then .all
      else .tails (if i'.val ≤ i.val then 0 else i')
                  (if j'.val ≤ j.val then 0 else j')
                  (if l'.val ≤ l.val then 0 else l')

@[simp] theorem le_all (a : ForkUp3 m n k) : le a .all := by cases a <;> trivial
@[simp] theorem le_all_tails (i : Fin (m + 1)) (j : Fin (n + 1)) (l : Fin (k + 1)) :
    le (.all : ForkUp3 m n k) (.tails i j l) ↔ False := Iff.rfl
@[simp] theorem le_tails (i i' : Fin (m + 1)) (j j' : Fin (n + 1)) (l l' : Fin (k + 1)) :
    le (.tails i j l : ForkUp3 m n k) (.tails i' j' l')
      ↔ (i'.val ≤ i.val ∧ j'.val ≤ j.val ∧ l'.val ≤ l.val) := Iff.rfl

@[simp] theorem inf_all_left (y : ForkUp3 m n k) : inf .all y = y := rfl
@[simp] theorem inf_all_right (x : ForkUp3 m n k) : inf x .all = x := by cases x <;> rfl
@[simp] theorem inf_tails (i i' : Fin (m + 1)) (j j' : Fin (n + 1)) (l l' : Fin (k + 1)) :
    inf (.tails i j l : ForkUp3 m n k) (.tails i' j' l')
      = .tails (mx i i') (mx j j') (mx l l') := rfl

@[simp] theorem sup_all_left (y : ForkUp3 m n k) : sup .all y = .all := rfl
@[simp] theorem sup_all_right (x : ForkUp3 m n k) : sup x .all = .all := by cases x <;> rfl
@[simp] theorem sup_tails (i i' : Fin (m + 1)) (j j' : Fin (n + 1)) (l l' : Fin (k + 1)) :
    sup (.tails i j l : ForkUp3 m n k) (.tails i' j' l')
      = .tails (mn i i') (mn j j') (mn l l') := rfl

@[simp] theorem himp_all_right (x : ForkUp3 m n k) : himp x .all = .all := by cases x <;> rfl
@[simp] theorem himp_all_left (y : ForkUp3 m n k) : himp .all y = y := by cases y <;> rfl
@[simp] theorem himp_tails (i i' : Fin (m + 1)) (j j' : Fin (n + 1)) (l l' : Fin (k + 1)) :
    himp (.tails i j l : ForkUp3 m n k) (.tails i' j' l')
      = if i'.val ≤ i.val ∧ j'.val ≤ j.val ∧ l'.val ≤ l.val then .all
        else .tails (if i'.val ≤ i.val then 0 else i')
                    (if j'.val ≤ j.val then 0 else j')
                    (if l'.val ≤ l.val then 0 else l') := rfl

theorem le_refl' (a : ForkUp3 m n k) : le a a := by cases a <;> simp
theorem le_trans' {a b c : ForkUp3 m n k} : le a b → le b c → le a c := by
  cases a <;> cases b <;> cases c <;> simp_all <;> omega
theorem le_antisymm' {a b : ForkUp3 m n k} : le a b → le b a → a = b := by
  cases a <;> cases b <;> simp_all <;> intros <;>
    exact ⟨Fin.ext (by omega), Fin.ext (by omega), Fin.ext (by omega)⟩
theorem inf_le_left' (a b : ForkUp3 m n k) : le (inf a b) a := by
  cases a <;> cases b <;> simp [mx] <;> omega
theorem inf_le_right' (a b : ForkUp3 m n k) : le (inf a b) b := by
  cases a <;> cases b <;> simp [mx] <;> omega
theorem le_inf' {a b c : ForkUp3 m n k} : le a b → le a c → le a (inf b c) := by
  cases a <;> cases b <;> cases c <;> simp_all [mx] <;> omega
theorem le_sup_left' (a b : ForkUp3 m n k) : le a (sup a b) := by
  cases a <;> cases b <;> simp [mn] <;> omega
theorem le_sup_right' (a b : ForkUp3 m n k) : le b (sup a b) := by
  cases a <;> cases b <;> simp [mn] <;> omega
theorem sup_le' {a b c : ForkUp3 m n k} : le a c → le b c → le (sup a b) c := by
  cases a <;> cases b <;> cases c <;> simp_all [mn] <;> omega
theorem himp_adj' (a b c : ForkUp3 m n k) : le (inf a b) c ↔ le a (himp b c) := by
  cases a <;> cases b <;> cases c <;> simp [mx] <;>
    (repeat' split) <;> simp_all <;> omega

instance : PartialOrder (ForkUp3 m n k) where
  le := le
  le_refl := le_refl'
  le_trans := le_trans'
  le_antisymm := le_antisymm'

instance : Lattice (ForkUp3 m n k) where
  inf := inf
  sup := sup
  inf_le_left := inf_le_left'
  inf_le_right := inf_le_right'
  le_inf := le_inf'
  le_sup_left := le_sup_left'
  le_sup_right := le_sup_right'
  sup_le := sup_le'

instance : BoundedLattice (ForkUp3 m n k) where
  top := .all
  bot := .tails (Fin.last m) (Fin.last n) (Fin.last k)
  le_top := le_all
  bot_le a := by
    cases a with
    | all => trivial
    | tails i j l =>
      have h1 := i.isLt; have h2 := j.isLt; have h3 := l.isLt
      exact ⟨by simp only [Fin.val_last]; omega,
             by simp only [Fin.val_last]; omega,
             by simp only [Fin.val_last]; omega⟩

instance : HeytingAlgebra (ForkUp3 m n k) where
  himp := himp
  himp_adj := himp_adj'

end ForkUp3

/-! ## Kites by their upsets

A kite is a fork closed off by a tip above both branches.  Its upward closed
sets are the fork's, each now carrying the tip along, plus one more: the tip
alone, which the branches reach without being reached. -/

/-- An upward closed set of the kite with paths of lengths `m` and `n`:
everything, or a tail of each branch together with the tip, or nothing.  The
extra case is the tip, which the branches can reach without being reached. -/
inductive KiteUp (m n : Nat) where
  | all
  | tails : Fin (m + 1) → Fin (n + 1) → KiteUp m n
  | empty
  deriving DecidableEq, Repr

namespace KiteUp
variable {m n : Nat}

open ForkUp (mx mn)

instance (p : KiteUp m n → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  if h : p .all ∧ p .empty ∧ ∀ i j, p (.tails i j) then
    isTrue (by
      intro x
      cases x with
      | all => exact h.1
      | tails i j => exact h.2.2 i j
      | empty => exact h.2.1)
  else isFalse (fun hall => h ⟨hall _, hall _, fun _ _ => hall _⟩)

def le : KiteUp m n → KiteUp m n → Prop
  | _, .all => True
  | .empty, _ => True
  | .all, _ => False
  | .tails _ _, .empty => False
  | .tails i j, .tails i' j' => i'.val ≤ i.val ∧ j'.val ≤ j.val

def inf : KiteUp m n → KiteUp m n → KiteUp m n
  | .all, y => y
  | x, .all => x
  | .empty, _ => .empty
  | _, .empty => .empty
  | .tails i j, .tails i' j' => .tails (mx i i') (mx j j')

def sup : KiteUp m n → KiteUp m n → KiteUp m n
  | .all, _ => .all
  | _, .all => .all
  | .empty, y => y
  | x, .empty => x
  | .tails i j, .tails i' j' => .tails (mn i i') (mn j j')

/-- The branch condition is the fork's; the tip goes along with the branches,
and the root survives only when both tails already lie inside. -/
def himp : KiteUp m n → KiteUp m n → KiteUp m n
  | _, .all => .all
  | .all, y => y
  | .empty, _ => .all
  | .tails _ _, .empty => .empty
  | .tails i j, .tails i' j' =>
      if i'.val ≤ i.val ∧ j'.val ≤ j.val then .all
      else .tails (if i'.val ≤ i.val then 0 else i') (if j'.val ≤ j.val then 0 else j')

@[simp] theorem le_all (a : KiteUp m n) : le a .all := by cases a <;> trivial
@[simp] theorem le_empty_left (a : KiteUp m n) : le .empty a := by cases a <;> trivial
@[simp] theorem le_all_tails (i : Fin (m + 1)) (j : Fin (n + 1)) :
    le (.all : KiteUp m n) (.tails i j) ↔ False := Iff.rfl
@[simp] theorem le_all_empty : le (.all : KiteUp m n) .empty ↔ False := Iff.rfl
@[simp] theorem le_tails_empty (i : Fin (m + 1)) (j : Fin (n + 1)) :
    le (.tails i j : KiteUp m n) .empty ↔ False := Iff.rfl
@[simp] theorem le_tails (i i' : Fin (m + 1)) (j j' : Fin (n + 1)) :
    le (.tails i j : KiteUp m n) (.tails i' j') ↔ (i'.val ≤ i.val ∧ j'.val ≤ j.val) := Iff.rfl

@[simp] theorem inf_all_left (y : KiteUp m n) : inf .all y = y := rfl
@[simp] theorem inf_all_right (x : KiteUp m n) : inf x .all = x := by cases x <;> rfl
@[simp] theorem inf_empty_left (y : KiteUp m n) : inf .empty y = .empty := by cases y <;> rfl
@[simp] theorem inf_empty_right (x : KiteUp m n) : inf x .empty = .empty := by cases x <;> rfl
@[simp] theorem inf_tails (i i' : Fin (m + 1)) (j j' : Fin (n + 1)) :
    inf (.tails i j : KiteUp m n) (.tails i' j') = .tails (mx i i') (mx j j') := rfl

@[simp] theorem sup_all_left (y : KiteUp m n) : sup .all y = .all := rfl
@[simp] theorem sup_all_right (x : KiteUp m n) : sup x .all = .all := by cases x <;> rfl
@[simp] theorem sup_empty_left (y : KiteUp m n) : sup .empty y = y := by cases y <;> rfl
@[simp] theorem sup_empty_right (x : KiteUp m n) : sup x .empty = x := by cases x <;> rfl
@[simp] theorem sup_tails (i i' : Fin (m + 1)) (j j' : Fin (n + 1)) :
    sup (.tails i j : KiteUp m n) (.tails i' j') = .tails (mn i i') (mn j j') := rfl

@[simp] theorem himp_all_right (x : KiteUp m n) : himp x .all = .all := by cases x <;> rfl
@[simp] theorem himp_all_left (y : KiteUp m n) : himp .all y = y := by cases y <;> rfl
@[simp] theorem himp_empty_left (y : KiteUp m n) : himp .empty y = .all := by cases y <;> rfl
@[simp] theorem himp_tails_empty (i : Fin (m + 1)) (j : Fin (n + 1)) :
    himp (.tails i j : KiteUp m n) .empty = .empty := rfl
@[simp] theorem himp_tails (i i' : Fin (m + 1)) (j j' : Fin (n + 1)) :
    himp (.tails i j : KiteUp m n) (.tails i' j')
      = if i'.val ≤ i.val ∧ j'.val ≤ j.val then .all
        else .tails (if i'.val ≤ i.val then 0 else i') (if j'.val ≤ j.val then 0 else j') := rfl

theorem le_refl' (a : KiteUp m n) : le a a := by cases a <;> simp
theorem le_trans' {a b c : KiteUp m n} : le a b → le b c → le a c := by
  cases a <;> cases b <;> cases c <;> simp_all <;> omega
theorem le_antisymm' {a b : KiteUp m n} : le a b → le b a → a = b := by
  cases a <;> cases b <;> simp_all <;> intros <;>
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
theorem inf_le_left' (a b : KiteUp m n) : le (inf a b) a := by
  cases a <;> cases b <;> simp [mx] <;> omega
theorem inf_le_right' (a b : KiteUp m n) : le (inf a b) b := by
  cases a <;> cases b <;> simp [mx] <;> omega
theorem le_inf' {a b c : KiteUp m n} : le a b → le a c → le a (inf b c) := by
  cases a <;> cases b <;> cases c <;> simp_all [mx] <;> omega
theorem le_sup_left' (a b : KiteUp m n) : le a (sup a b) := by
  cases a <;> cases b <;> simp [mn] <;> omega
theorem le_sup_right' (a b : KiteUp m n) : le b (sup a b) := by
  cases a <;> cases b <;> simp [mn] <;> omega
theorem sup_le' {a b c : KiteUp m n} : le a c → le b c → le (sup a b) c := by
  cases a <;> cases b <;> cases c <;> simp_all [mn] <;> omega
theorem himp_adj' (a b c : KiteUp m n) : le (inf a b) c ↔ le a (himp b c) := by
  cases a <;> cases b <;> cases c <;> simp [mx] <;>
    (repeat' split) <;> simp_all <;> omega

instance : PartialOrder (KiteUp m n) where
  le := le
  le_refl := le_refl'
  le_trans := le_trans'
  le_antisymm := le_antisymm'

instance decLe : ∀ a b : KiteUp m n, Decidable (a ⊑ b)
  | .all, .all | .empty, .all | .tails _ _, .all | .empty, .empty | .empty, .tails _ _ =>
      isTrue True.intro
  | .all, .empty | .all, .tails _ _ | .tails _ _, .empty => isFalse id
  | .tails i j, .tails i' j' => inferInstanceAs (Decidable (i'.val ≤ i.val ∧ j'.val ≤ j.val))

instance : Lattice (KiteUp m n) where
  inf := inf
  sup := sup
  inf_le_left := inf_le_left'
  inf_le_right := inf_le_right'
  le_inf := le_inf'
  le_sup_left := le_sup_left'
  le_sup_right := le_sup_right'
  sup_le := sup_le'

instance : BoundedLattice (KiteUp m n) where
  top := .all
  bot := .empty
  le_top := le_all
  bot_le := le_empty_left

instance : HeytingAlgebra (KiteUp m n) where
  himp := himp
  himp_adj := himp_adj'

/-- The class operations *are* the raw ones.  Without this, `simp` cannot
compute a composite of two concrete values: it sees `⊓`, which is a projection
of the `Lattice` instance, and has no rule that reaches the definition
underneath.  With it, the equations above do the rest. -/
theorem inf_def (a b : KiteUp m n) : a ⊓ b = KiteUp.inf a b := rfl
theorem sup_def (a b : KiteUp m n) : a ⊔ b = KiteUp.sup a b := rfl
theorem himp_def (a b : KiteUp m n) : (a ⇨ b) = KiteUp.himp a b := rfl

end KiteUp
