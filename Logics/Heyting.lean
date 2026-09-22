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

end HeytingAlgebra

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

end Chain
