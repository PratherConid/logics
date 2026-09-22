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

end DerivesFromSchema

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

end ForkUp

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

end KiteUp
