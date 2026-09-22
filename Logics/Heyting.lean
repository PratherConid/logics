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

/-! ## The diamond

Not every Heyting algebra is a chain.  The diamond is the six element algebra of
upward closed subsets of the four point frame with a root, two incomparable
middle points `x` and `y`, and a top.  Each element is coded by the bit mask of
the set of frame points it names, which makes the operations computable and the
axioms decidable. -/

inductive Diamond where
  | bot | e | x | y | m | top
  deriving DecidableEq, Repr

namespace Diamond

instance decForallDiamond (p : Diamond → Prop) [DecidablePred p] : Decidable (∀ a, p a) :=
  if h : p bot ∧ p e ∧ p x ∧ p y ∧ p m ∧ p top then
    isTrue (by
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      intro a
      cases a
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
      · exact h6)
  else
    isFalse (fun hall => h ⟨hall _, hall _, hall _, hall _, hall _, hall _⟩)

/-- The bit mask of the upward closed set each element names. -/
def mask : Diamond → Nat
  | bot => 0 | e => 8 | x => 10 | y => 12 | m => 14 | top => 15

def ofMask (n : Nat) : Diamond :=
  if n = 0 then bot else if n = 8 then e else if n = 10 then x
  else if n = 12 then y else if n = 14 then m else top

/-- The principal upward closed set of each of the four frame points. -/
def upset : Nat → Nat
  | 0 => 15 | 1 => 10 | 2 => 12 | _ => 8

abbrev le (a b : Diamond) : Prop := mask a &&& mask b = mask a
abbrev inf (a b : Diamond) : Diamond := ofMask (mask a &&& mask b)
abbrev sup (a b : Diamond) : Diamond := ofMask (mask a ||| mask b)
/-- `a ⇨ b` collects the frame points whose whole upward closed set meets `a`
only inside `b`. -/
abbrev himp (a b : Diamond) : Diamond :=
  ofMask ((List.range 4).foldl
    (fun acc q => if upset q &&& mask a &&& (15 ^^^ mask b) = 0 then acc ||| (1 <<< q) else acc) 0)

theorem le_refl' : ∀ a, le a a := by decide
theorem le_trans' : ∀ a b c, le a b → le b c → le a c := by decide
theorem le_antisymm' : ∀ a b, le a b → le b a → a = b := by decide
theorem le_top' : ∀ a, le a top := by decide
theorem bot_le' : ∀ a, le bot a := by decide
theorem inf_le_left' : ∀ a b, le (inf a b) a := by decide
theorem inf_le_right' : ∀ a b, le (inf a b) b := by decide
theorem le_inf' : ∀ a b c, le a b → le a c → le a (inf b c) := by decide
theorem le_sup_left' : ∀ a b, le a (sup a b) := by decide
theorem le_sup_right' : ∀ a b, le b (sup a b) := by decide
theorem sup_le' : ∀ a b c, le a c → le b c → le (sup a b) c := by decide
theorem himp_adj' : ∀ a b c, le (inf a b) c ↔ le a (himp b c) := by decide

instance : PartialOrder Diamond where
  le := le
  le_refl := le_refl'
  le_trans := le_trans' _ _ _
  le_antisymm := le_antisymm' _ _

instance : Lattice Diamond where
  inf := inf
  sup := sup
  inf_le_left := inf_le_left'
  inf_le_right := inf_le_right'
  le_inf := le_inf' _ _ _
  le_sup_left := le_sup_left'
  le_sup_right := le_sup_right'
  sup_le := sup_le' _ _ _

instance : BoundedLattice Diamond where
  top := top
  bot := bot
  le_top := le_top'
  bot_le := bot_le'

instance : HeytingAlgebra Diamond where
  himp := himp
  himp_adj := himp_adj'

/-- The diamond is not a chain: `x` and `y` are incomparable. -/
theorem x_y_incomparable : ¬ le x y ∧ ¬ le y x := by decide

/-- Nor is it classical. -/
theorem em_fails : sup x (himp x bot) ≠ top := by decide

end Diamond

/-! ## The fork

The five element algebra of upward closed subsets of the three point frame with
a root and two incomparable points above it.  Unlike the diamond it has no top
point, and that is what separates it from the diamond as a countermodel: the
join of the two incomparable elements falls short of the top. -/

inductive Fork where
  | bot | x | y | m | top
  deriving DecidableEq, Repr

namespace Fork

instance decForallFork (p : Fork → Prop) [DecidablePred p] : Decidable (∀ a, p a) :=
  if h : p bot ∧ p x ∧ p y ∧ p m ∧ p top then
    isTrue (by
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      intro a
      cases a
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5)
  else
    isFalse (fun hall => h ⟨hall _, hall _, hall _, hall _, hall _⟩)

/-- The bit mask of the upward closed set each element names. -/
def mask : Fork → Nat
  | bot => 0 | x => 2 | y => 4 | m => 6 | top => 7

def ofMask (n : Nat) : Fork :=
  if n = 0 then bot else if n = 2 then x else if n = 4 then y
  else if n = 6 then m else top

/-- The principal upward closed set of each of the three frame points. -/
def upset : Nat → Nat
  | 0 => 7 | 1 => 2 | _ => 4

abbrev le (a b : Fork) : Prop := mask a &&& mask b = mask a
abbrev inf (a b : Fork) : Fork := ofMask (mask a &&& mask b)
abbrev sup (a b : Fork) : Fork := ofMask (mask a ||| mask b)
abbrev himp (a b : Fork) : Fork :=
  ofMask ((List.range 3).foldl
    (fun acc q => if upset q &&& mask a &&& (7 ^^^ mask b) = 0 then acc ||| (1 <<< q) else acc) 0)

theorem le_refl' : ∀ a, le a a := by decide
theorem le_trans' : ∀ a b c, le a b → le b c → le a c := by decide
theorem le_antisymm' : ∀ a b, le a b → le b a → a = b := by decide
theorem le_top' : ∀ a, le a top := by decide
theorem bot_le' : ∀ a, le bot a := by decide
theorem inf_le_left' : ∀ a b, le (inf a b) a := by decide
theorem inf_le_right' : ∀ a b, le (inf a b) b := by decide
theorem le_inf' : ∀ a b c, le a b → le a c → le a (inf b c) := by decide
theorem le_sup_left' : ∀ a b, le a (sup a b) := by decide
theorem le_sup_right' : ∀ a b, le b (sup a b) := by decide
theorem sup_le' : ∀ a b c, le a c → le b c → le (sup a b) c := by decide
theorem himp_adj' : ∀ a b c, le (inf a b) c ↔ le a (himp b c) := by decide

instance : PartialOrder Fork where
  le := le
  le_refl := le_refl'
  le_trans := le_trans' _ _ _
  le_antisymm := le_antisymm' _ _

instance : Lattice Fork where
  inf := inf
  sup := sup
  inf_le_left := inf_le_left'
  inf_le_right := inf_le_right'
  le_inf := le_inf' _ _ _
  le_sup_left := le_sup_left'
  le_sup_right := le_sup_right'
  sup_le := sup_le' _ _ _

instance : BoundedLattice Fork where
  top := top
  bot := bot
  le_top := le_top'
  bot_le := bot_le'

instance : HeytingAlgebra Fork where
  himp := himp
  himp_adj := himp_adj'

/-- The two incomparable elements join to `m`, which is not the top.  This is
the shape the diamond lacks. -/
theorem sup_x_y : sup x y = m ∧ m ≠ top := by decide

end Fork
