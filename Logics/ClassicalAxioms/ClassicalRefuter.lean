import Logics.ClassicalAxioms.Refuter.StrictImply

/-!
# The three value chain decides classicality

The previous file separates principles by exhibiting an algebra in which one
holds and another fails.  That method has a limit at the top of the hierarchy,
and this file proves what the limit is: a schema derives excluded middle
exactly when it misses the top value somewhere in `Fin 3`.

The reason is that the three value chain sits inside every algebra in which
excluded middle fails.  Given any formula `a`, the three formulas

* `⊥`,
* `a ∨ ¬ a`,
* `⊤`

behave, under derivability, exactly like the three elements of `Fin 3`: the
middle one is its own double negation and its negation is `⊥`, which is the one
equation that makes the chain a Heyting algebra rather than an arbitrary chain.
So a valuation into `Fin 3` and a substitution built from those three formulas
are the same data, and a valuation refuting a schema turns directly into an
instantiation of it that proves excluded middle.

Two consequences.  Nothing below excluded middle can be separated from it by an
algebra other than one containing `Fin 3`, so `Fin 3` is not merely a
convenient witness at the top step but the smallest one that could ever work.
And a schema that proves excluded middle needs only *one* instantiation to do
it, never two, with the instantiation read off the refuting valuation.
-/

/-! ## Formulas naming the elements of the chain -/

/-- The formula standing for the `i`-th element of `Fin 3`, relative to the
formula `a` whose excluded middle is the goal.  The middle element is named by
`a ∨ ¬ a` itself. -/
def emRep (a : Form) (i : Fin 3) : Form :=
  match i.val with
  | 0 => .fls
  | 1 => excludedMiddleForm a
  | _ => Form.tru

theorem emRep_of_val_zero {a : Form} {i : Fin 3} (h : i.val = 0) : emRep a i = .fls := by
  simp [emRep, h]

theorem emRep_of_val_one {a : Form} {i : Fin 3} (h : i.val = 1) :
    emRep a i = excludedMiddleForm a := by
  simp [emRep, h]

theorem emRep_of_val_two {a : Form} {i : Fin 3} (h : i.val = 2) : emRep a i = Form.tru := by
  simp [emRep, h]

theorem emRep_bot (a : Form) : emRep a (⊥ : Fin 3) = .fls := emRep_of_val_zero (by decide)

theorem emRep_top (a : Form) : emRep a (⊤ : Fin 3) = Form.tru := emRep_of_val_two (by decide)

/-- Bigger value, weaker formula. -/
theorem emRep_mono (a : Form) {x y : Fin 3} (h : x.val ≤ y.val) : Ent (emRep a x) (emRep a y) := by
  have hx := x.isLt
  have hy := y.isLt
  by_cases h0 : x.val = 0
  · rw [emRep_of_val_zero h0]; exact Ent.fls _
  by_cases h2 : y.val = 2
  · rw [emRep_of_val_two h2]; exact Ent.tru _
  rw [emRep_of_val_one (by omega : x.val = 1), emRep_of_val_one (by omega : y.val = 1)]
  exact Ent.refl _

/-- The one fact that makes the middle formula behave like the middle element:
its negation is absurd, because `¬ (a ∨ ¬ a)` refutes both disjuncts. -/
theorem neg_em_ent (a : Form) : Ent (.imp (excludedMiddleForm a) .fls) .fls := by
  have hax : [Form.imp (excludedMiddleForm a) .fls] ⊢ .imp (excludedMiddleForm a) .fls :=
    Derives.ax (by simp)
  have hna : [Form.imp (excludedMiddleForm a) .fls] ⊢ Form.neg a :=
    Derives.impI (Derives.impE
      (Derives.weaken hax _ (by intro r hr; simp at hr; simp [hr]))
      (Derives.orI₁ (Derives.ax (by simp))))
  exact Derives.impE hax (Derives.orI₂ hna)

/-! ## The three formulas name the chain

The connectives match the operations of `Fin 3` under derivability, so the
naming is a `FormRep`.  Meet and join are the smaller and the larger value, so
both directions reduce to `emRep_mono`; only implication has a case with real
content, and that case is `neg_em_ent`. -/

/-- Naming the elements of `Fin 3` by `⊥`, `a ∨ ¬ a` and `⊤`. -/
def emFormRep (a : Form) : FormRep (Fin 3) where
  toForm := emRep a
  bot := by rw [emRep_bot]; exact Ent.refl _
  inf_le x y := by
    by_cases h : x.val ≤ y.val
    · rw [Chain.inf_eq_left h]; exact Ent.and_left _ _
    · rw [Chain.inf_eq_right h]; exact Ent.and_right _ _
  le_inf x y := by
    by_cases h : x.val ≤ y.val
    · rw [Chain.inf_eq_left h]; exact Ent.and_intro (Ent.refl _) (emRep_mono a h)
    · rw [Chain.inf_eq_right h]
      exact Ent.and_intro (emRep_mono a (by omega)) (Ent.refl _)
  sup_le x y := by
    by_cases h : x.val ≤ y.val
    · rw [Chain.sup_eq_right h]; exact Ent.or_elim (emRep_mono a h) (Ent.refl _)
    · rw [Chain.sup_eq_left h]; exact Ent.or_elim (Ent.refl _) (emRep_mono a (by omega))
  le_sup x y := by
    by_cases h : x.val ≤ y.val
    · rw [Chain.sup_eq_right h]; exact Ent.or_right _ _
    · rw [Chain.sup_eq_left h]; exact Ent.or_left _ _
  himp_le x y := by
    by_cases h : x.val ≤ y.val
    · rw [(Chain.himp_eq_top_iff x y).mpr h, emRep_top]; exact Ent.tru _
    · rw [Chain.himp_eq_of_not_le h]
      have hx := x.isLt
      by_cases h2 : x.val = 2
      · rw [emRep_of_val_two h2]; exact Ent.imp_tru_left _
      · rw [emRep_of_val_one (by omega : x.val = 1), emRep_of_val_zero (by omega : y.val = 0)]
        exact neg_em_ent a
  le_himp x y := by
    by_cases h : x.val ≤ y.val
    · rw [(Chain.himp_eq_top_iff x y).mpr h, emRep_top]
      exact Ent.imp_intro (emRep_mono a h)
    · rw [Chain.himp_eq_of_not_le h]; exact Ent.imp_weak _ _

/-- The substitution naming a valuation. -/
def emSub (a : Form) (v : Nat → Fin 3) : Nat → Form := (emFormRep a).subst v

/-! ## A refuting valuation is an instantiation -/

/-- A valuation missing the top value turns into a single instantiation that
derives excluded middle at any formula. -/
theorem derives_em_of_eval_ne_top {X : Form} {v : Nat → Fin 3} (h : X.eval v ≠ ⊤)
    (a : Form) : [X.subst (emSub a v)] ⊢ excludedMiddleForm a := by
  refine Ent.trans ((emFormRep a).ent_eval v X).1 ?_
  show Ent (emRep a (X.eval v)) (excludedMiddleForm a)
  have hlt : (X.eval v).val ≤ 1 := by
    have hx := (X.eval v).isLt
    by_cases h2 : (X.eval v).val = 2
    · exact absurd (Fin.ext (h2 : (X.eval v).val = (⊤ : Fin 3).val)) h
    · omega
  by_cases h0 : (X.eval v).val = 0
  · rw [emRep_of_val_zero h0]; exact Ent.fls _
  · rw [emRep_of_val_one (by omega : (X.eval v).val = 1)]; exact Ent.refl _

/-- **A schema proves excluded middle exactly when it fails in `Fin 3`.**

The forward direction is soundness: every instantiation of a schema valid
throughout an algebra is valid there, and excluded middle is not.  The backward
direction is the construction above, which needs only one instantiation. -/
theorem derivesFromSchema_em_iff {X : Form} :
    DerivesFromSchema X (excludedMiddleForm (.var 0)) ↔ ∃ v : Nat → Fin 3, X.eval v ≠ ⊤ := by
  constructor
  · intro h
    refine Classical.byContradiction fun hne => ?_
    have hv : ∀ w : Nat → Fin 3, X.eval w = ⊤ := fun w =>
      Classical.byContradiction fun hw => hne ⟨w, hw⟩
    exact excludedMiddleForm_nvalid_three
      (DerivesFromSchema.valid hv h (fun _ => (1 : Fin 3)))
  · intro ⟨v, hv⟩
    exact ⟨[X.subst (emSub (.var 0) v)],
      by intro q hq; simp at hq; exact ⟨emSub (.var 0) v, hq⟩,
      derives_em_of_eval_ne_top hv (.var 0)⟩

/-- Contrapositive of the forward direction, in the form the separation
arguments use: a schema holding throughout `Fin 3` proves nothing classical. -/
theorem not_derivesFromSchema_em {X : Form} (hv : ∀ w : Nat → Fin 3, X.eval w = ⊤) :
    ¬ DerivesFromSchema X (excludedMiddleForm (.var 0)) := fun h =>
  excludedMiddleForm_nvalid_three (DerivesFromSchema.valid hv h (fun _ => (1 : Fin 3)))
