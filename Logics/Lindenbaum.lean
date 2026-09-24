import Logics.Homomorphism

/-!
# The Lindenbaum algebra

Formulas ordered by entailment are almost a Heyting algebra already: `Ent`
is reflexive and transitive, conjunction and disjunction are meet and join,
and implication is the residual.  The one thing missing is antisymmetry, since
two different formulas can entail each other.  Quotienting by exactly that —
interderivability — repairs it, and the result is a Heyting algebra built out
of syntax.

Everything here is relative to a schema `X`, whose instances may be used freely
as extra hypotheses.  The algebra it produces validates `X` at every valuation,
because a valuation into a quotient of formulas is a substitution, so a formula
evaluates to the class of its own instance.  That is what makes the
construction a countermodel machine: whatever a schema fails to prove, this one
algebra already fails to prove.

The consequence is completeness, the converse of soundness.  Underivability
from `X` is established by exhibiting a single algebra validating `X`, and
derivability by ranging over all of them, so the two techniques are
interchangeable.  Taking `X` to be `⊤`, which says nothing, gives the
unrelativized statement: a formula is derivable exactly when it is valid.
Since validity travels down the Jankov order, the algebras to range over can be
taken low in it (`DerivesFromSchema.of_sh`).
-/

/-! ## Entailment over a schema -/

/-- `q` follows from `p` together with finitely many instances of `X`. -/
def EntOf (X p q : Form) : Prop :=
  ∃ Γ : List Form, (∀ r ∈ Γ, ∃ σ : Nat → Form, r = X.subst σ) ∧ ((p :: Γ) ⊢ q)

namespace EntOf

variable {X p p' q q' r : Form}

theorem instances_append {Γ Δ : List Form}
    (h₁ : ∀ s ∈ Γ, ∃ σ : Nat → Form, s = X.subst σ)
    (h₂ : ∀ s ∈ Δ, ∃ σ : Nat → Form, s = X.subst σ) :
    ∀ s ∈ Γ ++ Δ, ∃ σ : Nat → Form, s = X.subst σ := by
  intro s hs
  rcases List.mem_append.mp hs with h | h
  · exact h₁ s h
  · exact h₂ s h

/-- Plain entailment is entailment over any schema: use no instances. -/
theorem of_ent (h : Ent p q) : EntOf X p q := ⟨[], by simp, h⟩

theorem refl (p : Form) : EntOf X p p := of_ent (Ent.refl p)
theorem fls (p : Form) : EntOf X .fls p := of_ent (Ent.fls p)
theorem tru (p : Form) : EntOf X p Form.tru := of_ent (Ent.tru p)
theorem and_left (p q : Form) : EntOf X (.and p q) p := of_ent (Ent.and_left p q)
theorem and_right (p q : Form) : EntOf X (.and p q) q := of_ent (Ent.and_right p q)
theorem or_left (p q : Form) : EntOf X p (.or p q) := of_ent (Ent.or_left p q)
theorem or_right (p q : Form) : EntOf X q (.or p q) := of_ent (Ent.or_right p q)

/-- Chaining two entailments pools the instances they use. -/
theorem trans (h₁ : EntOf X p q) (h₂ : EntOf X q r) : EntOf X p r := by
  obtain ⟨Γ, hΓ, d₁⟩ := h₁
  obtain ⟨Δ, hΔ, d₂⟩ := h₂
  refine ⟨Γ ++ Δ, instances_append hΓ hΔ, ?_⟩
  refine Derives.cut (Derives.weaken d₁ _ ?_) (Derives.weaken d₂ _ ?_)
  · intro s hs
    simp only [List.mem_cons, List.mem_append] at hs ⊢
    exact hs.imp id Or.inl
  · intro s hs
    simp only [List.mem_cons, List.mem_append] at hs ⊢
    exact hs.imp id (fun h => Or.inr (Or.inr h))

theorem and_intro (h₁ : EntOf X r p) (h₂ : EntOf X r q) : EntOf X r (.and p q) := by
  obtain ⟨Γ, hΓ, d₁⟩ := h₁
  obtain ⟨Δ, hΔ, d₂⟩ := h₂
  refine ⟨Γ ++ Δ, instances_append hΓ hΔ, Derives.andI ?_ ?_⟩
  · refine Derives.weaken d₁ _ ?_
    intro s hs
    simp only [List.mem_cons, List.mem_append] at hs ⊢
    exact hs.imp id Or.inl
  · refine Derives.weaken d₂ _ ?_
    intro s hs
    simp only [List.mem_cons, List.mem_append] at hs ⊢
    exact hs.imp id Or.inr

theorem or_elim (h₁ : EntOf X p r) (h₂ : EntOf X q r) : EntOf X (.or p q) r := by
  obtain ⟨Γ, hΓ, d₁⟩ := h₁
  obtain ⟨Δ, hΔ, d₂⟩ := h₂
  refine ⟨Γ ++ Δ, instances_append hΓ hΔ,
    Derives.orE (p := p) (q := q) (Derives.ax (by simp)) ?_ ?_⟩
  · refine Derives.weaken d₁ _ ?_
    intro s hs
    simp only [List.mem_cons, List.mem_append] at hs ⊢
    exact hs.imp id (fun h => Or.inr (Or.inl h))
  · refine Derives.weaken d₂ _ ?_
    intro s hs
    simp only [List.mem_cons, List.mem_append] at hs ⊢
    exact hs.imp id (fun h => Or.inr (Or.inr h))

theorem curry (h : EntOf X (.and p q) r) : EntOf X p (.imp q r) := by
  obtain ⟨Γ, hΓ, d⟩ := h
  refine ⟨Γ, hΓ, Derives.impI ?_⟩
  have hd : (Form.and p q :: q :: p :: Γ) ⊢ r := by
    refine Derives.weaken d _ ?_
    intro s hs
    simp only [List.mem_cons] at hs ⊢
    exact hs.imp id (fun h => Or.inr (Or.inr h))
  have hand : (q :: p :: Γ) ⊢ Form.and p q :=
    Derives.andI (Derives.ax (by simp)) (Derives.ax (by simp))
  exact Derives.cut hand hd

theorem uncurry (h : EntOf X p (.imp q r)) : EntOf X (.and p q) r := by
  obtain ⟨Γ, hΓ, d⟩ := h
  refine ⟨Γ, hΓ, ?_⟩
  have hp : (Form.and p q :: Γ) ⊢ p := Derives.andE₁ (q := q) (Derives.ax (by simp))
  have hq : (Form.and p q :: Γ) ⊢ q := Derives.andE₂ (p := p) (Derives.ax (by simp))
  have hd : (p :: Form.and p q :: Γ) ⊢ Form.imp q r := by
    refine Derives.weaken d _ ?_
    intro s hs
    simp only [List.mem_cons] at hs ⊢
    exact hs.imp id Or.inr
  exact Derives.impE (Derives.cut hp hd) hq

theorem and_cong (h₁ : EntOf X p p') (h₂ : EntOf X q q') :
    EntOf X (.and p q) (.and p' q') :=
  and_intro (trans (and_left p q) h₁) (trans (and_right p q) h₂)

theorem or_cong (h₁ : EntOf X p p') (h₂ : EntOf X q q') :
    EntOf X (.or p q) (.or p' q') :=
  or_elim (trans h₁ (or_left p' q')) (trans h₂ (or_right p' q'))

theorem imp_cong (h₁ : EntOf X p' p) (h₂ : EntOf X q q') :
    EntOf X (.imp p q) (.imp p' q') :=
  curry (trans (and_cong (refl _) h₁) (trans (uncurry (refl _)) h₂))

end EntOf

/-! ## The quotient -/

/-- Two formulas are interderivable over `X` when each entails the other. -/
def Interderivable (X p q : Form) : Prop := EntOf X p q ∧ EntOf X q p

/-- The setoid of interderivability over `X`.  It is not an instance, since
there is one for every schema. -/
def Form.interSetoid (X : Form) : Setoid Form where
  r := Interderivable X
  iseqv :=
    ⟨fun p => ⟨EntOf.refl p, EntOf.refl p⟩,
     fun h => ⟨h.2, h.1⟩,
     fun h₁ h₂ => ⟨EntOf.trans h₁.1 h₂.1, EntOf.trans h₂.2 h₁.2⟩⟩

/-- Formulas modulo interderivability over the schema `X`. -/
def Lindenbaum (X : Form) : Type := Quotient (Form.interSetoid X)

namespace Lindenbaum

variable {X : Form}

/-- The class of a formula. -/
def mk (X p : Form) : Lindenbaum X := Quotient.mk (Form.interSetoid X) p

theorem mk_eq_mk {p q : Form} : mk X p = mk X q ↔ Interderivable X p q := by
  constructor
  · exact fun h => Quotient.exact h
  · exact fun h => Quotient.sound h

/-! ## The operations

Each connective descends to the quotient because the entailment calculus makes
it monotone, contravariantly in the hypothesis of an implication. -/

def le (x y : Lindenbaum X) : Prop :=
  Quotient.liftOn₂ x y (fun p q => EntOf X p q)
    (fun _ _ _ _ hp hq => propext
      ⟨fun h => EntOf.trans (EntOf.trans hp.2 h) hq.1,
       fun h => EntOf.trans (EntOf.trans hp.1 h) hq.2⟩)

def inf (x y : Lindenbaum X) : Lindenbaum X :=
  Quotient.liftOn₂ x y (fun p q => mk X (.and p q))
    (fun _ _ _ _ hp hq =>
      Quotient.sound ⟨EntOf.and_cong hp.1 hq.1, EntOf.and_cong hp.2 hq.2⟩)

def sup (x y : Lindenbaum X) : Lindenbaum X :=
  Quotient.liftOn₂ x y (fun p q => mk X (.or p q))
    (fun _ _ _ _ hp hq =>
      Quotient.sound ⟨EntOf.or_cong hp.1 hq.1, EntOf.or_cong hp.2 hq.2⟩)

def himp (x y : Lindenbaum X) : Lindenbaum X :=
  Quotient.liftOn₂ x y (fun p q => mk X (.imp p q))
    (fun _ _ _ _ hp hq =>
      Quotient.sound ⟨EntOf.imp_cong hp.2 hq.1, EntOf.imp_cong hp.1 hq.2⟩)

@[simp] theorem le_mk (p q : Form) : le (mk X p) (mk X q) ↔ EntOf X p q := Iff.rfl
@[simp] theorem inf_mk (p q : Form) : inf (mk X p) (mk X q) = mk X (.and p q) := rfl
@[simp] theorem sup_mk (p q : Form) : sup (mk X p) (mk X q) = mk X (.or p q) := rfl
@[simp] theorem himp_mk (p q : Form) : himp (mk X p) (mk X q) = mk X (.imp p q) := rfl

/-! ## The Heyting algebra

Every axiom is a rule of the entailment calculus, read through the quotient. -/

instance : PartialOrder (Lindenbaum X) where
  le := le
  le_refl x := Quotient.inductionOn x (fun p => EntOf.refl p)
  le_trans {x y z} := by
    refine Quotient.inductionOn₃ x y z (fun _ _ _ h₁ h₂ => ?_)
    exact EntOf.trans h₁ h₂
  le_antisymm {x y} := by
    refine Quotient.inductionOn₂ x y (fun _ _ h₁ h₂ => ?_)
    exact mk_eq_mk.mpr ⟨h₁, h₂⟩

instance : Lattice (Lindenbaum X) where
  inf := inf
  sup := sup
  inf_le_left x y := Quotient.inductionOn₂ x y (fun p q => EntOf.and_left p q)
  inf_le_right x y := Quotient.inductionOn₂ x y (fun p q => EntOf.and_right p q)
  le_inf {x y z} := by
    refine Quotient.inductionOn₃ x y z (fun _ _ _ h₁ h₂ => ?_)
    exact EntOf.and_intro h₁ h₂
  le_sup_left x y := Quotient.inductionOn₂ x y (fun p q => EntOf.or_left p q)
  le_sup_right x y := Quotient.inductionOn₂ x y (fun p q => EntOf.or_right p q)
  sup_le {x y z} := by
    refine Quotient.inductionOn₃ x y z (fun _ _ _ h₁ h₂ => ?_)
    exact EntOf.or_elim h₁ h₂

instance : BoundedLattice (Lindenbaum X) where
  top := mk X Form.tru
  bot := mk X .fls
  le_top x := Quotient.inductionOn x (fun p => EntOf.tru p)
  bot_le x := Quotient.inductionOn x (fun p => EntOf.fls p)

instance : HeytingAlgebra (Lindenbaum X) where
  himp := himp
  himp_adj x y z := by
    refine Quotient.inductionOn₃ x y z (fun _ _ _ => ?_)
    exact ⟨EntOf.curry, EntOf.uncurry⟩

/-! ## The top element

The top element is the class of exactly the formulas the schema derives. -/

theorem mk_eq_top_iff (X p : Form) : mk X p = ⊤ ↔ DerivesFromSchema X p := by
  constructor
  · intro h
    obtain ⟨Γ, hΓ, d⟩ := (mk_eq_mk.mp h).2
    exact ⟨Γ, hΓ, Derives.cut Derives.tru d⟩
  · intro ⟨Γ, hΓ, d⟩
    refine mk_eq_mk.mpr ⟨EntOf.tru p, ⟨Γ, hΓ, ?_⟩⟩
    refine Derives.weaken d _ ?_
    intro s hs
    exact List.mem_cons_of_mem _ hs

/-! ## Evaluation is substitution

A valuation into the quotient is a family of classes, and picking a
representative of each turns it into a substitution.  Evaluating a formula
under it then lands on the class of the substituted formula, which is why `X`
itself reaches the top value at every valuation. -/

theorem eval_mk (X : Form) (σ : Nat → Form) : ∀ p : Form,
    p.eval (fun n => mk X (σ n)) = mk X (p.subst σ)
  | .var _ => rfl
  | .fls => rfl
  | .and p q => by
      show p.eval _ ⊓ q.eval _ = mk X (.and (p.subst σ) (q.subst σ))
      rw [eval_mk X σ p, eval_mk X σ q]; rfl
  | .or p q => by
      show p.eval _ ⊔ q.eval _ = mk X (.or (p.subst σ) (q.subst σ))
      rw [eval_mk X σ p, eval_mk X σ q]; rfl
  | .imp p q => by
      show (p.eval _ ⇨ q.eval _) = mk X (.imp (p.subst σ) (q.subst σ))
      rw [eval_mk X σ p, eval_mk X σ q]; rfl

/-- The valuation sending each variable to its own class. -/
def vars (X : Form) : Nat → Lindenbaum X := fun n => mk X (.var n)

theorem eval_vars (X p : Form) : p.eval (vars X) = mk X p := by
  show p.eval (fun n => mk X (Form.var n)) = mk X p
  rw [eval_mk X Form.var p, Form.subst_var p]

/-- **The algebra validates its own schema.**  A valuation is a substitution up
to choice of representatives, so `X` evaluates to the class of one of its own
instances, which is at the top. -/
theorem schema_valid (X : Form) (w : Nat → Lindenbaum X) : X.eval w = ⊤ := by
  have hrep : ∀ n, ∃ p : Form, mk X p = w n := fun n => Quotient.exists_rep (w n)
  have hw : w = fun n => mk X (Classical.choose (hrep n)) :=
    funext (fun n => (Classical.choose_spec (hrep n)).symm)
  rw [hw, eval_mk]
  exact (mk_eq_top_iff X _).mpr
    ⟨[X.subst (fun n => Classical.choose (hrep n))],
     by intro s hs; simp only [List.mem_singleton] at hs; exact ⟨_, hs⟩,
     Derives.ax (by simp)⟩

/-! ## Completeness -/

/-- **Completeness for a schema**: if `p` holds in every algebra where every
instance of `X` holds, then some finite set of instances of `X` derives `p`.
One algebra already forces it, namely this one. -/
theorem schema_completeness {X p : Form}
    (h : ∀ (α : Type) [HeytingAlgebra α], (∀ w : Nat → α, X.eval w = ⊤) →
      ∀ v : Nat → α, p.eval v = ⊤) : DerivesFromSchema X p :=
  (mk_eq_top_iff X p).mp (by
    rw [← eval_vars X p]
    exact h (Lindenbaum X) (schema_valid X) (vars X))

/-- Derivability from a schema and validity over its models coincide. -/
theorem derivesFromSchema_iff {X p : Form} :
    DerivesFromSchema X p ↔
      ∀ (α : Type) [HeytingAlgebra α], (∀ w : Nat → α, X.eval w = ⊤) →
        ∀ v : Nat → α, p.eval v = ⊤ := by
  constructor
  · intro hd α _ hX v
    exact DerivesFromSchema.valid hX hd v
  · exact schema_completeness

/-! ## The unrelativized case

The schema `⊤` says nothing: all of its instances are `⊤` again, so they can be
cut away and derivability from it is plain derivability. -/

theorem derives_of_schema_tru {p : Form} : ∀ Γ : List Form,
    (∀ r ∈ Γ, ∃ σ : Nat → Form, r = Form.tru.subst σ) → (Γ ⊢ p) → ([] ⊢ p)
  | [], _, d => d
  | r :: Γ, hΓ, d => by
      obtain ⟨_, hr⟩ := hΓ r (by simp)
      have hr' : r = Form.tru := hr
      subst hr'
      exact derives_of_schema_tru Γ (fun s hs => hΓ s (List.mem_cons_of_mem _ hs))
        (Derives.cut Derives.tru d)

theorem derivesFromSchema_tru_iff {p : Form} :
    DerivesFromSchema Form.tru p ↔ ([] ⊢ p) := by
  constructor
  · intro ⟨Γ, hΓ, d⟩
    exact derives_of_schema_tru Γ hΓ d
  · intro h
    exact ⟨[], by simp, h⟩

/-- **Completeness**: a formula valid in every Heyting algebra is derivable. -/
theorem completeness {p : Form} (h : Valid p) : [] ⊢ p :=
  derivesFromSchema_tru_iff.mp (schema_completeness (fun α _ _ v => h α v))

/-- Derivability and validity coincide. -/
theorem valid_iff_derives {p : Form} : Valid p ↔ ([] ⊢ p) :=
  ⟨completeness, Derives.valid_of_derives⟩

/-! ## Consistency

The construction is not vacuous.  If every formula were derivable the quotient
would collapse to a point, and the two element algebra rules that out. -/

/-- `⊥` has no derivation. -/
theorem not_derives_fls : ¬ ([] ⊢ Form.fls) := fun h =>
  absurd (Derives.valid_of_derives h (Fin 2) (fun _ => 0)) (by decide)

/-- So the algebra over the empty schema has at least two elements. -/
theorem bot_ne_top : (⊥ : Lindenbaum Form.tru) ≠ ⊤ := fun h =>
  not_derives_fls (derivesFromSchema_tru_iff.mp ((mk_eq_top_iff Form.tru Form.fls).mp h))

end Lindenbaum

/-- **Deriving through the order.**  If below every algebra refuting `p` lies
one refuting the schema, the schema derives `p`: an algebra validating the
schema validates everything below it, so it cannot refute `p`. -/
theorem DerivesFromSchema.of_sh {X p : Form}
    (h : ∀ (α : Type) [HeytingAlgebra α], (¬ ∀ v : Nat → α, p.eval v = ⊤) →
      ∃ (A : Type) (_ : HeytingAlgebra A), SH A α ∧ ¬ ∀ w : Nat → A, X.eval w = ⊤) :
    DerivesFromSchema X p := by
  refine Lindenbaum.derivesFromSchema_iff.mpr fun α _ hX v => ?_
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨A, _, hsh, hA⟩ := h α fun hall => hne (hall v)
  exact hA (valid_of_sh hsh hX)
