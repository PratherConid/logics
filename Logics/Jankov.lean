import Logics.Filter
import Logics.Lindenbaum

/-!
# Jankov's theorem

`Logics/Homomorphism.lean` orders algebras by `SH α β`, "`α` is a subalgebra of
a homomorphic image of `β`", and shows that validity travels down it.  Jankov's
theorem says that for a suitable `A` the whole of that relation is visible
inside the logic: there is a single formula `χ(A)`, the *characteristic formula*
of `A`, with

    `B` refutes `χ(A)`   ⟺   `A` sits below `B`.

Suitable means finite and subdirectly irreducible.  Both halves are recorded as
data in `FiniteSI`: an enumeration of the elements, and a largest non-top
element — the coatom — which is what subdirect irreducibility amounts to for a
Heyting algebra.

**The formula.**  Give every element `a` of `A` a propositional variable `pₐ`.
The *diagram* of `A` is the conjunction, over all pairs of elements, of

    `p_{a ⊓ b} ↔ pₐ ∧ p_b`,  `p_{a ⊔ b} ↔ pₐ ∨ p_b`,  `p_{a ⇨ b} ↔ (pₐ → p_b)`

together with `p_⊤` and `¬ p_⊥`.  It is the multiplication table of `A`, written
out as a formula.  The characteristic formula is

    `χ(A) = diagram → p_c`,   `c` the coatom.

**Why the two halves hold.**  Reading each variable as the element it names
makes every conjunct of the diagram an identity, so `χ(A)` evaluates in `A` to
`⊤ ⇨ c`, that is to `c`, which is not `⊤`.  So `A` refutes its own
characteristic formula, and a refutation travels up the order.

Conversely, a valuation `v` refuting `χ(A)` in `B` makes the diagram's value `d`
fail to reach `p_c`'s.  Quotient `B` by the filter above `d`.  Every conjunct of
the diagram lies above `d`, hence becomes `⊤` in the quotient, which is exactly
to say that `a ↦ [v(pₐ)]` preserves the operations.  It is injective too: were
two elements identified, the element `(a ⇨ b) ⊓ (b ⇨ a)` measuring their
distance would be non-top, hence below the coatom, and the quotient would send
the coatom to `⊤` — making `d ⊑ v(p_c)` after all.  So `A` embeds in a
homomorphic image of `B`.

**Splitting.**  The consequence `derivesFromSchema_char_iff` is the form the
theorem is usually used in: a schema derives `χ(A)` exactly when it fails in
`A`.  So no logic can both contain `χ(A)` and be contained in the logic of `A`,
and every logic is on one side or the other — the pair splits the lattice of
intermediate logics in two.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

/-! ## Finite conjunctions and biconditionals

The diagram is a conjunction of a list of formulas, one batch per pair of
elements, so the language needs a fold and the two facts bounding its value:
each conjunct is above it, and anything below all of them is below it. -/

namespace Form

/-- The conjunction of a list of formulas, `⊤` when the list is empty. -/
def conj : List Form → Form
  | [] => Form.tru
  | p :: ps => .and p (conj ps)

theorem conj_eval_le {α : Type u} [HeytingAlgebra α] (v : Nat → α) :
    ∀ (ps : List Form) {p : Form}, p ∈ ps → (conj ps).eval v ⊑ p.eval v := by
  intro ps
  induction ps with
  | nil => intro p hp; exact absurd hp (by simp)
  | cons q ps ih =>
    intro p hp
    show q.eval v ⊓ (conj ps).eval v ⊑ p.eval v
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact inf_le_left _ _
    · exact le_trans (inf_le_right _ _) (ih hp')

theorem le_conj_eval {α : Type u} [HeytingAlgebra α] (v : Nat → α) {x : α} :
    ∀ ps : List Form, (∀ p ∈ ps, x ⊑ p.eval v) → x ⊑ (conj ps).eval v := by
  intro ps
  induction ps with
  | nil =>
    intro _
    show x ⊑ ((⊥ : α) ⇨ ⊥)
    exact le_trans (le_top x) (le_of_eq (himp_eq_top_of_le le_rfl).symm)
  | cons q ps ih =>
    intro h
    exact le_inf (h q (List.mem_cons.mpr (Or.inl rfl)))
      (ih (fun p hp => h p (List.mem_cons.mpr (Or.inr hp))))

/-- `p ↔ q`, spelled out as a pair of implications. -/
def iff (p q : Form) : Form := .and (.imp p q) (.imp q p)

/-- A biconditional between formulas of equal value is at the top. -/
theorem iff_eval_eq_top {α : Type u} [HeytingAlgebra α] (v : Nat → α) {p q : Form}
    (h : p.eval v = q.eval v) : (Form.iff p q).eval v = ⊤ := by
  show ((p.eval v ⇨ q.eval v) ⊓ (q.eval v ⇨ p.eval v)) = ⊤
  rw [h, himp_eq_top_of_le le_rfl, inf_top]

end Form

/-! ## Finite subdirectly irreducible algebras

The two hypotheses of the theorem, as data.  `elts` and `elt` make the algebra
finite and its elements nameable by variables; `coatom` makes it subdirectly
irreducible, since for a Heyting algebra that is precisely the existence of a
largest element other than the top. -/

/-- A finite Heyting algebra with a largest non-top element. -/
structure FiniteSI (A : Type) [HeytingAlgebra A] where
  /-- The variable index naming an element. -/
  idx : A → Nat
  /-- A left inverse, so that the naming is faithful. -/
  elt : Nat → A
  elt_idx : ∀ a : A, elt (idx a) = a
  /-- An enumeration of the algebra. -/
  elts : List A
  mem_elts : ∀ a : A, a ∈ elts
  /-- The largest element other than the top. -/
  coatom : A
  coatom_ne_top : coatom ≠ ⊤
  le_coatom : ∀ x : A, x ≠ ⊤ → x ⊑ coatom

namespace FiniteSI

variable {A : Type} [HeytingAlgebra A] (J : FiniteSI A)

/-! ### The characteristic formula -/

/-- The variable naming an element. -/
def var (a : A) : Form := .var (J.idx a)

/-- What one pair of elements contributes to the diagram: that the three binary
operations agree with the three binary connectives. -/
def pairConds (a b : A) : List Form :=
  [Form.iff (J.var (a ⊓ b)) (.and (J.var a) (J.var b)),
   Form.iff (J.var (a ⊔ b)) (.or (J.var a) (J.var b)),
   Form.iff (J.var (a ⇨ b)) (.imp (J.var a) (J.var b))]

/-- Every conjunct of the diagram: the two constants, and the operations on
every pair. -/
def conds : List Form :=
  J.var ⊤ :: Form.neg (J.var ⊥) ::
    J.elts.flatMap (fun a => J.elts.flatMap (fun b => J.pairConds a b))

/-- The multiplication table of the algebra, written as a formula. -/
def diagram : Form := Form.conj J.conds

/-- **The characteristic formula of `A`.** -/
def char : Form := .imp J.diagram (J.var J.coatom)

theorem var_top_mem : J.var ⊤ ∈ J.conds := List.mem_cons.mpr (Or.inl rfl)

theorem neg_var_bot_mem : Form.neg (J.var ⊥) ∈ J.conds :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

theorem mem_conds_of_pair {a b : A} {p : Form} (h : p ∈ J.pairConds a b) :
    p ∈ J.conds :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
    (List.mem_flatMap.mpr ⟨a, J.mem_elts a,
      List.mem_flatMap.mpr ⟨b, J.mem_elts b, h⟩⟩))))

theorem inf_cond_mem (a b : A) :
    Form.iff (J.var (a ⊓ b)) (.and (J.var a) (J.var b)) ∈ J.conds :=
  J.mem_conds_of_pair (List.mem_cons.mpr (Or.inl rfl))

theorem sup_cond_mem (a b : A) :
    Form.iff (J.var (a ⊔ b)) (.or (J.var a) (J.var b)) ∈ J.conds :=
  J.mem_conds_of_pair (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))

theorem himp_cond_mem (a b : A) :
    Form.iff (J.var (a ⇨ b)) (.imp (J.var a) (J.var b)) ∈ J.conds :=
  J.mem_conds_of_pair (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
    (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))

/-! ### The algebra refutes its own characteristic formula

Under the valuation naming each element by itself every conjunct of the diagram
becomes an identity, so the formula evaluates to the coatom. -/

theorem eval_var (a : A) : (J.var a).eval J.elt = a := J.elt_idx a

theorem diagram_eval_self : J.diagram.eval J.elt = ⊤ := by
  refine (eq_top_iff _).mpr (Form.le_conj_eval J.elt J.conds ?_)
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact le_of_eq (J.eval_var ⊤).symm
  rcases List.mem_cons.mp hp with rfl | hp
  · show (⊤ : A) ⊑ ((J.var ⊥).eval J.elt ⇨ ⊥)
    rw [J.eval_var ⊥, himp_eq_top_of_le le_rfl]
    exact le_rfl
  obtain ⟨a, _, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨b, _, hp⟩ := List.mem_flatMap.mp hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact le_of_eq (Form.iff_eval_eq_top J.elt
      (by show _ = ((J.var a).eval J.elt ⊓ (J.var b).eval J.elt)
          rw [J.eval_var, J.eval_var, J.eval_var])).symm
  rcases List.mem_cons.mp hp with rfl | hp
  · exact le_of_eq (Form.iff_eval_eq_top J.elt
      (by show _ = ((J.var a).eval J.elt ⊔ (J.var b).eval J.elt)
          rw [J.eval_var, J.eval_var, J.eval_var])).symm
  rcases List.mem_cons.mp hp with rfl | hp
  · exact le_of_eq (Form.iff_eval_eq_top J.elt
      (by show _ = ((J.var a).eval J.elt ⇨ (J.var b).eval J.elt)
          rw [J.eval_var, J.eval_var, J.eval_var])).symm
  exact absurd hp (by simp)

theorem eval_char_self : J.char.eval J.elt = J.coatom := by
  show (J.diagram.eval J.elt ⇨ (J.var J.coatom).eval J.elt) = J.coatom
  rw [J.diagram_eval_self, J.eval_var, himp_top_left]

/-- **An algebra refutes its own characteristic formula**, at the valuation
naming each element by itself. -/
theorem char_ne_top : J.char.eval J.elt ≠ ⊤ := by
  rw [J.eval_char_self]
  exact J.coatom_ne_top

/-- **The easy half.**  A refutation travels up the order, so everything above
`A` refutes `χ(A)` as well. -/
theorem refutes_of_sh {B : Type} [HeytingAlgebra B] (h : SH A B) :
    ¬ ∀ v : Nat → B, J.char.eval v = ⊤ :=
  exists_ne_top_of_sh h J.char_ne_top

/-! ### The hard half

Fix a valuation `v` of `B` refuting `χ(A)` and quotient by the filter above the
diagram's value.  Each conjunct of the diagram lies above that value, so each
becomes `⊤` in the quotient; that is what makes the induced map a
homomorphism. -/

section Hard

variable {B : Type} [HeytingAlgebra B] (v : Nat → B)

/-- The filter generated by the value of the diagram. -/
def filt : Filter B := Filter.up (J.diagram.eval v)

theorem mem_filt {p : Form} (hp : p ∈ J.conds) : (J.filt v).mem (p.eval v) :=
  Form.conj_eval_le v J.conds hp

/-- A biconditional among the conjuncts identifies its two sides in the
quotient. -/
theorem mk_eq_of_cond {p q : Form} (h : Form.iff p q ∈ J.conds) :
    FilterQuot.mk (J.filt v) (p.eval v) = FilterQuot.mk (J.filt v) (q.eval v) :=
  have hm := J.mem_filt v h
  FilterQuot.mk_eq_mk.mpr
    ⟨(J.filt v).upward hm (inf_le_left _ _), (J.filt v).upward hm (inf_le_right _ _)⟩

/-- The class of the value of an element's variable. -/
def toQuot (a : A) : FilterQuot (J.filt v) :=
  FilterQuot.mk (J.filt v) ((J.var a).eval v)

/-- **The induced map is a homomorphism**, one conjunct of the diagram per
field. -/
def hom : Hom A (FilterQuot (J.filt v)) where
  toFun := J.toQuot v
  map_bot :=
    FilterQuot.mk_eq_mk.mpr
      ⟨J.mem_filt v J.neg_var_bot_mem, (J.filt v).mem_of_le (bot_le _)⟩
  map_top := (FilterQuot.mk_eq_top_iff _ _).mpr (J.mem_filt v J.var_top_mem)
  map_inf a b := J.mk_eq_of_cond v (J.inf_cond_mem a b)
  map_sup a b := J.mk_eq_of_cond v (J.sup_cond_mem a b)
  map_himp a b := J.mk_eq_of_cond v (J.himp_cond_mem a b)

/-- Two elements are equal as soon as each implies the other. -/
theorem eq_of_himp_inf_eq_top {a b : A} (h : ((a ⇨ b) ⊓ (b ⇨ a)) = ⊤) : a = b :=
  le_antisymm
    (le_of_himp_eq_top ((eq_top_iff _).mpr (h ▸ inf_le_left (a ⇨ b) (b ⇨ a))))
    (le_of_himp_eq_top ((eq_top_iff _).mpr (h ▸ inf_le_right (a ⇨ b) (b ⇨ a))))

/-- **The map is injective.**  Identifying two elements would send their
distance, and with it the coatom, to the top, which is to say that the diagram's
value already reaches the coatom's variable — contradicting the refutation. -/
theorem hom_injective (hv : J.char.eval v ≠ ⊤) :
    Function.Injective (J.hom v).toFun := by
  intro a b hab
  refine Classical.byContradiction fun hne => hv ?_
  have hd : ((a ⇨ b) ⊓ (b ⇨ a)) ≠ ⊤ := fun h => hne (eq_of_himp_inf_eq_top h)
  have htop : (J.hom v).toFun ((a ⇨ b) ⊓ (b ⇨ a)) = ⊤ := by
    rw [(J.hom v).map_inf, (J.hom v).map_himp, (J.hom v).map_himp, hab,
      himp_eq_top_of_le le_rfl, inf_top]
  have hc : (J.hom v).toFun J.coatom = ⊤ :=
    (eq_top_iff _).mpr (le_trans (le_of_eq htop.symm) ((J.hom v).mono (J.le_coatom _ hd)))
  show (J.diagram.eval v ⇨ (J.var J.coatom).eval v) = ⊤
  exact himp_eq_top_of_le (Filter.up_mem.mp ((FilterQuot.mk_eq_top_iff _ _).mp hc))

end Hard

/-- **The hard half.**  An algebra refuting `χ(A)` carries `A` below it. -/
theorem sh_of_refutes {B : Type} [HeytingAlgebra B]
    (h : ¬ ∀ v : Nat → B, J.char.eval v = ⊤) : SH A B := by
  obtain ⟨v, hv⟩ := exists_ne_top h
  exact ⟨FilterQuot (J.filt v), inferInstance, FilterQuot.onto _,
    ⟨J.hom v, J.hom_injective v hv⟩⟩

/-- **Jankov's theorem.**  The characteristic formula of a finite subdirectly
irreducible algebra defines its position in the order on algebras: an algebra
refutes it exactly when it lies above `A`. -/
theorem sh_iff_refutes {B : Type} [HeytingAlgebra B] :
    SH A B ↔ ¬ ∀ v : Nat → B, J.char.eval v = ⊤ :=
  ⟨J.refutes_of_sh, J.sh_of_refutes⟩

/-- **Splitting.**  A schema derives the characteristic formula exactly when it
fails in `A`.  So the logic of `A` and the logic axiomatised by `χ(A)` divide
the intermediate logics between them: no logic lies in both, and every logic
lies in one. -/
theorem derivesFromSchema_char_iff (X : Form) :
    DerivesFromSchema X J.char ↔ ¬ ∀ w : Nat → A, X.eval w = ⊤ := by
  constructor
  · intro h hv
    exact J.char_ne_top (DerivesFromSchema.valid hv h J.elt)
  · intro hX
    refine Lindenbaum.derivesFromSchema_iff.mpr ?_
    intro α iα hv v
    refine Classical.byContradiction fun hne => ?_
    have hnv : ¬ ∀ u : Nat → α, J.char.eval u = ⊤ := fun hall => hne (hall v)
    exact hX (@valid_of_sh A α _ iα (J.sh_of_refutes hnv) _ hv)

end FiniteSI

/-! ## Chains are finite and subdirectly irreducible

A witness that the hypotheses can be met: every chain with at least two
elements below the top is one, its coatom being the element just under the
top. -/

namespace Chain

/-- The chain `Fin (n + 2)`, as a finite subdirectly irreducible algebra. -/
def finiteSI (n : Nat) : FiniteSI (Fin (n + 2)) where
  idx := Fin.val
  elt k := if h : k < n + 2 then ⟨k, h⟩ else 0
  elt_idx a := by simp [a.isLt]
  elts := List.finRange (n + 2)
  mem_elts := List.mem_finRange
  coatom := ⟨n, by omega⟩
  coatom_ne_top := by
    intro h
    have hv : n = n + 1 := congrArg Fin.val h
    omega
  le_coatom x hx := by
    show x.val ≤ n
    refine Classical.byContradiction fun hle => hx (Fin.ext ?_)
    show x.val = n + 1
    have := x.isLt
    omega

end Chain
