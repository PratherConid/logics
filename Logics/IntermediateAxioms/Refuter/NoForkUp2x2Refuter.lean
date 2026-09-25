import Logics.IntermediateAxioms.AxiomDef
import Logics.PointEmbed
import Logics.Lindenbaum

/-!
# Where `noForkUp2x2Form` sits, exactly

The tall fork `ForkUp 2 2` is a root with two branches of two points each, `x₁`
below `x₂` and `y₁` below `y₂`.  It refutes `noForkUp2x2Form`, and this file
shows that it is the formula's only minimal refuter, answering the two questions
`NoDiamondRefuter` answers for the diamond.

**Can it be shrunk?**  No: `refuterLB_fork22_noForkUp2x2`.  A refuting pair
generates the whole ten element algebra, each element being the value of a
formula in the pair, which evaluation checks.

**Which schemas derive the formula?**  Exactly those missing the top value in
the tall fork: `derivesFromSchema_noForkUp2x2_iff`.  That rests on
`sh_fork22_of_refutes_noForkUp2x2`, which puts the tall fork below every algebra
refuting the formula.  The embedding goes through the fork's points
(`Logics/PointEmbed.lean`), each sent to the value of a formula in the refuting
pair `a`, `b`:

* `x₁` to `¬ a` and `x₂` to `¬ a ∧ b`;
* `y₁` to `a` and `y₂` to `a ∧ b`.

This happens in the quotient by the filter above the formula's premise `P`.
Everything the embedding asks of those values -- how they are ordered, how they
meet, one arrow for each point, and that the join of all four lies below the
formula's conclusion `C` -- is a derivation under `P`.

**The proofs.**  Each derivation is a natural deduction tree.  Hypotheses are
named by position (`Derives.h₀`, `h₁`, …), the most recent first, and the
comments beside a tree read it as a proof in Lean's own logic, naming the
hypotheses: a case split is `orE`, `Or.inl` is `orI₁`, introducing a hypothesis
is `impI`, applying one is `impE`, `absurd` is `flsE` of an `impE` into `fls`,
a `have` is a `cut` at the formula it states, and using another entailment is
`Ent.mp`.  `hP` is the premise `P`, and `k` the arrow an arrow condition
assumes.

**Why they hold.**  The order, the meets and the conclusion need nothing from
`P`: an upper point's formula is its lower neighbour's with `b` added, the two
branches' formulas contradict each other, and each of them decides `a`, which
is `C`.  `P` is for the arrows.  It grants `¬ ¬ b`, and excluded middle at `a`
as soon as `¬ a → b` or `a → b` holds.  The arrow at a lower point gives one of
those two implications, under `¬ a` on the `x` branch and under `a` on the `y`
branch, so `a` is decided and either case lands in the join.  The arrow at an
upper point refutes `b` on that side of `a`, which `¬ ¬ b` turns into refuting
that side.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra PointEmbed

namespace NoForkUp2x2Witness

/-! ## The tall fork through its points -/

/-- The points of the tall fork, as the upsets they generate: the root, `x₁`,
`x₂`, `y₁` and `y₂`.  `co` sends each to the upset of the points not below
it. -/
def points : Points (ForkUp 2 2) where
  J := [.all, .tails 0 2, .tails 1 2, .tails 2 0, .tails 2 1]
  co j :=
    if j = .tails 0 2 then .tails 1 0 else if j = .tails 1 2 then .tails 2 0
    else if j = .tails 2 0 then .tails 0 1 else if j = .tails 2 1 then .tails 0 2
    else .tails 0 0
  c := .tails 0 0
  top_mem := by decide
  not_le_bot := by decide
  le_supList := by decide
  prime := by decide
  le_co := by decide
  infList_le_himp := by decide
  le_coatom := by decide

/-! ## The witnesses and their derivations -/

/-- The formula's premise. -/
def P : Form :=
  .and
    (.imp (.or (.imp (Form.neg (.var 0)) (.var 1)) (.imp (.var 0) (.var 1)))
      (excludedMiddleForm (.var 0)))
    (Form.neg (Form.neg (.var 1)))

/-- The formula's conclusion, excluded middle at `a`. -/
def C : Form := excludedMiddleForm (.var 0)

def Tx1 : Form := Form.neg (.var 0)
def Tx2 : Form := .and Tx1 (.var 1)
def Ty1 : Form := .var 0
def Ty2 : Form := .and Ty1 (.var 1)

/-- The formula naming each point, the root's being `⊤`. -/
def T (j : ForkUp 2 2) : Form :=
  if j = .tails 0 2 then Tx1 else if j = .tails 1 2 then Tx2
  else if j = .tails 2 0 then Ty1 else if j = .tails 2 1 then Ty2 else Form.tru

/-! Each derivation below is one condition of `PointEmbed.Images`, under the
premise `P`, named after the points it concerns: `mono_j_k` derives `k`'s
formula from `j`'s, `k` lying below `j` in the frame; `meet_j_k` derives, from
the formulas of two incomparable points, the join of those of the points above
both, here none; `arrow_k` is the arrow condition at `k`; and `con` derives the
conclusion `C` from the join of all four.  The order and the meets hold in any
context, and are stated so. -/

/-! ### Order and meets -/

/-- `h.1`. -/
theorem mono_x2_x1 {Γ : List Form} : (Tx2 :: Γ) ⊢ Tx1 := .andE₁ .h₀

/-- `h.1`. -/
theorem mono_y2_y1 {Γ : List Form} : (Ty2 :: Γ) ⊢ Ty1 := .andE₁ .h₀

/-! The `x` branch's formulas refute `a`, and the `y` branch's give it. -/

theorem meet_x1_y1 {Γ : List Form} : (.and Tx1 Ty1 :: Γ) ⊢ Form.disj [] :=
  .impE (.andE₁ .h₀) (.andE₂ .h₀)       -- h.1 h.2

theorem meet_x1_y2 {Γ : List Form} : (.and Tx1 Ty2 :: Γ) ⊢ Form.disj [] :=
  .impE (.andE₁ .h₀) (.andE₁ (.andE₂ .h₀))  -- h.1 h.2.1

theorem meet_x2_y1 {Γ : List Form} : (.and Tx2 Ty1 :: Γ) ⊢ Form.disj [] :=
  .impE (.andE₁ (.andE₁ .h₀)) (.andE₂ .h₀)  -- h.1.1 h.2

theorem meet_x2_y2 {Γ : List Form} : (.and Tx2 Ty2 :: Γ) ⊢ Form.disj [] :=
  .impE (.andE₁ (.andE₁ .h₀)) (.andE₁ (.andE₂ .h₀))  -- h.1.1 h.2.1

theorem meet_y1_x1 {Γ : List Form} : (.and Ty1 Tx1 :: Γ) ⊢ Form.disj [] :=
  .impE (.andE₂ .h₀) (.andE₁ .h₀)       -- h.2 h.1

theorem meet_y1_x2 {Γ : List Form} : (.and Ty1 Tx2 :: Γ) ⊢ Form.disj [] :=
  .impE (.andE₁ (.andE₂ .h₀)) (.andE₁ .h₀)  -- h.2.1 h.1

theorem meet_y2_x1 {Γ : List Form} : (.and Ty2 Tx1 :: Γ) ⊢ Form.disj [] :=
  .impE (.andE₂ .h₀) (.andE₁ (.andE₁ .h₀))  -- h.2 h.1.1

theorem meet_y2_x2 {Γ : List Form} : (.and Ty2 Tx2 :: Γ) ⊢ Form.disj [] :=
  .impE (.andE₁ (.andE₂ .h₀)) (.andE₁ (.andE₁ .h₀))  -- h.2.1 h.1.1

/-! ### Joins

Joins of the formulas of sets of points, the form in which the arrow conditions
conclude.  The `x` branch's join refutes `a` and the `y` branch's gives it; the
join over the points not below a lower point gives `b` on that point's side of
`a`. -/

/-- Both `x` formulas refute `a`. -/
theorem disj_x_neg : Ent (Form.disj [Tx1, Tx2]) (Form.neg (.var 0)) :=
  .orE .h₀ .h₀                          -- cases h; | inl hx => hx
    (.orE .h₀ (.andE₁ .h₀) (.flsE .h₀)) -- | inr h => cases h; | inl hx => hx.1

/-- Both `y` formulas give `a`. -/
theorem disj_y_a : Ent (Form.disj [Ty1, Ty2]) (.var 0) :=
  .orE .h₀ .h₀                          -- cases h; | inl hy => hy
    (.orE .h₀ (.andE₁ .h₀) (.flsE .h₀)) -- | inr h => cases h; | inl hy => hy.1

/-- The points not below `x₁` are `x₂`, `y₁` and `y₂`; under `¬ a` their
formulas give `b`, `x₂`'s and `y₂`'s outright and `y₁`'s by contradiction. -/
theorem disj_not_x1 : Ent (Form.disj [Tx2, Ty1, Ty2]) (.imp (Form.neg (.var 0)) (.var 1)) :=
  .impI (.orE .h₁ (.andE₂ .h₀)          -- intro hna; cases h; | inl hx => hx.2
    (.orE .h₀ (.flsE (.impE .h₂ .h₀))   -- | inr h => cases h; | inl ha => absurd ha hna
      (.orE .h₀ (.andE₂ .h₀) (.flsE .h₀))))  --   | inr h => cases h; | inl hy => hy.2

/-- The points not below `y₁` are `x₁`, `x₂` and `y₂`; under `a` their
formulas give `b`, `y₂`'s outright and the other two by contradiction. -/
theorem disj_not_y1 : Ent (Form.disj [Tx1, Tx2, Ty2]) (.imp (.var 0) (.var 1)) :=
  .impI (.orE .h₁ (.flsE (.impE .h₀ .h₁))  -- intro ha; cases h; | inl hna => absurd ha hna
    (.orE .h₀ (.flsE (.impE (.andE₁ .h₀) .h₂))  -- | inr h => cases h; | inl hx => absurd ha hx.1
      (.orE .h₀ (.andE₂ .h₀) (.flsE .h₀))))  --   | inr h => cases h; | inl hy => hy.2

/-! ### Arrows -/

/-- Under `¬ a`, `k` gives the join and so `b` (`disj_not_x1`).  That is
`¬ a → b`, so `P` decides `a`: `a` is `y₁`'s formula, and `¬ a` gives the join
through `k`. -/
theorem arrow_x1 : [.imp Tx1 (Form.disj [Tx2, Ty1, Ty2]), P] ⊢ Form.disj [Tx2, Ty1, Ty2] :=
  .orE (.impE (.andE₁ .h₁)              -- cases hP.1 (Or.inl (fun hna => …))
      (.orI₁ (.impI (.impE (disj_not_x1.mp (.impE .h₁ .h₀)) .h₀))))
                                        --   disj_not_x1 (k hna) hna
    (.orI₂ (.orI₁ .h₀))                 -- | inl ha => Or.inr (Or.inl ha)
    (.impE .h₁ .h₀)                     -- | inr hna => k hna

/-- `¬ a` and `b` give `x₂`'s formula, which `k` turns into `a` (`disj_y_a`), so
`¬ a` refutes `b`, and `¬ ¬ b` refutes `¬ a`.  Then `¬ a → b` holds vacuously,
so `P` decides `a`, and `a` is `y₁`'s formula. -/
theorem arrow_x2 : [.imp Tx2 (Form.disj [Ty1, Ty2]), P] ⊢ Form.disj [Ty1, Ty2] :=
  .cut (p := Form.neg (Form.neg (.var 0)))  -- have hnna : ¬ ¬ a
    (.impI (.impE (.andE₂ .h₂) (.impI   --   fun hna => hP.2 (fun hb =>
      (.impE .h₁ (disj_y_a.mp (.impE .h₂ (.andI .h₁ .h₀)))))))  --   hna (disj_y_a (k ⟨hna, hb⟩)))
    (.orE (.impE (.andE₁ .h₂)           -- cases hP.1 (Or.inl (fun hna => absurd hna hnna))
        (.orI₁ (.impI (.flsE (.impE .h₁ .h₀)))))
      (.orI₁ .h₀)                       -- | inl ha => Or.inl ha
      (.flsE (.impE .h₁ .h₀)))          -- | inr hna => absurd hna hnna

/-- Under `a`, `k` gives the join and so `b` (`disj_not_y1`).  That is `a → b`,
so `P` decides `a`: `a` gives the join through `k`, and `¬ a` is `x₁`'s
formula. -/
theorem arrow_y1 : [.imp Ty1 (Form.disj [Tx1, Tx2, Ty2]), P] ⊢ Form.disj [Tx1, Tx2, Ty2] :=
  .orE (.impE (.andE₁ .h₁)              -- cases hP.1 (Or.inr (fun ha => …))
      (.orI₂ (.impI (.impE (disj_not_y1.mp (.impE .h₁ .h₀)) .h₀))))
                                        --   disj_not_y1 (k ha) ha
    (.impE .h₁ .h₀)                     -- | inl ha => k ha
    (.orI₁ .h₀)                         -- | inr hna => Or.inl hna

/-- `a` and `b` give `y₂`'s formula, which `k` turns into `¬ a` (`disj_x_neg`),
so `a` refutes `b`, and `¬ ¬ b` refutes `a`: that is `x₁`'s formula. -/
theorem arrow_y2 : [.imp Ty2 (Form.disj [Tx1, Tx2]), P] ⊢ Form.disj [Tx1, Tx2] :=
  .orI₁ (.impI (.impE (.andE₂ .h₂) (.impI  -- Or.inl (fun ha => hP.2 (fun hb =>
    (.impE (disj_x_neg.mp (.impE .h₂ (.andI .h₁ .h₀))) .h₁))))  --   disj_x_neg (k ⟨ha, hb⟩) ha))

/-- The `x` formulas refute `a` and the `y` formulas give it. -/
theorem con : [Form.disj [Tx1, Tx2, Ty1, Ty2], P] ⊢ C :=
  .orE .h₀ (.orI₂ .h₀)                  -- cases h; | inl hx => Or.inr hx
    (.orE .h₀ (.orI₂ (.andE₁ .h₀))      -- | inr h => cases h; | inl hx => Or.inr hx.1
      (.orE .h₀ (.orI₁ .h₀)             --   | inr h => cases h; | inl hy => Or.inl hy
        (.orE .h₀ (.orI₁ (.andE₁ .h₀)) (.flsE .h₀))))  -- | inr h => … | inl hy => Or.inl hy.1

/-! ## The embedding -/

theorem sh_of_refutes_pair {α : Type} [HeytingAlgebra α] (v : Nat → α)
    (hv : (noForkUp2x2Form (.var 0) (.var 1)).eval v ≠ ⊤) : SH (ForkUp 2 2) α :=
  PointEmbed.sh_of_refutes points T (P := P) (C := C) Derives.tru
    (fun j hj k hk h₁ h₂ h₃ => by
      simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hj hk
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd h₁ (by decide)
          | exact absurd rfl h₂
          | exact absurd rfl h₃
          | exact mono_x2_x1 | exact mono_y2_y1)
    (fun j hj k hk h₁ h₂ => by
      simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hj hk
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd (by decide) h₁
          | exact absurd (by decide) h₂
          | exact meet_x1_y1 | exact meet_x1_y2 | exact meet_x2_y1 | exact meet_x2_y2
          | exact meet_y1_x1 | exact meet_y1_x2 | exact meet_y2_x1 | exact meet_y2_x2)
    (fun k hk h₁ => by
      simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl h₁
          | exact arrow_x1 | exact arrow_x2 | exact arrow_y1 | exact arrow_y2)
    con v hv

/-! ## Nothing smaller refutes it -/

/-- Every element of the tall fork, named through the points. -/
def terms : List Form :=
  ([.all, .tails 0 0, .tails 0 1, .tails 0 2, .tails 1 0, .tails 1 1, .tails 1 2,
      .tails 2 0, .tails 2 1, .tails 2 2] : List (ForkUp 2 2)).map
    fun w => Form.disj ((below points.J w).map T)

theorem nvalid :
    ¬ ∀ a b : ForkUp 2 2, (noForkUp2x2Form (.var 0) (.var 1)).eval (valPair a b) = ⊤ := by decide

end NoForkUp2x2Witness

open NoForkUp2x2Witness

/-- **Nothing below the tall fork refutes `noForkUp2x2Form`.** -/
theorem refuterLB_fork22_noForkUp2x2 : RefuterLB (ForkUp 2 2) (noForkUp2x2Form (.var 0) (.var 1)) :=
  refuterLB_of_generates (c := .tails 0 0) terms (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- **Every algebra refuting `noForkUp2x2Form` carries the tall fork below it.** -/
theorem sh_fork22_of_refutes_noForkUp2x2 (α : Type) (iα : HeytingAlgebra α)
    (h : ¬ ∀ v : Nat → α, (noForkUp2x2Form (.var 0) (.var 1)).eval v = ⊤) :
    @SH (ForkUp 2 2) α _ iα := by
  obtain ⟨v, hv⟩ := @exists_ne_top α iα _ h
  exact @sh_of_refutes_pair α iα v hv

/-- **The criterion.**  A schema derives `noForkUp2x2Form` exactly when it misses
the top value in the tall fork. -/
theorem derivesFromSchema_noForkUp2x2_iff (X : Form) :
    DerivesFromSchema X (noForkUp2x2Form (.var 0) (.var 1)) ↔
      ¬ ∀ w : Nat → ForkUp 2 2, X.eval w = ⊤ := by
  constructor
  · intro h hv
    exact nvalid fun _ _ => DerivesFromSchema.valid hv h _
  · exact fun hX => DerivesFromSchema.of_sh fun α iα hnv =>
      ⟨ForkUp 2 2, inferInstance, sh_fork22_of_refutes_noForkUp2x2 α iα hnv, hX⟩
