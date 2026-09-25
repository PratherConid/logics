import Logics.IntermediateAxioms.Derivation
import Logics.PointEmbed
import Logics.Lindenbaum

/-!
# Where `noKiteUp1x2Form` sits, exactly

The uneven kite `KiteUp 1 2` is a root and a top joined by two paths, one through
a single point `x`, the other through `y₁` below `y₂`.  It refutes
`noKiteUp1x2Form`, and this file shows that it is the formula's only minimal
refuter, answering the two questions `NoDiamondRefuter` answers for the diamond.

**Can it be shrunk?**  No: `refuterLB_kite12_noKiteUp1x2`.  A refuting pair
generates the whole eight element algebra, each element being the value of a
formula in the pair, which evaluation checks.

**Which schemas derive the formula?**  Exactly those missing the top value in the
uneven kite: `derivesFromSchema_noKiteUp1x2_iff`.  That rests on
`sh_kite12_of_refutes_noKiteUp1x2`, which puts the uneven kite below every
algebra refuting the formula.  The embedding goes through the kite's points
(`Logics/PointEmbed.lean`), each sent to the value of a formula in the refuting
pair `a`, `b`:

* `x` to `b ∨ ¬ b`, `y₁` to `b → (a ∨ ¬ a)` and `y₂` to `a ∨ ¬ a`;
* the top `t` to `(a ∧ b) ∨ (a → ¬ b)`.

This happens in the quotient by the filter above the formula's premise `P`.
Everything the embedding asks of those values -- how they are ordered, how they
meet, one arrow for each point, and that the join of all four lies below the
formula's conclusion `C` -- is a derivation under `P`.

**The proofs.**  Each derivation is a natural deduction tree.  Hypotheses are
named by position (`Derives.h₀`, `h₁`, …), the most recent first, and the
comments beside a tree read it as a proof in Lean's own logic, naming the
hypotheses: a case split is `orE`, `Or.inl` is `orI₁`, introducing a hypothesis
is `impI`, applying one is `impE`, `absurd` is `flsE` of an `impE` into `fls`,
and using another entailment is `Ent.mp`.  `hP` is the premise `P`, and `k` the
arrow an arrow condition assumes.

**Why they hold.**  Most of them do not need `P`.  The formula for `t` is
excluded middle at `a ∧ b` with its second case curried: it gives the formula
for `y₁`, it follows from those for `x` and `y₁`, and its double negation is
provable.  The formula for `y₂` gives the one for `y₁` outright.  `P` enters
through its antecedent, Peirce's law at `a` and `b ∨ ¬ b`, which holds as soon
as `a → b ∨ ¬ b` does.  So under `P` that arrow gives `a ∨ b`, and then
`b ∨ ¬ b`, `a` through the arrow and `b` directly.  This is how the formula for
`t` gives those for `x` and `y₂`, and how the arrow at `y₂` is met.  The arrow
at `y₁` is the one place where Peirce's antecedent has to be discharged in full.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra PointEmbed

namespace NoKiteUp1x2Witness

/-! ## The uneven kite through its points -/

/-- The points of the uneven kite, as the upsets they generate: the root, `x`,
`y₁`, `y₂` and the top `t`.  `co` sends each to the upset of the points not
below it. -/
def points : Points (KiteUp 1 2) where
  J := [.all, .tails 0 2, .tails 1 0, .tails 1 1, .tails 1 2]
  co j :=
    if j = .tails 0 2 then .tails 1 0 else if j = .tails 1 0 then .tails 0 1
    else if j = .tails 1 1 then .tails 0 2 else if j = .tails 1 2 then .empty
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
def P : Form := .imp (peirceForm (.var 0) (excludedMiddleForm (.var 1))) (.or (.var 0) (.var 1))

/-- The formula's conclusion. -/
def C : Form := .or (.var 1) (.imp (.var 1) (excludedMiddleForm (.var 0)))

def Tx : Form := excludedMiddleForm (.var 1)
def Ty1 : Form := .imp (.var 1) (excludedMiddleForm (.var 0))
def Ty2 : Form := excludedMiddleForm (.var 0)
def Tt : Form := .or (.and (.var 0) (.var 1)) (.imp (.var 0) (Form.neg (.var 1)))

/-- The formula naming each point, the root's being `⊤`. -/
def T (j : KiteUp 1 2) : Form :=
  if j = .tails 0 2 then Tx else if j = .tails 1 0 then Ty1
  else if j = .tails 1 1 then Ty2 else if j = .tails 1 2 then Tt else Form.tru

/-! ### What Peirce's law and the premise give -/

/-- Peirce's law holds once its left argument implies its right one:
`fun h => h hpq`. -/
private theorem imp_ent_peirce (p q : Form) : Ent (.imp p q) (peirceForm p q) :=
  .impI (.impE .h₀ .h₁)

/-- **Under `P`, an arrow from `a` into `b ∨ ¬ b` gives `a ∨ b`**, since it gives
`P`'s antecedent: `fun h => hP (imp_ent_peirce h)`. -/
theorem p_ent_or : Ent P (.imp (.imp (.var 0) Tx) (.or (.var 0) (.var 1))) :=
  .impI (.impE .h₁ ((imp_ent_peirce _ _).mp .h₀))

/-- Under `P`, an arrow from `a` into `b ∨ ¬ b` gives `b ∨ ¬ b`. -/
theorem p_ent_tx : Ent P (.imp (.imp (.var 0) Tx) Tx) :=
  .impI (.orE (.impE (p_ent_or.mp .h₁) .h₀)  -- intro h; cases p_ent_or hP h
    (.impE .h₁ .h₀)                     -- | inl ha => h ha
    (.orI₁ .h₀))                        -- | inr hb => Or.inl hb

/-! ### What the formula for `t` gives, and what gives it -/

/-- `(a ∧ b) ∨ (a → ¬ b)` gives `b → a ∨ ¬ a`. -/
theorem tt_ent_ty1 : Ent Tt Ty1 :=
  .impI (.orE .h₁                       -- intro hb; cases ht
    (.orI₁ (.andE₁ .h₀))                -- | inl hab => Or.inl hab.1
    (.orI₂ (.impI (.impE (.impE .h₁ .h₀) .h₂))))  -- | inr hn => Or.inr (fun ha => hn ha hb)

/-- `(a ∧ b) ∨ (a → ¬ b)` gives `a → b ∨ ¬ b`. -/
theorem tt_ent_imp : Ent Tt (.imp (.var 0) Tx) :=
  .impI (.orE .h₁                       -- intro ha; cases ht
    (.orI₁ (.andE₂ .h₀))                -- | inl hab => Or.inl hab.2
    (.orI₂ (.impE .h₀ .h₁)))            -- | inr hn => Or.inr (hn ha)

/-- `b ∨ ¬ b` and `b → a ∨ ¬ a` give `(a ∧ b) ∨ (a → ¬ b)`. -/
theorem txTy1_ent_tt : Ent (.and Tx Ty1) Tt :=
  .orE (.andE₁ .h₀)                     -- cases h.1
    (.orE (.impE (.andE₂ .h₁) .h₀)      -- | inl hb => cases h.2 hb
      (.orI₁ (.andI .h₀ .h₁))           --   | inl ha => Or.inl ⟨ha, hb⟩
      (.orI₂ (.impI (.flsE (.impE .h₁ .h₀)))))  --   | inr hna => Or.inr (fun ha => absurd ha hna)
    (.orI₂ (.impI .h₁))                 -- | inr hnb => Or.inr (fun _ => hnb)

/-! ### Joins of the formulas

Each is a case split over the disjuncts, one entailment for each. -/

/-- Each of `b → a ∨ ¬ a`, `a ∨ ¬ a` and `(a ∧ b) ∨ (a → ¬ b)` gives
`b → a ∨ ¬ a`. -/
theorem disj_ent_ty1 : Ent (Form.disj [Ty1, Ty2, Tt]) Ty1 :=
  Ent.or_elim (Ent.refl Ty1) (Ent.or_elim (Ent.imp_weak (.var 1) Ty2)
    (Ent.or_elim tt_ent_ty1 (Ent.fls Ty1)))

/-- Each of `b ∨ ¬ b` and `(a ∧ b) ∨ (a → ¬ b)` gives `a → b ∨ ¬ b`. -/
theorem disj_ent_imp : Ent (Form.disj [Tx, Tt]) (.imp (.var 0) Tx) :=
  Ent.or_elim (Ent.imp_weak (.var 0) Tx) (Ent.or_elim tt_ent_imp (Ent.fls _))

/-- Each of `b ∨ ¬ b`, `a ∨ ¬ a` and `(a ∧ b) ∨ (a → ¬ b)` gives Peirce's law
at `a` and `b ∨ ¬ b`, the first and the last through `a → b ∨ ¬ b`. -/
theorem disj_ent_peirce : Ent (Form.disj [Tx, Ty2, Tt]) (peirceForm (.var 0) Tx) :=
  Ent.or_elim ((Ent.imp_weak (.var 0) Tx).trans (imp_ent_peirce _ _))
    (Ent.or_elim (em_ent_peirce _ _)
      (Ent.or_elim (tt_ent_imp.trans (imp_ent_peirce _ _)) (Ent.fls _)))

/-! ### The conditions

Each derivation below is one condition of `PointEmbed.Images`, under the
premise `P`, named after the points it concerns: `mono_j_k` derives `k`'s
formula from `j`'s, `k` lying below `j` in the frame; `meet_j_k` derives, from
the formulas of two incomparable points, the join of those of the points above
both; `arrow_k` is the arrow condition at `k`; and `con` derives the conclusion
`C` from the join of all four. -/

theorem mono_y2_y1 : [Ty2, P] ⊢ Ty1 :=
  .impI .h₁                             -- fun _ => hy

/-- The formula for `t` gives an arrow from `a` into `b ∨ ¬ b` (`tt_ent_imp`),
which gives `b ∨ ¬ b` under `P` (`p_ent_tx`). -/
theorem mono_t_x : [Tt, P] ⊢ Tx :=
  .impE (p_ent_tx.mp .h₁) (tt_ent_imp.mp .h₀)  -- p_ent_tx hP (tt_ent_imp ht)

theorem mono_t_y1 : [Tt, P] ⊢ Ty1 :=
  tt_ent_ty1.mp .h₀

/-- The same arrow gives `a ∨ b` under `P` (`p_ent_or`).  `a` is one case of
`a ∨ ¬ a`, and `b` gives `a ∨ ¬ a` through `tt_ent_ty1`. -/
theorem mono_t_y2 : [Tt, P] ⊢ Ty2 :=
  .orE (.impE (p_ent_or.mp .h₁) (tt_ent_imp.mp .h₀))  -- cases p_ent_or hP (tt_ent_imp ht)
    (.orI₁ .h₀)                         -- | inl ha => Or.inl ha
    (.impE (tt_ent_ty1.mp .h₁) .h₀)     -- | inr hb => tt_ent_ty1 ht hb

/-! The four meet conditions are one, `txTy1_ent_tt`: `t` is the only point
above `x` and `y₁`, and the formula for `y₂` gives the one for `y₁`. -/

theorem meet_x_y1 : [.and Tx Ty1, P] ⊢ Form.disj [Tt] :=
  .orI₁ (txTy1_ent_tt.mp .h₀)           -- Or.inl (txTy1_ent_tt h)

theorem meet_y1_x : [.and Ty1 Tx, P] ⊢ Form.disj [Tt] :=
  .orI₁ (txTy1_ent_tt.mp (.andI (.andE₂ .h₀) (.andE₁ .h₀)))  -- Or.inl (txTy1_ent_tt ⟨h.2, h.1⟩)

theorem meet_x_y2 : [.and Tx Ty2, P] ⊢ Form.disj [Tt] :=
  .orI₁ (txTy1_ent_tt.mp (.andI (.andE₁ .h₀) (.impI (.andE₂ .h₁))))
                                        -- Or.inl (txTy1_ent_tt ⟨h.1, fun _ => h.2⟩)

theorem meet_y2_x : [.and Ty2 Tx, P] ⊢ Form.disj [Tt] :=
  .orI₁ (txTy1_ent_tt.mp (.andI (.andE₂ .h₀) (.impI (.andE₁ .h₁))))
                                        -- Or.inl (txTy1_ent_tt ⟨h.2, fun _ => h.1⟩)

/-- Under `b`, `b ∨ ¬ b` holds and `k` gives the join, which gives
`b → a ∨ ¬ a` (`disj_ent_ty1`) and so `a ∨ ¬ a` at that `b`. -/
theorem arrow_x : [.imp Tx (Form.disj [Ty1, Ty2, Tt]), P] ⊢ Form.disj [Ty1, Ty2, Tt] :=
  .orI₁ (.impI (.impE (disj_ent_ty1.mp (.impE .h₁ (.orI₁ .h₀))) .h₀))
                                        -- Or.inl (fun hb => disj_ent_ty1 (k (Or.inl hb)) hb)

/-- `P`'s antecedent holds.  Given `h : (a → b ∨ ¬ b) → a`, `b` gives `a`, so
`b → a ∨ ¬ a` holds and `k` gives the join, each disjunct of which gives
Peirce's law (`disj_ent_peirce`), and so `a` through `h`.  Of the resulting
`a ∨ b`, `a` gives `b → a ∨ ¬ a` and so the join through `k`, and `b` gives
`b ∨ ¬ b`. -/
theorem arrow_y1 : [.imp Ty1 (Form.disj [Tx, Ty2, Tt]), P] ⊢ Form.disj [Tx, Ty2, Tt] :=
  .orE (.impE .h₁ (.impI                -- cases hP (fun h => …)
      (.impE (disj_ent_peirce.mp (.impE .h₁  --   disj_ent_peirce (k (fun hb => …)) h
        (.impI (.orI₁ (.impE .h₁ (.impI (.orI₁ .h₁))))))) .h₀)))
                                        --     Or.inl (h (fun _ => Or.inl hb))
    (.impE .h₁ (.impI (.orI₁ .h₁)))     -- | inl ha => k (fun _ => Or.inl ha)
    (.orI₁ (.orI₁ .h₀))                 -- | inr hb => Or.inl (Or.inl hb)

/-- `a` gives `a ∨ ¬ a`, so `k` gives the join, which with `a` gives
`b ∨ ¬ b` (`disj_ent_imp`).  That is an arrow from `a` into `b ∨ ¬ b`, and
`p_ent_tx` turns it into `b ∨ ¬ b`. -/
theorem arrow_y2 : [.imp Ty2 (Form.disj [Tx, Tt]), P] ⊢ Form.disj [Tx, Tt] :=
  .orI₁ (.impE (p_ent_tx.mp .h₁)        -- Or.inl (p_ent_tx hP (fun ha => …))
    (.impI (.impE (disj_ent_imp.mp (.impE .h₁ (.orI₁ .h₀))) .h₀)))
                                        --   disj_ent_imp (k (Or.inl ha)) ha

/-- `(a ∧ b) ∨ (a → ¬ b)` is not refutable: refuting it refutes `a ∧ b`, and
that gives `a → ¬ b`. -/
theorem arrow_t : [.imp Tt (Form.disj []), P] ⊢ Form.disj [] :=
  .impE .h₀ (.orI₂ (.impI (.impI (.impE .h₂ (.orI₁ (.andI .h₁ .h₀))))))
                                        -- k (Or.inr (fun ha hb => k (Or.inl ⟨ha, hb⟩)))

/-- `b ∨ ¬ b` gives `C` by cases, and the other three give `b → a ∨ ¬ a`
(`disj_ent_ty1`). -/
theorem con : [Form.disj [Tx, Ty1, Ty2, Tt], P] ⊢ C :=
  .orE .h₀                              -- cases h
    (.orE .h₀ (.orI₁ .h₀)               -- | inl hx => cases hx; | inl hb => Or.inl hb
      (.orI₂ (.impI (.flsE (.impE .h₁ .h₀)))))  --   | inr hnb => Or.inr (fun hb => absurd hb hnb)
    (.orI₂ (disj_ent_ty1.mp .h₀))       -- | inr h' => Or.inr (disj_ent_ty1 h')

/-! ## The embedding -/

theorem sh_of_refutes_pair {α : Type} [HeytingAlgebra α] (v : Nat → α)
    (hv : noKiteUp1x2Form.eval v ≠ ⊤) : SH (KiteUp 1 2) α :=
  PointEmbed.sh_of_refutes points T (P := P) (C := C) Derives.tru
    (fun j hj k hk h₁ h₂ h₃ => by
      simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hj hk
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd h₁ (by decide)
          | exact absurd rfl h₂
          | exact absurd rfl h₃
          | exact mono_y2_y1 | exact mono_t_x | exact mono_t_y1 | exact mono_t_y2)
    (fun j hj k hk h₁ h₂ => by
      simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hj hk
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd (by decide) h₁
          | exact absurd (by decide) h₂
          | exact meet_x_y1 | exact meet_x_y2 | exact meet_y1_x | exact meet_y2_x)
    (fun k hk h₁ => by
      simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl h₁
          | exact arrow_x | exact arrow_y1 | exact arrow_y2 | exact arrow_t)
    con v hv

/-! ## Nothing smaller refutes it -/

/-- Every element of the uneven kite, named through the points. -/
def terms : List Form :=
  ([.empty, .all, .tails 0 0, .tails 0 1, .tails 0 2, .tails 1 0, .tails 1 1, .tails 1 2] :
      List (KiteUp 1 2)).map fun w => Form.disj ((below points.J w).map T)

theorem nvalid : ¬ ∀ a b : KiteUp 1 2, noKiteUp1x2Form.eval (valPair a b) = ⊤ := by decide

end NoKiteUp1x2Witness

open NoKiteUp1x2Witness

/-- **Nothing below the uneven kite refutes `noKiteUp1x2Form`.** -/
theorem refuterLB_kite12_noKiteUp1x2 : RefuterLB (KiteUp 1 2) noKiteUp1x2Form :=
  refuterLB_of_generates (c := .tails 0 0) terms (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- **Every algebra refuting `noKiteUp1x2Form` carries the uneven kite below
it.** -/
theorem sh_kite12_of_refutes_noKiteUp1x2 (α : Type) (iα : HeytingAlgebra α)
    (h : ¬ ∀ v : Nat → α, noKiteUp1x2Form.eval v = ⊤) : @SH (KiteUp 1 2) α _ iα := by
  obtain ⟨v, hv⟩ := @exists_ne_top α iα _ h
  exact @sh_of_refutes_pair α iα v hv

/-- **The criterion.**  A schema derives `noKiteUp1x2Form` exactly when it misses
the top value in the uneven kite. -/
theorem derivesFromSchema_noKiteUp1x2_iff (X : Form) :
    DerivesFromSchema X noKiteUp1x2Form ↔ ¬ ∀ w : Nat → KiteUp 1 2, X.eval w = ⊤ := by
  constructor
  · intro h hv
    exact nvalid fun _ _ => DerivesFromSchema.valid hv h _
  · exact fun hX => DerivesFromSchema.of_sh fun α iα hnv =>
      ⟨KiteUp 1 2, inferInstance, sh_kite12_of_refutes_noKiteUp1x2 α iα hnv, hX⟩
