import Logics.IntermediateAxioms.AxiomDef
import Logics.PointEmbed
import Logics.Lindenbaum
import Logics.Adjoin

/-!
# Where `noDiamondHairForm` sits, exactly

The diamond with a hair is a root, two points `u` and `v` above it with a
common successor `m`, and one more maximal point `z` above `v` alone; its
algebra is `DiamondHair`.  It refutes `noDiamondHairForm`, and this file shows
that it is the formula's only minimal refuter, answering the two questions
`NoDiamondRefuter` answers for the diamond.

**Can it be shrunk?**  No: `refuterLB_diamondHair_noDiamondHair`.  A refuting
pair generates the whole nine element algebra, each element being the value of
a formula in the pair, which evaluation checks.

**Which schemas derive the formula?**  Exactly those missing the top value in
`DiamondHair`: `derivesFromSchema_noDiamondHair_iff`.  That rests on
`sh_diamondHair_of_refutes_noDiamondHair`, which puts `DiamondHair` below every
algebra refuting the formula.  The embedding goes through the frame's points
(`Logics/PointEmbed.lean`), each sent to the value of a formula in the refuting
pair `a`, `b`:

* `u` to `¬ a → a` and the hair `z` to `¬ a`;
* `v` to `(¬ a → a) → b ∨ ¬ b`, and the top `m`, where `u` and `v` meet, to the
  meet of those two.

This happens in the quotient by the filter above the formula's premise `P`.
Everything the embedding asks of those values -- how they are ordered, how they
meet, one arrow for each point, and that the join of all four lies below the
formula's conclusion, bounded depth two -- is a derivation under `P`, and each
is a short natural deduction tree.  Most need nothing from `P`: `m`'s formula
is literally the meet of `u`'s and `v`'s, `v`'s is an arrow out of `u`'s and
`u`'s one out of `z`'s, so the order, the meets and three of the arrows come
down to projections, contraction, and excluded middle being irrefutable.  `P` is
needed twice, for the arrow at `v` and for the conclusion.  Its hypothesis
`b → ¬ a ∨ (¬ a → a)` asks `b` for the formula of `z` or of `u`, and once that
is supplied `P` splits the argument into the cases `a` and `b`.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra PointEmbed

namespace NoDiamondHairWitness

/-! ## The diamond with a hair through its points -/

/-- The element with parts `x` and `y` in the two glued chains. -/
abbrev pt (x y : Fin 3) (h : y ⊑ 1 ∨ 1 ⊑ x := by decide) : DiamondHair := .of ⟨x, y, h⟩

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The points of the diamond with a hair, as the upsets they generate: the
root, `u`, `v`, the hair `z` and the top `m`.  `co` sends each to the upset of
the points not below it. -/
def points : Points DiamondHair where
  J := [.top, pt 2 0, pt 1 2, pt 0 1, pt 1 0]
  co j :=
    if j = pt 2 0 then pt 1 2 else if j = pt 1 2 then pt 2 1
    else if j = pt 0 1 then pt 2 0 else if j = pt 1 0 then pt 0 1
    else pt 2 2
  c := pt 2 2
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
  .imp (.imp (.var 1) (.or (Form.neg (.var 0)) (.imp (Form.neg (.var 0)) (.var 0))))
    (.or (.var 0) (.var 1))

/-- The formula's conclusion, bounded depth two. -/
def C : Form := bd2Form (.var 0) (.var 1)

/-- `u`'s formula, `¬ a → a`. -/
def Tu : Form := .imp (Form.neg (.var 0)) (.var 0)
/-- `v`'s formula, `(¬ a → a) → b ∨ ¬ b`: an arrow out of `u`'s. -/
def Tv : Form := .imp Tu (excludedMiddleForm (.var 1))
/-- The hair's formula, `¬ a`. -/
def Tz : Form := Form.neg (.var 0)
/-- `m`'s formula, the meet of `u`'s and `v`'s, as `m` is where `u` and `v`
meet. -/
def Tm : Form := .and Tu Tv

/-- The formula naming each point, the root's being `⊤`. -/
def T (j : DiamondHair) : Form :=
  if j = pt 2 0 then Tu else if j = pt 1 2 then Tv
  else if j = pt 0 1 then Tz else if j = pt 1 0 then Tm else Form.tru

/-! Each derivation below is one condition of `PointEmbed.Images`, under the
premise `P`, named after the points it concerns: `mono_j_k` derives `k`'s
formula from `j`'s, `k` lying below `j` in the frame; `meet_j_k` derives, from
the formulas of two incomparable points, the join of those of the points above
both; `arrow_k` is the arrow condition at `k`; and `con` derives the conclusion
`C` from the join of all four.

Only `arrow_v` and `con` use `P`; the others hold in any context, and are
stated so.  Hypotheses are named by position (`Derives.h₀`, `h₁`, …), the most
recent first, and the comments beside a tree read it as a proof in Lean's own
logic: a case split is `orE`, `Or.inl` is `orI₁`, introducing a hypothesis is
`impI`, applying one is `impE`, `absurd` is `flsE` of an `impE` into `fls`, a
`have` is a `cut` at the formula it states, and using an entailment is
`Ent.mp`. -/

/-! ### Two general steps -/

/-- A hypothesis `p ∧ q` serves as `q ∧ p`: discharged, it is an arrow out of
`p ∧ q`, which the swap `q ∧ p ⊢ p ∧ q` turns into one out of `q ∧ p`. -/
private theorem and_swap {Γ : List Form} {p q r : Form} (d : (.and p q :: Γ) ⊢ r) :
    (.and q p :: Γ) ⊢ r :=
  Derives.deduction.mpr ((Ent.imp_cong (.andI (.andE₂ .h₀) (.andE₁ .h₀)) (Ent.refl r)).mp
    (Derives.deduction.mp d))

/-- **Contraction**: an arrow from `p` into anything that gives `p → q` gives
`p → q`, `fun hp => hD (h hp) hp`. -/
private theorem imp_contract {Γ : List Form} {p q D : Form} (hD : Ent D (.imp p q)) :
    (.imp p D :: Γ) ⊢ .imp p q :=
  .impI (.impE (hD.mp (.impE .h₁ .h₀)) .h₀)

/-! ### Order -/

/-- `¬ a` refutes `¬ a → a`: `fun hu => absurd (hu hz) hz`. -/
theorem mono_z_v {Γ : List Form} : (Tz :: Γ) ⊢ Tv :=
  .impI (.flsE (.impE .h₁ (.impE .h₀ .h₁)))

/-- `hm.1`. -/
theorem mono_m_u {Γ : List Form} : (Tm :: Γ) ⊢ Tu := .andE₁ .h₀

/-- `hm.2`. -/
theorem mono_m_v {Γ : List Form} : (Tm :: Γ) ⊢ Tv := .andE₂ .h₀

/-! ### Joins

Joins of the formulas of sets of points, the form in which the meet and arrow
conditions conclude.  The join over the points above `u`, or above `v`, gives
that point's formula back, by the order; the join over the points not below `v`
gives `¬ a ∨ (¬ a → a)`, what `P`'s hypothesis asks of `b`. -/

/-- The points above `v` are `v`, `z` and `m`. -/
theorem disj_above_v : Ent (Form.disj [Tv, Tz, Tm]) Tv :=
  .orE .h₀ .h₀                          -- cases h; | inl hv => hv
    (.orE .h₀ mono_z_v                  -- | inr h => cases h; | inl hz => mono_z_v hz
      (.orE .h₀ mono_m_v (.flsE .h₀)))  --   | inr h => cases h; | inl hm => mono_m_v hm

/-- The points above `u` are `u` and `m`. -/
theorem disj_above_u : Ent (Form.disj [Tu, Tm]) Tu :=
  .orE .h₀ .h₀                          -- cases h; | inl hu => hu
    (.orE .h₀ mono_m_u (.flsE .h₀))     -- | inr h => cases h; | inl hm => mono_m_u hm

/-- The points not below `v` are `u`, `z` and `m`. -/
theorem disj_u_z_m : Ent (Form.disj [Tu, Tz, Tm]) (.or Tz Tu) :=
  .orE .h₀ (.orI₂ .h₀)                  -- cases h; | inl hu => Or.inr hu
    (.orE .h₀ (.orI₁ .h₀)               -- | inr h => cases h; | inl hz => Or.inl hz
      (.orE .h₀ (.orI₂ mono_m_u) (.flsE .h₀)))  -- | inr h => cases h; | inl hm => Or.inr hm.1

/-! ### Meets -/

/-- `m`'s formula is the meet itself: `Or.inl h`. -/
theorem meet_u_v {Γ : List Form} : (.and Tu Tv :: Γ) ⊢ Form.disj [Tm] := .orI₁ .h₀

theorem meet_v_u {Γ : List Form} : (.and Tv Tu :: Γ) ⊢ Form.disj [Tm] := and_swap meet_u_v

/-- `¬ a → a` refutes `¬ a`: `h.2 (h.1 h.2)`. -/
theorem meet_u_z {Γ : List Form} : (.and Tu Tz :: Γ) ⊢ Form.disj [] :=
  .impE (.andE₂ .h₀) (.impE (.andE₁ .h₀) (.andE₂ .h₀))

theorem meet_z_u {Γ : List Form} : (.and Tz Tu :: Γ) ⊢ Form.disj [] := and_swap meet_u_z

/-- `m` lies above `u`, so this is `meet_u_z` again: `meet_u_z ⟨h.1.1, h.2⟩`. -/
theorem meet_m_z {Γ : List Form} : (.and Tm Tz :: Γ) ⊢ Form.disj [] :=
  .cut (.andI (.andE₁ (.andE₁ .h₀)) (.andE₂ .h₀)) meet_u_z

theorem meet_z_m {Γ : List Form} : (.and Tz Tm :: Γ) ⊢ Form.disj [] := and_swap meet_m_z

/-! ### Arrows -/

/-- `v`'s formula is an arrow out of `u`'s, so this is contraction:
`Or.inl (fun hu => disj_above_v (h hu) hu)`. -/
theorem arrow_u {Γ : List Form} :
    (.imp Tu (Form.disj [Tv, Tz, Tm]) :: Γ) ⊢ Form.disj [Tv, Tz, Tm] :=
  .orI₁ (imp_contract disj_above_v)

/-- `P`'s hypothesis holds: `b` gives `v`'s formula, which `h` turns into the
formula of `u`, `z` or `m`, and so into `¬ a ∨ (¬ a → a)` by `disj_u_z_m`.  So
`a ∨ b`; then `a` gives `u`'s formula, and `b` the conclusion through `h` once
more. -/
theorem arrow_v : [.imp Tv (Form.disj [Tu, Tz, Tm]), P] ⊢ Form.disj [Tu, Tz, Tm] :=
  .orE (.impE .h₁ (.impI                -- cases hP (fun hb => …)
      (disj_u_z_m.mp (.impE .h₁ (.impI (.orI₁ .h₁))))))
                                        --   disj_u_z_m (h (fun _ => Or.inl hb))
    (.orI₁ (.impI .h₁))                 -- | inl ha => Or.inl (fun _ => ha)
    (.impE .h₁ (.impI (.orI₁ .h₁)))     -- | inr hb => h (fun _ => Or.inl hb)

/-- `u`'s formula is an arrow out of the hair's, so this is contraction too:
`Or.inl (fun hz => disj_above_u (h hz) hz)`. -/
theorem arrow_z {Γ : List Form} : (.imp Tz (Form.disj [Tu, Tm]) :: Γ) ⊢ Form.disj [Tu, Tm] :=
  .orI₁ (imp_contract disj_above_u)

/-- Under `a`, `u`'s formula holds, and excluded middle at `b` then gives `m`'s,
which `h` turns into `¬ a`.  So `a` refutes that excluded middle, which cannot
be refuted. -/
theorem arrow_m {Γ : List Form} : (.imp Tm (Form.disj [Tz]) :: Γ) ⊢ Form.disj [Tz] :=
  .orI₁ (.impI                          -- Or.inl; intro ha
    (.cut (p := Form.neg (excludedMiddleForm (.var 1)))  -- have k : ¬ (b ∨ ¬ b)
      (.impI (.orE (.impE .h₂ (.andI (.impI .h₂) (.impI .h₁)))
                                        --   fun hem => cases h ⟨fun _ => ha, fun _ => hem⟩
        (.impE .h₀ .h₂)                 --   | inl hz => hz ha
        .h₀))                           --   | inr f => f
      (.impE .h₀ (.orI₂ (.impI (.impE .h₁ (.orI₁ .h₀)))))))
                                        -- k (Or.inr (fun hb => k (Or.inl hb)))

/-- `u`'s formula gives `P`'s hypothesis, so `a ∨ b`, and either gives `C`.  The
other three give `v`'s, by `disj_above_v`, which is `C`'s right disjunct once
`a` gives `u`'s. -/
theorem con : [Form.disj [Tu, Tv, Tz, Tm], P] ⊢ C :=
  .orE .h₀                              -- cases h
    (.orE (.impE .h₂ (.impI (.orI₂ .h₁)))  -- | inl hu => cases hP (fun _ => Or.inr hu)
      (.orI₁ .h₀)                       --   | inl ha => Or.inl ha
      (.orI₂ (.impI (.orI₁ .h₁))))      --   | inr hb => Or.inr (fun _ => Or.inl hb)
    (.orI₂ (.impI (.impE (disj_above_v.mp .h₁) (.impI .h₁))))
                                        -- | inr h => Or.inr (fun ha => disj_above_v h fun _ => ha)

/-! ## The embedding -/

theorem sh_of_refutes_pair {α : Type} [HeytingAlgebra α] (v : Nat → α)
    (hv : (noDiamondHairForm (.var 0) (.var 1)).eval v ≠ ⊤) : SH DiamondHair α :=
  PointEmbed.sh_of_refutes points T (P := P) (C := C) Derives.tru
    (fun j hj k hk h₁ h₂ h₃ => by
      simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hj hk
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd h₁ (by decide)
          | exact absurd rfl h₂
          | exact absurd rfl h₃
          | exact mono_z_v | exact mono_m_u | exact mono_m_v)
    (fun j hj k hk h₁ h₂ => by
      simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hj hk
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd (by decide) h₁
          | exact absurd (by decide) h₂
          | exact meet_u_v | exact meet_u_z | exact meet_v_u | exact meet_z_u
          | exact meet_z_m | exact meet_m_z)
    (fun k hk h₁ => by
      simp only [points, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl h₁
          | exact arrow_u | exact arrow_v | exact arrow_z | exact arrow_m)
    con v hv

/-! ## Nothing smaller refutes it -/

/-- Every element of `DiamondHair`, named through the points. -/
def terms : List Form :=
  ([.top, pt 0 0, pt 0 1, pt 1 0, pt 1 1, pt 1 2, pt 2 0, pt 2 1, pt 2 2] : List DiamondHair).map
    fun w => Form.disj ((below points.J w).map T)

theorem nvalid :
    ¬ ∀ a b : DiamondHair, (noDiamondHairForm (.var 0) (.var 1)).eval (valPair a b) = ⊤ := by decide

end NoDiamondHairWitness

open NoDiamondHairWitness

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Nothing below the diamond with a hair refutes `noDiamondHairForm`.** -/
theorem refuterLB_diamondHair_noDiamondHair :
    RefuterLB DiamondHair (noDiamondHairForm (.var 0) (.var 1)) :=
  refuterLB_of_generates (c := pt 2 2) terms (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- **Every algebra refuting `noDiamondHairForm` carries the diamond with a hair
below it.** -/
theorem sh_diamondHair_of_refutes_noDiamondHair (α : Type) (iα : HeytingAlgebra α)
    (h : ¬ ∀ v : Nat → α, (noDiamondHairForm (.var 0) (.var 1)).eval v = ⊤) :
    @SH DiamondHair α _ iα := by
  obtain ⟨v, hv⟩ := @exists_ne_top α iα _ h
  exact @sh_of_refutes_pair α iα v hv

/-- **The criterion.**  A schema derives `noDiamondHairForm` exactly when it
misses the top value in the diamond with a hair. -/
theorem derivesFromSchema_noDiamondHair_iff (X : Form) :
    DerivesFromSchema X (noDiamondHairForm (.var 0) (.var 1)) ↔
      ¬ ∀ w : Nat → DiamondHair, X.eval w = ⊤ := by
  constructor
  · intro h hv
    exact nvalid fun _ _ => DerivesFromSchema.valid hv h _
  · exact fun hX => DerivesFromSchema.of_sh fun α iα hnv =>
      ⟨DiamondHair, inferInstance, sh_diamondHair_of_refutes_noDiamondHair α iα hnv, hX⟩
