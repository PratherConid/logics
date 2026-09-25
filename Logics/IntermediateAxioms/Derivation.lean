import Logics.IntermediateAxioms.AxiomDef

/-!
# Derivations between the principles

The derivations the hierarchy of principles rests on, in the calculus of
`Logics/Heyting.lean`: those joining the members of each class, and every edge
between the classes.

**The statements.**  Each principle appears as a schema, taken at the variables
`.var 0`, `.var 1`, which are the `a`, `b` of the descriptions.  That the
principle `X` taken at arguments `s, t` yields the principle `Y` is
`Ent (X s t) (Y (.var 0) (.var 1))`: that instance of `X` entails the schema
`Y`.  Two premises become a curried `Ent A (.imp B C)`.  A lemma used at many
arguments is stated for arbitrary formulas.

**The proofs.**  Each is a natural deduction tree.  Hypotheses are named by
position (`Derives.h₀`, `h₁`, …), the most recent first, and the comments
beside a tree read it as a proof in Lean's own logic, naming the hypotheses: a
case split is `orE`, `Or.inl` is `orI₁`, introducing a hypothesis is `impI`,
applying one is `impE`, `absurd` is `flsE` of an `impE` into `fls`, a `have` is
a `cut` at the formula it states, and using another entailment is `Ent.mp`.

**The derivations.**  An entailment from an instance of `X` is a derivation
from the schema `X` (`DerivesFromSchema.of_ent`, `of_ent₂` for two
instances), given the substitution producing the instance, `Form.args [s, t]`
for `X s t`; a derivation from instances of several schemas together is
`DerivesFromSchemas`.  Each class ends with its members' equivalence to the
class's representative (`SchemaEquiv`).

**The shifts.**  Most entailments take one principle at a *shifted* instance
and conclude another at the plain one.  The shifts are what make the combined
principles interderivable: `¬ a ∨ b` and `a ∨ b` relate the De Morgan and
`impOrForm` versions, `b ∨ (b → a)` relates the De Morgan version to the
swapped Peirce one, and `a → b` and `a ∨ b` place the swapped `impOrForm`
version between two others.  In each case the shift makes the left disjunct's
own premise provable, so that disjunct collapses to a bare disjunction whose
cases can be dispatched separately.  Swapping an argument does not always
change anything: for a principle whose left disjunct is symmetric the swap
merely transposes it, while for the others it moves the principle to a
different strength.

Where several proofs run the same argument, it is proved once, among the steps
after the one argument principles, and the proofs call it.
-/

open Derives

/-! ## The basic principles -/

/-- `impOrForm` at equal arguments is excluded middle. -/
theorem impOr_ent_em (p : Form) : Ent (impOrForm p p) (excludedMiddleForm p) :=
  -- Or.symm (hImpOr id)
  .orE (.impE .h₀ (.impI .h₀)) (.orI₂ .h₀) (.orI₁ .h₀)

/-- Excluded middle at `p` gives `impOrForm p q`. -/
theorem em_ent_impOr (p q : Form) : Ent (excludedMiddleForm p) (impOrForm p q) :=
  .impI (.orE .h₁                  -- intro hab; cases hEx
    (.orI₂ (.impE .h₁ .h₀))       -- | inl ha => Or.inr (hab ha)
    (.orI₁ .h₀))                  -- | inr hna => Or.inl hna

/-- Excluded middle gives double negation elimination. -/
theorem em_ent_notNot (p : Form) : Ent (excludedMiddleForm p) (notNotForm p) :=
  .impI (.orE .h₁ .h₀              -- intro nna; cases hEm; | inl ha => ha
    (.flsE (.impE .h₁ .h₀)))      -- | inr hna => False.elim (nna hna)

/-- Excluded middle gives consequentia mirabilis. -/
theorem em_ent_cm (p : Form) : Ent (excludedMiddleForm p) (consequentiaMirabilisForm p) :=
  .orE .h₀                        -- cases hEm
    (.impI .h₁)                   -- | inl h => fun _ => h
    (.impI (.impE .h₀ .h₁))       -- | inr h => fun f => f h

/-- Consequentia mirabilis at `p ∨ ¬ p` is excluded middle at `p`. -/
theorem cm_ent_em (p : Form) :
    Ent (consequentiaMirabilisForm (excludedMiddleForm p)) (excludedMiddleForm p) :=
  .impE .h₀ (.impI                -- apply hCm; intro hn
    (.orI₂ (.impI (.impE .h₁ (.orI₁ .h₀)))))  -- Or.inr (not_or.mp hn).left

/-- Consequentia mirabilis gives double negation elimination. -/
theorem cm_ent_notNot (p : Form) : Ent (consequentiaMirabilisForm p) (notNotForm p) :=
  .impI (.impE .h₁ (.impI         -- intro hnna; apply hCm; intro hna
    (.flsE (.impE .h₁ .h₀))))     -- contradiction

/-- Double negation elimination gives consequentia mirabilis. -/
theorem notNot_ent_cm (p : Form) : Ent (notNotForm p) (consequentiaMirabilisForm p) :=
  .impI (.impE .h₁ (.impI         -- intro hi; apply hnn; intro hna
    (.impE .h₀ (.impE .h₁ .h₀)))) -- hna (hi hna)

/-- Consequentia mirabilis at `p` gives Peirce's law at `p` and any `q`. -/
theorem cm_ent_peirce (p q : Form) : Ent (consequentiaMirabilisForm p) (peirceForm p q) :=
  .impI (.impE .h₁ (.impI         -- intro hab; apply hCm; intro hna
    (.impE .h₁ (.impI             -- apply hab; intro ha
      (.flsE (.impE .h₁ .h₀))))))  -- contradiction

/-- Peirce's law at `p` against its own negation is consequentia mirabilis. -/
theorem peirce_ent_cm (p : Form) :
    Ent (peirceForm p (Form.neg p)) (consequentiaMirabilisForm p) :=
  .impI (.impE .h₁ (.impI         -- intro h; apply hPc; intro hana
    (.impE .h₁ (.impI             -- apply h; intro ha
      (.impE (.impE .h₁ .h₀) .h₀)))))  -- hana ha ha

/-! ## Steps shared between proofs

Each of these is a stretch of argument that two or more of the proofs below
would otherwise spell out separately. -/

/-- Excluded middle gives Peirce's law, through consequentia mirabilis.  In
every proof from excluded middle to a principle with Peirce as a disjunct. -/
theorem em_ent_peirce (p q : Form) : Ent (excludedMiddleForm p) (peirceForm p q) :=
  (em_ent_cm p).trans (cm_ent_peirce p q)

/-- An arrow out of `a ∨ ¬ a` is an arrow out of `a`: `fun ha => k (Or.inl ha)`.
In `bd2_ent_em₁OrLuk₂₁`, and in both halves of `notNotAnd_ent_noDiamond` and of
`linearity_ent_noDiamond`. -/
theorem imp_em_ent (p q : Form) : Ent (.imp (excludedMiddleForm p) q) (.imp p q) :=
  .impI (.impE .h₁ (.orI₁ .h₀))

/-- `¬ ¬ (a ∨ ¬ a)`, derivable anywhere:
`fun hn => hn (Or.inr (fun ha => hn (Or.inl ha)))`. -/
theorem nn_em (p : Form) {Γ : List Form} :
    Γ ⊢ Form.neg (Form.neg (excludedMiddleForm p)) :=
  .impI (.impE .h₀ (.orI₂ (.impI (.impE .h₁ (.orI₁ .h₀)))))

/-- **An arrow into an excluded middle gives the converse of contraposition**:
from `a → b ∨ ¬ b`, `¬ b → ¬ a` yields `a → b`.  Both halves of
`noDiamond_ent_luk₁₂OrLuk₂₁`, and `bd2_ent_em₁OrLuk₂₁`. -/
theorem himp_em_ent_luk (p q : Form) : Ent (.imp p (excludedMiddleForm q)) (lukForm q p) :=
  .impI (.impI (.orE (.impE .h₂ .h₀)   -- fun hn ha => cases k ha
    .h₀                                 -- | inl hb => hb
    (.flsE (.impE (.impE .h₂ .h₀) .h₁))))  -- | inr hnb => absurd ha (hn hnb)

/-- Łukasiewicz at `a` and `a ∨ b` gives it at `a` and `b`.  In
`impOr₁₂OrLuk₂₁_ent_pierce₁₂OrLuk₁₂` and
`impOr₁₂OrLuk₁₂_ent_demorgan₁₂OrLuk₁₂`. -/
theorem luk_sup_ent (p q : Form) : Ent (lukForm p (.or p q)) (lukForm p q) :=
  .impI (.impI                          -- intro hnn hb
    (.cut (p := .imp (Form.neg p) (Form.neg (.or p q)))  -- have hpre : ¬ a → ¬ (a ∨ b)
      (.impI (.impI (.orE .h₀           --   intro hna hab; cases hab
        (.impE .h₂ .h₀)                 --   | inl ha => hna ha
        (.impE (.impE .h₄ .h₂) .h₀))))  --   | inr hb' => hnn hna hb'
      (.impE (.impE .h₃ .h₀) (.orI₂ .h₁))))  -- hLuk hpre (Or.inr hb)

/-- From `¬ a → ¬ b` and `b`, `¬ a` gives anything, `a` being doubly negated.
In `demorgan₁₂OrLuk₁₂_ent_impOr₁₂OrLuk₁₂` and
`pierce₁₂OrLuk₂₁_ent_demorgan₁₂OrLuk₁₂`. -/
theorem neg_imp_neg_ent (p q r : Form) :
    Ent (.and (.imp (Form.neg p) (Form.neg q)) q) (.imp (Form.neg p) r) :=
  .cut (p := Form.neg (Form.neg p))     -- have hnna : ¬ ¬ a
    (.impI (.impE (.impE (.andE₁ .h₁) .h₀) (.andE₂ .h₁)))  --   fun hna => hnn hna hb
    (.impI (.flsE (.impE .h₁ .h₀)))    -- fun hna => absurd hna hnna

/-- Łukasiewicz at `b → a` and `b` gives it at `a` and `b`.  In
`emAOrB₁₂OrLuk₁₂_ent_demorgan₁₂OrLuk₁₂` and `demorgan₁₂OrLuk₁₂_himp_ent`. -/
theorem luk_himp_ent (p q : Form) : Ent (lukForm (.imp q p) q) (lukForm p q) :=
  .impI (.impI                          -- intro h hb
    (.impE (.impE (.impE .h₂            -- hLuk (fun hn hb' => …) hb hb
      (.impI (.impI (.impE (.impE .h₃   --   h (fun ha => hn (fun _ => ha)) hb'
        (.impI (.impE .h₂ (.impI .h₁)))) .h₀)))) .h₀) .h₀))

/-- `demorgan₁₂OrLuk₁₂Form` at `a → b` and `a` gives `a`, or Łukasiewicz at `b`
and `a`.  Four proofs run this and then place the two cases in their targets:
`demorgan₁₂OrLuk₁₂_ent_em₁OrLuk₂₁`, `demorgan₁₂OrLuk₁₂_ent_emAOrB₁₂OrLuk₂₁`,
`demorgan₁₂OrLuk₁₂_ent_emAOrNotB₁₂OrLuk₂₁`, and with the arguments swapped
`demorgan₁₂OrLuk₁₂_ent_emAOrB₁₂OrLuk₁₂`. -/
theorem demorgan₁₂OrLuk₁₂_himp_ent (p q : Form) :
    Ent (.or (demorganForm (.imp p q) p) (lukForm (.imp p q) p)) (.or p (lukForm q p)) :=
  .orE .h₀                              -- cases h
    (.orE (.impE .h₀                    -- | inl hDeM => cases hDeM (fun hc => …)
        (.impI (.impE (.andE₁ .h₀)      --   hc.left (fun ha => absurd ha hc.right)
          (.impI (.flsE (.impE (.andE₂ .h₁) .h₀))))))
      (.orI₂ (.impI .h₁))               --   | inl hab => Or.inr (fun _ => hab)
      (.orI₁ .h₀))                      --   | inr ha => a
    (.orI₂ ((luk_himp_ent q p).mp .h₀)) -- | inr hLuk

/-- Łukasiewicz between two excluded middles gives the arrow between them:
`fun hb => k (fun hx => absurd hx hna) (Or.inl hb)`.  Both halves of
`luk₁₂OrLuk₂₁_ent_noDiamond`. -/
theorem luk_em_ent (p q : Form) :
    Ent (lukForm (excludedMiddleForm p) (excludedMiddleForm q)) (.imp q (excludedMiddleForm p)) :=
  .impI (.impE (.impE .h₁ (.impI (.flsE (.impE (nn_em p) .h₀)))) (.orI₁ .h₀))

/-- `impOrForm` at `a` and `a ∧ b` gives Łukasiewicz at `a` and `b`.  In
`peirce₁₂OrImpOr₁₂_ent_pierce₁₂OrLuk₁₂` and
`impOr₁₂OrLuk₂₁_ent_luk₁₂OrLuk₂₁`. -/
theorem impOr_and_ent_luk (p q : Form) : Ent (impOrForm p (.and p q)) (lukForm p q) :=
  .impI (.impI                          -- intro hn hb
    (.orE (.impE .h₂ (.impI (.andI .h₀ .h₁)))  -- cases hIO (fun ha => ⟨ha, hb⟩)
      (.flsE (.impE (.impE .h₂ .h₀) .h₁))  -- | inl hna => absurd hb (hn hna)
      (.andE₁ .h₀)))                    -- | inr hab => hab.1

/-- Under Peirce's antecedent `(a → b) → a`, the antecedent at `a ∨ c` and
`a → b` holds: `fun hAB => Or.inl (hi (fun ha => hAB (Or.inl ha) ha))`.  In
`pierce₁₂OrLuk₁₂_ent_pierce₁₂OrPierce₂₁` and
`pierce₁₂OrLuk₁₂_ent_peirce₁₂OrImpOr₁₂`. -/
theorem peirce_ante_ent (p q r : Form) :
    Ent (.imp (.imp p q) p) (.imp (.imp (.or p r) (.imp p q)) (.or p r)) :=
  .impI (.orI₁ (.impE .h₁ (.impI (.impE (.impE .h₁ (.orI₁ .h₀)) .h₀))))

/-- Łukasiewicz at `a ∨ ¬ a` and `a → b` gives `impOrForm` at `a` and `b`, its
hypothesis being free.  In `luk₁₂OrLuk₂₁_ent_impOr₁₂OrLuk₂₁` and
`pierce₁₂OrLuk₁₂_ent_peirce₁₂OrImpOr₁₂`. -/
theorem luk_em_ent_impOr (p q : Form) :
    Ent (lukForm (excludedMiddleForm p) (.imp p q)) (impOrForm p q) :=
  .impI (.orE                           -- intro hab; cases hL (fun hn => absurd hn hnn) hab
    (.impE (.impE .h₁ (.impI (.flsE (.impE (nn_em p) .h₀)))) .h₀)
    (.orI₂ (.impE .h₁ .h₀))             -- | inl ha => Or.inr (hab ha)
    (.orI₁ .h₀))                        -- | inr hna => Or.inl hna

/-- An excluded middle whose second case is refuted is its first case.  In
`pierce₁₂OrDeMorgan₁₂_ent_em` and `demorgan₁₂OrImpOr₁₂_ent_em`. -/
theorem em_and_nn_ent (p : Form) :
    Ent (.and (excludedMiddleForm p) (Form.neg (Form.neg p))) p :=
  .orE (.andE₁ .h₀) .h₀                 -- | inl hX => hX
    (.flsE (.impE (.andE₂ .h₁) .h₀))    -- | inr hnX => absurd hnX hnn

/-! ## Excluded middle's class

The two three way splits are excluded middle on their own, each collapsing
under a substitution that makes one of its three disjuncts refutable.  The
other members join two basic principles without Łukasiewicz, and at suitable
arguments each disjunct collapses to excluded middle by itself. -/

/-- `emAOrNotBForm` is excluded middle: at `b := a` its third disjunct
`¬ (a → a)` is refutable, leaving the first two. -/
theorem emAOrNotB_ent_em : Ent (emAOrNotBForm (.var 0) (.var 0)) (excludedMiddleForm (.var 0)) :=
  .orE .h₀ (.orI₁ .h₀)                  -- cases h; | inl ha => Or.inl ha
    (.orE .h₀ (.orI₂ .h₀)               -- | inr h2 => cases h2; | inl hna => Or.inr hna
      (.flsE (.impE .h₀ (.impI .h₀))))  --   | inr hn => absurd (id : a → a) hn

/-- The converse needs excluded middle at *both* arguments, one for each of the
two ways the split can fail to reach `a`. -/
theorem em_ent_emAOrNotB :
    Ent (excludedMiddleForm (.var 0))
      (.imp (excludedMiddleForm (.var 1)) (emAOrNotBForm (.var 0) (.var 1))) :=
  .impI (.orE .h₁ (.orI₁ .h₀)           -- intro hB; cases hA; | inl ha => Or.inl ha
    (.orE .h₁                           -- | inr hna => cases hB
      (.orI₂ (.orI₂ (.impI (.impE .h₂ (.impE .h₀ .h₁)))))  -- | inl hb => … (fun h => hna (h hb))
      (.orI₂ (.orI₁ .h₀))))             --   | inr hnb => Or.inr (Or.inl hnb)

/-- `emAOrBForm` is excluded middle too, collapsing at `b := fls`: there `¬ b`
is provable, so `¬ b → a` is `a` and the third disjunct is `¬ a`. -/
theorem emAOrB_ent_em : Ent (emAOrBForm (.var 0) .fls) (excludedMiddleForm (.var 0)) :=
  .orE .h₀ (.orI₁ .h₀)                  -- cases h; | inl ha => Or.inl ha
    (.orE .h₀ (.flsE .h₀)               -- | inr h2 => cases h2; | inl hf => hf.elim
      (.orI₂ (.impI (.impE .h₁ (.impI .h₁)))))  -- | inr hn => Or.inr (fun ha => hn (fun _ => ha))

/-- The converse, again from excluded middle at both arguments. -/
theorem em_ent_emAOrB :
    Ent (excludedMiddleForm (.var 0))
      (.imp (excludedMiddleForm (.var 1)) (emAOrBForm (.var 0) (.var 1))) :=
  .impI (.orE .h₁ (.orI₁ .h₀)           -- intro hB; cases hA; | inl ha => Or.inl ha
    (.orE .h₁ (.orI₂ (.orI₁ .h₀))       -- | inr hna => cases hB; | inl hb => Or.inr (Or.inl hb)
      (.orI₂ (.orI₂ (.impI (.impE .h₂ (.impE .h₀ .h₁)))))))  -- | inr hnb => … (fun h => hna (h hnb))

/-- Joining Peirce with De Morgan rather than with Łukasiewicz gives excluded
middle back, so `pierce₁₂OrDeMorgan₁₂Form` is not an intermediate principle at
all.  At `a ∨ ¬ a` against its own negation both disjuncts collapse: Peirce
becomes consequentia mirabilis there, which is excluded middle, and De Morgan's
premise becomes provable, leaving `(a ∨ ¬ a) ∨ ¬ (a ∨ ¬ a)`, whose second case
`nn_em` refutes. -/
theorem pierce₁₂OrDeMorgan₁₂_ent_em :
    Ent
      (pierce₁₂OrDeMorgan₁₂Form (excludedMiddleForm (.var 0))
        (Form.neg (excludedMiddleForm (.var 0))))
      (excludedMiddleForm (.var 0)) :=
  .orE .h₀                              -- cases h
    ((cm_ent_em _).mp ((peirce_ent_cm _).mp .h₀))  -- | inl hPc => cm_ent_em (peirce_ent_cm hPc)
    ((em_and_nn_ent _).mp (.andI        -- | inr hDeM => cases hDeM (fun hc => hc.right hc.left)
      (.impE .h₀ (.impI (.impE (.andE₂ .h₀) (.andE₁ .h₀)))) (nn_em _)))

/-- Excluded middle gives it back, through the Peirce disjunct. -/
theorem em_ent_pierce₁₂OrDeMorgan₁₂ :
    Ent (excludedMiddleForm (.var 0)) (pierce₁₂OrDeMorgan₁₂Form (.var 0) (.var 1)) :=
  .orI₁ ((em_ent_peirce _ _).mp .h₀)

/-- Joining De Morgan with `impOrForm` is classical too, and needs no shift
beyond taking both arguments to be `a ∨ ¬ a`.  There De Morgan's premise is
provable, by `nn_em`, and its conclusion is the disjunction itself, while
`impOrForm` at equal arguments is excluded middle by `impOr_ent_em`. -/
theorem demorgan₁₂OrImpOr₁₂_ent_em :
    Ent (demorgan₁₂OrImpOr₁₂Form (excludedMiddleForm (.var 0)) (excludedMiddleForm (.var 0)))
      (excludedMiddleForm (.var 0)) :=
  .orE .h₀                              -- cases h
    (.orE (.impE .h₀ (.impI (.impE (nn_em _) (.andE₁ .h₀)))) .h₀ .h₀)
                                        -- | inl hDeM => (hDeM (fun hc => hnn hc.left)).elim id id
    ((em_and_nn_ent _).mp (.andI ((impOr_ent_em _).mp .h₀) (nn_em _)))
                                        -- | inr hIO => cases impOr_ent_em hIO

/-- Excluded middle gives it back, through the `impOrForm` disjunct. -/
theorem em_ent_demorgan₁₂OrImpOr₁₂ :
    Ent (excludedMiddleForm (.var 0)) (demorgan₁₂OrImpOr₁₂Form (.var 0) (.var 1)) :=
  .orI₂ ((em_ent_impOr _ _).mp .h₀)

/-- Doubling `impOrForm` is classical, and at equal arguments needs no work at
all: either disjunct is `impOrForm a a`, already excluded middle. -/
theorem impOr₁₂OrImpOr₂₁_ent_em :
    Ent (impOr₁₂OrImpOr₂₁Form (.var 0) (.var 0)) (excludedMiddleForm (.var 0)) :=
  .orE .h₀ ((impOr_ent_em _).mp .h₀) ((impOr_ent_em _).mp .h₀)

/-- Excluded middle gives it back, through the left disjunct. -/
theorem em_ent_impOr₁₂OrImpOr₂₁ :
    Ent (excludedMiddleForm (.var 0)) (impOr₁₂OrImpOr₂₁Form (.var 0) (.var 1)) :=
  .orI₁ ((em_ent_impOr _ _).mp .h₀)

theorem emAOrNotB_equiv_em :
    SchemaEquiv (emAOrNotBForm (.var 0) (.var 1)) (excludedMiddleForm (.var 0)) :=
  ⟨.of_ent emAOrNotB_ent_em ⟨Form.args [.var 0, .var 0], rfl⟩,
   .of_ent₂ em_ent_emAOrNotB ⟨.var, (Form.subst_var _).symm⟩ ⟨Form.args [.var 1], rfl⟩⟩

theorem emAOrB_equiv_em :
    SchemaEquiv (emAOrBForm (.var 0) (.var 1)) (excludedMiddleForm (.var 0)) :=
  ⟨.of_ent emAOrB_ent_em ⟨Form.args [.var 0, .fls], rfl⟩,
   .of_ent₂ em_ent_emAOrB ⟨.var, (Form.subst_var _).symm⟩ ⟨Form.args [.var 1], rfl⟩⟩

theorem pierce₁₂OrDeMorgan₁₂_equiv_em :
    SchemaEquiv (pierce₁₂OrDeMorgan₁₂Form (.var 0) (.var 1)) (excludedMiddleForm (.var 0)) :=
  ⟨.of_ent pierce₁₂OrDeMorgan₁₂_ent_em
      ⟨Form.args [excludedMiddleForm (.var 0), Form.neg (excludedMiddleForm (.var 0))], rfl⟩,
   .of_ent_self em_ent_pierce₁₂OrDeMorgan₁₂⟩

theorem demorgan₁₂OrImpOr₁₂_equiv_em :
    SchemaEquiv (demorgan₁₂OrImpOr₁₂Form (.var 0) (.var 1)) (excludedMiddleForm (.var 0)) :=
  ⟨.of_ent demorgan₁₂OrImpOr₁₂_ent_em
      ⟨Form.args [excludedMiddleForm (.var 0), excludedMiddleForm (.var 0)], rfl⟩,
   .of_ent_self em_ent_demorgan₁₂OrImpOr₁₂⟩

theorem impOr₁₂OrImpOr₂₁_equiv_em :
    SchemaEquiv (impOr₁₂OrImpOr₂₁Form (.var 0) (.var 1)) (excludedMiddleForm (.var 0)) :=
  ⟨.of_ent impOr₁₂OrImpOr₂₁_ent_em
      ⟨Form.args [.var 0, .var 0], rfl⟩,
   .of_ent_self em_ent_impOr₁₂OrImpOr₂₁⟩

/-! ## Smetanich's class

Smetanich's is the named axiom for this level; `peirce₁₂OrImpOr₂₁Form` is the
form the disjunctions of this development put there, and the other members are
joined to it.  The two directions between the pair are not alike.
`peirce₁₂OrImpOr₂₁Form` gives Smetanich's axiom at the same arguments, with no
shift at all.  Going back needs *two* instances: the target has to be fed in as
an argument first, to obtain `¬ b → a`, which is exactly what the instance at
`a, b` consumes.

Two members pair a three way split with Peirce.  The splits are excluded middle
on their own, but paired with a two argument principle they need not be: the
pairing is only classical when one side implies the other. -/

/-- `peirce₁₂OrImpOr₂₁Form` gives Smetanich's axiom at the same arguments. -/
theorem peirce₁₂OrImpOr₂₁_ent_smetanich :
    Ent (peirce₁₂OrImpOr₂₁Form (.var 0) (.var 1)) (smetanichForm (.var 0) (.var 1)) :=
  .impI (.impI (.orE .h₂                -- intro hnb k; cases h
    (.impE .h₀ .h₁)                     -- | inl hp => hp k
    (.orE (.impE .h₀ (.impI (.impE .h₂ (.impI .h₁))))  -- | inr himp => cases himp (fun hb => k (fun _ => hb))
      (.impE .h₃ .h₀)                   --   | inl hnb' => hnb hnb'
      .h₀)))                            --   | inr ha => ha

/-- Back, from two instances: Smetanich's axiom at `peirce₁₂OrImpOr₂₁Form` and
`a`, then at `a` and `b`. -/
theorem smetanich_ent_peirce₁₂OrImpOr₂₁ :
    Ent (smetanichForm (peirce₁₂OrImpOr₂₁Form (.var 0) (.var 1)) (.var 0))
      (.imp (smetanichForm (.var 0) (.var 1)) (peirce₁₂OrImpOr₂₁Form (.var 0) (.var 1))) :=
  .impI (.cut (p := .imp (Form.neg (.var 1)) (peirce₁₂OrImpOr₂₁Form (.var 0) (.var 1)))
    (.impI (.orI₂ (.impI (.orI₁ .h₁))))  -- have hnb := fun nb => Or.inr (fun _ => Or.inl nb)
    (.impE (.impE .h₂                   -- refine h₁ (fun na => …) ?_
      (.impI (.orI₂ (.impI (.orI₁ (.impI (.impE .h₂ (.impE .h₁ .h₀))))))))
                                        --   Or.inr (fun hba => Or.inl (fun hb => na (hba hb)))
      (.impI (.orI₁ (.impE .h₂          -- intro k; Or.inl (h₂ (fun nb => k (hnb nb)))
        (.impI (.impE .h₁ (.impE .h₂ .h₀))))))))

/-- `em₁OrPeirce₂₁Form` at `b, a` gives `peirce₁₂OrImpOr₂₁Form`: excluded middle
at `b` gives `impOrForm` at `b, a`. -/
theorem em₁OrPeirce₂₁_ent_peirce₁₂OrImpOr₂₁ :
    Ent (em₁OrPeirce₂₁Form (.var 1) (.var 0)) (peirce₁₂OrImpOr₂₁Form (.var 0) (.var 1)) :=
  .orE .h₀ (.orI₂ ((em_ent_impOr _ _).mp .h₀)) (.orI₁ .h₀)

/-- Back, at `a ∨ b` and `a`. -/
theorem peirce₁₂OrImpOr₂₁_ent_em₁OrPeirce₂₁ :
    Ent (peirce₁₂OrImpOr₂₁Form (.or (.var 0) (.var 1)) (.var 0))
      (em₁OrPeirce₂₁Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orI₂ (.impI (.orE                 -- | inl hPc => Or.inr; intro hi
      (.impE .h₁ (.impI (.orI₂ (.impE .h₁ (.impI (.impE .h₁ (.orI₂ .h₀)))))))
                                        --   cases hPc (fun hx => Or.inr (hi (fun hb => hx (Or.inr hb))))
      (.impE .h₁ (.impI .h₁))           --   | inl ha => hi (fun _ => ha)
      .h₀)))                            --   | inr hb => hb
    (.orE (.impE .h₀ (.impI (.orI₁ .h₀)))  -- | inr hIO => cases hIO Or.inl
      (.orI₁ (.orI₂ .h₀))               --   | inl hna => Or.inl (Or.inr hna)
      (.orE .h₀ (.orI₁ (.orI₁ .h₀))     --   | inr hab => cases hab; | inl ha => …
        (.orI₂ (.impI .h₁))))           --     | inr hb => Or.inr (fun _ => hb)

/-- `emAOrNotB₁₂OrPeirce₁₂Form` reaches `peirce₁₂OrImpOr₂₁Form` at the plain
arguments: the three way split is exactly what `impOrForm` at `b, a` needs once
`b → a` is assumed. -/
theorem emAOrNotB₁₂OrPeirce₁₂_ent_peirce₁₂OrImpOr₂₁ :
    Ent (emAOrNotB₁₂OrPeirce₁₂Form (.var 0) (.var 1)) (peirce₁₂OrImpOr₂₁Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orI₂ (.impI (.orE .h₁             -- | inl hE => Or.inr; intro hba; cases hE
      (.orI₂ .h₀)                       --   | inl ha => Or.inr ha
      (.orE .h₀ (.orI₁ .h₀)             --   | inr h2 => cases h2; | inl hnb => Or.inl hnb
        (.flsE (.impE .h₀ .h₂))))))     --     | inr hn => absurd hba hn
    (.orI₁ .h₀)                         -- | inr hPc => Or.inl hPc

/-- Back, at `a ∨ b` and `b`. -/
theorem peirce₁₂OrImpOr₂₁_ent_emAOrNotB₁₂OrPeirce₁₂ :
    Ent (peirce₁₂OrImpOr₂₁Form (.or (.var 0) (.var 1)) (.var 1))
      (emAOrNotB₁₂OrPeirce₁₂Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orI₂ (.impI (.orE                 -- | inl hPc => Or.inr; intro hi
      (.impE .h₁ (.impI (.orI₁ (.impE .h₁ (.impI (.impE .h₁ (.orI₁ .h₀)))))))
                                        --   cases hPc (fun hx => Or.inl (hi (fun ha => hx (Or.inl ha))))
      .h₀                               --   | inl ha => ha
      (.impE .h₁ (.impI .h₁)))))        --   | inr hb => hi (fun _ => hb)
    (.orE (.impE .h₀ (.impI (.orI₂ .h₀)))  -- | inr hIO => cases hIO Or.inr
      (.orI₁ (.orI₂ (.orI₁ .h₀)))       --   | inl hnb => Or.inl (Or.inr (Or.inl hnb))
      (.orE .h₀ (.orI₁ (.orI₁ .h₀))     --   | inr hab => cases hab; | inl ha => …
        (.orI₂ (.impI (.impE .h₀ (.impI .h₂))))))  --  | inr hb => Or.inr (fun hi => hi (fun _ => hb))

/-- Taking the split at `b, a` instead reaches the same level, now with the
split feeding `impOrForm` at `b, a` directly in all three cases. -/
theorem emAOrNotB₁₂OrPeirce₂₁_ent_peirce₁₂OrImpOr₂₁ :
    Ent (emAOrNotB₁₂OrPeirce₂₁Form (.var 1) (.var 0)) (peirce₁₂OrImpOr₂₁Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orI₂ (.impI (.orE .h₁             -- | inl hE => Or.inr; intro hba; cases hE
      (.orI₂ (.impE .h₁ .h₀))           --   | inl hb => Or.inr (hba hb)
      (.orE .h₀                         --   | inr h2 => cases h2
        (.orI₁ (.impI (.impE .h₁ (.impE .h₃ .h₀))))  -- | inl hna => Or.inl (fun hb => hna (hba hb))
        (.orI₁ (.impI (.impE .h₁ (.impI .h₁))))))))  -- | inr hn => Or.inl (fun hb => hn (fun _ => hb))
    (.orI₁ .h₀)                         -- | inr hPc => Or.inl hPc

/-- Back, at the split `a ∨ b ∨ (b → a)` and `b → a`.  That every case of the
split gives the target is one `cut`, used by both disjuncts. -/
theorem peirce₁₂OrImpOr₂₁_ent_emAOrNotB₁₂OrPeirce₂₁ :
    Ent
      (peirce₁₂OrImpOr₂₁Form (.or (.var 0) (.or (.var 1) (.imp (.var 1) (.var 0))))
        (.imp (.var 1) (.var 0)))
      (emAOrNotB₁₂OrPeirce₂₁Form (.var 0) (.var 1)) :=
  .cut (p := .imp (.or (.var 0) (.or (.var 1) (.imp (.var 1) (.var 0))))
      (emAOrNotB₁₂OrPeirce₂₁Form (.var 0) (.var 1)))       -- have fromA
    (.impI (.orE .h₀                    --   intro hA; cases hA
      (.orI₁ (.orI₁ .h₀))               --   | inl ha => Or.inl (Or.inl ha)
      (.orE .h₀ (.orI₂ (.impI .h₁))     --   | inr h2 => cases h2; | inl hb => Or.inr (fun _ => hb)
        (.orI₂ (.impI (.impE .h₀ .h₁)))))) --   | inr hba => Or.inr (fun hi => hi hba)
    (.orE .h₁                           -- cases h
      (.impE .h₁ (.impE .h₀ (.impI (.orI₂ (.orI₂ (.impI
        (.impE (.impE .h₁ (.orI₂ (.orI₁ .h₀))) .h₀)))))))
                                        -- | inl hPc => fromA (hPc (fun hAB => …))
      (.orE (.impE .h₀ (.impI (.orI₂ (.orI₂ .h₀))))  -- | inr hIO => cases hIO (fun hba => …)
        (.orI₁ (.orI₂ (.orI₂ .h₀)))     --   | inl hn => Or.inl (Or.inr (Or.inr hn))
        (.impE .h₂ .h₀)))               --   | inr hA => fromA hA

theorem peirce₁₂OrImpOr₂₁_equiv_smetanich :
    SchemaEquiv (peirce₁₂OrImpOr₂₁Form (.var 0) (.var 1)) (smetanichForm (.var 0) (.var 1)) :=
  ⟨.of_ent_self peirce₁₂OrImpOr₂₁_ent_smetanich,
   .of_ent₂ smetanich_ent_peirce₁₂OrImpOr₂₁
     ⟨Form.args [peirce₁₂OrImpOr₂₁Form (.var 0) (.var 1), .var 0], rfl⟩
     ⟨.var, (Form.subst_var _).symm⟩⟩

theorem em₁OrPeirce₂₁_equiv_smetanich :
    SchemaEquiv (em₁OrPeirce₂₁Form (.var 0) (.var 1)) (smetanichForm (.var 0) (.var 1)) :=
  SchemaEquiv.trans
    ⟨.of_ent em₁OrPeirce₂₁_ent_peirce₁₂OrImpOr₂₁ ⟨Form.args [.var 1, .var 0], rfl⟩,
     .of_ent peirce₁₂OrImpOr₂₁_ent_em₁OrPeirce₂₁ ⟨Form.args [.or (.var 0) (.var 1), .var 0], rfl⟩⟩
    peirce₁₂OrImpOr₂₁_equiv_smetanich

theorem emAOrNotB₁₂OrPeirce₁₂_equiv_smetanich :
    SchemaEquiv (emAOrNotB₁₂OrPeirce₁₂Form (.var 0) (.var 1)) (smetanichForm (.var 0) (.var 1)) :=
  SchemaEquiv.trans
    ⟨.of_ent_self emAOrNotB₁₂OrPeirce₁₂_ent_peirce₁₂OrImpOr₂₁,
     .of_ent peirce₁₂OrImpOr₂₁_ent_emAOrNotB₁₂OrPeirce₁₂
         ⟨Form.args [.or (.var 0) (.var 1), .var 1], rfl⟩⟩
    peirce₁₂OrImpOr₂₁_equiv_smetanich

theorem emAOrNotB₁₂OrPeirce₂₁_equiv_smetanich :
    SchemaEquiv (emAOrNotB₁₂OrPeirce₂₁Form (.var 0) (.var 1)) (smetanichForm (.var 0) (.var 1)) :=
  SchemaEquiv.trans
    ⟨.of_ent emAOrNotB₁₂OrPeirce₂₁_ent_peirce₁₂OrImpOr₂₁ ⟨Form.args [.var 1, .var 0], rfl⟩,
     .of_ent peirce₁₂OrImpOr₂₁_ent_emAOrNotB₁₂OrPeirce₂₁
         ⟨Form.args [.or (.var 0) (.or (.var 1) (.imp (.var 1) (.var 0))), .imp (.var 1) (.var 0)],
           rfl⟩⟩
    peirce₁₂OrImpOr₂₁_equiv_smetanich

/-- Excluded middle gives `peirce₁₂OrImpOr₂₁Form`, through the Peirce
disjunct. -/
theorem em_ent_peirce₁₂OrImpOr₂₁ :
    Ent (excludedMiddleForm (.var 0)) (peirce₁₂OrImpOr₂₁Form (.var 0) (.var 1)) :=
  .orI₁ ((em_ent_peirce _ _).mp .h₀)

/-- **Excluded middle derives Smetanich's axiom**, through
`peirce₁₂OrImpOr₂₁Form`. -/
theorem derives_smetanich_of_em :
    DerivesFromSchema (excludedMiddleForm (.var 0)) (smetanichForm (.var 0) (.var 1)) :=
  (DerivesFromSchema.of_ent_self em_ent_peirce₁₂OrImpOr₂₁).trans
    peirce₁₂OrImpOr₂₁_equiv_smetanich.1

/-! ## Bounded depth two's class

Every member is reached through `demorgan₁₂OrLuk₁₂Form`, which `em₁OrLuk₂₁Form`
joins to `bd2Form`.  Between those two, each direction needs one shifted
instance, and both shifts are the same idea: excluded middle at one argument is
what the two principles trade in.  `bd2Form` is asked about `a ∨ ¬ a`; coming
back, the Łukasiewicz principle is asked about `b ∨ ¬ b`, whose negation is
refuted and so discharges the hypothesis for free.

Five of the six principles joining a one argument principle to a two argument
one are here.  `em₁OrLuk₂₁Form`, `notNot₁OrLuk₂₁Form` and `cm₁OrLuk₂₁Form` are
reached from `demorgan₁₂OrLuk₁₂Form` and return to it through
`pierce₁₂OrLuk₂₁Form`; `cm₁OrPeirce₂₁Form` and `notNot₁OrPeirce₂₁Form` form a
second cycle to the same level.  The three pairings of a three way split with
Łukasiewicz are here too. -/

/-- `bd2Form` at `a ∨ ¬ a` and `b` gives `em₁OrLuk₂₁Form`. -/
theorem bd2_ent_em₁OrLuk₂₁ :
    Ent (bd2Form (excludedMiddleForm (.var 0)) (.var 1)) (em₁OrLuk₂₁Form (.var 0) (.var 1)) :=
  .orE .h₀ (.orI₁ .h₀)                  -- cases h; | inl hem => Or.inl hem
    (.orI₂ ((himp_em_ent_luk _ _).mp ((imp_em_ent _ _).mp .h₀)))
                                        -- | inr k => Or.inr (fun hn ha => … k (Or.inl ha) …)

/-- Back, at `a` and `b ∨ ¬ b`, where the premise `¬ ¬ (b ∨ ¬ b)` is
`nn_em`. -/
theorem em₁OrLuk₂₁_ent_bd2 :
    Ent (em₁OrLuk₂₁Form (.var 0) (excludedMiddleForm (.var 1))) (bd2Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orE .h₀ (.orI₁ .h₀)               -- | inl hem => cases hem; | inl ha => Or.inl ha
      (.orI₂ (.impI (.flsE (.impE .h₁ .h₀)))))  -- | inr na => Or.inr (fun ha => absurd ha na)
    (.orI₂ (.impE .h₀ (.impI (.flsE (.impE (nn_em _) .h₀)))))  -- | inr k => Or.inr (k (fun hn => …))

/-- `demorgan₁₂OrLuk₁₂Form` at `a` and `¬ a ∨ b` gives `impOr₁₂OrLuk₁₂Form`. -/
theorem demorgan₁₂OrLuk₁₂_ent_impOr₁₂OrLuk₁₂ :
    Ent (demorgan₁₂OrLuk₁₂Form (.var 0) (.or (Form.neg (.var 0)) (.var 1)))
      (impOr₁₂OrLuk₁₂Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.cut (p := Form.neg (.and (Form.neg (.var 0)) (Form.neg (.or (Form.neg (.var 0)) (.var 1)))))
      (.impI (.impE (.andE₂ .h₀) (.orI₁ (.andE₁ .h₀))))  -- | inl hDeM => have hpre
      (.orI₁ (.impI (.orE (.impE .h₂ .h₁)  -- Or.inl; intro hab; cases hDeM hpre
        (.orI₂ (.impE .h₁ .h₀))         --   | inl ha => Or.inr (hab ha)
        .h₀))))                         --   | inr hnab => hnab
    (.orI₂ (.impI (.impI (.impE (.impE .h₂  -- | inr hLuk => Or.inr; intro hnn hb
      ((neg_imp_neg_ent _ _ _).mp (.andI .h₁ .h₀))) (.orI₂ .h₀)))))
                                        --   hLuk (fun hna => absurd hna hnna) (Or.inr hb)

/-- Back, at `a` and `a ∨ b`. -/
theorem impOr₁₂OrLuk₁₂_ent_demorgan₁₂OrLuk₁₂ :
    Ent (impOr₁₂OrLuk₁₂Form (.var 0) (.or (.var 0) (.var 1)))
      (demorgan₁₂OrLuk₁₂Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orE (.impE .h₀ (.impI (.orI₁ .h₀)))  -- | inl hIO => cases hIO Or.inl
      (.orI₂ (.impI (.impI (.flsE (.impE (.impE .h₁ .h₂) .h₀)))))
                                        --   | inl hna => Or.inr (fun hnn hb => absurd hb (hnn hna))
      (.orI₁ (.impI .h₁)))              --   | inr hab => Or.inl (fun _ => hab)
    (.orI₂ ((luk_sup_ent _ _).mp .h₀))  -- | inr hLuk

/-- `demorgan₁₂OrLuk₁₂Form` at `b, a` gives `pierce₁₂OrLuk₂₁Form`: under
Peirce's premise the De Morgan premise holds. -/
theorem demorgan₁₂OrLuk₁₂_ent_pierce₁₂OrLuk₂₁ :
    Ent (demorgan₁₂OrLuk₁₂Form (.var 1) (.var 0)) (pierce₁₂OrLuk₂₁Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orI₁ (.impI                       -- | inl hDeM => Or.inl; intro hi
      (.cut (p := Form.neg (.and (Form.neg (.var 1)) (Form.neg (.var 0))))
        (.impI (.impE (.andE₂ .h₀) (.impE .h₁ (.impI (.flsE (.impE (.andE₂ .h₁) .h₀))))))
                                        --   have hpre := fun hc => hc.right (hi (fun ha => …))
        (.orE (.impE .h₂ .h₀)           --   cases hDeM hpre
          (.impE .h₂ (.impI .h₁))       --   | inl hb => hi (fun _ => hb)
          .h₀))))                       --   | inr ha => ha
    (.orI₂ .h₀)                         -- | inr hLuk => Or.inr hLuk

/-- Back, at `b ∨ (b → a)` and `a`. -/
theorem pierce₁₂OrLuk₂₁_ent_demorgan₁₂OrLuk₁₂ :
    Ent (pierce₁₂OrLuk₂₁Form (.or (.var 1) (.imp (.var 1) (.var 0))) (.var 0))
      (demorgan₁₂OrLuk₁₂Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orE (.impE .h₀ (.impI (.orI₂ (.impI (.impE .h₁ (.orI₁ .h₀))))))
                                        -- | inl hPc => cases hPc (fun hAa => Or.inr (fun hb => …))
      (.orI₁ (.impI (.orI₂ .h₁)))       --   | inl hb => Or.inl (fun _ => Or.inr hb)
      (.orI₂ (.impI .h₁)))              --   | inr hba => Or.inr (fun _ => hba)
    (.orI₂ (.impI (.impI (.impE (.impE .h₂  -- | inr hLuk => Or.inr; intro hnn hb
      ((neg_imp_neg_ent _ _ _).mp (.andI .h₁ .h₀))) (.orI₁ .h₀)))))
                                        --   hLuk (fun hna => absurd hna hnna) (Or.inl hb)

/-- `demorgan₁₂OrLuk₁₂Form` at `a → b` and `a` gives `em₁OrLuk₂₁Form`, through
`demorgan₁₂OrLuk₁₂_himp_ent`. -/
theorem demorgan₁₂OrLuk₁₂_ent_em₁OrLuk₂₁ :
    Ent (demorgan₁₂OrLuk₁₂Form (.imp (.var 0) (.var 1)) (.var 0))
      (em₁OrLuk₂₁Form (.var 0) (.var 1)) :=
  .orE ((demorgan₁₂OrLuk₁₂_himp_ent _ _).mp .h₀) (.orI₁ (.orI₁ .h₀)) (.orI₂ .h₀)

/-- Excluded middle gives double negation elimination, in the left disjunct. -/
theorem em₁OrLuk₂₁_ent_notNot₁OrLuk₂₁ :
    Ent (em₁OrLuk₂₁Form (.var 0) (.var 1)) (notNot₁OrLuk₂₁Form (.var 0) (.var 1)) :=
  Ent.or_cong (em_ent_notNot _) (Ent.refl _)

/-- Double negation elimination gives consequentia mirabilis, in the left
disjunct. -/
theorem notNot₁OrLuk₂₁_ent_cm₁OrLuk₂₁ :
    Ent (notNot₁OrLuk₂₁Form (.var 0) (.var 1)) (cm₁OrLuk₂₁Form (.var 0) (.var 1)) :=
  Ent.or_cong (notNot_ent_cm _) (Ent.refl _)

/-- Consequentia mirabilis gives Peirce's law, in the left disjunct. -/
theorem cm₁OrLuk₂₁_ent_pierce₁₂OrLuk₂₁ :
    Ent (cm₁OrLuk₂₁Form (.var 0) (.var 1)) (pierce₁₂OrLuk₂₁Form (.var 0) (.var 1)) :=
  Ent.or_cong (cm_ent_peirce _ _) (Ent.refl _)

/-- `demorgan₁₂OrLuk₁₂Form` at `a` and `b ∨ (b → a)` gives `cm₁OrPeirce₂₁Form`.
The shift makes De Morgan's premise provable, and in the Łukasiewicz case the
implication `B → a` supplies `b → a` through its own left injection, which is
what closes it. -/
theorem demorgan₁₂OrLuk₁₂_ent_cm₁OrPeirce₂₁ :
    Ent (demorgan₁₂OrLuk₁₂Form (.var 0) (.or (.var 1) (.imp (.var 1) (.var 0))))
      (cm₁OrPeirce₂₁Form (.var 0) (.var 1)) :=
  .cut (p := Form.neg (Form.neg (.or (.var 1) (.imp (.var 1) (.var 0)))))  -- have hnnB
    (.impI (.impE .h₀ (.orI₂ (.impI (.flsE (.impE .h₁ (.orI₁ .h₀)))))))
    (.orE .h₁                           -- cases h
      (.orE (.impE .h₀ (.impI (.impE .h₂ (.andE₂ .h₀))))  -- | inl hDeM => cases hDeM (fun hc => hnnB hc.right)
        (.orI₁ (.impI .h₁))             --   | inl ha => Or.inl (fun _ => ha)
        (.orE .h₀                       --   | inr hB => cases hB
          (.orI₂ (.impI .h₁))           --     | inl hb => Or.inr (fun _ => hb)
          (.orI₂ (.impI (.impE .h₀ .h₁)))))  -- | inr hba => Or.inr (fun hi => hi hba)
      (.orI₁ (.impI                     -- | inr hLuk => Or.inl; intro hcm
        (.cut (p := Form.neg (Form.neg (.var 0)))  -- have hnn := fun hna => hna (hcm hna)
          (.impI (.impE .h₀ (.impE .h₁ .h₀)))
          (.cut (p := .imp (.or (.var 1) (.imp (.var 1) (.var 0))) (.var 0))
            (.impE .h₂ (.impI (.flsE (.impE .h₁ .h₀))))  -- have g := hLuk (fun hna => absurd hna hnn)
            (.impE .h₀ (.orI₂ (.impI (.impE .h₁ (.orI₁ .h₀))))))))))
                                        -- g (Or.inr (fun hb => g (Or.inl hb)))

/-- Consequentia mirabilis gives double negation elimination, in the left
disjunct. -/
theorem cm₁OrPeirce₂₁_ent_notNot₁OrPeirce₂₁ :
    Ent (cm₁OrPeirce₂₁Form (.var 0) (.var 1)) (notNot₁OrPeirce₂₁Form (.var 0) (.var 1)) :=
  Ent.or_cong (cm_ent_notNot _) (Ent.refl _)

/-- Double negation elimination gives consequentia mirabilis, in the left
disjunct. -/
theorem notNot₁OrPeirce₂₁_ent_cm₁OrPeirce₂₁ :
    Ent (notNot₁OrPeirce₂₁Form (.var 0) (.var 1)) (cm₁OrPeirce₂₁Form (.var 0) (.var 1)) :=
  Ent.or_cong (notNot_ent_cm _) (Ent.refl _)

/-- `cm₁OrPeirce₂₁Form` at `b, a` gives `pierce₁₂OrLuk₂₁Form`: consequentia
mirabilis at `b` gives Łukasiewicz at `b, a`, and Peirce carries over. -/
theorem cm₁OrPeirce₂₁_ent_pierce₁₂OrLuk₂₁ :
    Ent (cm₁OrPeirce₂₁Form (.var 1) (.var 0)) (pierce₁₂OrLuk₂₁Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orI₂ (.impI (.impI (.impE .h₂     -- | inl hcm => Or.inr (fun hba ha => hcm (fun hnb => …))
      (.impI (.flsE (.impE (.impE .h₂ .h₀) .h₁)))))))  -- absurd ha (hba hnb)
    (.orI₁ .h₀)                         -- | inr hPc => Or.inl hPc

/-- Pairing the second split with Łukasiewicz lands on this level:
`emAOrB₁₂OrLuk₁₂Form` at `b → a` and `b` gives `demorgan₁₂OrLuk₁₂Form`.  There
the split's third disjunct is refutable, and its Łukasiewicz half turns on
`¬ (b → a)` giving `¬ a`. -/
theorem emAOrB₁₂OrLuk₁₂_ent_demorgan₁₂OrLuk₁₂ :
    Ent (emAOrB₁₂OrLuk₁₂Form (.imp (.var 1) (.var 0)) (.var 1))
      (demorgan₁₂OrLuk₁₂Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orE .h₀ (.orI₂ (.impI .h₁))       -- | inl hE => cases hE; | inl hba => Or.inr (fun _ => hba)
      (.orE .h₀ (.orI₁ (.impI (.orI₂ .h₁)))  -- | inr h2 => cases h2; | inl hb => Or.inl (fun _ => Or.inr hb)
        (.flsE (.impE .h₀ (.impI (.impI (.flsE (.impE .h₁ .h₀))))))))
                                        --     | inr hn => absurd (fun hnb hb => absurd hb hnb) hn
    (.orI₂ ((luk_himp_ent _ _).mp .h₀)) -- | inr hLuk

/-- Back, also at `b → a` and `b`. -/
theorem demorgan₁₂OrLuk₁₂_ent_emAOrB₁₂OrLuk₁₂ :
    Ent (demorgan₁₂OrLuk₁₂Form (.imp (.var 1) (.var 0)) (.var 1))
      (emAOrB₁₂OrLuk₁₂Form (.var 0) (.var 1)) :=
  .orE ((demorgan₁₂OrLuk₁₂_himp_ent _ _).mp .h₀) (.orI₁ (.orI₂ (.orI₁ .h₀))) (.orI₂ .h₀)

/-- Swapping Łukasiewicz's arguments keeps the same level.  Here the forward
direction, at `b, a`, needs no shift on the Łukasiewicz side at all, and the
split's third disjunct `¬ (¬ a → b)` delivers `¬ b`, which is enough for
Łukasiewicz. -/
theorem emAOrB₁₂OrLuk₂₁_ent_demorgan₁₂OrLuk₁₂ :
    Ent (emAOrB₁₂OrLuk₂₁Form (.var 1) (.var 0)) (demorgan₁₂OrLuk₁₂Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orE .h₀ (.orI₁ (.impI (.orI₂ .h₁)))  -- | inl hE => cases hE; | inl hb => Or.inl (fun _ => Or.inr hb)
      (.orE .h₀ (.orI₁ (.impI (.orI₁ .h₁)))  -- | inr h2 => cases h2; | inl ha => Or.inl (fun _ => Or.inl ha)
        (.orI₂ (.impI (.impI (.flsE (.impE .h₂ (.impI .h₁))))))))
                                        --     | inr hn => Or.inr (fun _ hb => absurd (fun _ => hb) hn)
    (.orI₂ .h₀)                         -- | inr hLuk => Or.inr hLuk

/-- Back, at `a → b` and `a`. -/
theorem demorgan₁₂OrLuk₁₂_ent_emAOrB₁₂OrLuk₂₁ :
    Ent (demorgan₁₂OrLuk₁₂Form (.imp (.var 0) (.var 1)) (.var 0))
      (emAOrB₁₂OrLuk₂₁Form (.var 0) (.var 1)) :=
  .orE ((demorgan₁₂OrLuk₁₂_himp_ent _ _).mp .h₀) (.orI₁ (.orI₁ .h₀)) (.orI₂ .h₀)

/-- The last pairing, again at this level, at `b, a`.  Every case of the split
feeds Łukasiewicz: `¬ a` directly, and `¬ (a → b)` through `¬ b`. -/
theorem emAOrNotB₁₂OrLuk₂₁_ent_demorgan₁₂OrLuk₁₂ :
    Ent (emAOrNotB₁₂OrLuk₂₁Form (.var 1) (.var 0)) (demorgan₁₂OrLuk₁₂Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orE .h₀ (.orI₁ (.impI (.orI₂ .h₁)))  -- | inl hE => cases hE; | inl hb => Or.inl (fun _ => Or.inr hb)
      (.orE .h₀                         --   | inr h2 => cases h2
        (.orI₂ (.impI (.impI (.flsE (.impE (.impE .h₁ .h₂) .h₀)))))
                                        --     | inl hna => Or.inr (fun hx hb => absurd hb (hx hna))
        (.orI₂ (.impI (.impI (.flsE (.impE .h₂ (.impI .h₁))))))))
                                        --     | inr hn => Or.inr (fun _ hb => absurd (fun _ => hb) hn)
    (.orI₂ .h₀)                         -- | inr hLuk => Or.inr hLuk

/-- Back, at `a → b` and `a`. -/
theorem demorgan₁₂OrLuk₁₂_ent_emAOrNotB₁₂OrLuk₂₁ :
    Ent (demorgan₁₂OrLuk₁₂Form (.imp (.var 0) (.var 1)) (.var 0))
      (emAOrNotB₁₂OrLuk₂₁Form (.var 0) (.var 1)) :=
  .orE ((demorgan₁₂OrLuk₁₂_himp_ent _ _).mp .h₀) (.orI₁ (.orI₁ .h₀)) (.orI₂ .h₀)

theorem derives_bd2_of_em₁OrLuk₂₁ :
    DerivesFromSchema (em₁OrLuk₂₁Form (.var 0) (.var 1)) (bd2Form (.var 0) (.var 1)) :=
  .of_ent em₁OrLuk₂₁_ent_bd2 ⟨Form.args [.var 0, excludedMiddleForm (.var 1)], rfl⟩

theorem derives_em₁OrLuk₂₁_of_bd2 :
    DerivesFromSchema (bd2Form (.var 0) (.var 1)) (em₁OrLuk₂₁Form (.var 0) (.var 1)) :=
  .of_ent bd2_ent_em₁OrLuk₂₁ ⟨Form.args [excludedMiddleForm (.var 0), .var 1], rfl⟩

theorem derives_em₁OrLuk₂₁_of_demorgan₁₂OrLuk₁₂ :
    DerivesFromSchema (demorgan₁₂OrLuk₁₂Form (.var 0) (.var 1))
      (em₁OrLuk₂₁Form (.var 0) (.var 1)) :=
  .of_ent demorgan₁₂OrLuk₁₂_ent_em₁OrLuk₂₁ ⟨Form.args [.imp (.var 0) (.var 1), .var 0], rfl⟩

theorem derives_notNot₁OrLuk₂₁_of_em₁OrLuk₂₁ :
    DerivesFromSchema (em₁OrLuk₂₁Form (.var 0) (.var 1)) (notNot₁OrLuk₂₁Form (.var 0) (.var 1)) :=
  .of_ent_self em₁OrLuk₂₁_ent_notNot₁OrLuk₂₁

theorem derives_cm₁OrLuk₂₁_of_notNot₁OrLuk₂₁ :
    DerivesFromSchema (notNot₁OrLuk₂₁Form (.var 0) (.var 1)) (cm₁OrLuk₂₁Form (.var 0) (.var 1)) :=
  .of_ent_self notNot₁OrLuk₂₁_ent_cm₁OrLuk₂₁

theorem derives_pierce₁₂OrLuk₂₁_of_cm₁OrLuk₂₁ :
    DerivesFromSchema (cm₁OrLuk₂₁Form (.var 0) (.var 1)) (pierce₁₂OrLuk₂₁Form (.var 0) (.var 1)) :=
  .of_ent_self cm₁OrLuk₂₁_ent_pierce₁₂OrLuk₂₁

theorem derives_demorgan₁₂OrLuk₁₂_of_pierce₁₂OrLuk₂₁ :
    DerivesFromSchema (pierce₁₂OrLuk₂₁Form (.var 0) (.var 1))
      (demorgan₁₂OrLuk₁₂Form (.var 0) (.var 1)) :=
  .of_ent pierce₁₂OrLuk₂₁_ent_demorgan₁₂OrLuk₁₂
      ⟨Form.args [.or (.var 1) (.imp (.var 1) (.var 0)), .var 0], rfl⟩

theorem derives_pierce₁₂OrLuk₂₁_of_cm₁OrPeirce₂₁ :
    DerivesFromSchema (cm₁OrPeirce₂₁Form (.var 0) (.var 1))
      (pierce₁₂OrLuk₂₁Form (.var 0) (.var 1)) :=
  .of_ent cm₁OrPeirce₂₁_ent_pierce₁₂OrLuk₂₁ ⟨Form.args [.var 1, .var 0], rfl⟩

theorem derives_cm₁OrPeirce₂₁_of_demorgan₁₂OrLuk₁₂ :
    DerivesFromSchema (demorgan₁₂OrLuk₁₂Form (.var 0) (.var 1))
      (cm₁OrPeirce₂₁Form (.var 0) (.var 1)) :=
  .of_ent demorgan₁₂OrLuk₁₂_ent_cm₁OrPeirce₂₁
      ⟨Form.args [.var 0, .or (.var 1) (.imp (.var 1) (.var 0))], rfl⟩

/-- **`demorgan₁₂OrLuk₁₂Form` axiomatises bounded depth two's level**: down
through `em₁OrLuk₂₁Form`, and back up along the cycle through
`notNot₁OrLuk₂₁Form`, `cm₁OrLuk₂₁Form` and `pierce₁₂OrLuk₂₁Form`. -/
theorem demorgan₁₂OrLuk₁₂_equiv_bd2 :
    SchemaEquiv (demorgan₁₂OrLuk₁₂Form (.var 0) (.var 1)) (bd2Form (.var 0) (.var 1)) :=
  ⟨derives_em₁OrLuk₂₁_of_demorgan₁₂OrLuk₁₂.trans derives_bd2_of_em₁OrLuk₂₁,
   derives_em₁OrLuk₂₁_of_bd2.trans (derives_notNot₁OrLuk₂₁_of_em₁OrLuk₂₁.trans
     (derives_cm₁OrLuk₂₁_of_notNot₁OrLuk₂₁.trans (derives_pierce₁₂OrLuk₂₁_of_cm₁OrLuk₂₁.trans
       derives_demorgan₁₂OrLuk₁₂_of_pierce₁₂OrLuk₂₁)))⟩

/-- A member joined to `demorgan₁₂OrLuk₁₂Form` both ways is at bounded depth
two's level. -/
theorem SchemaEquiv.bd2_of_demorgan₁₂OrLuk₁₂ {X : Form}
    (h₁ : DerivesFromSchema X (demorgan₁₂OrLuk₁₂Form (.var 0) (.var 1)))
    (h₂ : DerivesFromSchema (demorgan₁₂OrLuk₁₂Form (.var 0) (.var 1)) X) : SchemaEquiv X
    (bd2Form (.var 0) (.var 1)) :=
  SchemaEquiv.trans ⟨h₁, h₂⟩ demorgan₁₂OrLuk₁₂_equiv_bd2

theorem em₁OrLuk₂₁_equiv_bd2 :
    SchemaEquiv (em₁OrLuk₂₁Form (.var 0) (.var 1)) (bd2Form (.var 0) (.var 1)) :=
  ⟨derives_bd2_of_em₁OrLuk₂₁, derives_em₁OrLuk₂₁_of_bd2⟩

theorem impOr₁₂OrLuk₁₂_equiv_bd2 :
    SchemaEquiv (impOr₁₂OrLuk₁₂Form (.var 0) (.var 1)) (bd2Form (.var 0) (.var 1)) :=
  .bd2_of_demorgan₁₂OrLuk₁₂
    (.of_ent impOr₁₂OrLuk₁₂_ent_demorgan₁₂OrLuk₁₂ ⟨Form.args [.var 0, .or (.var 0) (.var 1)], rfl⟩)
    (.of_ent demorgan₁₂OrLuk₁₂_ent_impOr₁₂OrLuk₁₂
        ⟨Form.args [.var 0, .or (Form.neg (.var 0)) (.var 1)], rfl⟩)

theorem pierce₁₂OrLuk₂₁_equiv_bd2 :
    SchemaEquiv (pierce₁₂OrLuk₂₁Form (.var 0) (.var 1)) (bd2Form (.var 0) (.var 1)) :=
  .bd2_of_demorgan₁₂OrLuk₁₂ derives_demorgan₁₂OrLuk₁₂_of_pierce₁₂OrLuk₂₁
    (.of_ent demorgan₁₂OrLuk₁₂_ent_pierce₁₂OrLuk₂₁ ⟨Form.args [.var 1, .var 0], rfl⟩)

theorem notNot₁OrLuk₂₁_equiv_bd2 :
    SchemaEquiv (notNot₁OrLuk₂₁Form (.var 0) (.var 1)) (bd2Form (.var 0) (.var 1)) :=
  .bd2_of_demorgan₁₂OrLuk₁₂
    (derives_cm₁OrLuk₂₁_of_notNot₁OrLuk₂₁.trans (derives_pierce₁₂OrLuk₂₁_of_cm₁OrLuk₂₁.trans
      derives_demorgan₁₂OrLuk₁₂_of_pierce₁₂OrLuk₂₁))
    (derives_em₁OrLuk₂₁_of_demorgan₁₂OrLuk₁₂.trans derives_notNot₁OrLuk₂₁_of_em₁OrLuk₂₁)

theorem cm₁OrLuk₂₁_equiv_bd2 :
    SchemaEquiv (cm₁OrLuk₂₁Form (.var 0) (.var 1)) (bd2Form (.var 0) (.var 1)) :=
  .bd2_of_demorgan₁₂OrLuk₁₂
    (derives_pierce₁₂OrLuk₂₁_of_cm₁OrLuk₂₁.trans derives_demorgan₁₂OrLuk₁₂_of_pierce₁₂OrLuk₂₁)
    (derives_em₁OrLuk₂₁_of_demorgan₁₂OrLuk₁₂.trans (derives_notNot₁OrLuk₂₁_of_em₁OrLuk₂₁.trans
      derives_cm₁OrLuk₂₁_of_notNot₁OrLuk₂₁))

theorem cm₁OrPeirce₂₁_equiv_bd2 :
    SchemaEquiv (cm₁OrPeirce₂₁Form (.var 0) (.var 1)) (bd2Form (.var 0) (.var 1)) :=
  .bd2_of_demorgan₁₂OrLuk₁₂
    (derives_pierce₁₂OrLuk₂₁_of_cm₁OrPeirce₂₁.trans derives_demorgan₁₂OrLuk₁₂_of_pierce₁₂OrLuk₂₁)
    derives_cm₁OrPeirce₂₁_of_demorgan₁₂OrLuk₁₂

theorem notNot₁OrPeirce₂₁_equiv_bd2 :
    SchemaEquiv (notNot₁OrPeirce₂₁Form (.var 0) (.var 1)) (bd2Form (.var 0) (.var 1)) :=
  .bd2_of_demorgan₁₂OrLuk₁₂
    ((DerivesFromSchema.of_ent_self notNot₁OrPeirce₂₁_ent_cm₁OrPeirce₂₁).trans
      (derives_pierce₁₂OrLuk₂₁_of_cm₁OrPeirce₂₁.trans derives_demorgan₁₂OrLuk₁₂_of_pierce₁₂OrLuk₂₁))
    (derives_cm₁OrPeirce₂₁_of_demorgan₁₂OrLuk₁₂.trans
      (.of_ent_self cm₁OrPeirce₂₁_ent_notNot₁OrPeirce₂₁))

theorem emAOrB₁₂OrLuk₁₂_equiv_bd2 :
    SchemaEquiv (emAOrB₁₂OrLuk₁₂Form (.var 0) (.var 1)) (bd2Form (.var 0) (.var 1)) :=
  .bd2_of_demorgan₁₂OrLuk₁₂
    (.of_ent emAOrB₁₂OrLuk₁₂_ent_demorgan₁₂OrLuk₁₂
        ⟨Form.args [.imp (.var 1) (.var 0), .var 1], rfl⟩)
    (.of_ent demorgan₁₂OrLuk₁₂_ent_emAOrB₁₂OrLuk₁₂
        ⟨Form.args [.imp (.var 1) (.var 0), .var 1], rfl⟩)

theorem emAOrB₁₂OrLuk₂₁_equiv_bd2 :
    SchemaEquiv (emAOrB₁₂OrLuk₂₁Form (.var 0) (.var 1)) (bd2Form (.var 0) (.var 1)) :=
  .bd2_of_demorgan₁₂OrLuk₁₂
    (.of_ent emAOrB₁₂OrLuk₂₁_ent_demorgan₁₂OrLuk₁₂ ⟨Form.args [.var 1, .var 0], rfl⟩)
    (.of_ent demorgan₁₂OrLuk₁₂_ent_emAOrB₁₂OrLuk₂₁
        ⟨Form.args [.imp (.var 0) (.var 1), .var 0], rfl⟩)

theorem emAOrNotB₁₂OrLuk₂₁_equiv_bd2 :
    SchemaEquiv (emAOrNotB₁₂OrLuk₂₁Form (.var 0) (.var 1)) (bd2Form (.var 0) (.var 1)) :=
  .bd2_of_demorgan₁₂OrLuk₁₂
    (.of_ent emAOrNotB₁₂OrLuk₂₁_ent_demorgan₁₂OrLuk₁₂ ⟨Form.args [.var 1, .var 0], rfl⟩)
    (.of_ent demorgan₁₂OrLuk₁₂_ent_emAOrNotB₁₂OrLuk₂₁
        ⟨Form.args [.imp (.var 0) (.var 1), .var 0], rfl⟩)

/-- Swapping `impOrForm`'s arguments makes the principle strong enough to reach
`demorgan₁₂OrLuk₁₂Form`, which the unswapped version cannot.  The shift is to
the three way disjunction `a ∨ b ∨ (b → a)`, whose every case settles the
target: `a` and `b` give De Morgan's conclusion, and `b → a` is Łukasiewicz's.
That is one `cut`, used by both disjuncts.  Peirce reaches the disjunction
because its premise `(A → a) → A` is provable there, and `impOrForm` because
`a → A` is. -/
theorem peirce₁₂OrImpOr₂₁_ent_demorgan₁₂OrLuk₁₂ :
    Ent (peirce₁₂OrImpOr₂₁Form (.or (.var 0) (.or (.var 1) (.imp (.var 1) (.var 0)))) (.var 0))
      (demorgan₁₂OrLuk₁₂Form (.var 0) (.var 1)) :=
  .cut (p := .imp (.or (.var 0) (.or (.var 1) (.imp (.var 1) (.var 0))))
      (demorgan₁₂OrLuk₁₂Form (.var 0) (.var 1)))
    (.impI (.orE .h₀                    -- have key; intro hA; cases hA
      (.orI₁ (.impI (.orI₁ .h₁)))       --   | inl ha => Or.inl (fun _ => Or.inl ha)
      (.orE .h₀                         --   | inr hbr => cases hbr
        (.orI₁ (.impI (.orI₂ .h₁)))     --     | inl hb => Or.inl (fun _ => Or.inr hb)
        (.orI₂ (.impI .h₁)))))          --     | inr hba => Or.inr (fun _ => hba)
    (.orE .h₁                           -- cases h
      (.impE .h₁ (.impE .h₀ (.impI (.orI₂ (.orI₂ (.impI
        (.impE .h₁ (.orI₂ (.orI₁ .h₀)))))))))
                                        -- | inl hPc => key (hPc (fun hAa => Or.inr (Or.inr …)))
      (.orE (.impE .h₀ (.impI (.orI₁ .h₀)))  -- | inr hIO => cases hIO (fun ha => Or.inl ha)
        (.orI₂ (.impI (.impI (.flsE (.impE (.impE .h₁ .h₂) .h₀)))))
                                        --   | inl hna => Or.inr (fun hn hb => absurd hb (hn hna))
        (.impE .h₂ .h₀)))               --   | inr hA => key hA

/-- **Smetanich's axiom derives bounded depth two**, through
`peirce₁₂OrImpOr₂₁Form` and `demorgan₁₂OrLuk₁₂Form`. -/
theorem derives_bd2_of_smetanich :
    DerivesFromSchema (smetanichForm (.var 0) (.var 1)) (bd2Form (.var 0) (.var 1)) :=
  peirce₁₂OrImpOr₂₁_equiv_smetanich.2.trans
    ((DerivesFromSchema.of_ent peirce₁₂OrImpOr₂₁_ent_demorgan₁₂OrLuk₁₂
        ⟨Form.args [.or (.var 0) (.or (.var 1) (.imp (.var 1) (.var 0))), .var 0], rfl⟩).trans
      demorgan₁₂OrLuk₁₂_equiv_bd2.1)

/-! ## `noDiamondForm`'s class

`notNotAndForm` says the same level differently, that the two arguments are
comparable as soon as they are jointly consistent.  Every return trip to
`noDiamondForm` is the same shift, to `a ∨ ¬ a` and `b ∨ ¬ b`.  The principles
returning have a hypothesis that the shift discharges for free, since the
negation of an excluded middle is refuted, and what survives is a comparison
between the two excluded middles.  That is already `noDiamondForm`, because `a`
gives `a ∨ ¬ a` on its own.

`bd2Form` gives `noDiamondForm` at the same arguments, with nothing shifted:
the one change between them is the bare left disjunct `a`, which gives the
mirror image of the right one. -/

/-- Each disjunct of `noDiamondForm`, an arrow into an excluded middle, gives
one of Łukasiewicz's. -/
theorem noDiamond_ent_luk₁₂OrLuk₂₁ :
    Ent (noDiamondForm (.var 0) (.var 1)) (luk₁₂OrLuk₂₁Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orI₂ ((himp_em_ent_luk _ _).mp .h₀))  -- | inl k => Or.inr (fun hn ha => …)
    (.orI₁ ((himp_em_ent_luk _ _).mp .h₀))  -- | inr k => Or.inl (fun hn hb => …)

/-- Back, at `a ∨ ¬ a` and `b ∨ ¬ b`. -/
theorem luk₁₂OrLuk₂₁_ent_noDiamond :
    Ent (luk₁₂OrLuk₂₁Form (excludedMiddleForm (.var 0)) (excludedMiddleForm (.var 1)))
      (noDiamondForm (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orI₂ ((luk_em_ent _ _).mp .h₀))   -- | inl k => Or.inr (fun hb => …)
    (.orI₁ ((luk_em_ent _ _).mp .h₀))   -- | inr k => Or.inl (fun ha => …)

/-- `noDiamondForm` gives `notNotAndForm` at the same arguments.  Its two halves
differ in which half of `a ∧ b` they take, so they are not one argument. -/
theorem noDiamond_ent_notNotAnd :
    Ent (noDiamondForm (.var 0) (.var 1)) (notNotAndForm (.var 0) (.var 1)) :=
  .impI (.orE .h₁                       -- intro hnn; cases h
    (.orI₁ (.impI (.orE (.impE .h₁ .h₀) .h₀  -- | inl k => Or.inl (fun ha => cases k ha); | inl hb => hb
      (.flsE (.impE .h₃ (.impI (.impE .h₁ (.andE₂ .h₀))))))))
                                        --   | inr hnb => absurd (fun hab => hnb hab.2) hnn
    (.orI₂ (.impI (.orE (.impE .h₁ .h₀) .h₀  -- | inr k => Or.inr (fun hb => cases k hb); | inl ha => ha
      (.flsE (.impE .h₃ (.impI (.impE .h₁ (.andE₁ .h₀)))))))))
                                        --   | inr hna => absurd (fun hab => hna hab.1) hnn

/-- Back, at `a ∨ ¬ a` and `b ∨ ¬ b`, where the premise holds by `nn_em`
twice. -/
theorem notNotAnd_ent_noDiamond :
    Ent (notNotAndForm (excludedMiddleForm (.var 0)) (excludedMiddleForm (.var 1)))
      (noDiamondForm (.var 0) (.var 1)) :=
  .orE (.impE .h₀ (.impI (.impE (nn_em _) (.impI (.impE (nn_em _) (.impI
      (.impE .h₂ (.andI .h₁ .h₀))))))))  -- cases h (fun hn => hna (fun hx => hnb (fun hy => hn ⟨hx, hy⟩)))
    (.orI₁ ((imp_em_ent _ _).mp .h₀))  -- | inl k => Or.inl (fun ha => k (Or.inl ha))
    (.orI₂ ((imp_em_ent _ _).mp .h₀))  -- | inr k => Or.inr (fun hb => k (Or.inl hb))

/-- Doubling Łukasiewicz lands on this level too.  The shift to `a ∧ b` makes
`impOrForm`'s premise available under `b` and turns Łukasiewicz's conclusion
into `a → b`. -/
theorem impOr₁₂OrLuk₂₁_ent_luk₁₂OrLuk₂₁ :
    Ent (impOr₁₂OrLuk₂₁Form (.var 0) (.and (.var 0) (.var 1)))
      (luk₁₂OrLuk₂₁Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orI₁ ((impOr_and_ent_luk _ _).mp .h₀))  -- | inl hIO => Or.inl (…)
    (.orI₂ (.impI (.impI (.andE₂ (.impE (.impE .h₂  -- | inr hLuk => Or.inr; intro hba ha
      (.impI (.impI (.impE (.impE .h₃ (.impI (.impE .h₂ (.andI .h₁ .h₀)))) .h₀)))) .h₀)))))
                                        --   (hLuk (fun k ha' => hba (fun hb => k ⟨ha', hb⟩) ha') ha).2

/-- The converse, at `a → b` against excluded middle on `a`.  Both source
disjuncts have a premise that is free because `¬ (a ∨ ¬ a)` is refuted, and
the `a` assumed by the target is what supplies `a ∨ ¬ a` in the first case. -/
theorem luk₁₂OrLuk₂₁_ent_impOr₁₂OrLuk₂₁ :
    Ent (luk₁₂OrLuk₂₁Form (.imp (.var 0) (.var 1)) (excludedMiddleForm (.var 0)))
      (impOr₁₂OrLuk₂₁Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orI₂ (.impI (.impI                -- | inl hL => Or.inr; intro hba ha
      (.cut (p := Form.neg (Form.neg (.imp (.var 0) (.var 1))))
        (.impI (.impE (.impE .h₂ (.impI (.impE .h₁ (.impI .h₁)))) .h₁))
                                        --   have hnn := fun hn => hba (fun hb => hn (fun _ => hb)) ha
        (.impE (.impE (.impE .h₃ (.impI (.flsE (.impE .h₁ .h₀)))) (.orI₁ .h₁)) .h₁)))))
                                        --   hL (fun hnx => absurd hnx hnn) (Or.inl ha) ha
    (.orI₁ ((luk_em_ent_impOr _ _).mp .h₀))  -- | inr hL => Or.inl (…)

theorem derives_luk₁₂OrLuk₂₁_of_noDiamond :
    DerivesFromSchema (noDiamondForm (.var 0) (.var 1)) (luk₁₂OrLuk₂₁Form (.var 0) (.var 1)) :=
  .of_ent_self noDiamond_ent_luk₁₂OrLuk₂₁

theorem derives_impOr₁₂OrLuk₂₁_of_luk₁₂OrLuk₂₁ :
    DerivesFromSchema (luk₁₂OrLuk₂₁Form (.var 0) (.var 1)) (impOr₁₂OrLuk₂₁Form (.var 0) (.var 1)) :=
  .of_ent luk₁₂OrLuk₂₁_ent_impOr₁₂OrLuk₂₁
      ⟨Form.args [.imp (.var 0) (.var 1), excludedMiddleForm (.var 0)], rfl⟩

theorem luk₁₂OrLuk₂₁_equiv_noDiamond :
    SchemaEquiv (luk₁₂OrLuk₂₁Form (.var 0) (.var 1)) (noDiamondForm (.var 0) (.var 1)) :=
  ⟨.of_ent luk₁₂OrLuk₂₁_ent_noDiamond
      ⟨Form.args [excludedMiddleForm (.var 0), excludedMiddleForm (.var 1)], rfl⟩,
   derives_luk₁₂OrLuk₂₁_of_noDiamond⟩

theorem notNotAnd_equiv_noDiamond :
    SchemaEquiv (notNotAndForm (.var 0) (.var 1)) (noDiamondForm (.var 0) (.var 1)) :=
  ⟨.of_ent notNotAnd_ent_noDiamond
      ⟨Form.args [excludedMiddleForm (.var 0), excludedMiddleForm (.var 1)], rfl⟩,
   .of_ent_self noDiamond_ent_notNotAnd⟩

theorem impOr₁₂OrLuk₂₁_equiv_noDiamond :
    SchemaEquiv (impOr₁₂OrLuk₂₁Form (.var 0) (.var 1)) (noDiamondForm (.var 0) (.var 1)) :=
  SchemaEquiv.trans
    ⟨.of_ent impOr₁₂OrLuk₂₁_ent_luk₁₂OrLuk₂₁
        ⟨Form.args [.var 0, .and (.var 0) (.var 1)], rfl⟩,
     derives_impOr₁₂OrLuk₂₁_of_luk₁₂OrLuk₂₁⟩
    luk₁₂OrLuk₂₁_equiv_noDiamond

/-- `bd2Form` gives `noDiamondForm` at the same arguments. -/
theorem bd2_ent_noDiamond : Ent (bd2Form (.var 0) (.var 1)) (noDiamondForm (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orI₂ (.impI (.orI₁ .h₁)))         -- | inl ha => Or.inr (fun _ => Or.inl ha)
    (.orI₁ .h₀)                         -- | inr k => Or.inl k

/-- **Bounded depth two derives `noDiamondForm`.** -/
theorem derives_noDiamond_of_bd2 :
    DerivesFromSchema (bd2Form (.var 0) (.var 1)) (noDiamondForm (.var 0) (.var 1)) :=
  .of_ent_self bd2_ent_noDiamond

/-! ## Linearity and weak excluded middle

Neither is a combination of two principles, so neither belongs to the chain of
levels; each sits beside it.  Linearity is the stronger, and reaches weak
excluded middle by being asked about a formula against its own negation.

Smetanich's level reaches linearity: `peirce₁₂OrImpOr₂₁Form`, asked about
linearity itself and `b`, gives it back.  Each disjunct has a premise that
holds there, Peirce's because `a → b` follows from anything that turns
linearity into `b`, and `impOrForm`'s because `b` gives `a → b`.

The last entailment places linearity exactly.  Linearity gives weak excluded
middle and `noDiamondForm`, and those two give it back, at the plain arguments
and with no shift: once neither argument can be refuted, the disjunct of
`noDiamondForm` that holds delivers the comparison outright. -/

/-- `peirce₁₂OrImpOr₂₁Form` at linearity and `b` gives linearity. -/
theorem peirce₁₂OrImpOr₂₁_ent_linearity :
    Ent (peirce₁₂OrImpOr₂₁Form (linearityForm (.var 0) (.var 1)) (.var 1))
      (linearityForm (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.impE .h₀ (.impI (.orI₁ (.impI (.impE .h₁ (.orI₂ (.impI .h₁)))))))
                                        -- | inl hPc => hPc (fun f => Or.inl (fun ha => f (Or.inr …)))
    (.orE (.impE .h₀ (.impI (.orI₁ (.impI .h₁))))  -- | inr hIO => cases hIO (fun hb => Or.inl (fun _ => hb))
      (.orI₂ (.impI (.flsE (.impE .h₁ .h₀))))  -- | inl hnb => Or.inr (fun hb => absurd hb hnb)
      .h₀)                              --   | inr hL => hL

/-- Linearity at `a` against `¬ a` is weak excluded middle. -/
theorem linearity_ent_weakEm :
    Ent (linearityForm (.var 0) (Form.neg (.var 0))) (weakEmForm (.var 0)) :=
  .orE .h₀                              -- cases h
    (.orI₁ (.impI (.impE (.impE .h₁ .h₀) .h₀)))  -- | inl k => Or.inl (fun ha => k ha ha)
    (.orI₂ (.impI (.impE .h₀ (.impE .h₁ .h₀))))  -- | inr k => Or.inr (fun na => na (k na))

/-- Linearity between `a ∨ ¬ a` and `b ∨ ¬ b` gives `noDiamondForm`. -/
theorem linearity_ent_noDiamond :
    Ent (linearityForm (excludedMiddleForm (.var 0)) (excludedMiddleForm (.var 1)))
      (noDiamondForm (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orI₁ ((imp_em_ent _ _).mp .h₀))   -- | inl k => Or.inl (fun ha => k (Or.inl ha))
    (.orI₂ ((imp_em_ent _ _).mp .h₀))   -- | inr k => Or.inr (fun hb => k (Or.inl hb))

/-- **Smetanich's axiom derives linearity**, through `peirce₁₂OrImpOr₂₁Form`. -/
theorem derives_linearity_of_smetanich :
    DerivesFromSchema (smetanichForm (.var 0) (.var 1)) (linearityForm (.var 0) (.var 1)) :=
  peirce₁₂OrImpOr₂₁_equiv_smetanich.2.trans (.of_ent peirce₁₂OrImpOr₂₁_ent_linearity
      ⟨Form.args [linearityForm (.var 0) (.var 1), .var 1], rfl⟩)

/-- **Linearity derives weak excluded middle.** -/
theorem derives_weakEm_of_linearity :
    DerivesFromSchema (linearityForm (.var 0) (.var 1)) (weakEmForm (.var 0)) :=
  .of_ent linearity_ent_weakEm ⟨Form.args [.var 0, Form.neg (.var 0)], rfl⟩

/-- **Linearity derives `noDiamondForm`.** -/
theorem derives_noDiamond_of_linearity :
    DerivesFromSchema (linearityForm (.var 0) (.var 1)) (noDiamondForm (.var 0) (.var 1)) :=
  .of_ent linearity_ent_noDiamond
      ⟨Form.args [excludedMiddleForm (.var 0), excludedMiddleForm (.var 1)], rfl⟩

/-- **Weak excluded middle at both arguments, with `noDiamondForm`, gives
linearity.**  Each argument is either refutable, which settles the comparison
one way, or doubly negated, and then the `noDiamondForm` disjunct that holds
turns an excluded middle into the comparison itself. -/
theorem weakEm_noDiamond_ent_linearity :
    Ent (.and (weakEmForm (.var 0)) (.and (weakEmForm (.var 1)) (noDiamondForm (.var 0) (.var 1))))
      (linearityForm (.var 0) (.var 1)) :=
  .orE (.andE₁ .h₀)                     -- cases ha
    (.orI₁ (.impI (.flsE (.impE .h₁ .h₀))))  -- | inl na => Or.inl (fun x => absurd x na)
    (.orE (.andE₁ (.andE₂ .h₁))         -- | inr nna => cases hb
      (.orI₂ (.impI (.flsE (.impE .h₁ .h₀))))  -- | inl nb => Or.inr (fun y => absurd y nb)
      (.orE (.andE₂ (.andE₂ .h₂))       --   | inr nnb => cases hnd
        (.orI₁ (.impI (.orE (.impE .h₁ .h₀) .h₀  -- | inl k => Or.inl (fun x => cases k x); | inl y => y
          (.flsE (.impE .h₃ .h₀)))))    --     | inr nb => absurd nb nnb
        (.orI₂ (.impI (.orE (.impE .h₁ .h₀) .h₀  -- | inr k => Or.inr (fun y => cases k y); | inl x => x
          (.flsE (.impE .h₄ .h₀)))))))  --     | inr na => absurd na nna

/-! ## From `noDiamondForm` down to `pierce₁₂OrLuk₁₂Form`, and its class -/

/-- `impOr₁₂OrLuk₂₁Form` at `a ∨ b` and `a` gives `pierce₁₂OrLuk₁₂Form`. -/
theorem impOr₁₂OrLuk₂₁_ent_pierce₁₂OrLuk₁₂ :
    Ent (impOr₁₂OrLuk₂₁Form (.or (.var 0) (.var 1)) (.var 0))
      (pierce₁₂OrLuk₁₂Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orI₁ (.impI                       -- | inl hIO => Or.inl; intro hi
      (.cut (p := .imp (.or (.var 0) (.var 1)) (.var 0))  -- have hxa : (a ∨ b) → a
        (.impI (.orE .h₀ .h₀ (.impE .h₂ (.impI .h₁))))  --   fun hab => hab.elim id (fun hb => hi (fun _ => hb))
        (.orE (.impE .h₂ .h₀)           --   cases hIO hxa
          (.impE .h₂ (.impI (.flsE (.impE .h₁ (.orI₁ .h₀)))))
                                        --   | inl hn => hi (fun ha => absurd (Or.inl ha) hn)
          .h₀))))                       --   | inr ha => ha
    (.orI₂ ((luk_sup_ent _ _).mp .h₀))  -- | inr hLuk

theorem derives_pierce₁₂OrLuk₁₂_of_impOr₁₂OrLuk₂₁ :
    DerivesFromSchema (impOr₁₂OrLuk₂₁Form (.var 0) (.var 1))
      (pierce₁₂OrLuk₁₂Form (.var 0) (.var 1)) :=
  .of_ent impOr₁₂OrLuk₂₁_ent_pierce₁₂OrLuk₁₂ ⟨Form.args [.or (.var 0) (.var 1), .var 0], rfl⟩

/-- **`noDiamondForm` derives `pierce₁₂OrLuk₁₂Form`**, through two other members
of its class. -/
theorem derives_pierce₁₂OrLuk₁₂_of_noDiamond :
    DerivesFromSchema (noDiamondForm (.var 0) (.var 1)) (pierce₁₂OrLuk₁₂Form (.var 0) (.var 1)) :=
  derives_luk₁₂OrLuk₂₁_of_noDiamond.trans
    (derives_impOr₁₂OrLuk₂₁_of_luk₁₂OrLuk₂₁.trans derives_pierce₁₂OrLuk₁₂_of_impOr₁₂OrLuk₂₁)

/-- Shifting the second argument to `a ∧ b` turns `peirce₁₂OrImpOr₁₂Form` into
`pierce₁₂OrLuk₁₂Form`.  Peirce transfers because `a → a ∧ b` and `a → b` say the
same thing under the assumption `a`, and `impOrForm` transfers because its own
premise is available once `b` is assumed, as Łukasiewicz's conclusion does. -/
theorem peirce₁₂OrImpOr₁₂_ent_pierce₁₂OrLuk₁₂ :
    Ent (peirce₁₂OrImpOr₁₂Form (.var 0) (.and (.var 0) (.var 1)))
      (pierce₁₂OrLuk₁₂Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orI₁ (.impI (.impE .h₁ (.impI     -- | inl hPc => Or.inl; intro hi; hPc (fun hand => …)
      (.impE .h₁ (.impI (.andE₂ (.impE .h₁ .h₀))))))))  -- hi (fun ha => (hand ha).2)
    (.orI₂ ((impOr_and_ent_luk _ _).mp .h₀))  -- | inr hIO => Or.inr (…)

/-- The converse, which needs a deeper shift: `peirce₁₂OrImpOr₁₂Form` at `a` and
`b` comes from `pierce₁₂OrLuk₁₂Form` at excluded middle on `a` and at `a → b`.

Both disjuncts turn on `(a ∨ ¬ a) → (a → b)` being interderivable with `a → b`,
which collapses Peirce's premise to `(a → b) → (a ∨ ¬ a)`; Peirce then hands
back excluded middle on `a`, and Łukasiewicz hands back the same thing because
its own premise is free, `¬ (a ∨ ¬ a)` being refuted. -/
theorem pierce₁₂OrLuk₁₂_ent_peirce₁₂OrImpOr₁₂ :
    Ent (pierce₁₂OrLuk₁₂Form (excludedMiddleForm (.var 0)) (.imp (.var 0) (.var 1)))
      (peirce₁₂OrImpOr₁₂Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orI₁ (.impI (.orE                 -- | inl hPc => Or.inl; intro hi
      (.impE .h₁ ((peirce_ante_ent _ _ _).mp .h₀))  --   cases hPc (fun hAB => …)
      .h₀                               --   | inl ha => ha
      (.impE .h₁ (.impI (.flsE (.impE .h₁ .h₀)))))))  -- | inr hna => hi (fun ha => absurd ha hna)
    (.orI₂ ((luk_em_ent_impOr _ _).mp .h₀))  -- | inr hLuk => Or.inr (…)

theorem peirce₁₂OrImpOr₁₂_equiv_pierce₁₂OrLuk₁₂ :
    SchemaEquiv (peirce₁₂OrImpOr₁₂Form (.var 0) (.var 1)) (pierce₁₂OrLuk₁₂Form (.var 0) (.var 1)) :=
  ⟨.of_ent peirce₁₂OrImpOr₁₂_ent_pierce₁₂OrLuk₁₂ ⟨Form.args [.var 0, .and (.var 0) (.var 1)], rfl⟩,
   .of_ent pierce₁₂OrLuk₁₂_ent_peirce₁₂OrImpOr₁₂
       ⟨Form.args [excludedMiddleForm (.var 0), .imp (.var 0) (.var 1)], rfl⟩⟩

/-! ## The bottom step -/

/-- Doubling Peirce gives the weakest principle here, below even
`pierce₁₂OrLuk₁₂Form`.  At `a ∨ b` against `a → b` each source disjunct
supplies one half of the target: Peirce's premise is provable once
`(a → b) → a` is assumed, and Łukasiewicz's once `(b → a) → b` is. -/
theorem pierce₁₂OrLuk₁₂_ent_pierce₁₂OrPierce₂₁ :
    Ent (pierce₁₂OrLuk₁₂Form (.or (.var 0) (.var 1)) (.imp (.var 0) (.var 1)))
      (pierce₁₂OrPierce₂₁Form (.var 0) (.var 1)) :=
  .orE .h₀                              -- cases h
    (.orI₁ (.impI (.orE                 -- | inl hPc => Or.inl; intro hi
      (.impE .h₁ ((peirce_ante_ent _ _ _).mp .h₀))  --   cases hPc (fun hAB => …)
      .h₀                               --   | inl ha => ha
      (.impE .h₁ (.impI .h₁)))))        --   | inr hb => hi (fun _ => hb)
    (.orI₂ (.impI                       -- | inr hLuk => Or.inr; intro hi
      (.cut (p := .imp (.var 0) (.var 1))  -- have hab := fun ha => hi (fun _ => ha)
        (.impI (.impE .h₁ (.impI .h₁)))
        (.cut (p := .imp (Form.neg (.or (.var 0) (.var 1))) (Form.neg (.imp (.var 0) (.var 1))))
          (.impI (.impI (.impE .h₁ (.orI₂ (.impE .h₃ (.impI (.flsE (.impE .h₂ (.orI₂ .h₀)))))))))
                                        --   have hpre := fun hn _ => hn (Or.inr (hi (fun hb => …)))
          (.orE (.impE (.impE .h₃ .h₀) .h₁)  -- cases hLuk hpre hab
            (.impE .h₃ (.impI .h₁))     --   | inl ha => hi (fun _ => ha)
            .h₀)))))                    --   | inr hb => hb

/-- **`pierce₁₂OrLuk₁₂Form` derives `pierce₁₂OrPierce₂₁Form`.** -/
theorem derives_pierce₁₂OrPierce₂₁_of_pierce₁₂OrLuk₁₂ :
    DerivesFromSchema (pierce₁₂OrLuk₁₂Form (.var 0) (.var 1))
      (pierce₁₂OrPierce₂₁Form (.var 0) (.var 1)) :=
  .of_ent pierce₁₂OrLuk₁₂_ent_pierce₁₂OrPierce₂₁
      ⟨Form.args [.or (.var 0) (.var 1), .imp (.var 0) (.var 1)], rfl⟩

/-! ## Scott's axiom

It follows from weak excluded middle at the plain argument, with nothing
shifted: its conclusion *is* weak excluded middle, so the hypothesis is never
needed.  It also follows from bounded depth two. -/

/-- Weak excluded middle gives Scott's axiom, whose conclusion it is. -/
theorem weakEm_ent_scott : Ent (weakEmForm (.var 0)) (scottForm (.var 0)) :=
  .impI .h₁                             -- fun h _ => h

/-- Bounded depth two, asked about `¬ ¬ a` and `a`, gives Scott's axiom.  Either
`¬ ¬ a` holds, which is weak excluded middle's second case, or the arrow from it
into `a ∨ ¬ a` is double negation elimination at `a`, which Scott's hypothesis
turns into excluded middle. -/
theorem bd2_ent_scott :
    Ent (bd2Form (Form.neg (Form.neg (.var 0))) (.var 0)) (scottForm (.var 0)) :=
  .impI (.orE .h₁                       -- intro hS; cases h
    (.orI₂ .h₀)                         -- | inl hnn => Or.inr hnn
    (.cut (p := .imp (Form.neg (Form.neg (.var 0))) (.var 0))  -- | inr k => have hnna
      (.impI (.orE (.impE .h₁ .h₀) .h₀ (.flsE (.impE .h₁ .h₀))))
                                        --   fun hnn => (k hnn).elim id (fun hna => absurd hna hnn)
      (.orE (.impE .h₂ .h₀)             --   cases hS hnna
        (.orI₂ (.impI (.impE .h₀ .h₁))) --   | inl ha => Or.inr (fun hna => hna ha)
        (.orI₁ .h₀))))                  --   | inr hna => Or.inl hna

/-- **Weak excluded middle derives Scott's axiom.** -/
theorem derives_scott_of_weakEm : DerivesFromSchema (weakEmForm (.var 0)) (scottForm (.var 0)) :=
  .of_ent_self weakEm_ent_scott

/-- **Bounded depth two derives Scott's axiom.** -/
theorem derives_scott_of_bd2 : DerivesFromSchema (bd2Form (.var 0) (.var 1)) (scottForm (.var 0)) :=
  .of_ent bd2_ent_scott ⟨Form.args [Form.neg (Form.neg (.var 0)), .var 0], rfl⟩

/-! ## Kreisel and Putnam's axiom from weak excluded middle

It follows at the plain first argument, with nothing shifted, the two cases of
weak excluded middle being its two disjuncts.  If the first argument is doubly
negated then its negation is refuted, so either implication holds vacuously;
and if it is refutable then the hypothesis can be discharged outright, and
whichever disjunct it yields is the one to take. -/

/-- Weak excluded middle gives Kreisel and Putnam's axiom. -/
theorem weakEm_ent_kreiselPutnam :
    Ent (weakEmForm (.var 0)) (kreiselPutnamForm (.var 0) (.var 1) (.var 2)) :=
  .impI (.orE .h₁                       -- intro k; cases h
    (.orE (.impE .h₁ .h₀)               -- | inl na => cases k na
      (.orI₁ (.impI .h₁))               --   | inl hb => Or.inl (fun _ => hb)
      (.orI₂ (.impI .h₁)))              --   | inr hc => Or.inr (fun _ => hc)
    (.orI₁ (.impI (.flsE (.impE .h₁ .h₀)))))  -- | inr nna => Or.inl (fun na => absurd na nna)

/-- **Weak excluded middle derives Kreisel and Putnam's axiom.** -/
theorem derives_kreiselPutnam_of_weakEm :
    DerivesFromSchema (weakEmForm (.var 0)) (kreiselPutnamForm (.var 0) (.var 1) (.var 2)) :=
  .of_ent_self weakEm_ent_kreiselPutnam

/-! ## The tall fork's principle in two variables and in three

Each form is an instance of the other.  The three variable one at `a, ¬ a, b`
is the two variable one up to the order of a disjunction, its refutation of
`b → (a ∧ ¬ a)` being `¬ ¬ b`.  Conversely the two variable one at `a, c` asks
for excluded middle at `a`, which is as good as `a ∨ b` once the premise of the
three variable one holds: `b` refutes `a`, since with both `c → (a ∧ b)` would
hold, and `¬ a` makes `a → c` vacuous. -/

/-- The three variable form at `a, ¬ a, b` gives the two variable one:
`fun hP => h ⟨fun k => hP.1 k.symm, fun k => hP.2 (fun hb => (k hb).2 (k hb).1)⟩`. -/
theorem noForkUp2x2Var3_ent_noForkUp2x2 :
    Ent (noForkUp2x2Var3Form (.var 0) (Form.neg (.var 0)) (.var 1))
      (noForkUp2x2Form (.var 0) (.var 1)) :=
  .impI (.impE .h₁ (.andI               -- intro hP; apply h; constructor
    (.impI (.impE (.andE₁ .h₁)          -- · intro k; apply hP.1
      (.orE .h₀ (.orI₂ .h₀) (.orI₁ .h₀))))  --   k.symm
    (.impI (.impE (.andE₂ .h₁) (.impI   -- · intro k; apply hP.2; intro hb
      (.impE (.andE₂ (.impE .h₁ .h₀)) (.andE₁ (.impE .h₁ .h₀))))))))  --   (k hb).2 (k hb).1

/-- The two variable form at `a, c` gives the three variable one.  Its premise
holds: `a ∨ b` follows from either of `¬ a → c` and `a → c`, the first giving
`b → c` since `b` refutes `a`, and either case of `a ∨ b` decides `a`; and
`c → (a ∧ b)` being refuted refutes `¬ c`.  Of the resulting `a ∨ ¬ a`, `¬ a`
gives `a ∨ b` through `a → c`. -/
theorem noForkUp2x2_ent_noForkUp2x2Var3 :
    Ent (noForkUp2x2Form (.var 0) (.var 2)) (noForkUp2x2Var3Form (.var 0) (.var 1) (.var 2)) :=
  .impI (.cut (p := .imp (.var 1) (Form.neg (.var 0)))  -- intro hQ; have k : b → ¬ a
    (.impI (.impI (.impE (.andE₂ .h₂) (.impI (.andI .h₁ .h₂)))))
                                        --   fun hb ha => hQ.2 (fun _ => ⟨ha, hb⟩)
    (.orE (.impE .h₂ (.andI             -- cases h ⟨_, _⟩
      (.impI (.orE (.impE (.andE₁ .h₂)  -- · intro hc; cases hQ.1 (by cases hc
          (.orE .h₀                     --     | inl f =>
            (.orI₂ (.impI (.impE .h₁ (.impE .h₃ .h₀))))  --   Or.inr (fun hb => f (k hb))
            (.orI₁ .h₀)))               --     | inr g => Or.inl g)
        (.orI₁ .h₀)                     --   | inl ha => Or.inl ha
        (.orI₂ (.impE .h₂ .h₀))))       --   | inr hb => Or.inr (k hb)
      (.impI (.impE (.andE₂ .h₂)        -- · fun hnc => hQ.2 (fun hc => absurd hc hnc)
        (.impI (.flsE (.impE .h₁ .h₀)))))))
      (.orI₁ .h₀)                       -- | inl ha => Or.inl ha
      (.impE (.andE₁ .h₂) (.orI₁ (.impI (.flsE (.impE .h₁ .h₀)))))))
                                        -- | inr hna => hQ.1 (Or.inl (fun ha => absurd ha hna))

theorem noForkUp2x2_equiv_noForkUp2x2Var3 :
    SchemaEquiv (noForkUp2x2Form (.var 0) (.var 1))
      (noForkUp2x2Var3Form (.var 0) (.var 1) (.var 2)) :=
  ⟨.of_ent noForkUp2x2_ent_noForkUp2x2Var3 ⟨Form.args [.var 0, .var 2], rfl⟩,
   .of_ent noForkUp2x2Var3_ent_noForkUp2x2 ⟨Form.args [.var 0, Form.neg (.var 0), .var 1], rfl⟩⟩

/-! ## `pierce₁₂OrLuk₁₂Form` and the principles of its three smallest refuters

Among the finite frames, `pierce₁₂OrLuk₁₂Form` is refuted by three smallest
ones: the uneven kite, the diamond with a hair and the tall fork.  Each of them
is the only smallest refuter of a principle of its own, `noKiteUp1x2Form`,
`noDiamondHairForm` and `noForkUp2x2Form`, and each of those follows from a
single instance of `pierce₁₂OrLuk₁₂Form`.  The instances share a pattern: the
Łukasiewicz disjunct's premise is provable or granted, so that disjunct gives
the conclusion, or directly what the premise needs; the Peirce disjunct instead
discharges the principle's premise. -/

/-- At `a ∨ ¬ a, b`, Łukasiewicz's premise `¬ (a ∨ ¬ a) → ¬ b` is provable
(`nn_em`), leaving `b → a ∨ ¬ a`, the conclusion's right disjunct.  Peirce's law
there gives `noKiteUp1x2Form`'s premise, Peirce's law at `a` and `b ∨ ¬ b`:
given `j : (a → b ∨ ¬ b) → a`, it decides `a`, from an arrow `k` out of
`a ∨ ¬ a` into `b` through `fun ha => Or.inl (k (Or.inl ha))`.  The resulting
`a ∨ b` gives the conclusion either way. -/
theorem pierce₁₂OrLuk₁₂_ent_noKiteUp1x2 :
    Ent (pierce₁₂OrLuk₁₂Form (excludedMiddleForm (.var 0)) (.var 1))
      (noKiteUp1x2Form (.var 0) (.var 1)) :=
  .impI (.orE .h₁                       -- intro h; cases hPL
    (.orE (.impE .h₁ (.impI             -- | inl pe => cases h (fun j => …)
        (.orE (.impE .h₁ (.impI         --     cases pe (fun k =>
            (.orI₁ (.impE .h₁ (.impI    --       Or.inl (j (fun ha =>
              (.orI₁ (.impE .h₁ (.orI₁ .h₀))))))))  --  Or.inl (k (Or.inl ha)))))
          .h₀                           --     | inl ha => ha
          (.impE .h₁ (.impI (.flsE (.impE .h₁ .h₀)))))))  -- | inr hna => j (absurd · hna)
      (.orI₂ (.impI (.orI₁ .h₁)))       --   | inl ha => Or.inr (fun _ => Or.inl ha)
      (.orI₁ .h₀))                      --   | inr hb => Or.inl hb
    (.orI₂ (.impE .h₀ (.impI (.flsE (.impE (nn_em _) .h₀))))))
                                        -- | inr lk => Or.inr (lk (fun hn => absurd hn (nn_em _)))

/-- At `b, a`, `¬ ¬ b` grants Łukasiewicz's premise `¬ b → ¬ a`, leaving
`a → b`; and it lets Peirce's law give `¬ a → b`, since under `¬ a` an arrow
`b → a` refutes `b`.  Either implication is a disjunct of what the premise of
`noForkUp2x2Form` asks for excluded middle at `a`. -/
theorem pierce₁₂OrLuk₁₂_ent_noForkUp2x2 :
    Ent (pierce₁₂OrLuk₁₂Form (.var 1) (.var 0)) (noForkUp2x2Form (.var 0) (.var 1)) :=
  .impI (.orE .h₁                       -- intro hP; cases hPL
    (.impE (.andE₁ .h₁) (.orI₁ (.impI   -- | inl pe => hP.1 (Or.inl (fun hna =>
      (.impE .h₁ (.impI (.flsE (.impE (.andE₂ .h₃)  --   pe (fun k => absurd (hP.2 (fun hb =>
        (.impI (.impE .h₂ (.impE .h₁ .h₀))))))))))  --   hna (k hb))))))
    (.impE (.andE₁ .h₁) (.orI₂ (.impE .h₀  -- | inr lk => hP.1 (Or.inr (lk (fun hnb =>
      (.impI (.flsE (.impE (.andE₂ .h₂) .h₀)))))))  --   absurd hnb hP.2)))

/-- At `s = (a → ¬ b) ∨ (b ∧ (¬ a → a))` and `a`, Łukasiewicz's premise
`¬ s → ¬ a` is provable, since `a` makes `¬ b` give the first disjunct of `s`
and `b` the second; so `a` gives `s`, and `s` gives `b ∨ ¬ b`, the conclusion's
right disjunct.  Peirce's law gives the premise of `noDiamondHairForm`: under
`b`, an arrow `k` out of `s` into `a` yields `¬ a → a`, through the first
disjunct, so `s` holds through the second, and `s` then decides `¬ a` or gives
`¬ a → a`.  The resulting `a ∨ b` gives the conclusion either way. -/
theorem pierce₁₂OrLuk₁₂_ent_noDiamondHair :
    Ent (pierce₁₂OrLuk₁₂Form
        (.or (.imp (.var 0) (Form.neg (.var 1)))
          (.and (.var 1) (.imp (Form.neg (.var 0)) (.var 0))))
        (.var 0))
      (noDiamondHairForm (.var 0) (.var 1)) :=
  .impI (.orE .h₁                       -- intro h; cases hPL
    (.orE (.impE .h₁ (.impI             -- | inl pe => cases h (fun hb => …)
        (.orE (.impE .h₁ (.impI         --     cases pe (fun k => Or.inr ⟨hb, fun hna =>
            (.orI₂ (.andI .h₁ (.impI (.impE .h₁ (.orI₁ (.impI (.flsE (.impE .h₁ .h₀))))))))))
                                        --       k (Or.inl (fun ha => absurd ha hna))⟩)
          (.orI₁ (.impI (.impE (.impE .h₁ .h₀) .h₂)))  -- | inl f => Or.inl (fun ha => f ha hb)
          (.orI₂ (.andE₂ .h₀)))))       --     | inr p => Or.inr p.2
      (.orI₁ .h₀)                       --   | inl ha => Or.inl ha
      (.orI₂ (.impI (.orI₁ .h₁))))      --   | inr hb => Or.inr (fun _ => Or.inl hb)
    (.orI₂ (.impI (.orE                 -- | inr lk => Or.inr (fun ha => cases lk (…) ha
      (.impE (.impE .h₁ (.impI (.impI (.impE .h₁ (.orI₁ (.impI (.impI
          (.impE .h₃ (.orI₂ (.andI .h₀ (.impI .h₃))))))))))) .h₀)
                                        --   fun hns ha' => hns (Or.inl (fun _ hb =>
                                        --     hns (Or.inr ⟨hb, fun _ => ha'⟩)))
      (.orI₂ (.impE .h₀ .h₁))           --   | inl f => Or.inr (f ha)
      (.orI₁ (.andE₁ .h₀))))))          --   | inr p => Or.inl p.1

/-- **`pierce₁₂OrLuk₁₂Form` derives `noKiteUp1x2Form`.** -/
theorem derives_noKiteUp1x2_of_pierce₁₂OrLuk₁₂ :
    DerivesFromSchema (pierce₁₂OrLuk₁₂Form (.var 0) (.var 1)) (noKiteUp1x2Form (.var 0) (.var 1)) :=
  .of_ent pierce₁₂OrLuk₁₂_ent_noKiteUp1x2 ⟨Form.args [excludedMiddleForm (.var 0), .var 1], rfl⟩

/-- **`pierce₁₂OrLuk₁₂Form` derives `noForkUp2x2Form`.** -/
theorem derives_noForkUp2x2_of_pierce₁₂OrLuk₁₂ :
    DerivesFromSchema (pierce₁₂OrLuk₁₂Form (.var 0) (.var 1)) (noForkUp2x2Form (.var 0) (.var 1)) :=
  .of_ent pierce₁₂OrLuk₁₂_ent_noForkUp2x2 ⟨Form.args [.var 1, .var 0], rfl⟩

/-- **`pierce₁₂OrLuk₁₂Form` derives `noDiamondHairForm`.** -/
theorem derives_noDiamondHair_of_pierce₁₂OrLuk₁₂ :
    DerivesFromSchema (pierce₁₂OrLuk₁₂Form (.var 0) (.var 1))
      (noDiamondHairForm (.var 0) (.var 1)) :=
  .of_ent pierce₁₂OrLuk₁₂_ent_noDiamondHair
    ⟨Form.args [.or (.imp (.var 0) (Form.neg (.var 1)))
      (.and (.var 1) (.imp (Form.neg (.var 0)) (.var 0))), .var 0], rfl⟩

/-! ## `pierce₁₂OrLuk₁₂Form` from the principles of its three smallest refuters

Conversely, four instances of the three principles together derive
`pierce₁₂OrLuk₁₂Form`.  Write `π` for Peirce's law `((a → b) → a) → a`, `λ`
for Łukasiewicz's `(¬ a → ¬ b) → (b → a)`, so that the goal is `π ∨ λ`, and

* `n = ¬ (a ∧ ¬ b)`, `τ = a → b ∨ ¬ b` and `κ`, Peirce's law at `a` and
  `b ∨ ¬ b`;
* `U = π ∨ λ → λ ∨ (a → b)` and `V = λ → n ∨ ¬ n`.

The instances are `noKiteUp1x2Form` at `π ∧ (λ ∨ (a → b)), λ` and at `λ ∧ κ, τ`,
`noDiamondHairForm` at `n, λ` and `noForkUp2x2Form` at `n, a ∨ ¬ a`.  Each
proves one step towards `π ∨ λ`, proving its own premise from what the earlier
steps grant and turning both disjuncts of its conclusion into `π ∨ λ`:

* the first kite gives `(U → π ∨ λ) → π ∨ λ`;
* the second kite gives `U → (κ → π ∨ λ) → π ∨ λ`;
* the hair gives `U → (V → π ∨ λ) → π ∨ λ`;
* the fork gives `U → κ → V → π ∨ λ`;

and the four chain to `π ∨ λ`.

Read in a finite model where no two points satisfy the same formulas, the chain
is a case split at a highest point `w` where `π ∨ λ` fails.  Such a point sees a
point `p` where `b` holds and `a` fails but `¬ a` does not, `λ` failing exactly
at the points that see `p`, and it sees a *Peirce gap*, a point where
`(a → b) → a` holds but `a` does not.

* `U` fails when a proper successor of `w` sees `p` and a point of `a ∧ ¬ b`:
  the uneven kite.
* Otherwise `κ` fails when `w` sees a Peirce gap one of whose successors in `a`
  is not maximal: the uneven kite with its branches swapped.
* Otherwise `V` fails when `w` sees a point that sees the point of `a ∧ ¬ b`
  and another maximal point, but not `p`: the diamond with a hair.
* Otherwise the fork's instance fails, on the tall fork.

Parts of the arguments, `λ ∨ (a → b)`, `κ` and `a ∨ ¬ a`, hold on the points
around the configuration, and where such a point still defeats an instance it
forces an earlier case.  That is what lets one fixed list of instances serve
every frame. -/

namespace PierceLukOfThree

/-- `¬ (a ∧ ¬ b)`: no point above sees `a` true and `b` refuted. -/
abbrev notAndNot (p q : Form) : Form := Form.neg (.and p (Form.neg q))

/-- `a → b ∨ ¬ b`. -/
abbrev impEm (p q : Form) : Form := .imp p (excludedMiddleForm q)

/-- `κ`: Peirce's law at `a` and `b ∨ ¬ b`. -/
abbrev peirceEm (p q : Form) : Form := peirceForm p (excludedMiddleForm q)

/-- The first kite's left argument, `π ∧ (λ ∨ (a → b))`. -/
abbrev kiteArg₁ (p q : Form) : Form := .and (peirceForm p q) (.or (lukForm p q) (.imp p q))

/-- The second kite's left argument, `λ ∧ κ`. -/
abbrev kiteArg₂ (p q : Form) : Form := .and (lukForm p q) (peirceEm p q)

/-- `U = PL → λ ∨ (a → b)`. -/
abbrev stepU (p q : Form) : Form := .imp (pierce₁₂OrLuk₁₂Form p q) (.or (lukForm p q) (.imp p q))

/-- `V = λ → n ∨ ¬ n`. -/
abbrev stepV (p q : Form) : Form := .imp (lukForm p q) (excludedMiddleForm (notAndNot p q))

/-! ### Small steps -/

/-- `(a → b) → a` gives `λ`: `fun _ hb => hc (fun _ => hb)`. -/
theorem luk_of_imp_imp (p q : Form) : Ent (.imp (.imp p q) p) (lukForm p q) :=
  .impI (.impI (.impE .h₂ (.impI .h₁)))

/-- `b` gives `π`: `fun hc => hc (fun _ => hb)`. -/
theorem peirce_of_right (p q : Form) : Ent q (peirceForm p q) :=
  .impI (.impE .h₀ (.impI .h₂))

/-- `b` gives `π ∧ (λ ∨ (a → b))`: `⟨peirce_of_right hb, Or.inr (fun _ => hb)⟩`. -/
theorem kiteArg₁_of_right (p q : Form) : Ent q (kiteArg₁ p q) :=
  .andI ((peirce_of_right _ _).mp .h₀) (.orI₂ (.impI .h₁))

/-- `¬ λ` is absurd: it refutes `a` (which gives `λ`), and `¬ a` gives `λ`. -/
theorem neg_luk_ent_fls (p q : Form) : Ent (Form.neg (lukForm p q)) .fls :=
  .impE .h₀ (.impI (.impI              -- apply hnl; intro hi hb
    (.flsE (.impE (.impE .h₁           -- absurd hb (hi (fun ha => hnl (fun _ _ => ha)))
      (.impI (.impE .h₃ (.impI (.impI .h₂))))) .h₀))))

/-- `¬ (a → b ∨ ¬ b)` is absurd, `b ∨ ¬ b` being irrefutable. -/
theorem neg_imp_em_ent_fls (p q : Form) : Ent (Form.neg (.imp p (excludedMiddleForm q))) .fls :=
  .impE (nn_em q) (.impI (.impE .h₁ (.impI .h₁)))  -- nn_em (fun he => hn (fun _ => he))

/-- `a → b` gives `n`: `fun h => h.2 (hab h.1)`. -/
theorem notAndNot_of_imp (p q : Form) : Ent (.imp p q) (notAndNot p q) :=
  .impI (.impE (.andE₂ .h₀) (.impE .h₁ (.andE₁ .h₀)))

/-- `b` gives `n`: `fun h => h.2 hb`. -/
theorem notAndNot_of_right (p q : Form) : Ent q (notAndNot p q) :=
  .impI (.impE (.andE₂ .h₀) .h₁)

/-- `¬ n` gives `λ`: `fun _ hb => absurd (notAndNot_of_right hb) hnn`. -/
theorem luk_of_nn (p q : Form) : Ent (Form.neg (notAndNot p q)) (lukForm p q) :=
  .impI (.impI (.flsE (.impE .h₂ ((notAndNot_of_right _ _).mp .h₀))))

/-- `n → a ∨ ¬ a` gives `λ`: from `b`, `n` holds, and `¬ a` would refute `b`. -/
theorem luk_of_notAndNot_imp_em (p q : Form) :
    Ent (.imp (notAndNot p q) (excludedMiddleForm p)) (lukForm p q) :=
  .impI (.impI (.orE (.impE .h₂ ((notAndNot_of_right _ _).mp .h₀))
                                        -- intro hi hb; cases k (notAndNot_of_right hb)
    .h₀                                 -- | inl ha => ha
    (.flsE (.impE (.impE .h₂ .h₀) .h₁))))  -- | inr hna => absurd hb (hi hna)

/-- An arrow into `λ ∨ ¬ λ`, out of anything `b` gives, gives `λ`: under `b` it
decides `λ`, and `¬ λ` is absurd. -/
theorem luk_of_imp_emLuk {p q x : Form} (hx : Ent q x) :
    Ent (.imp x (excludedMiddleForm (lukForm p q))) (lukForm p q) :=
  .impI (.impI (.orE (.impE .h₂ (hx.mp .h₀))  -- intro hi hb; cases k (hx hb)
    (.impE (.impE .h₀ .h₂) .h₁)         -- | inl hl => hl hi hb
    (.flsE ((neg_luk_ent_fls _ _).mp .h₀))))  -- | inr hnl => absurd

/-- From `a → b ∨ ¬ b` and `n`, `a → b`. -/
theorem imp_of_impEm_notAndNot (p q : Form) : Ent (impEm p q) (.imp (notAndNot p q) (.imp p q)) :=
  .impI (.impI (.orE (.impE .h₂ .h₀)   -- intro hn ha; cases g ha
    .h₀                                -- | inl hb => hb
    (.flsE (.impE .h₂ (.andI .h₁ .h₀)))))  -- | inr hnb => absurd ⟨ha, hnb⟩ hn

/-- `(¬ ¬ x → ¬ x) → ¬ x`, at `x = a ∧ ¬ b`: `fun hx => k (fun hnx => hnx hx) hx`. -/
theorem notAndNot_of_imp_self (p q : Form) :
    Ent (.imp (Form.neg (notAndNot p q)) (notAndNot p q)) (notAndNot p q) :=
  .impI (.impE (.impE .h₁ (.impI (.impE .h₀ .h₁))) .h₀)

/-! ### Peirce's law when no Peirce gap is in sight -/

/-- `n` and `κ` give `π`: under `κ` it is enough to prove `a` from
`a → b ∨ ¬ b`, which with `n` is `a → b`. -/
theorem peirce_of_notAndNot_peirceEm (p q : Form) :
    Ent (notAndNot p q) (.imp (peirceEm p q) (peirceForm p q)) :=
  .impI (.impI (.impE .h₁ (.impI       -- intro hk hc; apply hk; intro g
    (.impE .h₁ (.impE ((imp_of_impEm_notAndNot _ _).mp .h₀) .h₃)))))  -- hc (… g hn)

/-- `¬ n → a ∨ ¬ a`, `V` and `κ` give `π`.  Given `(a → b) → a`, it gives `λ`,
so `V` decides `n`: with `n` as before, with `¬ n` excluded middle at `a`. -/
theorem peirce_of_three (p q : Form) :
    Ent (.imp (Form.neg (notAndNot p q)) (excludedMiddleForm p))
      (.imp (stepV p q) (.imp (peirceEm p q) (peirceForm p q))) :=
  .impI (.impI (.impI                  -- intro hV hk hc
    (.orE (.impE .h₂ ((luk_of_imp_imp _ _).mp .h₀))  -- cases hV (luk_of_imp_imp hc)
      (.impE (.impE ((peirce_of_notAndNot_peirceEm _ _).mp .h₀) .h₂) .h₁)
                                       -- | inl hn => peirce_of_notAndNot_peirceEm hn hk hc
      (.orE (.impE .h₄ .h₀)            -- | inr hnn => cases h hnn
        .h₀                            --   | inl ha => ha
        (.impE .h₂ (.impI (.flsE (.impE .h₁ .h₀))))))))  -- | inr hna => hc (absurd · hna)

/-! ### The four steps -/

/-- **The fork at `n, a ∨ ¬ a`**: `U → κ → V → PL`.  Its premise holds: an
arrow `¬ n → a ∨ ¬ a` gives `π` (with `V`, `κ`), so `U` decides between `λ`
(then `V`) and `a → b` (then `n`); an arrow `n → a ∨ ¬ a` gives `λ`, then `V`.
Then `n` gives `π` with `κ`, and `¬ n` gives `λ`. -/
theorem fork_step (p q : Form) :
    Ent (noForkUp2x2Form (notAndNot p q) (excludedMiddleForm p))
      (.imp (stepU p q) (.imp (peirceEm p q) (.imp (stepV p q) (pierce₁₂OrLuk₁₂Form p q)))) :=
  .impI (.impI (.impI                  -- intro hU hk hV
    (.orE (.impE .h₃ (.andI            -- cases hF ⟨_, nn_em⟩
      (.impI (.orE .h₀                 --   intro hD; cases hD
        (.orE (.impE .h₄ (.orI₁ (.impE (.impE ((peirce_of_three _ _).mp .h₀) .h₂) .h₃)))
                                       --   | inl h => cases hU (Or.inl (peirce_of_three h hV hk))
          (.impE .h₃ .h₀)              --     | inl hl => hV hl
          (.orI₁ ((notAndNot_of_imp _ _).mp .h₀)))  -- | inr hab => Or.inl (notAndNot_of_imp hab)
        (.impE .h₂ ((luk_of_notAndNot_imp_em _ _).mp .h₀))))  -- | inr h => hV (… h)
      (nn_em _)))
      (.orI₁ (.impE ((peirce_of_notAndNot_peirceEm _ _).mp .h₀) .h₂))
                                       -- | inl hn => Or.inl (… hn hk)
      (.orI₂ ((luk_of_nn _ _).mp .h₀)))))  -- | inr hnn => Or.inr (luk_of_nn hnn)

/-- **The hair at `n, λ`**: `U → (V → PL) → PL`.  Its premise
`λ → ¬ n ∨ (¬ n → n)` is `V`, whence `PL`, and `U` turns that into `n ∨ λ`.
Then `n` gives `V` outright, and `n → λ ∨ ¬ λ` gives `λ`. -/
theorem hair_step (p q : Form) :
    Ent (noDiamondHairForm (notAndNot p q) (lukForm p q))
      (.imp (stepU p q)
        (.imp (.imp (stepV p q) (pierce₁₂OrLuk₁₂Form p q)) (pierce₁₂OrLuk₁₂Form p q))) :=
  .impI (.impI                         -- intro hU hW
    (.orE (.impE .h₂ (.impI            -- cases hH (fun hy => …)
      (.orE (.impE .h₂ (.impE .h₁ (.impI  --   cases hU (hW (fun hl => …))
          (.orE (.impE .h₁ .h₀)         --     cases hy hl
            (.orI₂ .h₀)                 --     | inl hnn => Or.inr hnn
            (.orI₁ ((notAndNot_of_imp_self _ _).mp .h₀))))))  -- | inr k => Or.inl (… k)
        (.orI₂ .h₀)                     --   | inl hl => Or.inr hl
        (.orI₁ ((notAndNot_of_imp _ _).mp .h₀)))))  -- | inr hab => Or.inl (notAndNot_of_imp hab)
      (.impE .h₁ (.impI (.orI₁ .h₁)))   -- | inl hn => hW (fun _ => Or.inl hn)
      (.orI₂ ((luk_of_imp_emLuk (notAndNot_of_right _ _)).mp .h₀))))
                                        -- | inr k => Or.inr (luk_of_imp_emLuk … k)

/-- Peirce's law at `λ ∧ κ, τ ∨ ¬ τ` gives `κ`: given `τ → a`, an arrow
`λ ∧ κ → τ ∨ ¬ τ` yields `τ` (from `a`, both `λ` and `κ` hold), hence `a`, hence
`λ ∧ κ`. -/
theorem peirceEm_of_peirce_kiteArg₂ (p q : Form) :
    Ent (peirceForm (kiteArg₂ p q) (excludedMiddleForm (impEm p q))) (peirceEm p q) :=
  .impI (.impE (.andE₂ (.impE .h₁ (.impI  -- intro f; apply (hQ (fun g => …)).2 f
    (.cut (p := p)                      -- have ha : a := f (fun ha => …)
      (.impE .h₁ (.impI (.orE (.impE .h₁ (.andI (.impI (.impI .h₂)) (.impI .h₁)))
                                        --   cases g ⟨fun _ _ => ha, fun _ => ha⟩
        (.impE .h₀ .h₁)                 --   | inl ht => ht ha
        (.flsE ((neg_imp_em_ent_fls _ _).mp .h₀)))))  -- | inr hnt => absurd
      (.andI (.impI (.impI .h₂)) (.impI .h₁))))))  -- ⟨fun _ _ => ha, fun _ => ha⟩
    .h₀)

/-- `τ → (λ ∧ κ) ∨ ¬ (λ ∧ κ)` gives `λ`: from `b`, `τ` and `κ` hold, and
`¬ (λ ∧ κ)` would then refute `λ`. -/
theorem luk_of_impEm_imp_em_kiteArg₂ (p q : Form) :
    Ent (.imp (impEm p q) (excludedMiddleForm (kiteArg₂ p q))) (lukForm p q) :=
  .impI (.impI (.orE (.impE .h₂ (.impI (.orI₁ .h₁)))  -- intro hi hb; cases k (fun _ => Or.inl hb)
    (.impE (.impE (.andE₁ .h₀) .h₂) .h₁)             -- | inl hs => hs.1 hi hb
    (.flsE ((neg_luk_ent_fls _ _).mp (.impI (.impE .h₁  -- | inr hns => absurd (hns ⟨·, _⟩)
      (.andI .h₀ (.impI (.impE .h₀ (.impI (.orI₁ .h₄)))))))))))

/-- **The second kite, at `λ ∧ κ, τ`**: `U → (κ → PL) → PL`.  Its premise:
Peirce at `λ ∧ κ, τ ∨ ¬ τ` gives `κ`, so `PL`, and `U` turns that into
`λ ∧ κ` or `τ`.  Then `τ` gives `κ`, and `τ → (λ ∧ κ) ∨ ¬ (λ ∧ κ)` gives
`λ`. -/
theorem kite2_step (p q : Form) :
    Ent (noKiteUp1x2Form (kiteArg₂ p q) (impEm p q))
      (.imp (stepU p q)
        (.imp (.imp (peirceEm p q) (pierce₁₂OrLuk₁₂Form p q)) (pierce₁₂OrLuk₁₂Form p q))) :=
  .impI (.impI                         -- intro hU hW
    (.orE (.impE .h₂ (.impI            -- cases hK (fun hQ => …)
      (.cut (p := peirceEm p q) ((peirceEm_of_peirce_kiteArg₂ _ _).mp .h₀)  -- have hk := … hQ
        (.orE (.impE .h₃ (.impE .h₂ .h₀))  -- cases hU (hW hk)
          (.orI₁ (.andI .h₀ .h₁))       -- | inl hl => Or.inl ⟨hl, hk⟩
          (.orI₂ (.impI (.orI₁ (.impE .h₁ .h₀))))))))  -- | inr hab => Or.inr (Or.inl ∘ hab)
      (.impE .h₁ (.impI (.impE .h₀ .h₁)))  -- | inl ht => hW (fun f => f ht)
      (.orI₂ ((luk_of_impEm_imp_em_kiteArg₂ _ _).mp .h₀))))  -- | inr k => Or.inr (luk_of_… k)

/-- Peirce's law at `π ∧ (λ ∨ (a → b)), λ ∨ ¬ λ` gives `U`: given `π`, the
arrow `… → λ ∨ ¬ λ` gives `λ`, so `π ∧ (λ ∨ (a → b))`, whose right half is
the goal. -/
theorem stepU_of_peirce_kiteArg₁ (p q : Form) :
    Ent (peirceForm (kiteArg₁ p q) (excludedMiddleForm (lukForm p q))) (stepU p q) :=
  .impI (.orE .h₀                      -- intro hPL; cases hPL
    (.andE₂ (.impE .h₂ (.impI          -- | inl hπ => (hQ (fun g => …)).2
      (.andI .h₁ (.orI₁ ((luk_of_imp_emLuk (kiteArg₁_of_right _ _)).mp .h₀))))))
                                       -- ⟨hπ, Or.inl (luk_of_imp_emLuk … g)⟩
    (.orI₁ .h₀))                       -- | inr hl => Or.inl hl

/-- `λ → s ∨ ¬ s` for `s = π ∧ (λ ∨ (a → b))` gives `π`: from `(a → b) → a`,
`λ` holds; `s` gives `π`, and `¬ s` refutes `a`, so `a → b`. -/
theorem peirce_of_luk_imp_em_kiteArg₁ (p q : Form) :
    Ent (.imp (lukForm p q) (excludedMiddleForm (kiteArg₁ p q))) (peirceForm p q) :=
  .impI (.orE (.impE .h₁ ((luk_of_imp_imp _ _).mp .h₀))  -- intro hc; cases k (luk_of_imp_imp hc)
    (.impE (.andE₁ .h₀) .h₁)             -- | inl hs => hs.1 hc
    (.impE .h₁ (.impI (.flsE (.impE .h₁  -- | inr hns => hc (fun ha => absurd ⟨_, _⟩ hns)
      (.andI (.impI .h₁) (.orI₁ (.impI (.impI .h₂)))))))))

/-- **The first kite, at `π ∧ (λ ∨ (a → b)), λ`**: `(U → PL) → PL`.  Its
premise: Peirce at the arguments gives `U`, so `PL`, which with `U` is
`π ∧ (λ ∨ (a → b))` or `λ`.  Then `λ` is `PL`, and `λ → s ∨ ¬ s` gives `π`. -/
theorem kite1_step (p q : Form) :
    Ent (noKiteUp1x2Form (kiteArg₁ p q) (lukForm p q))
      (.imp (.imp (stepU p q) (pierce₁₂OrLuk₁₂Form p q)) (pierce₁₂OrLuk₁₂Form p q)) :=
  .impI                                -- intro hW
    (.orE (.impE .h₁ (.impI            -- cases hK (fun hQ => …)
      (.cut (p := stepU p q) ((stepU_of_peirce_kiteArg₁ _ _).mp .h₀)  -- have hU := … hQ
        (.orE (.impE .h₂ .h₀)          -- cases hW hU
          (.orI₁ (.andI .h₀ (.impE .h₁ (.orI₁ .h₀))))  -- | inl hπ => Or.inl ⟨hπ, hU (Or.inl hπ)⟩
          (.orI₂ .h₀)))))              -- | inr hl => Or.inr hl
      (.orI₂ .h₀)                      -- | inl hl => Or.inr hl
      (.orI₁ ((peirce_of_luk_imp_em_kiteArg₁ _ _).mp .h₀)))  -- | inr k => Or.inl (…)

/-! ### The four instances together -/

/-- The four instances together give `π ∨ λ`: the first kite reduces it to
`U → π ∨ λ`, the second kite to `κ → π ∨ λ` under `U`, the hair to `V → π ∨ λ`,
and the fork proves that. -/
theorem four_ent (p q : Form) :
    [noKiteUp1x2Form (kiteArg₁ p q) (lukForm p q), noKiteUp1x2Form (kiteArg₂ p q) (impEm p q),
      noDiamondHairForm (notAndNot p q) (lukForm p q),
      noForkUp2x2Form (notAndNot p q) (excludedMiddleForm p)] ⊢
      pierce₁₂OrLuk₁₂Form p q :=
  .impE ((kite1_step _ _).mp .h₀)       -- apply kite1_step; intro hU
    (.impI (.impE (.impE ((kite2_step _ _).mp .h₂) .h₀)  -- apply kite2_step hU; intro hk
      (.impI (.impE (.impE ((hair_step _ _).mp .h₄) .h₁)  -- apply hair_step hU; intro hV
        (.impI (.impE (.impE (.impE ((fork_step _ _).mp (.nth 6 rfl)) .h₂) .h₁) .h₀))))))
                                        -- fork_step hU hk hV

end PierceLukOfThree

open PierceLukOfThree in
/-- **The three principles derive `pierce₁₂OrLuk₁₂Form`**, from two instances of
`noKiteUp1x2Form` and one each of the other two.  By
`DerivesFromSchemas.iff_conj`, so does their conjunction as a single schema. -/
theorem derives_pierce₁₂OrLuk₁₂_of_three :
    DerivesFromSchemas
      [noForkUp2x2Form (.var 0) (.var 1), noKiteUp1x2Form (.var 0) (.var 1),
        noDiamondHairForm (.var 0) (.var 1)]
      (pierce₁₂OrLuk₁₂Form (.var 0) (.var 1)) := by
  refine ⟨_, ?_, four_ent (.var 0) (.var 1)⟩
  intro r hr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
      Form.args [kiteArg₁ (.var 0) (.var 1), lukForm (.var 0) (.var 1)], rfl⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
      Form.args [kiteArg₂ (.var 0) (.var 1), impEm (.var 0) (.var 1)], rfl⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      Form.args [notAndNot (.var 0) (.var 1), lukForm (.var 0) (.var 1)], rfl⟩
  · exact ⟨_, List.mem_cons_self ..,
      Form.args [notAndNot (.var 0) (.var 1), excludedMiddleForm (.var 0)], rfl⟩
