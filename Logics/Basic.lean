import Logics.Heyting

def ExcludedMiddleF := fun (a : Prop) => a ∨ ¬a

def PeirceF := fun a b : Prop => ((a → b) → a) → a

def NotNotF := fun a : Prop => ¬ ¬ a → a

def DeMorganNotAndNotF := fun a b : Prop => ¬ (¬ a ∧ ¬ b) → a ∨ b

def ImpOrF := fun a b : Prop => (a → b) → (¬ a ∨ b)

def ConsequentiaMirabilisF := fun a : Prop => (¬ a → a) → a

def LukasiewiczF := fun a b : Prop => (¬ a → ¬ b) → (b → a)

theorem ImpOrF_em (a : Prop) : ImpOrF a a → ExcludedMiddleF a := by
  intro hImpOr; apply Or.symm; apply hImpOr; exact id

theorem emF_ImpOrF (a b : Prop) : ExcludedMiddleF a → ImpOrF a b := by
  intro hEx hab
  cases hEx
  case inl ha => exact Or.inr (hab ha)
  case inr hna => exact Or.inl hna

theorem emF_demorganF (a b : Prop) : ExcludedMiddleF a → ExcludedMiddleF b → DeMorganNotAndNotF a b := by
  intro hExa hExb hn
  cases hExa
  case inl ha => exact Or.inl ha
  case inr hna =>
    cases hExb
    case inl hb => exact Or.inr hb
    case inr hnb => exact False.elim (hn ⟨hna, hnb⟩)

theorem demorganF_emF (a : Prop) : DeMorganNotAndNotF a (¬ a) → ExcludedMiddleF a := by
  intro hDe; apply hDe; intro h; exact h.right h.left

theorem emF_not_notF (a : Prop) : ExcludedMiddleF a → NotNotF a := by
  intro hEm nna
  cases hEm
  case inl ha => exact ha
  case inr hna => exact False.elim (nna hna)

theorem not_notF_emF (a : Prop) : NotNotF (a ∨ ¬ a) → ExcludedMiddleF a := by
  intro hnn; apply hnn; intro n
  have h := not_or.mp n
  exact h.right h.left

theorem emF_cmF (a : Prop) : ExcludedMiddleF a → ConsequentiaMirabilisF a := by
  intro hEm
  cases hEm
  case inl h => intro _; exact h
  case inr h => intro f; exact f h

theorem cmF_emF (a : Prop) : ConsequentiaMirabilisF (a ∨ ¬ a) → ExcludedMiddleF a := by
  intro hCm; apply hCm; intro hn
  have hn' := not_or.mp hn
  exact Or.inr hn'.left

theorem cmF_not_notF (a : Prop) : ConsequentiaMirabilisF a → NotNotF a := by
  intro hCm hnna; apply hCm; intro hna; contradiction

theorem not_notF_cmF (a : Prop) : NotNotF a → ConsequentiaMirabilisF a := by
  intro hnn hi; apply hnn; intro hna; exact hna (hi hna)

theorem cmF_peirceF (a b : Prop) : ConsequentiaMirabilisF a → PeirceF a b := by
  intro hCm hab; apply hCm; intro hna; apply hab; intro ha; contradiction

theorem peirceF_cmF (a : Prop) : PeirceF a (¬ a) → ConsequentiaMirabilisF a := by
  intro hPc h; apply hPc; intro hana; apply h; intro ha; exact hana ha ha

theorem lukF_not_notF (a : Prop) : LukasiewiczF a (¬ ¬ a) → NotNotF a := by
  intro hLuk; apply hLuk; intro hna hnna; exact hnna hna

theorem emF_lukF (a b : Prop) : ExcludedMiddleF a → LukasiewiczF a b := by
  intro hEx hn hb
  cases hEx
  case inl ha => exact ha
  case inr hna => exact False.elim (hn hna hb)

def PierceOrLukasiewiczF := fun (a b : Prop) => (((a → b) → a) → a) ∨ ((¬ a → ¬ b) → (b → a))

theorem emF_pierceOrLukF (a b : Prop) : ExcludedMiddleF a → PierceOrLukasiewiczF a b := by
  intro hEx; exact Or.inl (cmF_peirceF a b (emF_cmF a hEx))

theorem emF_pierceOrLukF' (a b : Prop) : ExcludedMiddleF b → PierceOrLukasiewiczF a b := by
  intro hEx
  cases hEx
  case inl hb => exact Or.inl (fun hi => hi (fun _ => hb))
  case inr hnb => exact Or.inr (fun _ hb => False.elim (hnb hb))

def DeMOrLukasiewiczF := fun (a b : Prop) => (¬ (¬ a ∧ ¬ b) → a ∨ b) ∨ ((¬ a → ¬ b) → (b → a))

theorem emF_demOrLukF (a b : Prop) : ExcludedMiddleF a → DeMOrLukasiewiczF a b := by
  intro hEx; exact Or.inr (emF_lukF a b hEx)

theorem emF_demOrLukF' (a b : Prop) : ExcludedMiddleF b → DeMOrLukasiewiczF a b := by
  intro hEx
  cases hEx
  case inl hb => exact Or.inl (fun _ => Or.inr hb)
  case inr hnb => exact Or.inr (fun _ hb => False.elim (hnb hb))

def ImpOrOrLukasiewiczF := fun (a b : Prop) => ((a → b) → (¬ a ∨ b)) ∨ ((¬ a → ¬ b) → (b → a))

theorem emF_impOrOrLukF (a b : Prop) : ExcludedMiddleF a → ImpOrOrLukasiewiczF a b := by
  intro hEx; exact Or.inl (emF_ImpOrF a b hEx)

theorem emF_impOrOrLukF' (a b : Prop) : ExcludedMiddleF b → ImpOrOrLukasiewiczF a b := by
  intro hEx
  cases hEx
  case inl hb => exact Or.inl (fun _ => Or.inr hb)
  case inr hnb => exact Or.inr (fun _ hb => False.elim (hnb hb))

/-! ## Underivability, formally

Everything above is a proof that one principle *follows* from another.  This
section does the opposite: it shows that certain principles cannot be proved at
all without assuming something classical.

The method is to allow more truth values than just true and false.  A Heyting
algebra is a set of truth values with operations for and, or, implies and false,
and `Fin 3` gives the smallest interesting one: three values ordered
`0 ⊏ 1 ⊏ 2`, where `0` means refuted, `2` means established, and the middle
value `1` means neither.  Negating the middle value lands on `0`, because
nothing refutes it, and that is exactly why `a ∨ ¬ a` fails to reach `2` there.

Soundness, proved in `Logics/Heyting.lean`, says that anything with a proof
takes the top value under every assignment.  Read backwards: a formula that
misses the top value somewhere has no proof.  Each theorem below picks an
assignment, computes, and concludes. -/

/-- Excluded middle is not derivable in intuitionistic propositional logic. -/
theorem em_not_derivable : ¬ ([] ⊢ .or (.var 0) (Form.neg (.var 0))) := by
  intro d
  have h := Derives.valid_of_derives d (Fin 3) (fun _ => (1 : Fin 3))
  exact absurd h (by decide)

/-- Double negation elimination is not derivable either. -/
theorem dne_not_derivable : ¬ ([] ⊢ .imp (Form.neg (Form.neg (.var 0))) (.var 0)) := by
  intro d
  have h := Derives.valid_of_derives d (Fin 3) (fun _ => (1 : Fin 3))
  exact absurd h (by decide)

/-- Nor is Peirce's law, the `PeirceF` of this file. -/
theorem peirce_not_derivable :
    ¬ ([] ⊢ .imp (.imp (.imp (.var 0) (.var 1)) (.var 0)) (.var 0)) := by
  intro d
  have h := Derives.valid_of_derives d (Fin 3) (fun n => if n = 0 then 1 else 0)
  exact absurd h (by decide)

/-! ## The tables, as theorems

The same three truth values also measure how strong the three combined
principles of this file are.  Each of the next three theorems says that its
principle reaches the top value for *every* pair of truth values, so every way
of instantiating it does too.  `em_not_top` says excluded middle does not.

Together they show the combined principles are genuinely weaker than excluded
middle: were excluded middle derivable from any instance of them, soundness
would force it to reach the top value as well, and it does not. -/

open HeytingAlgebra in
/-- `PierceOrLukasiewiczF`, every instance. -/
theorem pierceOrLuk_top (a b : Fin 3) :
    (((a ⇨ b) ⇨ a) ⇨ a) ⊔ ((neg a ⇨ neg b) ⇨ (b ⇨ a)) = ⊤ := by
  revert a b; decide

open HeytingAlgebra in
/-- `DeMOrLukasiewiczF`, every instance. -/
theorem deMOrLuk_top (a b : Fin 3) :
    (neg (neg a ⊓ neg b) ⇨ (a ⊔ b)) ⊔ ((neg a ⇨ neg b) ⇨ (b ⇨ a)) = ⊤ := by
  revert a b; decide

open HeytingAlgebra in
/-- `ImpOrOrLukasiewiczF`, every instance. -/
theorem impOrOrLuk_top (a b : Fin 3) :
    ((a ⇨ b) ⇨ (neg a ⊔ b)) ⊔ ((neg a ⇨ neg b) ⇨ (b ⇨ a)) = ⊤ := by
  revert a b; decide

open HeytingAlgebra in
/-- `ExcludedMiddleF`, by contrast, is not `⊤` throughout: it drops to `m`. -/
theorem em_not_top : ∃ a : Fin 3, a ⊔ neg a ≠ ⊤ :=
  ⟨1, Chain.em_fails (by decide) (by decide)⟩

/-! ## Longer chains

Three truth values do not separate the three combined principles from each
other; more values do.  `Fin 4` adds a second undecided value, `0 ⊏ 1 ⊏ 2 ⊏ 3`,
and there the principles part company.

The Peirce version still reaches the top value everywhere, in `Fin 4` and in
`Fin 5`.  The other two do not: both drop below the top at the single
assignment `a = 1`, `b = 2`.  So the Peirce version keeps working however many
intermediate values are added, while the De Morgan and `ImpOrF` versions stop
working as soon as there are two of them.

Excluded middle, meanwhile, still fails in all of these.  It fails in `Fin k`
for every `k` greater than two, since any value strictly between the bottom and
the top negates to the bottom and so cannot join back up to the top.  That is
`Chain.em_fails` in `Logics/Heyting.lean`, which holds at every such value in
every chain; `em_not_top_chain` below is the immediate consequence.  Only
`Fin 1` and `Fin 2` are classical, having no such value to begin with.  So the
separation above is not an artifact of the three value case: the combined
principles reach the top value in chains where excluded middle does not, no
matter how long the chain. -/

open HeytingAlgebra in
/-- Excluded middle fails in every chain with more than two values. -/
theorem em_not_top_chain {n : Nat} (hn : 2 ≤ n) : ∃ a : Fin (n + 1), a ⊔ neg a ≠ ⊤ :=
  ⟨⟨1, by omega⟩, Chain.em_fails Nat.zero_lt_one (by omega : 1 < n)⟩

open HeytingAlgebra in
/-- `PierceOrLukasiewiczF` still has no counterexample in the four element chain. -/
theorem pierceOrLuk_top_four (a b : Fin 4) :
    (((a ⇨ b) ⇨ a) ⇨ a) ⊔ ((neg a ⇨ neg b) ⇨ (b ⇨ a)) = ⊤ := by
  revert a b; decide

open HeytingAlgebra in
/-- Nor in the five element chain. -/
theorem pierceOrLuk_top_five (a b : Fin 5) :
    (((a ⇨ b) ⇨ a) ⇨ a) ⊔ ((neg a ⇨ neg b) ⇨ (b ⇨ a)) = ⊤ := by
  revert a b; decide

open HeytingAlgebra in
/-- `DeMOrLukasiewiczF`, by contrast, drops to `q` at `a = p`, `b = q`. -/
theorem deMOrLuk_not_top_four :
    (neg (neg (1 : Fin 4) ⊓ neg 2) ⇨ ((1 : Fin 4) ⊔ 2))
      ⊔ ((neg 1 ⇨ neg 2) ⇨ ((2 : Fin 4) ⇨ 1)) ≠ ⊤ := by
  decide

open HeytingAlgebra in
/-- And so does `ImpOrOrLukasiewiczF`, at the same instance. -/
theorem impOrOrLuk_not_top_four :
    (((1 : Fin 4) ⇨ 2) ⇨ (neg (1 : Fin 4) ⊔ 2))
      ⊔ ((neg 1 ⇨ neg 2) ⇨ ((2 : Fin 4) ⇨ 1)) ≠ ⊤ := by
  decide
