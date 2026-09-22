import Logics.ClassicalAxioms.AxiomDef

/-!
# Implications between the principles

Every proof here is intuitionistic, so each theorem says that one principle,
assumed at the arguments shown, yields another.  Three patterns account for
nearly all of them.

Excluded middle at either argument implies every combined principle, because
they all share `LukasiewiczF a b` as their right disjunct and `emF_lukF`
reaches it; the `emFb_` variants instead use `notF_lukF`, which gets there
from `¬ b` alone.

A principle at a *shifted* instance implies another at the plain one.  The
shifts are what make the combined principles interderivable: `¬ a ∨ b` and
`a ∨ b` relate the De Morgan and `ImpOrF` versions, `b ∨ (b → a)` relates the
De Morgan version to the swapped Peirce one, and `a → b` and `a ∨ b` place the
swapped `ImpOrF` version between two others.  In each case the shift makes the
left disjunct's own premise provable, so that disjunct collapses to a bare
disjunction whose cases can be dispatched separately.

Transposition is the third pattern, and it is trivial: `DeMorganNotAndNotF` is
symmetric in its arguments, so swapping Lukasiewicz's only transposes the whole
principle.
-/

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

theorem emF_notNotF (a : Prop) : ExcludedMiddleF a → NotNotF a := by
  intro hEm nna
  cases hEm
  case inl ha => exact ha
  case inr hna => exact False.elim (nna hna)

theorem notNotF_emF (a : Prop) : NotNotF (a ∨ ¬ a) → ExcludedMiddleF a := by
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

theorem cmF_notNotF (a : Prop) : ConsequentiaMirabilisF a → NotNotF a := by
  intro hCm hnna; apply hCm; intro hna; contradiction

theorem notNotF_cmF (a : Prop) : NotNotF a → ConsequentiaMirabilisF a := by
  intro hnn hi; apply hnn; intro hna; exact hna (hi hna)

theorem cmF_peirceF (a b : Prop) : ConsequentiaMirabilisF a → PeirceF a b := by
  intro hCm hab; apply hCm; intro hna; apply hab; intro ha; contradiction

theorem peirceF_cmF (a : Prop) : PeirceF a (¬ a) → ConsequentiaMirabilisF a := by
  intro hPc h; apply hPc; intro hana; apply h; intro ha; exact hana ha ha

theorem lukF_notNotF (a : Prop) : LukasiewiczF a (¬ ¬ a) → NotNotF a := by
  intro hLuk; apply hLuk; intro hna hnna; exact hnna hna

theorem emF_lukF (a b : Prop) : ExcludedMiddleF a → LukasiewiczF a b := by
  intro hEx hn hb
  cases hEx
  case inl ha => exact ha
  case inr hna => exact False.elim (hn hna hb)

theorem notF_lukF (a b : Prop) : ¬ b → LukasiewiczF a b := fun hnb _ hb => absurd hb hnb

theorem emFa_pierceOrLukF (a b : Prop) : ExcludedMiddleF a → PierceOrLukasiewiczF a b :=
  fun hEx => Or.inr (emF_lukF a b hEx)

theorem emFb_pierceOrLukF (a b : Prop) : ExcludedMiddleF b → PierceOrLukasiewiczF a b :=
  fun hEx => hEx.elim (fun hb => Or.inl (fun hi => hi (fun _ => hb)))
    (fun hnb => Or.inr (notF_lukF a b hnb))

theorem emFa_demorganOrLukF (a b : Prop) : ExcludedMiddleF a → DeMorganOrLukasiewiczF a b :=
  fun hEx => Or.inr (emF_lukF a b hEx)

theorem emFb_demorganOrLukF (a b : Prop) : ExcludedMiddleF b → DeMorganOrLukasiewiczF a b :=
  fun hEx => hEx.elim (fun hb => Or.inl (fun _ => Or.inr hb))
    (fun hnb => Or.inr (notF_lukF a b hnb))

theorem emFa_impOrOrLukF (a b : Prop) : ExcludedMiddleF a → ImpOrOrLukasiewiczF a b :=
  fun hEx => Or.inr (emF_lukF a b hEx)

theorem emFb_impOrOrLukF (a b : Prop) : ExcludedMiddleF b → ImpOrOrLukasiewiczF a b :=
  fun hEx => hEx.elim (fun hb => Or.inl (fun _ => Or.inr hb))
    (fun hnb => Or.inr (notF_lukF a b hnb))

theorem demorganOrLukF_impOrOrLukF (a b : Prop) :
    DeMorganOrLukasiewiczF a (¬ a ∨ b) → ImpOrOrLukasiewiczF a b := by
  intro h
  cases h
  case inl hDeM =>
    have hpre : ¬ (¬ a ∧ ¬ (¬ a ∨ b)) := fun hc => hc.right (Or.inl hc.left)
    refine Or.inl ?_
    intro hab
    cases hDeM hpre
    case inl ha => exact Or.inr (hab ha)
    case inr hnab => exact hnab
  case inr hLuk =>
    refine Or.inr ?_
    intro hnn hb
    have hnna : ¬ ¬ a := fun hna => hnn hna hb
    exact hLuk (fun hna => absurd hna hnna) (Or.inr hb)

theorem impOrOrLukF_demorganOrLukF (a b : Prop) :
    ImpOrOrLukasiewiczF a (a ∨ b) → DeMorganOrLukasiewiczF a b := by
  intro h
  cases h
  case inl hIO =>
    cases hIO Or.inl
    case inl hna =>
      refine Or.inr ?_
      intro hnn hb
      exact absurd hb (hnn hna)
    case inr hab => exact Or.inl (fun _ => hab)
  case inr hLuk =>
    refine Or.inr ?_
    intro hnn hb
    have hpre : ¬ a → ¬ (a ∨ b) := by
      intro hna hab
      cases hab
      case inl ha => exact hna ha
      case inr hb' => exact hnn hna hb'
    exact hLuk hpre (Or.inr hb)

theorem demorganOrLukF_pierceOrLukF' (a b : Prop) :
    DeMorganOrLukasiewiczF b a → PierceOrLukasiewiczF' a b := by
  intro h
  cases h
  case inl hDeM =>
    refine Or.inl ?_
    intro hi
    have hpre : ¬ (¬ b ∧ ¬ a) := fun hc => hc.right (hi (fun ha => absurd ha hc.right))
    cases hDeM hpre
    case inl hb => exact hi (fun _ => hb)
    case inr ha => exact ha
  case inr hLuk => exact Or.inr hLuk

theorem pierceOrLukF'_demorganOrLukF (a b : Prop) :
    PierceOrLukasiewiczF' (b ∨ (b → a)) a → DeMorganOrLukasiewiczF a b := by
  intro h
  cases h
  case inl hPc =>
    cases hPc (fun hAa => Or.inr (fun hb => hAa (Or.inl hb)))
    case inl hb => exact Or.inl (fun _ => Or.inr hb)
    case inr hba => exact Or.inr (fun _ => hba)
  case inr hLuk =>
    refine Or.inr ?_
    intro hnn hb
    have hnna : ¬ ¬ a := fun hna => hnn hna hb
    exact hLuk (fun hna => absurd hna hnna) (Or.inl hb)

/-- `DeMorganNotAndNotF` is symmetric in its two arguments, so swapping
Lukasiewicz's arguments only transposes the whole principle. -/
theorem demorganOrLukF_demorganOrLukF' (a b : Prop) :
    DeMorganOrLukasiewiczF b a → DeMorganOrLukasiewiczF' a b := by
  intro h
  cases h
  case inl hDeM => exact Or.inl (fun hn => (hDeM (fun hc => hn ⟨hc.right, hc.left⟩)).symm)
  case inr hLuk => exact Or.inr hLuk

theorem demorganOrLukF'_demorganOrLukF (a b : Prop) :
    DeMorganOrLukasiewiczF' a b → DeMorganOrLukasiewiczF b a := by
  intro h
  cases h
  case inl hDeM => exact Or.inl (fun hn => (hDeM (fun hc => hn ⟨hc.right, hc.left⟩)).symm)
  case inr hLuk => exact Or.inr hLuk

theorem demorganOrLukF'_pierceOrLukF' (a b : Prop) :
    DeMorganOrLukasiewiczF' a b → PierceOrLukasiewiczF' a b :=
  fun h => demorganOrLukF_pierceOrLukF' a b (demorganOrLukF'_demorganOrLukF a b h)

theorem demorganOrLukF_impOrOrLukF' (a b : Prop) :
    DeMorganOrLukasiewiczF (a → b) a → ImpOrOrLukasiewiczF' a b := by
  intro h
  cases h
  case inl hDeM =>
    have hpre : ¬ (¬ (a → b) ∧ ¬ a) := fun hc => hc.left (fun ha => absurd ha hc.right)
    cases hDeM hpre
    case inl hab => exact Or.inr (fun _ => hab)
    case inr ha => exact Or.inl (fun hab => Or.inr (hab ha))
  case inr hLuk =>
    refine Or.inr ?_
    intro hba ha
    have hstep : ¬ (a → b) → ¬ a := fun hn =>
      absurd (hba (fun hb => hn (fun _ => hb))) (fun hna => hn (fun ha' => absurd ha' hna))
    exact hLuk hstep ha ha

theorem impOrOrLukF'_pierceOrLukF (a b : Prop) :
    ImpOrOrLukasiewiczF' (a ∨ b) a → PierceOrLukasiewiczF a b := by
  intro h
  cases h
  case inl hIO =>
    refine Or.inl ?_
    intro hi
    have hxa : (a ∨ b) → a := fun hab => hab.elim id (fun hb => hi (fun _ => hb))
    cases hIO hxa
    case inl hn => exact hi (fun ha => absurd (Or.inl ha) hn)
    case inr ha => exact ha
  case inr hLuk =>
    refine Or.inr ?_
    intro hnn hb
    have hpre : ¬ a → ¬ (a ∨ b) := fun hna hab => hab.elim hna (fun hb' => hnn hna hb')
    exact hLuk hpre (Or.inr hb)
