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

Swapping an argument is the third pattern, and it does not always change
anything: for a principle whose left disjunct is symmetric the swap merely
transposes it, while for the others it moves the principle to a different
strength.
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

theorem emFa_peirceOrImpOrF (a b : Prop) : ExcludedMiddleF a → PeirceOrImpOrF a b :=
  fun hEx => Or.inl (cmF_peirceF a b (emF_cmF a hEx))

theorem emFb_peirceOrImpOrF (a b : Prop) : ExcludedMiddleF b → PeirceOrImpOrF a b :=
  fun hEx => Or.inr (fun hab => hEx.elim Or.inr (fun hnb => Or.inl (fun ha => hnb (hab ha))))

/-- Shifting the second argument to `a ∧ b` turns `PeirceOrImpOrF` into
`PierceOrLukasiewiczF`.  Peirce transfers because `a → a ∧ b` and `a → b` say
the same thing under the assumption `a`, and `ImpOrF` transfers because its own
premise is available once `b` is assumed, as Lukasiewicz's conclusion does. -/
theorem peirceOrImpOrF_pierceOrLukF (a b : Prop) :
    PeirceOrImpOrF a (a ∧ b) → PierceOrLukasiewiczF a b := by
  intro h
  cases h
  case inl hPc =>
    refine Or.inl ?_
    intro hi
    exact hPc (fun hand => hi (fun ha => (hand ha).2))
  case inr hIO =>
    refine Or.inr ?_
    intro hn hb
    cases hIO (fun ha => ⟨ha, hb⟩)
    case inl hna => exact absurd hb (hn hna)
    case inr hab => exact hab.1

/-- The converse, which needs a deeper shift: `PeirceOrImpOrF` at `a` and `b`
comes from `PierceOrLukasiewiczF` at excluded middle on `a` and at `a → b`.

Both disjuncts turn on `(a ∨ ¬ a) → (a → b)` being interderivable with `a → b`,
which collapses Peirce's premise to `(a → b) → (a ∨ ¬ a)`; Peirce then hands
back excluded middle on `a`, and Lukasiewicz hands back the same thing because
its own premise is free, `¬ (a ∨ ¬ a)` being absurd. -/
theorem pierceOrLukF_peirceOrImpOrF (a b : Prop) :
    PierceOrLukasiewiczF (a ∨ ¬ a) (a → b) → PeirceOrImpOrF a b := by
  intro h
  have hnn : ¬ ¬ (a ∨ ¬ a) := fun hn => hn (Or.inr (fun ha => hn (Or.inl ha)))
  cases h
  case inl hPc =>
    refine Or.inl ?_
    intro hi
    cases hPc (fun hAB => Or.inl (hi (fun ha => hAB (Or.inl ha) ha)))
    case inl ha => exact ha
    case inr hna => exact hi (fun ha => absurd ha hna)
  case inr hLuk =>
    refine Or.inr ?_
    intro hab
    cases hLuk (fun hn => absurd hn hnn) hab
    case inl ha => exact Or.inr (hab ha)
    case inr hna => exact Or.inl hna

theorem emFa_peirceOrImpOrF' (a b : Prop) : ExcludedMiddleF a → PeirceOrImpOrF' a b :=
  fun hEx => Or.inl (cmF_peirceF a b (emF_cmF a hEx))

theorem emFb_peirceOrImpOrF' (a b : Prop) : ExcludedMiddleF b → PeirceOrImpOrF' a b :=
  fun hEx => Or.inr (emF_ImpOrF b a hEx)

/-- Swapping `ImpOrF`'s arguments makes the principle strong enough to reach
`DeMorganOrLukasiewiczF`, which the unswapped version cannot.  The shift is to
the three way disjunction `a ∨ b ∨ (b → a)`, whose every case settles the
target: `a` and `b` give De Morgan's conclusion, and `b → a` is Lukasiewicz's.
Peirce reaches that disjunction because its premise `(A → a) → A` is provable
there, and `ImpOrF` because `a → A` is. -/
theorem peirceOrImpOrF'_demorganOrLukF (a b : Prop) :
    PeirceOrImpOrF' (a ∨ b ∨ (b → a)) a → DeMorganOrLukasiewiczF a b := by
  intro h
  have key : (a ∨ b ∨ (b → a)) → DeMorganOrLukasiewiczF a b := by
    intro hA
    cases hA
    case inl ha => exact Or.inl (fun _ => Or.inl ha)
    case inr hbr =>
      cases hbr
      case inl hb => exact Or.inl (fun _ => Or.inr hb)
      case inr hba => exact Or.inr (fun _ => hba)
  cases h
  case inl hPc =>
    exact key (hPc (fun hAa => Or.inr (Or.inr (fun hb => hAa (Or.inr (Or.inl hb))))))
  case inr hIO =>
    cases hIO (fun ha => Or.inl ha)
    case inl hna => exact Or.inr (fun hn hb => absurd hb (hn hna))
    case inr hA => exact key hA

theorem emFa_pierceOrDeMorganF (a b : Prop) :
    ExcludedMiddleF a → PierceOrDeMorganF a b :=
  fun hEx => Or.inl (cmF_peirceF a b (emF_cmF a hEx))

/-- Joining Peirce with De Morgan rather than with Lukasiewicz gives excluded
middle back, so `PierceOrDeMorganF` is not an intermediate principle at all.
At `a ∨ ¬ a` against its own negation both disjuncts collapse: Peirce becomes
`ConsequentiaMirabilisF` there, which is excluded middle, and De Morgan's
premise becomes provable, leaving `(a ∨ ¬ a) ∨ ¬ (a ∨ ¬ a)` whose second case
is absurd. -/
theorem pierceOrDeMorganF_emF (a : Prop) :
    PierceOrDeMorganF (a ∨ ¬ a) (¬ (a ∨ ¬ a)) → ExcludedMiddleF a := by
  intro h
  have hnn : ¬ ¬ (a ∨ ¬ a) := fun hn => hn (Or.inr (fun ha => hn (Or.inl ha)))
  cases h
  case inl hPc => exact cmF_emF a (peirceF_cmF (a ∨ ¬ a) hPc)
  case inr hDeM =>
    cases hDeM (fun hc => hc.right hc.left)
    case inl hX => exact hX
    case inr hnX => exact absurd hnX hnn

theorem emFa_demorganOrImpOrF (a b : Prop) :
    ExcludedMiddleF a → DeMorganOrImpOrF a b :=
  fun hEx => Or.inr (emF_ImpOrF a b hEx)

/-- Joining De Morgan with `ImpOrF` is classical too, and needs no shift beyond
taking both arguments to be `a ∨ ¬ a`.  There De Morgan's premise is provable
and its conclusion is the disjunction itself, while `ImpOrF` at equal arguments
is excluded middle by `ImpOrF_em`. -/
theorem demorganOrImpOrF_emF (a : Prop) :
    DeMorganOrImpOrF (a ∨ ¬ a) (a ∨ ¬ a) → ExcludedMiddleF a := by
  intro h
  have hnn : ¬ ¬ (a ∨ ¬ a) := fun hn => hn (Or.inr (fun ha => hn (Or.inl ha)))
  cases h
  case inl hDeM => exact (hDeM (fun hc => hnn hc.left)).elim id id
  case inr hIO =>
    cases ImpOrF_em (a ∨ ¬ a) hIO
    case inl hX => exact hX
    case inr hnX => exact absurd hnX hnn

/-! ### The self disjunctions

A principle joined with its own transpose.  Where each lands depends entirely
on which principle is doubled. -/

theorem emFa_pierceOrPierceF' (a b : Prop) :
    ExcludedMiddleF a → PierceOrPierceF' a b :=
  fun hEx => Or.inl (cmF_peirceF a b (emF_cmF a hEx))

/-- Doubling Peirce gives the weakest principle here, below even
`PierceOrLukasiewiczF`.  At `a ∨ b` against `a → b` each source disjunct
supplies one half of the target: Peirce's premise is provable once `(a → b) → a`
is assumed, and Lukasiewicz's once `(b → a) → b` is. -/
theorem pierceOrLukF_pierceOrPierceF' (a b : Prop) :
    PierceOrLukasiewiczF (a ∨ b) (a → b) → PierceOrPierceF' a b := by
  intro h
  cases h
  case inl hPc =>
    refine Or.inl ?_
    intro hi
    cases hPc (fun hAB => Or.inl (hi (fun ha => hAB (Or.inl ha) ha)))
    case inl ha => exact ha
    case inr hb => exact hi (fun _ => hb)
  case inr hLuk =>
    refine Or.inr ?_
    intro hi
    have hab : a → b := fun ha => hi (fun _ => ha)
    have hpre : ¬ (a ∨ b) → ¬ (a → b) :=
      fun hn _ => hn (Or.inr (hi (fun hb => absurd (Or.inr hb) hn)))
    cases hLuk hpre hab
    case inl ha => exact hi (fun _ => ha)
    case inr hb => exact hb

theorem emFa_impOrOrImpOrF' (a b : Prop) :
    ExcludedMiddleF a → ImpOrOrImpOrF' a b :=
  fun hEx => Or.inl (emF_ImpOrF a b hEx)

/-- Doubling `ImpOrF` is classical, and at equal arguments needs no work at
all: `ImpOrF a a` is already excluded middle. -/
theorem impOrOrImpOrF'_emF (a : Prop) : ImpOrOrImpOrF' a a → ExcludedMiddleF a :=
  fun h => h.elim (ImpOrF_em a) (ImpOrF_em a)

theorem emFa_lukOrLukF' (a b : Prop) :
    ExcludedMiddleF a → LukasiewiczOrLukasiewiczF' a b :=
  fun hEx => Or.inl (emF_lukF a b hEx)

/-- Doubling Lukasiewicz lands on `ImpOrOrLukasiewiczF'`, one level above the
bottom.  The shift to `a ∧ b` makes `ImpOrF`'s premise available under `b` and
turns Lukasiewicz's conclusion into `a → b`. -/
theorem impOrOrLukF'_lukOrLukF' (a b : Prop) :
    ImpOrOrLukasiewiczF' a (a ∧ b) → LukasiewiczOrLukasiewiczF' a b := by
  intro h
  cases h
  case inl hIO =>
    refine Or.inl ?_
    intro hn hb
    cases hIO (fun ha => ⟨ha, hb⟩)
    case inl hna => exact absurd hb (hn hna)
    case inr hab => exact hab.1
  case inr hLuk =>
    refine Or.inr ?_
    intro hba ha
    exact (hLuk (fun k ha' => hba (fun hb => k ⟨ha', hb⟩) ha') ha).2

/-- The converse, at `a → b` against excluded middle on `a`.  Both source
disjuncts have a premise that is free because `¬ (a ∨ ¬ a)` is absurd, and the
`a` assumed by the target is what supplies `a ∨ ¬ a` in the first case. -/
theorem lukOrLukF'_impOrOrLukF' (a b : Prop) :
    LukasiewiczOrLukasiewiczF' (a → b) (a ∨ ¬ a) → ImpOrOrLukasiewiczF' a b := by
  intro h
  have hnnY : ¬ ¬ (a ∨ ¬ a) := fun hn => hn (Or.inr (fun ha => hn (Or.inl ha)))
  cases h
  case inl hL =>
    refine Or.inr ?_
    intro hba ha
    have hnn : ¬ ¬ (a → b) := fun hn => hba (fun hb => hn (fun _ => hb)) ha
    exact hL (fun hnx => absurd hnx hnn) (Or.inl ha) ha
  case inr hL =>
    refine Or.inl ?_
    intro hab
    cases hL (fun hnY => absurd hnY hnnY) hab
    case inl ha => exact Or.inr (hab ha)
    case inr hna => exact Or.inl hna

