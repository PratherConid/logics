import Logics.IntermediateAxioms.AxiomDef

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

/-- `EmAOrNotBF` is excluded middle: at `b := a` its third disjunct `¬ (a → a)`
is refutable, leaving the first two. -/
theorem emAOrNotBF_emF (a : Prop) : EmAOrNotBF a a → ExcludedMiddleF a := by
  intro h
  cases h
  case inl ha => exact Or.inl ha
  case inr h2 =>
    cases h2
    case inl hna => exact Or.inr hna
    case inr hn => exact absurd (id : a → a) hn

/-- The converse needs excluded middle at *both* arguments, one for each of the
two ways the split can fail to reach `a`. -/
theorem emF_emAOrNotBF (a b : Prop) :
    ExcludedMiddleF a → ExcludedMiddleF b → EmAOrNotBF a b := by
  intro hA hB
  cases hA
  case inl ha => exact Or.inl ha
  case inr hna =>
    cases hB
    case inl hb => exact Or.inr (Or.inr (fun h => hna (h hb)))
    case inr hnb => exact Or.inr (Or.inl hnb)

/-- `EmAOrBF` is excluded middle too, collapsing at `b := False`: there `¬ b`
is provable, so `¬ b → a` is `a` and the third disjunct is `¬ a`. -/
theorem emAOrBF_emF (a : Prop) : EmAOrBF a False → ExcludedMiddleF a := by
  intro h
  cases h
  case inl ha => exact Or.inl ha
  case inr h2 =>
    cases h2
    case inl hf => exact hf.elim
    case inr hn => exact Or.inr (fun ha => hn (fun _ => ha))

theorem emF_emAOrBF (a b : Prop) :
    ExcludedMiddleF a → ExcludedMiddleF b → EmAOrBF a b := by
  intro hA hB
  cases hA
  case inl ha => exact Or.inl ha
  case inr hna =>
    cases hB
    case inl hb => exact Or.inr (Or.inl hb)
    case inr hnb => exact Or.inr (Or.inr (fun h => hna (h hnb)))

theorem emFa_pierce₁₂OrLuk₁₂F (a b : Prop) : ExcludedMiddleF a → Pierce₁₂OrLukasiewicz₁₂F a b :=
  fun hEx => Or.inr (emF_lukF a b hEx)

theorem emFb_pierce₁₂OrLuk₁₂F (a b : Prop) : ExcludedMiddleF b → Pierce₁₂OrLukasiewicz₁₂F a b :=
  fun hEx => hEx.elim (fun hb => Or.inl (fun hi => hi (fun _ => hb)))
    (fun hnb => Or.inr (notF_lukF a b hnb))

theorem emFa_demorgan₁₂OrLuk₁₂F (a b : Prop) : ExcludedMiddleF a → DeMorgan₁₂OrLukasiewicz₁₂F a b :=
  fun hEx => Or.inr (emF_lukF a b hEx)

theorem emFb_demorgan₁₂OrLuk₁₂F (a b : Prop) : ExcludedMiddleF b → DeMorgan₁₂OrLukasiewicz₁₂F a b :=
  fun hEx => hEx.elim (fun hb => Or.inl (fun _ => Or.inr hb))
    (fun hnb => Or.inr (notF_lukF a b hnb))

theorem emFa_impOr₁₂OrLuk₁₂F (a b : Prop) : ExcludedMiddleF a → ImpOr₁₂OrLukasiewicz₁₂F a b :=
  fun hEx => Or.inr (emF_lukF a b hEx)

theorem emFb_impOr₁₂OrLuk₁₂F (a b : Prop) : ExcludedMiddleF b → ImpOr₁₂OrLukasiewicz₁₂F a b :=
  fun hEx => hEx.elim (fun hb => Or.inl (fun _ => Or.inr hb))
    (fun hnb => Or.inr (notF_lukF a b hnb))

theorem demorgan₁₂OrLuk₁₂F_impOr₁₂OrLuk₁₂F (a b : Prop) :
    DeMorgan₁₂OrLukasiewicz₁₂F a (¬ a ∨ b) → ImpOr₁₂OrLukasiewicz₁₂F a b := by
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

theorem impOr₁₂OrLuk₁₂F_demorgan₁₂OrLuk₁₂F (a b : Prop) :
    ImpOr₁₂OrLukasiewicz₁₂F a (a ∨ b) → DeMorgan₁₂OrLukasiewicz₁₂F a b := by
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

theorem demorgan₁₂OrLuk₁₂F_pierce₁₂OrLuk₂₁F (a b : Prop) :
    DeMorgan₁₂OrLukasiewicz₁₂F b a → Pierce₁₂OrLukasiewicz₂₁F a b := by
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

theorem pierce₁₂OrLuk₂₁F_demorgan₁₂OrLuk₁₂F (a b : Prop) :
    Pierce₁₂OrLukasiewicz₂₁F (b ∨ (b → a)) a → DeMorgan₁₂OrLukasiewicz₁₂F a b := by
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

theorem demorgan₁₂OrLuk₁₂F_impOr₁₂OrLuk₂₁F (a b : Prop) :
    DeMorgan₁₂OrLukasiewicz₁₂F (a → b) a → ImpOr₁₂OrLukasiewicz₂₁F a b := by
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

theorem impOr₁₂OrLuk₂₁F_pierce₁₂OrLuk₁₂F (a b : Prop) :
    ImpOr₁₂OrLukasiewicz₂₁F (a ∨ b) a → Pierce₁₂OrLukasiewicz₁₂F a b := by
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

theorem emFa_peirce₁₂OrImpOr₁₂F (a b : Prop) : ExcludedMiddleF a → Peirce₁₂OrImpOr₁₂F a b :=
  fun hEx => Or.inl (cmF_peirceF a b (emF_cmF a hEx))

theorem emFb_peirce₁₂OrImpOr₁₂F (a b : Prop) : ExcludedMiddleF b → Peirce₁₂OrImpOr₁₂F a b :=
  fun hEx => Or.inr (fun hab => hEx.elim Or.inr (fun hnb => Or.inl (fun ha => hnb (hab ha))))

/-- Shifting the second argument to `a ∧ b` turns `Peirce₁₂OrImpOr₁₂F` into
`Pierce₁₂OrLukasiewicz₁₂F`.  Peirce transfers because `a → a ∧ b` and `a → b` say
the same thing under the assumption `a`, and `ImpOrF` transfers because its own
premise is available once `b` is assumed, as Lukasiewicz's conclusion does. -/
theorem peirce₁₂OrImpOr₁₂F_pierce₁₂OrLuk₁₂F (a b : Prop) :
    Peirce₁₂OrImpOr₁₂F a (a ∧ b) → Pierce₁₂OrLukasiewicz₁₂F a b := by
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

/-- The converse, which needs a deeper shift: `Peirce₁₂OrImpOr₁₂F` at `a` and `b`
comes from `Pierce₁₂OrLukasiewicz₁₂F` at excluded middle on `a` and at `a → b`.

Both disjuncts turn on `(a ∨ ¬ a) → (a → b)` being interderivable with `a → b`,
which collapses Peirce's premise to `(a → b) → (a ∨ ¬ a)`; Peirce then hands
back excluded middle on `a`, and Lukasiewicz hands back the same thing because
its own premise is free, `¬ (a ∨ ¬ a)` being absurd. -/
theorem pierce₁₂OrLuk₁₂F_peirce₁₂OrImpOr₁₂F (a b : Prop) :
    Pierce₁₂OrLukasiewicz₁₂F (a ∨ ¬ a) (a → b) → Peirce₁₂OrImpOr₁₂F a b := by
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

theorem emFa_peirce₁₂OrImpOr₂₁F (a b : Prop) : ExcludedMiddleF a → Peirce₁₂OrImpOr₂₁F a b :=
  fun hEx => Or.inl (cmF_peirceF a b (emF_cmF a hEx))

theorem emFb_peirce₁₂OrImpOr₂₁F (a b : Prop) : ExcludedMiddleF b → Peirce₁₂OrImpOr₂₁F a b :=
  fun hEx => Or.inr (emF_ImpOrF b a hEx)

/-- Swapping `ImpOrF`'s arguments makes the principle strong enough to reach
`DeMorgan₁₂OrLukasiewicz₁₂F`, which the unswapped version cannot.  The shift is to
the three way disjunction `a ∨ b ∨ (b → a)`, whose every case settles the
target: `a` and `b` give De Morgan's conclusion, and `b → a` is Lukasiewicz's.
Peirce reaches that disjunction because its premise `(A → a) → A` is provable
there, and `ImpOrF` because `a → A` is. -/
theorem peirce₁₂OrImpOr₂₁F_demorgan₁₂OrLuk₁₂F (a b : Prop) :
    Peirce₁₂OrImpOr₂₁F (a ∨ b ∨ (b → a)) a → DeMorgan₁₂OrLukasiewicz₁₂F a b := by
  intro h
  have key : (a ∨ b ∨ (b → a)) → DeMorgan₁₂OrLukasiewicz₁₂F a b := by
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

theorem emFa_pierce₁₂OrDeMorgan₁₂F (a b : Prop) :
    ExcludedMiddleF a → Pierce₁₂OrDeMorgan₁₂F a b :=
  fun hEx => Or.inl (cmF_peirceF a b (emF_cmF a hEx))

/-- Joining Peirce with De Morgan rather than with Lukasiewicz gives excluded
middle back, so `Pierce₁₂OrDeMorgan₁₂F` is not an intermediate principle at all.
At `a ∨ ¬ a` against its own negation both disjuncts collapse: Peirce becomes
`ConsequentiaMirabilisF` there, which is excluded middle, and De Morgan's
premise becomes provable, leaving `(a ∨ ¬ a) ∨ ¬ (a ∨ ¬ a)` whose second case
is absurd. -/
theorem pierce₁₂OrDeMorgan₁₂F_emF (a : Prop) :
    Pierce₁₂OrDeMorgan₁₂F (a ∨ ¬ a) (¬ (a ∨ ¬ a)) → ExcludedMiddleF a := by
  intro h
  have hnn : ¬ ¬ (a ∨ ¬ a) := fun hn => hn (Or.inr (fun ha => hn (Or.inl ha)))
  cases h
  case inl hPc => exact cmF_emF a (peirceF_cmF (a ∨ ¬ a) hPc)
  case inr hDeM =>
    cases hDeM (fun hc => hc.right hc.left)
    case inl hX => exact hX
    case inr hnX => exact absurd hnX hnn

theorem emFa_demorgan₁₂OrImpOr₁₂F (a b : Prop) :
    ExcludedMiddleF a → DeMorgan₁₂OrImpOr₁₂F a b :=
  fun hEx => Or.inr (emF_ImpOrF a b hEx)

/-- Joining De Morgan with `ImpOrF` is classical too, and needs no shift beyond
taking both arguments to be `a ∨ ¬ a`.  There De Morgan's premise is provable
and its conclusion is the disjunction itself, while `ImpOrF` at equal arguments
is excluded middle by `ImpOrF_em`. -/
theorem demorgan₁₂OrImpOr₁₂F_emF (a : Prop) :
    DeMorgan₁₂OrImpOr₁₂F (a ∨ ¬ a) (a ∨ ¬ a) → ExcludedMiddleF a := by
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

theorem emFa_pierce₁₂OrPierce₂₁F (a b : Prop) :
    ExcludedMiddleF a → Pierce₁₂OrPierce₂₁F a b :=
  fun hEx => Or.inl (cmF_peirceF a b (emF_cmF a hEx))

/-- Doubling Peirce gives the weakest principle here, below even
`Pierce₁₂OrLukasiewicz₁₂F`.  At `a ∨ b` against `a → b` each source disjunct
supplies one half of the target: Peirce's premise is provable once `(a → b) → a`
is assumed, and Lukasiewicz's once `(b → a) → b` is. -/
theorem pierce₁₂OrLuk₁₂F_pierce₁₂OrPierce₂₁F (a b : Prop) :
    Pierce₁₂OrLukasiewicz₁₂F (a ∨ b) (a → b) → Pierce₁₂OrPierce₂₁F a b := by
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

theorem emFa_impOr₁₂OrImpOr₂₁F (a b : Prop) :
    ExcludedMiddleF a → ImpOr₁₂OrImpOr₂₁F a b :=
  fun hEx => Or.inl (emF_ImpOrF a b hEx)

/-- Doubling `ImpOrF` is classical, and at equal arguments needs no work at
all: `ImpOrF a a` is already excluded middle. -/
theorem impOr₁₂OrImpOr₂₁F_emF (a : Prop) : ImpOr₁₂OrImpOr₂₁F a a → ExcludedMiddleF a :=
  fun h => h.elim (ImpOrF_em a) (ImpOrF_em a)

theorem emFa_luk₁₂OrLuk₂₁F (a b : Prop) :
    ExcludedMiddleF a → Lukasiewicz₁₂OrLukasiewicz₂₁F a b :=
  fun hEx => Or.inl (emF_lukF a b hEx)

/-- Doubling Lukasiewicz lands on `ImpOr₁₂OrLukasiewicz₂₁F`, one level above the
bottom.  The shift to `a ∧ b` makes `ImpOrF`'s premise available under `b` and
turns Lukasiewicz's conclusion into `a → b`. -/
theorem impOr₁₂OrLuk₂₁F_luk₁₂OrLuk₂₁F (a b : Prop) :
    ImpOr₁₂OrLukasiewicz₂₁F a (a ∧ b) → Lukasiewicz₁₂OrLukasiewicz₂₁F a b := by
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
theorem luk₁₂OrLuk₂₁F_impOr₁₂OrLuk₂₁F (a b : Prop) :
    Lukasiewicz₁₂OrLukasiewicz₂₁F (a → b) (a ∨ ¬ a) → ImpOr₁₂OrLukasiewicz₂₁F a b := by
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

/-! ### One argument principles joined with two argument ones

Each of the six sits at a level the hierarchy already has, and the theorems
below are what places it there: a cycle of derivations through a known member
of that level, so that every principle on the cycle proves every other.

`Em₁OrLuk₂₁F`, `NotNot₁OrLuk₂₁F` and `CM₁OrLuk₂₁F` are reached from
`DeMorgan₁₂OrLukasiewicz₁₂F` and return to it through
`Pierce₁₂OrLukasiewicz₂₁F`, which the file already shows equivalent to it.
`CM₁OrPeirce₂₁F` and `NotNot₁OrPeirce₂₁F` form a second cycle to the same
level.  `Em₁OrPeirce₂₁F` is one level up, interderivable with
`Peirce₁₂OrImpOr₂₁F`. -/

theorem demorgan₁₂OrLuk₁₂F_em₁OrLuk₂₁F (a b : Prop) :
    DeMorgan₁₂OrLukasiewicz₁₂F (a → b) a → Em₁OrLuk₂₁F a b := by
  intro h
  cases h
  case inl hDeM =>
    cases hDeM (fun hc => hc.left (fun ha => absurd ha hc.right))
    case inl hab => exact Or.inr (fun _ => hab)
    case inr ha => exact Or.inl (Or.inl ha)
  case inr hLuk =>
    refine Or.inr ?_
    intro hba ha
    exact hLuk (fun hn ha' => hba (fun hb => hn (fun _ => hb)) ha') ha ha

theorem em₁OrLuk₂₁F_notNot₁OrLuk₂₁F (a b : Prop) :
    Em₁OrLuk₂₁F a b → NotNot₁OrLuk₂₁F a b :=
  fun h => h.elim (fun hEm => Or.inl (emF_notNotF a hEm)) Or.inr

theorem notNot₁OrLuk₂₁F_cm₁OrLuk₂₁F (a b : Prop) :
    NotNot₁OrLuk₂₁F a b → CM₁OrLuk₂₁F a b :=
  fun h => h.elim (fun hn => Or.inl (notNotF_cmF a hn)) Or.inr

theorem cm₁OrLuk₂₁F_pierce₁₂OrLuk₂₁F (a b : Prop) :
    CM₁OrLuk₂₁F a b → Pierce₁₂OrLukasiewicz₂₁F a b :=
  fun h => h.elim (fun hc => Or.inl (cmF_peirceF a b hc)) Or.inr

/-- The shift to `b ∨ (b → a)` makes De Morgan's premise provable, and in the
Lukasiewicz case the implication `B → a` supplies `b → a` through its own left
injection, which is what closes it. -/
theorem demorgan₁₂OrLuk₁₂F_cm₁OrPeirce₂₁F (a b : Prop) :
    DeMorgan₁₂OrLukasiewicz₁₂F a (b ∨ (b → a)) → CM₁OrPeirce₂₁F a b := by
  intro h
  have hnnB : ¬ ¬ (b ∨ (b → a)) := fun hn => hn (Or.inr (fun hb => absurd (Or.inl hb) hn))
  cases h
  case inl hDeM =>
    cases hDeM (fun hc => hnnB hc.right)
    case inl ha => exact Or.inl (fun _ => ha)
    case inr hB =>
      cases hB
      case inl hb => exact Or.inr (fun _ => hb)
      case inr hba => exact Or.inr (fun hi => hi hba)
  case inr hLuk =>
    refine Or.inl ?_
    intro hcm
    have hnn : ¬ ¬ a := fun hna => hna (hcm hna)
    have g : (b ∨ (b → a)) → a := hLuk (fun hna => absurd hna hnn)
    exact g (Or.inr (fun hb => g (Or.inl hb)))

theorem cm₁OrPeirce₂₁F_notNot₁OrPeirce₂₁F (a b : Prop) :
    CM₁OrPeirce₂₁F a b → NotNot₁OrPeirce₂₁F a b :=
  fun h => h.elim (fun hc => Or.inl (cmF_notNotF a hc)) Or.inr

theorem notNot₁OrPeirce₂₁F_cm₁OrPeirce₂₁F (a b : Prop) :
    NotNot₁OrPeirce₂₁F a b → CM₁OrPeirce₂₁F a b :=
  fun h => h.elim (fun hn => Or.inl (notNotF_cmF a hn)) Or.inr

theorem cm₁OrPeirce₂₁F_pierce₁₂OrLuk₂₁F (a b : Prop) :
    CM₁OrPeirce₂₁F b a → Pierce₁₂OrLukasiewicz₂₁F a b := by
  intro h
  cases h
  case inl hcm => exact Or.inr (fun hba ha => hcm (fun hnb => absurd ha (hba hnb)))
  case inr hPc => exact Or.inl hPc

theorem em₁OrPeirce₂₁F_peirce₁₂OrImpOr₂₁F (a b : Prop) :
    Em₁OrPeirce₂₁F b a → Peirce₁₂OrImpOr₂₁F a b :=
  fun h => h.elim (fun hEm => Or.inr (emF_ImpOrF b a hEm)) Or.inl

theorem peirce₁₂OrImpOr₂₁F_em₁OrPeirce₂₁F (a b : Prop) :
    Peirce₁₂OrImpOr₂₁F (a ∨ b) a → Em₁OrPeirce₂₁F a b := by
  intro h
  cases h
  case inl hPc =>
    refine Or.inr ?_
    intro hi
    cases hPc (fun hx => Or.inr (hi (fun hb => hx (Or.inr hb))))
    case inl ha => exact hi (fun _ => ha)
    case inr hb => exact hb
  case inr hIO =>
    cases hIO Or.inl
    case inl hna => exact Or.inl (Or.inr hna)
    case inr hab =>
      cases hab
      case inl ha => exact Or.inl (Or.inl ha)
      case inr hb => exact Or.inr (fun _ => hb)

/-! ### Pairings with the three way splits

`EmAOrNotBF` and `EmAOrBF` are each excluded middle on their own, but paired
with a two-argument principle they need not be: the pairing is only classical
when one side implies the other.  Where it is not, the result lands on a level
the hierarchy already has, and the two theorems for each pairing place it
there. -/

/-- `EmAOrNotB₁₂OrPeirce₁₂F` reaches `Peirce₁₂OrImpOr₂₁F` at the plain
arguments: the three way split is exactly what `ImpOrF b a` needs once `b → a`
is assumed. -/
theorem emAOrNotB₁₂OrPeirce₁₂F_peirce₁₂OrImpOr₂₁F (a b : Prop) :
    EmAOrNotB₁₂OrPeirce₁₂F a b → Peirce₁₂OrImpOr₂₁F a b := by
  intro h
  cases h
  case inr hPc => exact Or.inl hPc
  case inl hE =>
    refine Or.inr ?_
    intro hba
    cases hE
    case inl ha => exact Or.inr ha
    case inr h2 =>
      cases h2
      case inl hnb => exact Or.inl hnb
      case inr hn => exact absurd hba hn

theorem peirce₁₂OrImpOr₂₁F_emAOrNotB₁₂OrPeirce₁₂F (a b : Prop) :
    Peirce₁₂OrImpOr₂₁F (a ∨ b) b → EmAOrNotB₁₂OrPeirce₁₂F a b := by
  intro h
  cases h
  case inl hPc =>
    refine Or.inr ?_
    intro hi
    cases hPc (fun hx => Or.inl (hi (fun ha => hx (Or.inl ha))))
    case inl ha => exact ha
    case inr hb => exact hi (fun _ => hb)
  case inr hIO =>
    cases hIO Or.inr
    case inl hnb => exact Or.inl (Or.inr (Or.inl hnb))
    case inr hab =>
      cases hab
      case inl ha => exact Or.inl (Or.inl ha)
      case inr hb => exact Or.inr (fun hi => hi (fun _ => hb))

/-- Taking the split at `(b, a)` instead reaches the same level, now with the
split feeding `ImpOrF b a` directly in all three cases. -/
theorem emAOrNotB₁₂OrPeirce₂₁F_peirce₁₂OrImpOr₂₁F (a b : Prop) :
    EmAOrNotB₁₂OrPeirce₂₁F b a → Peirce₁₂OrImpOr₂₁F a b := by
  intro h
  cases h
  case inr hPc => exact Or.inl hPc
  case inl hE =>
    refine Or.inr ?_
    intro hba
    cases hE
    case inl hb => exact Or.inr (hba hb)
    case inr h2 =>
      cases h2
      case inl hna => exact Or.inl (fun hb => hna (hba hb))
      case inr hn => exact Or.inl (fun hb => hn (fun _ => hb))

theorem peirce₁₂OrImpOr₂₁F_emAOrNotB₁₂OrPeirce₂₁F (a b : Prop) :
    Peirce₁₂OrImpOr₂₁F (a ∨ b ∨ (b → a)) (b → a) → EmAOrNotB₁₂OrPeirce₂₁F a b := by
  intro h
  have fromA : (a ∨ b ∨ (b → a)) → EmAOrNotB₁₂OrPeirce₂₁F a b := by
    intro hA
    cases hA
    case inl ha => exact Or.inl (Or.inl ha)
    case inr h2 =>
      cases h2
      case inl hb => exact Or.inr (fun _ => hb)
      case inr hba => exact Or.inr (fun hi => hi hba)
  cases h
  case inl hPc =>
    exact fromA (hPc (fun hAB => Or.inr (Or.inr (fun hb => hAB (Or.inr (Or.inl hb)) hb))))
  case inr hIO =>
    cases hIO (fun hba => Or.inr (Or.inr hba))
    case inl hn => exact Or.inl (Or.inr (Or.inr hn))
    case inr hA => exact fromA hA

/-- Pairing the other split with Lukasiewicz drops a level, to
`DeMorgan₁₂OrLukasiewicz₁₂F`.  Both directions shift to `(b → a, b)`, where the
split's third disjunct becomes refutable and its Lukasiewicz half turns on
`¬ (b → a)` giving `¬ a`. -/
theorem emAOrB₁₂OrLuk₁₂F_demorgan₁₂OrLuk₁₂F (a b : Prop) :
    EmAOrB₁₂OrLuk₁₂F (b → a) b → DeMorgan₁₂OrLukasiewicz₁₂F a b := by
  intro h
  cases h
  case inl hE =>
    cases hE
    case inl hba => exact Or.inr (fun _ => hba)
    case inr h2 =>
      cases h2
      case inl hb => exact Or.inl (fun _ => Or.inr hb)
      case inr hn => exact absurd (fun hnb hb => absurd hb hnb) hn
  case inr hLuk =>
    refine Or.inr ?_
    intro h hb
    exact hLuk (fun hn hb' => h (fun ha => hn (fun _ => ha)) hb') hb hb

theorem demorgan₁₂OrLuk₁₂F_emAOrB₁₂OrLuk₁₂F (a b : Prop) :
    DeMorgan₁₂OrLukasiewicz₁₂F (b → a) b → EmAOrB₁₂OrLuk₁₂F a b := by
  intro h
  cases h
  case inl hDeM =>
    cases hDeM (fun hc => hc.left (fun hb => absurd hb hc.right))
    case inl hba => exact Or.inr (fun _ => hba)
    case inr hb => exact Or.inl (Or.inr (Or.inl hb))
  case inr hLuk =>
    refine Or.inr ?_
    intro h hb
    exact hLuk (fun hn hb' => h (fun ha => hn (fun _ => ha)) hb') hb hb

/-- Swapping Lukasiewicz's arguments keeps the same level.  Here the forward
direction needs no shift on the Lukasiewicz side at all, and the split's third
disjunct `¬ (¬ a → b)` delivers `¬ b`, which is enough for Lukasiewicz. -/
theorem emAOrB₁₂OrLuk₂₁F_demorgan₁₂OrLuk₁₂F (a b : Prop) :
    EmAOrB₁₂OrLuk₂₁F b a → DeMorgan₁₂OrLukasiewicz₁₂F a b := by
  intro h
  cases h
  case inr hLuk => exact Or.inr hLuk
  case inl hE =>
    cases hE
    case inl hb => exact Or.inl (fun _ => Or.inr hb)
    case inr h2 =>
      cases h2
      case inl ha => exact Or.inl (fun _ => Or.inl ha)
      case inr hn => exact Or.inr (fun _ hb => absurd (fun _ => hb) hn)

theorem demorgan₁₂OrLuk₁₂F_emAOrB₁₂OrLuk₂₁F (a b : Prop) :
    DeMorgan₁₂OrLukasiewicz₁₂F (a → b) a → EmAOrB₁₂OrLuk₂₁F a b := by
  intro h
  cases h
  case inl hDeM =>
    cases hDeM (fun hc => hc.left (fun ha => absurd ha hc.right))
    case inl hab => exact Or.inr (fun _ => hab)
    case inr ha => exact Or.inl (Or.inl ha)
  case inr hLuk =>
    refine Or.inr ?_
    intro h ha
    exact hLuk (fun hn ha' => h (fun hb => hn (fun _ => hb)) ha') ha ha

/-- The last nontrivial pairing, again at the De Morgan level.  Every case of
the split feeds Lukasiewicz: `¬ a` directly, and `¬ (a → b)` through `¬ b`. -/
theorem emAOrNotB₁₂OrLuk₂₁F_demorgan₁₂OrLuk₁₂F (a b : Prop) :
    EmAOrNotB₁₂OrLuk₂₁F b a → DeMorgan₁₂OrLukasiewicz₁₂F a b := by
  intro h
  cases h
  case inr hLuk => exact Or.inr hLuk
  case inl hE =>
    cases hE
    case inl hb => exact Or.inl (fun _ => Or.inr hb)
    case inr h2 =>
      cases h2
      case inl hna => exact Or.inr (fun hx hb => absurd hb (hx hna))
      case inr hn => exact Or.inr (fun _ hb => absurd (fun _ => hb) hn)

theorem demorgan₁₂OrLuk₁₂F_emAOrNotB₁₂OrLuk₂₁F (a b : Prop) :
    DeMorgan₁₂OrLukasiewicz₁₂F (a → b) a → EmAOrNotB₁₂OrLuk₂₁F a b := by
  intro h
  cases h
  case inl hDeM =>
    cases hDeM (fun hc => hc.left (fun ha => absurd ha hc.right))
    case inl hab => exact Or.inr (fun _ => hab)
    case inr ha => exact Or.inl (Or.inl ha)
  case inr hLuk =>
    refine Or.inr ?_
    intro h ha
    exact hLuk (fun hn ha' => h (fun hb => hn (fun _ => hb)) ha') ha ha

/-! ## Smetanich's axiom and `Peirce₁₂OrImpOr₂₁F` axiomatise the same level

Smetanich's is the named axiom for that level; the combined principle is the
form the disjunctions of this development put there.  Each derives the other,
so the two are interchangeable wherever the level is meant.

The two directions are not alike.  `Peirce₁₂OrImpOr₂₁F` gives Smetanich's
axiom at the same arguments, with no shift at all.  Going back needs *two*
instances, and no single one suffices: the target has to be fed in as an
argument first, to obtain `¬ b → a`, which is exactly what the instance at
`a, b` consumes. -/

theorem peirce₁₂OrImpOr₂₁F_smetanichF (a b : Prop) :
    Peirce₁₂OrImpOr₂₁F a b → SmetanichF a b := by
  intro h hnb k
  cases h with
  | inl hp => exact hp k
  | inr himp =>
      cases himp (fun hb => k (fun _ => hb)) with
      | inl hnb' => exact hnb hnb'
      | inr ha => exact ha

theorem smetanichF_peirce₁₂OrImpOr₂₁F (a b : Prop)
    (h₁ : SmetanichF (Peirce₁₂OrImpOr₂₁F a b) a) (h₂ : SmetanichF a b) :
    Peirce₁₂OrImpOr₂₁F a b := by
  have hnb : ¬ b → Peirce₁₂OrImpOr₂₁F a b := fun nb => Or.inr (fun _ => Or.inl nb)
  refine h₁ (fun na => Or.inr (fun hba => Or.inl (fun hb => na (hba hb)))) ?_
  intro k
  exact Or.inl (h₂ (fun nb => k (hnb nb)))

/-! ## `BD2F` and `Em₁OrLuk₂₁F` axiomatise the same level

`BD2F` is bounded depth two, the named axiom for the level below Smetanich's.
Each direction needs one shifted instance, and both shifts are the same idea:
excluded middle at one argument is what the two principles trade in.  Going up,
`BD2F` is asked about `a ∨ ¬ a`; coming back, the Lukasiewicz principle is asked
about `b ∨ ¬ b`, whose negation is absurd and so discharges the hypothesis for
free. -/

theorem bd2F_em₁OrLuk₂₁F (a b : Prop) : BD2F (a ∨ ¬ a) b → Em₁OrLuk₂₁F a b := by
  intro h
  cases h with
  | inl hem => exact Or.inl hem
  | inr k =>
      refine Or.inr (fun hn ha => ?_)
      cases k (Or.inl ha) with
      | inl hb => exact hb
      | inr nb => exact absurd ha (hn nb)

theorem em₁OrLuk₂₁F_bd2F (a b : Prop) : Em₁OrLuk₂₁F a (b ∨ ¬ b) → BD2F a b := by
  intro h
  cases h with
  | inl hem =>
      cases hem with
      | inl ha => exact Or.inl ha
      | inr na => exact Or.inr (fun ha => absurd ha na)
  | inr k =>
      exact Or.inr (k (fun hn => absurd (Or.inr (fun hb => hn (Or.inl hb))) hn))

/-! ## `NoDiamondF` and `NotNotAndF` axiomatise the level below `BD2F`

`NoDiamondF` is `BD2F` with its bare left disjunct replaced by the mirror image
of its right one, and that one change is the whole step down: `BD2F` gives it at
the same arguments, with nothing shifted.  `NotNotAndF` says the same level
differently, that the two arguments are comparable as soon as they are jointly
consistent.

Every return trip below is the same shift, to `a ∨ ¬ a` and `b ∨ ¬ b`.  Both
principles have a hypothesis that the shift discharges for free, since the
negation of an excluded middle is absurd, and what survives is a comparison
between the two excluded middles.  That is already `NoDiamondF`, because `a`
gives `a ∨ ¬ a` on its own. -/

theorem bd2F_noDiamondF (a b : Prop) : BD2F a b → NoDiamondF a b := by
  intro h
  cases h with
  | inl ha => exact Or.inr (fun _ => Or.inl ha)
  | inr k => exact Or.inl k

theorem noDiamondF_luk₁₂OrLuk₂₁F (a b : Prop) :
    NoDiamondF a b → Lukasiewicz₁₂OrLukasiewicz₂₁F a b := by
  intro h
  cases h with
  | inl k =>
      refine Or.inr (fun hn ha => ?_)
      cases k ha with
      | inl hb => exact hb
      | inr hnb => exact absurd ha (hn hnb)
  | inr k =>
      refine Or.inl (fun hn hb => ?_)
      cases k hb with
      | inl ha => exact ha
      | inr hna => exact absurd hb (hn hna)

theorem luk₁₂OrLuk₂₁F_noDiamondF (a b : Prop) :
    Lukasiewicz₁₂OrLukasiewicz₂₁F (a ∨ ¬ a) (b ∨ ¬ b) → NoDiamondF a b := by
  intro h
  have hna : ¬ ¬ (a ∨ ¬ a) := fun hn => hn (Or.inr (fun ha => hn (Or.inl ha)))
  have hnb : ¬ ¬ (b ∨ ¬ b) := fun hn => hn (Or.inr (fun hb => hn (Or.inl hb)))
  cases h with
  | inl k => exact Or.inr (fun hb => k (fun hx => absurd hx hna) (Or.inl hb))
  | inr k => exact Or.inl (fun ha => k (fun hx => absurd hx hnb) (Or.inl ha))

theorem noDiamondF_notNotAndF (a b : Prop) : NoDiamondF a b → NotNotAndF a b := by
  intro h hnn
  cases h with
  | inl k =>
      refine Or.inl (fun ha => ?_)
      cases k ha with
      | inl hb => exact hb
      | inr hnb => exact absurd (fun hab : a ∧ b => hnb hab.2) hnn
  | inr k =>
      refine Or.inr (fun hb => ?_)
      cases k hb with
      | inl ha => exact ha
      | inr hna => exact absurd (fun hab : a ∧ b => hna hab.1) hnn

theorem notNotAndF_noDiamondF (a b : Prop) :
    NotNotAndF (a ∨ ¬ a) (b ∨ ¬ b) → NoDiamondF a b := by
  intro h
  have hna : ¬ ¬ (a ∨ ¬ a) := fun hn => hn (Or.inr (fun ha => hn (Or.inl ha)))
  have hnb : ¬ ¬ (b ∨ ¬ b) := fun hn => hn (Or.inr (fun hb => hn (Or.inl hb)))
  cases h (fun hn => hna (fun hx => hnb (fun hy => hn ⟨hx, hy⟩))) with
  | inl k => exact Or.inl (fun ha => k (Or.inl ha))
  | inr k => exact Or.inr (fun hb => k (Or.inl hb))

/-! ## Linearity and weak excluded middle

Neither is a combination of two principles, so neither belongs to the chain of
levels; each sits beside it.  Linearity is the stronger, and reaches weak
excluded middle by being asked about a proposition against its own negation.

The last theorem is the one that places linearity exactly.  Weak excluded
middle and `NoDiamondF` together give it back, at the plain arguments and with
no shift: once neither argument can be refuted, the disjunct of `NoDiamondF`
that holds delivers the comparison outright. -/

theorem linearityF_weakEmF (a : Prop) : LinearityF a (¬ a) → WeakEmF a := by
  intro h
  cases h with
  | inl k => exact Or.inl (fun ha => k ha ha)
  | inr k => exact Or.inr (fun na => na (k na))

theorem linearityF_notNotAndF (a b : Prop) : LinearityF a b → NotNotAndF a b :=
  fun h _ => h

theorem linearityF_noDiamondF (a b : Prop) :
    LinearityF (a ∨ ¬ a) (b ∨ ¬ b) → NoDiamondF a b := by
  intro h
  cases h with
  | inl k => exact Or.inl (fun ha => k (Or.inl ha))
  | inr k => exact Or.inr (fun hb => k (Or.inl hb))

/-- **Linearity is exactly weak excluded middle together with `NoDiamondF`.**
Each argument is either refutable, which settles the comparison one way, or
doubly negated, and then the `NoDiamondF` disjunct that holds turns an excluded
middle into the comparison itself. -/
theorem weakEmF_noDiamondF_linearityF (a b : Prop)
    (ha : WeakEmF a) (hb : WeakEmF b) (hnd : NoDiamondF a b) : LinearityF a b := by
  cases ha with
  | inl na => exact Or.inl (fun x => absurd x na)
  | inr nna =>
      cases hb with
      | inl nb => exact Or.inr (fun x => absurd x nb)
      | inr nnb =>
          cases hnd with
          | inl k =>
              refine Or.inl (fun hx => ?_)
              cases k hx with
              | inl hy => exact hy
              | inr nb => exact absurd nb nnb
          | inr k =>
              refine Or.inr (fun hy => ?_)
              cases k hy with
              | inl hx => exact hx
              | inr na => exact absurd na nna
