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

/-!
### `PierceOrLukasiewiczF` is strictly weaker than the principles above

Excluded middle on *either* side implies it (see the two theorems below), but
there is no instantiation of `a` and `b` making the converse provable: it is not
intuitionistically equivalent to `ExcludedMiddleF`, `NotNotF`, `PeirceF`,
`ConsequentiaMirabilisF`, or any of the other axioms in this file.

The separating models are the `k`-chains, which come in two guises.

**The frame.** A Kripke model for intuitionistic logic is a poset of states of
knowledge in which truth is monotone: once `a` holds it holds in every later
state.  The `k`-chain is the frame whose `k` worlds are totally ordered,
`w₀ < w₁ < ⋯ < w_{k-1}`.

**The algebra.** A proposition is the set of worlds where it holds, which
monotonicity forces to be upward closed.  Over the `k`-chain the upward closed
sets are `∅ ⊆ {w_{k-1}} ⊆ {w_{k-2}, w_{k-1}} ⊆ ⋯`, so they form a chain of
`k + 1` elements, and this is the Heyting algebra in which formulas get
evaluated.  For `k = 2` that is the three element chain `0 < m < 1`, with

* `x → y = 1` if `x ≤ y`, and `x → y = y` otherwise,
* `¬x = x → 0`, so `¬0 = 1` but `¬m = ¬1 = 0`,
* `∨ = max` and `∧ = min`.

Read `m` as "unsettled at `w₀`, true at `w₁`".  Nothing refutes such a
proposition, which is why `¬m = 0` and hence `m ∨ ¬m = m ≠ 1`: excluded middle
already fails in the smallest nonclassical chain.

**Why this separates them.** Tabulating both disjuncts over `0 < m < 1`:

```
  a  b | Peirce  Luk   join
  0  *  |   1      1     1
  m  0  |   m      1     1      -- Peirce dips, Lukasiewicz saves it
  m  m  |   1      1     1
  m  1  |   1      m     1      -- Lukasiewicz dips, Peirce saves it
  1  *  |   1      1     1
```

The join is `1` in every row, so `PierceOrLukasiewiczF X Y` evaluates to `1`
whatever formulas are substituted for `X` and `Y` — the algebra sees only values,
not the syntax of the instance.  But `ExcludedMiddleF a` evaluates to `m` at
`a = m`.  Since a derivation in intuitionistic logic sends `1` to `1`, no
derivation of `ExcludedMiddleF a` from instances of `PierceOrLukasiewiczF` can
exist.  The same computation rules out the other axioms here, each of which also
takes the value `m` somewhere in this algebra.

The two "dip" rows are the whole obstruction: the values that weaken Peirce
(`b` false, `a` unsettled) are exactly the ones that make Lukasiewicz's premise
`¬a → ¬b` vacuous, and conversely.  They never dip together, so no single choice
of `b` leaves both disjuncts informative.

**Two further facts.**  The principle is not intuitionistically provable either:
it fails at the root of the fork of two 2-chains, where one branch settles `a`
only later with `b` false (refuting Peirce) and the other has `b` true at the
bottom with `a` appearing only above (refuting Lukasiewicz).  And it does not
even imply weak excluded middle `¬a ∨ ¬¬a`, which fails in the five element
algebra of upward closed sets of a root with two incomparable successors while
every instance of `PierceOrLukasiewiczF` there is still `1`.  So it is a genuine
intermediate principle, valid in every chain and therefore at or below
Goedel-Dummett `LC`, but well below classical logic.
-/

theorem emF_pierceOrLukF (a b : Prop) : ExcludedMiddleF a → PierceOrLukasiewiczF a b := by
  intro hEx; exact Or.inl (cmF_peirceF a b (emF_cmF a hEx))

theorem emF_pierceOrLukF' (a b : Prop) : ExcludedMiddleF b → PierceOrLukasiewiczF a b := by
  intro hEx
  cases hEx
  case inl hb => exact Or.inl (fun hi => hi (fun _ => hb))
  case inr hnb => exact Or.inr (fun _ hb => False.elim (hnb hb))

def DeMOrLukasiewiczF := fun (a b : Prop) => (¬ (¬ a ∧ ¬ b) → a ∨ b) ∨ ((¬ a → ¬ b) → (b → a))

/-!
### `DeMOrLukasiewiczF` is also strictly weaker

The same `k`-chain models settle this one, and the two element frame already
suffices.  In the three element algebra `0 < m < 1` of upward closed sets of the
2-chain:

```
  a  b | DeM  Luk  join          a  b | DeM  Luk  join
  0  0 |  1    1    1            m  0 |  m    1    1
  0  m |  m    1    1            m  m |  m    1    1
  0  1 |  1    1    1            m  1 |  1    m    1
  1  *  |  1    1    1
```

Every instance again evaluates to `1`, while `ExcludedMiddleF a` is `m` at
`a = m`, so no instantiation of `DeMOrLukasiewiczF` derives excluded middle, nor
any of the other axioms in this file.  Weak excluded middle `¬a ∨ ¬¬a` is out of
reach too: it fails in the five element algebra of a root with two incomparable
successors, where every instance of `DeMOrLukasiewiczF` is still `1`.

Note the contrast with a disjunction built on Peirce instead of De Morgan: this
one is *not* valid in every chain.  In the four element chain `0 < p < q < 1` the
instance `a = p`, `b = q` gives `DeM = q` and `Luk = p`, so the disjunction is
`q ≠ 1`.  Validity here tracks frames of depth at most two rather than linearity.
-/

theorem emF_demOrLukF (a b : Prop) : ExcludedMiddleF a → DeMOrLukasiewiczF a b := by
  intro hEx; exact Or.inr (emF_lukF a b hEx)

theorem emF_demOrLukF' (a b : Prop) : ExcludedMiddleF b → DeMOrLukasiewiczF a b := by
  intro hEx
  cases hEx
  case inl hb => exact Or.inl (fun _ => Or.inr hb)
  case inr hnb => exact Or.inr (fun _ hb => False.elim (hnb hb))

def ImpOrOrLukasiewiczF := fun (a b : Prop) => ((a → b) → (¬ a ∨ b)) ∨ ((¬ a → ¬ b) → (b → a))

/-!
### `ImpOrOrLukasiewiczF` is strictly weaker too, and lands where De Morgan does

Again the three element algebra `0 < m < 1` of upward closed sets of the 2-chain
validates every instance:

```
  a  b | ImpOr  Luk  join          a  b | ImpOr  Luk  join
  0  * |   1     1    1            m  m |   m     1    1
  m  0 |   1     1    1            m  1 |   1     m    1
  1  * |   1     1    1
```

so `ExcludedMiddleF a`, which is `m` at `a = m`, is not derivable from any
instantiation, and neither is anything else in this file.  Weak excluded middle
is again out of reach, by the same root-with-two-successors algebra.

Replacing De Morgan by `ImpOrF` does not move the boundary: like
`DeMOrLukasiewiczF`, and unlike `PierceOrLukasiewiczF`, this fails in the four
element chain `0 < p < q < 1` at `a = p`, `b = q`, where `ImpOr = q` and
`Luk = p`.  Peirce is the only one of the three left disjuncts strong enough to
cover Lukasiewicz all the way up a chain.
-/

theorem emF_impOrOrLukF (a b : Prop) : ExcludedMiddleF a → ImpOrOrLukasiewiczF a b := by
  intro hEx; exact Or.inl (emF_ImpOrF a b hEx)

theorem emF_impOrOrLukF' (a b : Prop) : ExcludedMiddleF b → ImpOrOrLukasiewiczF a b := by
  intro hEx
  cases hEx
  case inl hb => exact Or.inl (fun _ => Or.inr hb)
  case inr hnb => exact Or.inr (fun _ hb => False.elim (hnb hb))
