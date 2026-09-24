import Logics.Heyting

/-!
# Kreisel and Putnam's axiom, read on frames

Every other axiom in this directory gets a *criterion*: a short list of
algebras refuting it minimally, and a theorem saying a schema derives the axiom
exactly when it misses the top value in all of them.  Kreisel and Putnam's
axiom,

    (¬a → b ⊔ c) → (¬a → b) ⊔ (¬a → c),

gets none, and this file explains why rather than supplying one.

## The condition

A point `r` and an upward closed set `a` cut out a region, `↑r ⊓ ¬a`: the
points above `r` that refute `a` outright.  Then

* the axiom holds at `r` for every `b` and `c` exactly when that region is
  entered at a single point (`kp_top_iff_principal`), and
* it fails exactly when the region is entered at two unrelated points
  (`kp_ntop_iff_splits`).

So refuting the axiom is never about the two disjuncts.  They only witness a
fork that the frame already has, and any `b`, `c` splitting the region will do.
That is the whole reason the refuters are so much freer here than elsewhere: a
frame refutes the axiom as soon as some region has two entrances, and there are
many unrelated ways to arrange that.

`¬a` is what keeps the regions from being arbitrary.  In a finite frame a point
lies in `¬a` exactly when every maximal point above it avoids `a`, so the
regions are the sets of points *pure* for a set of maximal points.  That
reading is not formalised here -- it needs maximal points to exist, a second
use of finiteness -- and nothing below depends on it.

## Both halves, and what each costs

One entrance suffices in *any* frame, with no finiteness at all: the least
point of the region settles which disjunct to take, and upward closure carries
it to the rest.  The converse needs minimal points to exist, and that is the
only thing `HasMinimal` is for.  Given a minimal point `m` of the region, the
axiom instantiated at the region with that point's cone removed, and at the
cone itself, forces the point below the whole region -- the first disjunct
being refuted by the point itself.

Everything is stated for preorders, since a frame here carries no antisymmetry,
so the proofs never compare points for equality.

## Why there is no criterion

A search outside Lean, over every frame with at most nine points, turns up new
minimal refuters at each size: one with four points, two with five, three with
six, three with seven, five with eight and six with nine, with no sign of
stopping.  From seven points on they are strikingly uniform -- exactly two
maximal points, and a fixed pure part of two points over a shared tip, with all
the variation in the impure layer routing the root to them.  None of that is
formalised, and it is evidence rather than proof; but it is why this file
carries a condition on frames instead of a list of algebras.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

/-- The axiom's value at a triple, as an expression. -/
abbrev kpAt {α : Type} [HeytingAlgebra α] (a b c : α) : α :=
  (neg a ⇨ (b ⊔ c)) ⇨ ((neg a ⇨ b) ⊔ (neg a ⇨ c))

/-! ## Regions -/

/-- The region the axiom speaks about: the points above `r` refuting `a`. -/
def kpRegion {P : Type} [Frame P] (r : P) (a : Upset P) : Upset P :=
  Upset.up r ⊓ neg a

/-- The region with everything below `m` removed.  It stays upward closed
because a point above one that misses `m` misses `m` too. -/
def kpTrim {P : Type} [Frame P] (r : P) (a : Upset P) (m : P) : Upset P :=
  ⟨fun q => (kpRegion r a).mem q ∧ ¬ q ≼ m,
   fun hxy hx => ⟨(kpRegion r a).upward hxy hx.1,
     fun hym => hx.2 (Frame.le_trans hxy hym)⟩⟩

/-- **One entrance is enough.**  If every region has a least point the axiom
holds, whatever the frame: the least point settles which disjunct to take, and
upward closure carries it to the rest of the region. -/
theorem kp_top_of_principal {P : Type} [Frame P]
    (h : ∀ (r : P) (a : Upset P), (kpRegion r a).Principal) :
    ∀ a b c : Upset P, kpAt a b c = ⊤ := by
  intro a b c
  refine (BoundedLattice.eq_top_iff _).mpr ?_
  intro p _ r _ hr
  by_cases hemp : ∃ s, (kpRegion r a).mem s
  · obtain ⟨s, hs⟩ := hemp
    obtain ⟨m, hmem, hmin⟩ := h r a s hs
    rcases hr m hmem.1 hmem.2 with hb | hc
    · exact Or.inl fun s' hrs' hna' => b.upward (hmin s' ⟨hrs', hna'⟩) hb
    · exact Or.inr fun s' hrs' hna' => c.upward (hmin s' ⟨hrs', hna'⟩) hc
  · exact Or.inl fun s' hrs' hna' => absurd ⟨s', hrs', hna'⟩ hemp

/-- **And it is necessary.**  Given a minimal point `m` of the region, the
axiom at `kpTrim r a m` and `↑m` -- the region with the cone of `m` removed,
and that cone -- forces `m` to lie below the whole region. -/
theorem principal_of_kp_top {P : Type} [Frame P] (hm : HasMinimal P)
    (h : ∀ a b c : Upset P, kpAt a b c = ⊤) (r : P) (a : Upset P) :
    (kpRegion r a).Principal := by
  intro p hp
  obtain ⟨m, hmem, hmin⟩ := hm (kpRegion r a).mem ⟨p, hp⟩
  refine ⟨m, hmem, ?_⟩
  have hkp : (kpAt a (kpTrim r a m) (Upset.up m)).mem r := by
    rw [h a (kpTrim r a m) (Upset.up m)]; trivial
  have hant : (neg a ⇨ (kpTrim r a m ⊔ Upset.up m)).mem r := by
    intro s hrs hna
    by_cases hsm : s ≼ m
    · exact Or.inr (hmin s ⟨hrs, hna⟩ hsm)
    · exact Or.inl ⟨⟨hrs, hna⟩, hsm⟩
  rcases hkp r (Frame.le_refl r) hant with hb | hc
  · exact absurd (Frame.le_refl m) (hb m hmem.1 hmem.2).2
  · exact fun q hq => hc q hq.1 hq.2

/-- **The frame condition.** -/
theorem kp_top_iff_principal {P : Type} [Frame P] (hm : HasMinimal P) :
    (∀ a b c : Upset P, kpAt a b c = ⊤) ↔
      ∀ (r : P) (a : Upset P), (kpRegion r a).Principal :=
  ⟨fun h r a => principal_of_kp_top hm h r a, kp_top_of_principal⟩

/-- **The failure form.**  The axiom fails in a frame exactly when, for some
point and some upward closed set, the region they cut out is entered at two
unrelated points. -/
theorem kp_ntop_iff_splits {P : Type} [Frame P] (hm : HasMinimal P) :
    (¬ ∀ a b c : Upset P, kpAt a b c = ⊤) ↔
      ∃ (r : P) (a : Upset P), (kpRegion r a).Splits := by
  constructor
  · intro h
    refine Classical.byContradiction fun hcon => h (kp_top_of_principal ?_)
    intro r a
    exact Classical.byContradiction fun hnp =>
      hcon ⟨r, a, (Upset.not_principal_iff_splits hm _).mp hnp⟩
  · rintro ⟨r, a, hsp⟩ hall
    exact (Upset.not_principal_iff_splits hm _).mpr hsp
      (principal_of_kp_top hm hall r a)
