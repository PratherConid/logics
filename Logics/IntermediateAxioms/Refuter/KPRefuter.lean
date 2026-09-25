import Logics.IntermediateAxioms.AxiomDef
import Logics.FiniteFrame

/-!
# Kreisel and Putnam's axiom, read on frames

Every other axiom in this directory gets a criterion from a short list of
algebras: a schema derives the axiom exactly when it misses the top value in
all of them.  Kreisel and Putnam's axiom,

    (¬a → b ⊔ c) → (¬a → b) ⊔ (¬a → c),

gets its criterion from an *infinite* list instead.  This file supplies that
list, proves it sound, and proves it complete wherever completeness can be had.

## The condition

Everything here is about a frame `P`: a preorder of points, with the
variables ranging over its upward closed sets.  The axiom holds at a point
when that point lies in its value under every choice of the variables, and
holds in the frame when it holds at every point, that is, when its value in
`Upset P` is always the top.  The condition below is a property of the order
on points; no algebra appears in it.

A point `r` of the frame and an upward closed set of points `a` cut out a
region, `↑r ⊓ ¬a`: the points above `r` that have no point of `a` above them.
The axiom holds in the frame exactly when every such region is entered at a
single point (`kp_top_iff_principal`), and fails exactly when some region is
entered at two unrelated points (`kp_ntop_iff_splits`).  So refuting the axiom
is never about the two disjuncts; they only witness a fork the frame already
has.

The condition is about the whole frame, not one point.  The axiom holds at `r`
only if the region at `r` has one entrance, but that is not enough: holding at
`r` means holding at every point above `r`, and a region further up can still
be entered twice.  One entrance at every region from `r` up is enough
(`kp_mem_of_principal`).

Every region having one entrance suffices in any frame, with no finiteness at
all.  The converse needs minimal points, which `HasMinimal` names and every
finite frame has (`hasMinimal_of_list`).  Everything is stated for preorders,
so the proofs never compare points for equality.

## The list

`𝓛` is the class of finite rooted frames in which some region is entered at
two unrelated points (`InKPList`).  By the condition these are exactly the
finite rooted frames refuting the axiom.

* **Soundness**, `kpList_sound`: a schema deriving the axiom fails on every
  frame of `𝓛`.  This needs neither finiteness nor a root.
* **Completeness against finite frames**, `kpList_complete_finite`: a schema
  failing on every frame of `𝓛` validates the axiom on every finite frame it
  holds on.  Where the axiom fails, the points above the failure form a rooted
  frame of `𝓛` (`Above`), and restricting to them is onto, so the schema still
  holds there.
* **The criterion**, `kpList_criterion`, for every schema with the finite
  model property at the axiom (`HasFMPAtKP`): one that derives the axiom as
  soon as every finite frame validating it validates the axiom.  Every schema
  whose logic is tabular or locally finite qualifies.

Whether the criterion holds for *every* schema is open.  It fails exactly if
some finitely axiomatised logic validates the axiom on all its finite frames
without deriving it, and such a logic would have to lack the finite model
property.  No computation over finite frames can reach that question.

## Why the list is infinite

`𝓜`, the frames of `𝓛` minimal in the Jankov order, is infinite: a ladder of
frames, one of each size from seven points up, are all members.  Two steps from
there are argued rather than formalised.  A list that is a criterion must
contain every member of `𝓜`; and a list that decided the axiom on arbitrary
algebras, rather than schema by schema, would by compactness have to be finite.
So no finite list of either kind exists.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

/-- The axiom's value at a triple, as an expression. -/
abbrev kpAt {α : Type} [HeytingAlgebra α] (a b c : α) : α :=
  (neg a ⇨ (b ⊔ c)) ⇨ ((neg a ⇨ b) ⊔ (neg a ⇨ c))

/-- The formula and the expression agree, the formula having three
variables. -/
theorem kreiselPutnamForm_valid_iff {α : Type} [HeytingAlgebra α] :
    (∀ v : Nat → α, (kreiselPutnamForm (.var 0) (.var 1) (.var 2)).eval v = ⊤) ↔ ∀ a b c : α, kpAt a
      b c = ⊤ :=
  ⟨fun h a b c => h (fun n => if n = 0 then a else if n = 1 then b else c),
   fun h v => h (v 0) (v 1) (v 2)⟩

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

/-- **One entrance is enough, point by point.**  If every region above `x` has
a least point, the axiom holds at `x`: the least point settles which disjunct
to take, and upward closure carries it to the rest of the region. -/
theorem kp_mem_of_principal {P : Type} [Frame P] {x : P} {a : Upset P}
    (h : ∀ r, x ≼ r → (kpRegion r a).Principal) (b c : Upset P) :
    (kpAt a b c).mem x := by
  intro r hxr hr
  by_cases hemp : ∃ s, (kpRegion r a).mem s
  · obtain ⟨s, hs⟩ := hemp
    obtain ⟨m, hmem, hmin⟩ := h r hxr s hs
    rcases hr m hmem.1 hmem.2 with hb | hc
    · exact Or.inl fun s' hrs' hna' => b.upward (hmin s' ⟨hrs', hna'⟩) hb
    · exact Or.inr fun s' hrs' hna' => c.upward (hmin s' ⟨hrs', hna'⟩) hc
  · exact Or.inl fun s' hrs' hna' => absurd ⟨s', hrs', hna'⟩ hemp

/-- **One entrance is enough.**  If every region has a least point the axiom
holds at every point, whatever the frame. -/
theorem kp_top_of_principal {P : Type} [Frame P]
    (h : ∀ (r : P) (a : Upset P), (kpRegion r a).Principal) :
    ∀ a b c : Upset P, kpAt a b c = ⊤ := fun a b c =>
  (BoundedLattice.eq_top_iff _).mpr fun _ _ => kp_mem_of_principal (fun r _ => h r a) b c

/-- **Under the axiom a minimal point is least.**  The axiom at `kpTrim r a m`
and `↑m` -- the region with the cone of `m` removed, and that cone -- forces
`m` below the whole region, the first disjunct being refuted by `m` itself.
Only that one instance of the axiom is used. -/
theorem least_of_minimal {P : Type} [Frame P] {r : P} {a : Upset P} {m : P}
    (h : kpAt a (kpTrim r a m) (Upset.up m) = ⊤)
    (hm : (kpRegion r a).Minimal m) : (kpRegion r a).Least m := by
  obtain ⟨hmem, hmin⟩ := hm
  refine ⟨hmem, ?_⟩
  have hkp : (kpAt a (kpTrim r a m) (Upset.up m)).mem r := by
    rw [h]; trivial
  have hant : (neg a ⇨ (kpTrim r a m ⊔ Upset.up m)).mem r := by
    intro s hrs hna
    by_cases hsm : s ≼ m
    · exact Or.inr (hmin s ⟨hrs, hna⟩ hsm)
    · exact Or.inl ⟨⟨hrs, hna⟩, hsm⟩
  rcases hkp r (Frame.le_refl r) hant with hb | hc
  · exact absurd (Frame.le_refl m) (hb m hmem.1 hmem.2).2
  · exact fun q hq => hc q hq.1 hq.2

/-- **And one entrance is necessary**, wherever minimal points exist. -/
theorem principal_of_kp_top {P : Type} [Frame P] (hm : HasMinimal P)
    (h : ∀ a b c : Upset P, kpAt a b c = ⊤) (r : P) (a : Upset P) :
    (kpRegion r a).Principal := by
  intro p hp
  obtain ⟨m, hmem, hmin⟩ := hm (kpRegion r a).mem ⟨p, hp⟩
  exact ⟨m, least_of_minimal (h _ _ _) ⟨hmem, hmin⟩⟩

/-- **A split refutes the axiom**, in any frame: of two unrelated minimal
points, the axiom would put each below the other. -/
theorem kp_ntop_of_splits {P : Type} [Frame P] {r : P} {a : Upset P}
    (hs : (kpRegion r a).Splits) : ¬ ∀ a b c : Upset P, kpAt a b c = ⊤ := by
  obtain ⟨m, m', hm, hm', hmm', _⟩ := hs
  exact fun h => hmm' ((least_of_minimal (h _ _ _) hm).2 m' hm'.1)

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
  · rintro ⟨r, a, hsp⟩
    exact kp_ntop_of_splits hsp

/-! ## The points above a point

The points above a failure form a rooted frame (`Above`), and the region at
the failure is the region at that frame's root. -/

namespace Above

variable {P : Type} [Frame P] {r : P}

/-- A point above `r` is in the region at the root exactly when it is in the
region at `r` of the whole frame. -/
theorem region_iff (a : Upset P) (q : Above r) :
    (kpRegion (root r) (restrict a)).mem q ↔ (kpRegion r a).mem q.pt :=
  ⟨fun ⟨_, hn⟩ => ⟨q.above, fun p hqp hap =>
      hn ⟨p, Frame.le_trans q.above hqp⟩ hqp hap⟩,
   fun ⟨_, hn⟩ => ⟨q.above, fun q' hqq' haq' => hn q'.pt hqq' haq'⟩⟩

/-- A split at `r` is a split at the root of the points above `r`. -/
theorem splits {a : Upset P} (hs : (kpRegion r a).Splits) :
    (kpRegion (root r) (restrict a)).Splits := by
  obtain ⟨m, m', ⟨hm, hmin⟩, ⟨hm', hmin'⟩, hmm', hm'm⟩ := hs
  refine ⟨⟨m, hm.1⟩, ⟨m', hm'.1⟩,
    ⟨(region_iff a _).mpr hm,
      fun q hq hqm => hmin q.pt ((region_iff a q).mp hq) hqm⟩,
    ⟨(region_iff a _).mpr hm',
      fun q hq hqm => hmin' q.pt ((region_iff a q).mp hq) hqm⟩,
    hmm', hm'm⟩

end Above

/-! ## The list -/

/-- **The list `𝓛`**: finite rooted frames in which some region is entered at
two unrelated points. -/
structure InKPList (P : Type) [Frame P] : Prop where
  finite : ∃ l : List P, ∀ p, p ∈ l
  rooted : ∃ r : P, ∀ p, r ≼ p
  splits : ∃ (r : P) (a : Upset P), (kpRegion r a).Splits

/-- **Soundness.**  A schema deriving the axiom fails on every frame of `𝓛`,
since the split refutes the axiom there. -/
theorem kpList_sound {X : Form}
    (h : DerivesFromSchema X (kreiselPutnamForm (.var 0) (.var 1) (.var 2)))
    {P : Type} [Frame P] (hP : InKPList P) :
    ¬ ∀ w : Nat → Upset P, X.eval w = ⊤ := fun hv => by
  obtain ⟨_, _, hs⟩ := hP.splits
  exact kp_ntop_of_splits hs
    (kreiselPutnamForm_valid_iff.mp (DerivesFromSchema.valid hv h))

/-- **Completeness against finite frames.**  A schema failing on every frame of
`𝓛` validates the axiom on every finite frame it holds on: where the axiom
fails, the points above the failure would be a frame of `𝓛` validating the
schema. -/
theorem kpList_complete_finite {X : Form}
    (hX : ∀ (Q : Type) [Frame Q], InKPList Q → ¬ ∀ w : Nat → Upset Q, X.eval w = ⊤)
    {P : Type} [Frame P] (hfin : ∃ l : List P, ∀ p, p ∈ l)
    (hv : ∀ w : Nat → Upset P, X.eval w = ⊤) :
    ∀ v : Nat → Upset P, (kreiselPutnamForm (.var 0) (.var 1) (.var 2)).eval v = ⊤ := by
  obtain ⟨l, hl⟩ := hfin
  refine kreiselPutnamForm_valid_iff.mpr (Classical.byContradiction fun hkp => ?_)
  obtain ⟨r, a, hs⟩ := (kp_ntop_iff_splits (hasMinimal_of_list l hl)).mp hkp
  exact hX (Above r)
    ⟨⟨Above.cover r l, Above.mem_cover hl⟩, ⟨Above.root r, fun q => q.above⟩,
      ⟨Above.root r, Above.restrict a, Above.splits hs⟩⟩
    (valid_of_onto (Above.onto r) hv)

/-- The finite model property of a schema at the axiom: it derives the axiom
as soon as every finite frame validating it validates the axiom.  Every schema
whose logic has the finite model property has it here. -/
def HasFMPAtKP (X : Form) : Prop :=
  (∀ (P : Type) [Frame P], (∃ l : List P, ∀ p, p ∈ l) →
      (∀ w : Nat → Upset P, X.eval w = ⊤) →
      ∀ v : Nat → Upset P, (kreiselPutnamForm (.var 0) (.var 1) (.var 2)).eval v = ⊤) →
    DerivesFromSchema X (kreiselPutnamForm (.var 0) (.var 1) (.var 2))

/-- **Completeness**, for a schema with the finite model property at the
axiom. -/
theorem kpList_complete {X : Form} (hfmp : HasFMPAtKP X)
    (hX : ∀ (Q : Type) [Frame Q], InKPList Q → ¬ ∀ w : Nat → Upset Q, X.eval w = ⊤) :
    DerivesFromSchema X (kreiselPutnamForm (.var 0) (.var 1) (.var 2)) :=
  hfmp fun P iP hfin hv => @kpList_complete_finite X hX P iP hfin hv

/-- **The criterion.**  For a schema with the finite model property at the
axiom, deriving the axiom is the same as failing on every frame of `𝓛`. -/
theorem kpList_criterion {X : Form} (hfmp : HasFMPAtKP X) :
    DerivesFromSchema X (kreiselPutnamForm (.var 0) (.var 1) (.var 2)) ↔
      ∀ (Q : Type) [Frame Q], InKPList Q → ¬ ∀ w : Nat → Upset Q, X.eval w = ⊤ :=
  ⟨fun h _ _ hQ => kpList_sound h hQ, kpList_complete hfmp⟩
