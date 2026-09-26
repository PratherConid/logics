import Logics.IntermediateAxioms.Refuter.KPRefuter
import Logics.Reduction

/-!
# The minimal refuters of Kreisel and Putnam's axiom

`𝓜` is the part of the list `𝓛` that is minimal in the Jankov order: frames
refuting the axiom below which nothing smaller refutes it (`InKPMin`).  It is
taken among posets.  That loses nothing, since a preorder has the same upward
closed sets as the poset of its equivalence classes, and it is needed, since
duplicating a point changes the frame without changing the algebra.

Three results, in turn: the shape every member has; an exact description of the
members in the one regime that grows; and a ladder of members, one of each size
from seven points up, so that `𝓜` is infinite.

## The method

Every clause below is proved the same way: shrink the frame, check that the
axiom still fails, and conclude that a member of `𝓜` admits no such shrinking.

*Counting* (`length_le_of_sh`): an algebra of upward closed sets lies below
another only if its poset has at most as many points.  So nothing strictly
smaller refuting the axiom lies below a member of `𝓜` (`no_smaller`).

*Two shrinkings*: the points above a point, a homomorphic image; and merging
points, a subalgebra.  Every merge used collapses a set of points onto one of
its members.  The axiom's failure survives a merge in one of two ways: the
split itself survives, its entrances kept minimal and apart
(`no_collapse_single`), or the failure at one entrance survives, the three sets
witnessing it never separating merged points (`no_collapse_triple`).

The two shrinkings are all there is.  A frame of `𝓛` is in `𝓜` exactly when the
axiom fails only at points below everything and holds after merging any α- or
β-pair (`inKPMin_iff`): a condition on finitely many smaller frames, and the one
a machine search checks.

## The shape

Fix a member of `𝓜` and a split (`RootSplit`): two unrelated minimal points
`u`, `v` of the region cut out at a point.

* The split is at the root (`root_of_splits`), and the root is the only point
  below both entrances (`eq_root_of_le_both`).
* Exactly one maximal point `A` lies outside the region (`exists_outside`,
  `outside_unique`), everything outside the region lies below it
  (`le_outside`), and the region is exactly what lies off it (`mem_iff`).
* The entrances are both maximal or both not (`max_iff`).  With `u` maximal,
  collapsing everything above `v` onto `v` keeps the failure at `u`.
* **Both maximal.**  The region is `{u, v}` (`regimeA_region`); every other
  point but the root sees `A` and exactly one entrance (`regimeA_points`); and
  at most one point sees each entrance alone (`regimeA_side`).  So there are at
  most six points, and at most three such frames up to isomorphism: the three
  branch fork on `A`, `u` and `v`, and that fork with a point added below `A`
  and one entrance, or below `A` and each entrance.
* **Neither maximal.**  The region has one maximal point `B`
  (`regimeB_max_unique`) and is `{u, v, B}` (`regimeB_region`), with `u` and `v`
  covered by `B` alone (`regimeB_above_u`), and every point off the region but
  `A` sees both `A` and `B` (`regimeB_sees`).  That is the second regime's shape
  (`InKPMin.exists_regimeB`), which the next part decides exactly.

So the first regime is finite, and every other member lies in the second.

## The second regime, exactly

A frame of the second regime's shape (`RegimeB`) has a root `r`, maximal points
`A` and `B`, entrances `u` and `v` covered by `B` alone, and the rest, the
*wiring*, below `A` and `B` with none but the root seeing both entrances.  It is
*reduced* when no wiring point takes part in an α- or β-pair
(`RegimeB.Reduced`); the pairs it still has lie among `A`, `B`, `u` and `v`
(`RegimeB.pair_cases`).

**A finite poset of the shape is in `𝓜` exactly when it is reduced**
(`RegimeB.inKPMin_iff_reduced`).  So the members of `𝓜` split at non-maximal
entrances are exactly the reduced finite posets of the shape
(`inKPMin_regimeB_iff`).

* *A member is reduced.*  A pair touching the wiring avoids `A` and both
  entrances, so merging it keeps the split (Tool A, `no_merge_single`).
* *A reduced frame is a member*, by `inKPMin_iff`.  Every region has one
  entrance except the region `{u, v, B}` at the root (`RegimeB.principal`), so
  the axiom fails only there; and the steps that remain, merging `A` with `B` or
  two of `u`, `v`, `B`, leave no triple of sets that splits that region
  (`RegimeB.kp_top_of`).

## `𝓜` is infinite

`kpMin_infinite`: the ladder frames `LPt n` are all members, and no two of them
lie below each other both ways.

`LPt n` has a root; two maximal points `A` and `B`; `u` and `v`, each covered by
`B` alone; a point `c0` covered by `A` and `B`; and a Rieger--Nishimura ladder
`w 0, …, w n` on the side of `u`.  Every rung sees `u`, `A` and `B` but not `v`;
rung `i` sees rung `j` exactly when `j + 2 ≤ i`; and every rung but the bottom
one sees `c0`.  There are `n + 7` points (`length_all`), and the ladder has the
second regime's shape (`LPt.regimeB`).

So it is a member once it is reduced (`LPt.reduced`), and that is where the
ladder's shape is used.  The wiring is `c0` and the rungs.  `c0` sees neither
entrance and the rungs see `u`, so `c0` pairs with no rung; two rungs differ in
what lies strictly above them (`not_beta_w`); and no rung collapses into
another, which would have to lie below `c0` and below the rungs two and three
beneath the first.

Two ladders of different lengths are told apart by counting points
(`le_of_sh`).

## What is not here

That the three frames of the first regime pass the test of `inKPMin_iff` is
checked by machine but not formalised.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

/-- Homomorphisms carry the axiom's value along. -/
theorem Hom.map_kpAt {α β : Type} [HeytingAlgebra α] [HeytingAlgebra β] (f : Hom α β)
    (a b c : α) : f.toFun (kpAt a b c) = kpAt (f.toFun a) (f.toFun b) (f.toFun c) := by
  simp only [kpAt, f.map_himp, f.map_sup, f.map_neg]

/-! ## How a merge keeps the axiom refuted, or validates it -/

namespace Merger

variable {M : Type} [Frame M] (m : Merger M)

/-- A failure of the axiom at sets that never separate merged points survives
the merge: lift the three sets, and pulling back returns them. -/
theorem kp_ntop_of_sat {a b c : Upset M}
    (ha : ∀ x, a.mem x ↔ a.mem (m.g x)) (hb : ∀ x, b.mem x ↔ b.mem (m.g x))
    (hc : ∀ x, c.mem x ↔ c.mem (m.g x)) (hne : kpAt a b c ≠ ⊤) :
    ¬ ∀ a b c : Upset m.Pt, kpAt a b c = ⊤ := by
  intro h
  apply hne
  have := congrArg m.pullHom.toFun (h (m.lift a ha) (m.lift b hb) (m.lift c hc))
  rw [Hom.map_kpAt, m.pullHom.map_top] at this
  show kpAt a b c = ⊤
  rw [← m.pull_lift a ha, ← m.pull_lift b hb, ← m.pull_lift c hc]
  exact this

/-- **The axiom holds after a merge** when it holds at every triple of sets
never separating merged points: those are the sets pulled back, and pulling
back is one to one. -/
theorem kp_top_of_sat
    (h : ∀ a b c : Upset M, (∀ x, a.mem x ↔ a.mem (m.g x)) → (∀ x, b.mem x ↔ b.mem (m.g x)) →
      (∀ x, c.mem x ↔ c.mem (m.g x)) → kpAt a b c = ⊤) :
    ∀ a b c : Upset m.Pt, kpAt a b c = ⊤ := fun a b c =>
  m.pull_injective ((Hom.map_kpAt m.pullHom a b c).trans
    ((h _ _ _ ((m.pulled_iff _).mp ⟨a, rfl⟩) ((m.pulled_iff _).mp ⟨b, rfl⟩)
      ((m.pulled_iff _).mp ⟨c, rfl⟩)).trans m.pullHom.map_top.symm))

/-- Collapsing two maximal points onto one of them merges correctly: nothing
lies above either but itself. -/
theorem max_pair_merges {x₀ x₁ : M} (h₀ : IsMaxPt x₀) (h₁ : IsMaxPt x₁) {x x' y : M}
    (hx : x = x₀ ∨ x = x₁) (_ : x' = x₀ ∨ x' = x₁) (hxy : x ≼ y) :
    (y = x₀ ∨ y = x₁) ∨ x' ≼ y := by
  left
  rcases hx with rfl | rfl
  · exact Or.inl (h₀ y hxy)
  · exact Or.inr (h₁ y hxy)

/-- With `ρ` a root and `a` never separating merged points, a representative is
in the merged region exactly when it is in the original one. -/
theorem region_iff {ρ : M} (hρ : ∀ p, ρ ≼ p) {a : Upset M}
    (ha : ∀ x, a.mem x ↔ a.mem (m.g x)) (q : m.Pt) :
    (kpRegion (m.proj ρ) (m.lift a ha)).mem q ↔ (kpRegion ρ a).mem q.pt := by
  constructor
  · rintro ⟨_, hn⟩
    refine ⟨hρ q.pt, fun y hqy hay => hn (m.proj y) ?_ ((ha y).mp hay)⟩
    have := m.proj_mono hqy
    rwa [m.proj_fixed] at this
  · rintro ⟨_, hn⟩
    refine ⟨?_, fun q' hqq' haq' => ?_⟩
    · have := m.proj_mono (hρ q.pt)
      rwa [m.proj_fixed] at this
    · obtain ⟨y, hy, hqy⟩ := hqq'
      exact hn y hqy ((ha y).mpr (by rw [hy]; exact haq'))

/-- **A split survives a merge** whose classes of the two entrances consist of
minimal points and lie apart. -/
theorem splits {ρ : M} (hρ : ∀ p, ρ ≼ p) {a : Upset M}
    (ha : ∀ x, a.mem x ↔ a.mem (m.g x)) {u v : M}
    (hcu : ∀ y, m.g y = m.g u → (kpRegion ρ a).Minimal y)
    (hcv : ∀ y, m.g y = m.g v → (kpRegion ρ a).Minimal y)
    (hinc : ∀ y y', m.g y = m.g u → m.g y' = m.g v → ¬ y ≼ y')
    (hinc' : ∀ y y', m.g y = m.g u → m.g y' = m.g v → ¬ y' ≼ y) :
    (kpRegion (m.proj ρ) (m.lift a ha)).Splits := by
  have hmin : ∀ w : M, (∀ y, m.g y = m.g w → (kpRegion ρ a).Minimal y) →
      (kpRegion (m.proj ρ) (m.lift a ha)).Minimal (m.proj w) := by
    intro w hw
    refine ⟨(m.region_iff hρ ha _).mpr (hw (m.g w) (m.idem w)).1, fun q hq hqw => ?_⟩
    obtain ⟨y, hy, hqy⟩ := hqw
    have hyq : y ≼ q.pt := (hw y hy).2 q.pt ((m.region_iff hρ ha q).mp hq) hqy
    have := m.proj_mono hyq
    rwa [m.proj_fixed, show m.proj y = m.proj w from Pt.ext m hy] at this
  refine ⟨m.proj u, m.proj v, hmin u hcu, hmin v hcv, ?_, ?_⟩
  · rintro ⟨y, hy, huy⟩
    exact hinc (m.g u) y (m.idem u) hy huy
  · rintro ⟨y, hy, hvy⟩
    exact hinc' y (m.g v) hy (m.idem v) hvy

end Merger

/-! ## The minimal refuters -/

/-- **The minimal refuters `𝓜`**, taken among posets. -/
structure InKPMin (M : Type) [Frame M] : Prop where
  list : InKPList M
  antisymm : Frame.Antisymm M
  minimal : RefuterLB (Upset M) (kreiselPutnamForm (.var 0) (.var 1) (.var 2))

namespace InKPMin

variable {M : Type} [Frame M]

theorem exists_nodup (hM : InKPMin M) : ∃ l : List M, l.Nodup ∧ ∀ p, p ∈ l := by
  obtain ⟨l, hl⟩ := hM.list.finite
  exact ListCount.exists_nodup_of_mem hl

theorem exists_max_above (hM : InKPMin M) (x : M) : ∃ m, x ≼ m ∧ IsMaxPt m :=
  let ⟨_, hl⟩ := hM.list.finite
  _root_.exists_max_above hM.antisymm hl x

/-- **Nothing smaller below refutes the axiom.**  Minimality would put the
member below the smaller frame, and counting forbids that. -/
theorem no_smaller (hM : InKPMin M) {lM : List M} (hnd : lM.Nodup) (hlM : ∀ p, p ∈ lM)
    {Q : Type} [Frame Q] {lQ : List Q} (hlQ : ∀ q, q ∈ lQ) (hlt : lQ.length < lM.length)
    (hsh : SH (Upset Q) (Upset M)) (hkp : ¬ ∀ a b c : Upset Q, kpAt a b c = ⊤) :
    False :=
  absurd (length_le_of_sh hM.antisymm hnd hlM hlQ
      (hM.minimal (Upset Q) inferInstance hsh
        (fun hv => hkp (kreiselPutnamForm_valid_iff.mp hv))))
    (Nat.not_le.mpr hlt)

/-- No merge that really merges keeps the axiom refuted. -/
theorem no_merge (hM : InKPMin M) (m : Merger M) {x : M} (hx : m.g x ≠ x)
    (hkp : ¬ ∀ a b c : Upset m.Pt, kpAt a b c = ⊤) : False := by
  obtain ⟨l, hnd, hl⟩ := hM.exists_nodup
  exact hM.no_smaller hnd hl (m.mem_cover hl) (m.length_cover_lt (hl x) hx) m.sh hkp

/-- **The axiom fails only at the root**: a split anywhere is a split at a
point below everything, since the points above it would be a smaller refuter. -/
theorem root_of_splits (hM : InKPMin M) {x : M} {a : Upset M}
    (hs : (kpRegion x a).Splits) : ∀ p, x ≼ p := by
  intro p
  refine Classical.byContradiction fun hxp => ?_
  obtain ⟨l, hnd, hl⟩ := hM.exists_nodup
  exact hM.no_smaller hnd hl (Above.mem_cover hl) (Above.length_cover_lt (hl p) hxp)
    (Above.sh x) (kp_ntop_of_splits (Above.splits hs))

end InKPMin

/-! ## Membership, read on frames

What lies below the algebra of a finite poset is reached by passing to the
points of an upward closed set and by merging, and a merge that does anything
lies below a single α- or β-step (`refuterLB_iff_steps`).  For the axiom the
first kind of step needs no separate check: a failure on the points of an upward
closed set is a failure of the whole frame at one of those points
(`Within.splits_pt`), so it is ruled out by the axiom failing only at points
below everything. -/

namespace Within

variable {M : Type} [Frame M] {U : Upset M}

/-- A point of `U` is in a region there exactly when it is in the region of the
whole frame cut out by the extended set. -/
theorem region_iff {r : Within U} (a : Upset (Within U)) (q : Within U) :
    (kpRegion r a).mem q ↔ (kpRegion r.pt (extend a)).mem q.pt :=
  ⟨fun ⟨hr, hn⟩ => ⟨hr, fun y hqy ⟨hy, hay⟩ => hn ⟨y, hy⟩ hqy hay⟩,
   fun ⟨hr, hn⟩ => ⟨hr, fun q' hqq' haq' => hn q'.pt hqq' ⟨q'.mem, haq'⟩⟩⟩

/-- A split on the points of `U` is a split of the whole frame, the region lying
inside `U`. -/
theorem splits_pt {r : Within U} {a : Upset (Within U)} (hs : (kpRegion r a).Splits) :
    (kpRegion r.pt (extend a)).Splits := by
  obtain ⟨m, m', ⟨hm, hmin⟩, ⟨hm', hmin'⟩, hmm', hm'm⟩ := hs
  have hU : ∀ {z : M}, (kpRegion r.pt (extend a)).mem z → U.mem z :=
    fun hz => U.upward hz.1 r.mem
  exact ⟨m.pt, m'.pt,
    ⟨(region_iff a m).mp hm, fun z hz hzm => hmin ⟨z, hU hz⟩ ((region_iff a _).mpr hz) hzm⟩,
    ⟨(region_iff a m').mp hm', fun z hz hzm => hmin' ⟨z, hU hz⟩ ((region_iff a _).mpr hz) hzm⟩,
    hmm', hm'm⟩

end Within

/-- **Membership in `𝓜`, read on frames.**  A frame of `𝓛` that is a poset is a
minimal refuter exactly when the axiom fails only at points below everything and
holds after merging any α- or β-pair.  The points of a proper upward closed set
then validate the axiom, since a failure there would be a failure at a point
of the set, which is not below everything. -/
theorem inKPMin_iff {M : Type} [Frame M] :
    InKPMin M ↔ InKPList M ∧ Frame.Antisymm M ∧
      (∀ (r : M) (a : Upset M), (kpRegion r a).Splits → ∀ p, r ≼ p) ∧
      ∀ (x y : M) (h : IsAlpha x y ∨ IsBeta x y),
        ∀ a b c : Upset (Merger.pair x y h).Pt, kpAt a b c = ⊤ := by
  constructor
  · intro hM
    obtain ⟨l, hl⟩ := hM.list.finite
    exact ⟨hM.list, hM.antisymm, fun _ _ hs => hM.root_of_splits hs, fun x y h =>
      kreiselPutnamForm_valid_iff.mp
        (((refuterLB_iff_steps hM.antisymm l hl _).mp hM.minimal).2 x y h)⟩
  · rintro ⟨hL, hA, hroot, hstep⟩
    obtain ⟨l, hl⟩ := hL.finite
    refine ⟨hL, hA, (refuterLB_iff_steps hA l hl _).mpr ⟨fun U hU => ?_, fun x y h =>
      kreiselPutnamForm_valid_iff.mpr (hstep x y h)⟩⟩
    refine kreiselPutnamForm_valid_iff.mpr (Classical.byContradiction fun hkp => hU ?_)
    obtain ⟨r, a, hs⟩ :=
      (kp_ntop_iff_splits (hasMinimal_of_list _ (Within.mem_cover hl))).mp hkp
    have hr := hroot _ _ (Within.splits_pt hs)
    exact Upset.eq_top_of_mem fun p => U.upward (hr p) r.mem

/-- A split at the root: two unrelated minimal points of the region that `a`
cuts out there. -/
structure RootSplit (M : Type) [Frame M] where
  root : M
  isRoot : ∀ p, root ≼ p
  a : Upset M
  u : M
  v : M
  min_u : (kpRegion root a).Minimal u
  min_v : (kpRegion root a).Minimal v
  not_uv : ¬ u ≼ v
  not_vu : ¬ v ≼ u

namespace RootSplit

variable {M : Type} [Frame M] (S : RootSplit M)

/-- The region, which is what the clauses are about. -/
abbrev R : Upset M := kpRegion S.root S.a

/-- The same split, entrances exchanged. -/
def swap : RootSplit M :=
  ⟨S.root, S.isRoot, S.a, S.v, S.u, S.min_v, S.min_u, S.not_vu, S.not_uv⟩

@[simp] theorem swap_R : S.swap.R = S.R := rfl
@[simp] theorem swap_u : S.swap.u = S.v := rfl
@[simp] theorem swap_v : S.swap.v = S.u := rfl

/-- The region's own negation cuts the same region out, and it is the choice
of defining set that merges keep: whether a point reaches the region. -/
theorem region_canon : kpRegion S.root (neg S.R) = S.R := by
  have htop : Upset.up S.root = ⊤ := Upset.eq_top_of_mem S.isRoot
  show Upset.up S.root ⊓ neg (neg (Upset.up S.root ⊓ neg S.a)) =
    Upset.up S.root ⊓ neg S.a
  have ht : ∀ x : Upset M, ⊤ ⊓ x = x := fun x => by rw [inf_comm, inf_top]
  rw [htop]
  simp only [ht]
  exact neg_neg_neg _

theorem root_not_mem : ¬ S.R.mem S.root := fun h =>
  S.not_uv (Frame.le_trans (S.min_u.2 S.root h (S.isRoot S.u)) (S.isRoot S.v))

theorem exists_a_of_not_mem {x : M} (hx : ¬ S.R.mem x) : ∃ y, x ≼ y ∧ S.a.mem y :=
  Classical.byContradiction fun hc =>
    hx ⟨S.isRoot x, fun y hxy hay => hc ⟨y, hxy, hay⟩⟩

theorem not_mem_of_a {y : M} (hy : S.a.mem y) : ¬ S.R.mem y :=
  fun h => h.2 y (Frame.le_refl y) hy

end RootSplit

namespace InKPMin

variable {M : Type} [Frame M]

theorem exists_rootSplit (hM : InKPMin M) : Nonempty (RootSplit M) := by
  obtain ⟨x, a, u, v, hu, hv, huv, hvu⟩ := hM.list.splits
  exact ⟨⟨x, hM.root_of_splits ⟨u, v, hu, hv, huv, hvu⟩, a, u, v, hu, hv, huv, hvu⟩⟩

/-- **Tool A**: a merge keeping both entrances' classes minimal and apart, and
never merging a point that reaches the region with one that does not. -/
theorem no_merge_split (hM : InKPMin M) (S : RootSplit M) (m : Merger M)
    (hsat : ∀ x, (neg S.R).mem x ↔ (neg S.R).mem (m.g x))
    (hcu : ∀ y, m.g y = m.g S.u → S.R.Minimal y)
    (hcv : ∀ y, m.g y = m.g S.v → S.R.Minimal y)
    (hinc : ∀ y y', m.g y = m.g S.u → m.g y' = m.g S.v → ¬ y ≼ y' ∧ ¬ y' ≼ y)
    {x : M} (hx : m.g x ≠ x) : False := by
  have hc := S.region_canon
  refine hM.no_merge m hx (kp_ntop_of_splits (m.splits S.isRoot hsat ?_ ?_
    (fun y y' hy hy' => (hinc y y' hy hy').1) (fun y y' hy hy' => (hinc y y' hy hy').2)))
  · intro y hy; rw [hc]; exact hcu y hy
  · intro y hy; rw [hc]; exact hcv y hy

/-- Tool A for merges that leave both entrances alone. -/
theorem no_merge_single (hM : InKPMin M) (S : RootSplit M) (m : Merger M)
    (hsat : ∀ x, (neg S.R).mem x ↔ (neg S.R).mem (m.g x))
    (hu : ∀ y, m.g y = m.g S.u → y = S.u) (hv : ∀ y, m.g y = m.g S.v → y = S.v)
    {x : M} (hx : m.g x ≠ x) : False :=
  hM.no_merge_split S m hsat (fun y hy => hu y hy ▸ S.min_u) (fun y hy => hv y hy ▸ S.min_v)
    (fun y y' hy hy' => by rw [hu y hy, hv y' hy']; exact ⟨S.not_uv, S.not_vu⟩) hx

/-- **Tool B**: a merge never separating the points that reach the region, nor
the region with `u`'s cone removed, nor `u`'s cone. -/
theorem no_merge_triple (hM : InKPMin M) (S : RootSplit M) (m : Merger M)
    (hsa : ∀ x, (neg S.R).mem x ↔ (neg S.R).mem (m.g x))
    (hsb : ∀ x, (S.R.mem x ∧ ¬ x ≼ S.u) ↔ (S.R.mem (m.g x) ∧ ¬ m.g x ≼ S.u))
    (hsc : ∀ x, S.u ≼ x ↔ S.u ≼ m.g x)
    {x : M} (hx : m.g x ≠ x) : False := by
  have hc := S.region_canon
  have hmin : (kpRegion S.root (neg S.R)).Minimal S.u := by rw [hc]; exact S.min_u
  have hne : kpAt (neg S.R) (kpTrim S.root (neg S.R) S.u) (Upset.up S.u) ≠ ⊤ :=
    fun h => S.not_uv ((least_of_minimal h hmin).2 S.v (by rw [hc]; exact S.min_v.1))
  have key : ∀ z, (kpTrim S.root (neg S.R) S.u).mem z ↔ (S.R.mem z ∧ ¬ z ≼ S.u) := by
    intro z
    show ((kpRegion S.root (neg S.R)).mem z ∧ ¬ z ≼ S.u) ↔ _
    rw [hc]
  exact hM.no_merge m hx (m.kp_ntop_of_sat hsa (fun y => by rw [key, key]; exact hsb y)
    hsc hne)

/-- Tool A for collapsing a set, missing both entrances, onto one of its
members. -/
theorem no_collapse_single (hM : InKPMin M) (S : RootSplit M) (N : M → Prop) (c : M)
    (hc : N c) (h : ∀ {x x' y : M}, N x → N x' → x ≼ y → N y ∨ x' ≼ y)
    (hsat : ∀ x, N x → ((neg S.R).mem x ↔ (neg S.R).mem c))
    (hu : ¬ N S.u) (hv : ¬ N S.v) {x : M} (hxN : N x) (hxc : x ≠ c) : False :=
  hM.no_merge_single S (Merger.collapse N c hc h) (Merger.collapse_sat hsat)
    (Merger.collapse_eq_not hu) (Merger.collapse_eq_not hv) (x := x)
    (by rw [Merger.collapse_mem hxN]; exact fun h' => hxc h'.symm)

/-- Tool B for collapsing a set onto one of its members. -/
theorem no_collapse_triple (hM : InKPMin M) (S : RootSplit M) (N : M → Prop) (c : M)
    (hc : N c) (h : ∀ {x x' y : M}, N x → N x' → x ≼ y → N y ∨ x' ≼ y)
    (hsa : ∀ x, N x → ((neg S.R).mem x ↔ (neg S.R).mem c))
    (hsb : ∀ x, N x → ((S.R.mem x ∧ ¬ x ≼ S.u) ↔ (S.R.mem c ∧ ¬ c ≼ S.u)))
    (hsc : ∀ x, N x → (S.u ≼ x ↔ S.u ≼ c))
    {x : M} (hxN : N x) (hxc : x ≠ c) : False :=
  hM.no_merge_triple S (Merger.collapse N c hc h) (Merger.collapse_sat hsa)
    (Merger.collapse_sat hsb) (Merger.collapse_sat hsc) (x := x)
    (by rw [Merger.collapse_mem hxN]; exact fun h' => hxc h'.symm)

/-- Tool A for collapsing the points above `x` onto `x`, which always merges
correctly. -/
theorem no_collapse_cone (hM : InKPMin M) (S : RootSplit M) (x : M)
    (hsat : ∀ y, x ≼ y → ((neg S.R).mem y ↔ (neg S.R).mem x))
    (hu : ¬ x ≼ S.u) (hv : ¬ x ≼ S.v) {y : M} (hxy : x ≼ y) (hyx : y ≠ x) : False :=
  hM.no_collapse_single S (fun y => x ≼ y) x (Frame.le_refl x)
    (fun hy _ hyz => Or.inl (Frame.le_trans hy hyz)) hsat hu hv hxy hyx

/-- **Only the root lies below both entrances**: a point below both would
carry the same split, and the axiom fails only at the root. -/
theorem eq_root_of_le_both (hM : InKPMin M) (S : RootSplit M) {x : M}
    (hxu : x ≼ S.u) (hxv : x ≼ S.v) : x = S.root := by
  have sub : ∀ q, (kpRegion x S.a).mem q → S.R.mem q := fun q hq => ⟨S.isRoot q, hq.2⟩
  have hroot := hM.root_of_splits (a := S.a) ⟨S.u, S.v,
    ⟨⟨hxu, S.min_u.1.2⟩, fun q hq hqu => S.min_u.2 q (sub q hq) hqu⟩,
    ⟨⟨hxv, S.min_v.1.2⟩, fun q hq hqv => S.min_v.2 q (sub q hq) hqv⟩,
    S.not_uv, S.not_vu⟩
  exact hM.antisymm _ _ (hroot S.root) (S.isRoot x)

end InKPMin

namespace RootSplit

variable {M : Type} [Frame M] (S : RootSplit M)

/-- A point below one in the region reaches it. -/
theorem not_neg_of_le {x y : M} (hxy : x ≼ y) (hy : S.R.mem y) : ¬ (neg S.R).mem x :=
  fun h => h y hxy hy

theorem not_neg_of_mem {x : M} (hx : S.R.mem x) : ¬ (neg S.R).mem x :=
  S.not_neg_of_le (Frame.le_refl x) hx

end RootSplit

namespace InKPMin

variable {M : Type} [Frame M]

theorem neg_of_max {S : RootSplit M} {z : M} (hz : IsMaxPt z) (hzR : ¬ S.R.mem z) :
    (neg S.R).mem z := fun y hzy hy => hzR (hz y hzy ▸ hy)

/-- A point of the region below an entrance is that entrance. -/
theorem eq_u_of_le (hM : InKPMin M) (S : RootSplit M) {x : M} (hx : S.R.mem x)
    (hxu : x ≼ S.u) : x = S.u :=
  hM.antisymm _ _ hxu (S.min_u.2 x hx hxu)

/-! ### One maximal point outside the region -/

theorem exists_outside (hM : InKPMin M) (S : RootSplit M) :
    ∃ A, IsMaxPt A ∧ ¬ S.R.mem A := by
  obtain ⟨y, _, hay⟩ := S.exists_a_of_not_mem S.root_not_mem
  obtain ⟨A, hyA, hA⟩ := hM.exists_max_above y
  exact ⟨A, hA, S.not_mem_of_a (S.a.upward hyA hay)⟩

/-- **At most one maximal point lies outside the region**: two would merge and
keep the split. -/
theorem outside_unique (hM : InKPMin M) (S : RootSplit M) {A A' : M}
    (hA : IsMaxPt A) (hA' : IsMaxPt A') (hAR : ¬ S.R.mem A) (hA'R : ¬ S.R.mem A') :
    A = A' := by
  refine Classical.byContradiction fun hne => ?_
  have hout : ∀ {w : M}, S.R.mem w → ¬ (w = A ∨ w = A') := by
    rintro w hw (rfl | rfl)
    · exact hAR hw
    · exact hA'R hw
  exact hM.no_collapse_single S (fun x => x = A ∨ x = A') A (Or.inl rfl)
    (Merger.max_pair_merges hA hA')
    (fun x hx => ⟨fun _ => neg_of_max hA hAR, fun _ => by
      rcases hx with rfl | rfl
      · exact neg_of_max hA hAR
      · exact neg_of_max hA' hA'R⟩)
    (hout S.min_u.1) (hout S.min_v.1) (x := A') (Or.inr rfl) (fun h => hne h.symm)

/-- Every point outside the region lies below the maximal point outside it. -/
theorem le_outside (hM : InKPMin M) (S : RootSplit M) {A : M} (hA : IsMaxPt A)
    (hAR : ¬ S.R.mem A) {x : M} (hx : ¬ S.R.mem x) : x ≼ A := by
  obtain ⟨y, hxy, hay⟩ := S.exists_a_of_not_mem hx
  obtain ⟨A', hyA', hA'⟩ := hM.exists_max_above y
  rw [hM.outside_unique S hA hA' hAR (S.not_mem_of_a (S.a.upward hyA' hay))]
  exact Frame.le_trans hxy hyA'

/-- So the region is exactly what lies off that maximal point. -/
theorem mem_iff (hM : InKPMin M) (S : RootSplit M) {A : M} (hA : IsMaxPt A)
    (hAR : ¬ S.R.mem A) (x : M) : S.R.mem x ↔ ¬ x ≼ A :=
  ⟨fun hx hxA => hAR (S.R.upward hxA hx),
   fun hxA => Classical.byContradiction fun hx => hxA (hM.le_outside S hA hAR hx)⟩

/-! ### The two regimes -/

/-- **The entrances are both maximal or both not.**  With `u` maximal, collapse
everything above `v` onto `v`: that makes `v` maximal too and keeps the axiom
failing at `u`, so a minimal refuter must have had `v` maximal already. -/
theorem max_of_max (hM : InKPMin M) (S : RootSplit M) (hu : IsMaxPt S.u) :
    IsMaxPt S.v := by
  refine Classical.byContradiction fun hv => ?_
  obtain ⟨p, hvp, hpv⟩ := exists_ne_above hv
  have hvR : ∀ {x : M}, S.v ≼ x → S.R.mem x := fun hx => S.R.upward hx S.min_v.1
  have hnu : ∀ {x : M}, S.v ≼ x → ¬ x ≼ S.u :=
    fun hx hxu => S.not_vu (Frame.le_trans hx hxu)
  have hun : ∀ {x : M}, S.v ≼ x → ¬ S.u ≼ x := fun hx hux => by
    have := hu _ hux
    exact S.not_vu (this ▸ hx)
  exact hM.no_collapse_triple S (fun x => S.v ≼ x) S.v (Frame.le_refl _)
    (fun hx _ hxy => Or.inl (Frame.le_trans hx hxy))
    (fun x hx => ⟨fun h => absurd h (S.not_neg_of_mem (hvR hx)),
       fun h => absurd h (S.not_neg_of_mem (hvR (Frame.le_refl _)))⟩)
    (fun x hx => ⟨fun _ => ⟨hvR (Frame.le_refl _), hnu (Frame.le_refl _)⟩,
       fun _ => ⟨hvR hx, hnu hx⟩⟩)
    (fun x hx => ⟨fun h => absurd h (hun hx), fun h => absurd h (hun (Frame.le_refl _))⟩)
    (x := p) hvp hpv

theorem max_iff (hM : InKPMin M) (S : RootSplit M) : IsMaxPt S.u ↔ IsMaxPt S.v :=
  ⟨hM.max_of_max S, hM.max_of_max S.swap⟩

end InKPMin

namespace InKPMin

variable {M : Type} [Frame M]

/-! ### The first regime: both entrances maximal -/

/-- **The region's maximal points are the entrances**: a third would merge into
`u` without disturbing the failure at `v`. -/
theorem regimeA_max (hM : InKPMin M) (S : RootSplit M) (hu : IsMaxPt S.u)
    (hv : IsMaxPt S.v) {w : M} (hw : IsMaxPt w) (hwR : S.R.mem w) :
    w = S.u ∨ w = S.v := by
  refine Classical.byContradiction fun hne => ?_
  have hwu : w ≠ S.u := fun h => hne (Or.inl h)
  have hwv : w ≠ S.v := fun h => hne (Or.inr h)
  have hvw : ¬ S.v ≼ w := fun h => hwv (hv w h)
  have hwv' : ¬ w ≼ S.v := fun h => hwv (hw S.v h).symm
  refine hM.no_collapse_triple S.swap (fun x => x = S.u ∨ x = w) S.u (Or.inl rfl)
    (Merger.max_pair_merges hu hw)
    ?_ ?_ ?_ (x := w) (Or.inr rfl) hwu
  · intro x hx
    rcases hx with rfl | rfl
    · exact Iff.rfl
    · exact ⟨fun h => absurd h (S.not_neg_of_mem hwR),
        fun h => absurd h (S.not_neg_of_mem S.min_u.1)⟩
  · intro x hx
    rcases hx with rfl | rfl
    · exact Iff.rfl
    · exact ⟨fun _ => ⟨S.min_u.1, S.not_uv⟩, fun _ => ⟨hwR, hwv'⟩⟩
  · intro x hx
    rcases hx with rfl | rfl
    · exact Iff.rfl
    · exact ⟨fun h => absurd h hvw, fun h => absurd h S.not_vu⟩

/-- **The region is the two entrances.** -/
theorem regimeA_region (hM : InKPMin M) (S : RootSplit M) (hu : IsMaxPt S.u)
    (hv : IsMaxPt S.v) (x : M) : S.R.mem x ↔ x = S.u ∨ x = S.v := by
  constructor
  · intro hx
    obtain ⟨m, hxm, hm⟩ := hM.exists_max_above x
    rcases hM.regimeA_max S hu hv hm (S.R.upward hxm hx) with h | h
    · rw [h] at hxm
      exact Or.inl (hM.eq_u_of_le S hx hxm)
    · rw [h] at hxm
      exact Or.inr (hM.eq_u_of_le S.swap hx hxm)
  · rintro (h | h)
    · rw [h]; exact S.min_u.1
    · rw [h]; exact S.min_v.1

/-- **Every point off the region but `A` sees an entrance**: one seeing
neither would carry everything above it onto itself. -/
theorem regimeA_sees (hM : InKPMin M) (S : RootSplit M) (hu : IsMaxPt S.u)
    (hv : IsMaxPt S.v) {A : M} (hA : IsMaxPt A) (hAR : ¬ S.R.mem A) {x : M}
    (hx : ¬ S.R.mem x) (hxA : x ≠ A) : x ≼ S.u ∨ x ≼ S.v := by
  refine Classical.byContradiction fun hc => ?_
  have hnu : ¬ x ≼ S.u := fun h => hc (Or.inl h)
  have hnv : ¬ x ≼ S.v := fun h => hc (Or.inr h)
  have hneg : ∀ {y : M}, x ≼ y → (neg S.R).mem y := by
    intro y hxy z hyz hz
    rcases (hM.regimeA_region S hu hv z).mp hz with h | h
    · rw [h] at hyz; exact hnu (Frame.le_trans hxy hyz)
    · rw [h] at hyz; exact hnv (Frame.le_trans hxy hyz)
  exact hM.no_collapse_cone S x
    (fun y hy => ⟨fun _ => hneg (Frame.le_refl x), fun _ => hneg hy⟩)
    hnu hnv (hM.le_outside S hA hAR hx) (Ne.symm hxA)

/-- **At most one point sees `u` alone**, and by symmetry at most one sees `v`
alone: all of them would merge into one. -/
theorem regimeA_side (hM : InKPMin M) (S : RootSplit M) (hu : IsMaxPt S.u)
    (hv : IsMaxPt S.v) {A : M} (hA : IsMaxPt A) (hAR : ¬ S.R.mem A) {x x' : M}
    (hx : ¬ S.R.mem x) (hxA : x ≠ A) (hxu : x ≼ S.u) (hxv : ¬ x ≼ S.v)
    (hx' : ¬ S.R.mem x') (hx'A : x' ≠ A) (hx'u : x' ≼ S.u) (hx'v : ¬ x' ≼ S.v) :
    x = x' := by
  refine Classical.byContradiction fun hne => ?_
  have hN : ∀ {y y' z : M},
      (¬ S.R.mem y ∧ y ≠ A ∧ y ≼ S.u ∧ ¬ y ≼ S.v) →
      (¬ S.R.mem y' ∧ y' ≠ A ∧ y' ≼ S.u ∧ ¬ y' ≼ S.v) → y ≼ z →
      (¬ S.R.mem z ∧ z ≠ A ∧ z ≼ S.u ∧ ¬ z ≼ S.v) ∨ y' ≼ z := by
    intro y y' z hy hy' hyz
    by_cases hzR : S.R.mem z
    · rcases (hM.regimeA_region S hu hv z).mp hzR with h | h
      · rw [h]; exact Or.inr hy'.2.2.1
      · rw [h] at hyz; exact absurd hyz hy.2.2.2
    · by_cases hzA : z = A
      · rw [hzA]; exact Or.inr (hM.le_outside S hA hAR hy'.1)
      · rcases hM.regimeA_sees S hu hv hA hAR hzR hzA with hzu | hzv
        · exact Or.inl ⟨hzR, hzA, hzu, fun h => hy.2.2.2 (Frame.le_trans hyz h)⟩
        · exact absurd (Frame.le_trans hyz hzv) hy.2.2.2
  exact hM.no_collapse_single S (fun y => ¬ S.R.mem y ∧ y ≠ A ∧ y ≼ S.u ∧ ¬ y ≼ S.v) x
    ⟨hx, hxA, hxu, hxv⟩ hN
    (fun y hy => ⟨fun h => absurd h (S.not_neg_of_le hy.2.2.1 S.min_u.1),
      fun h => absurd h (S.not_neg_of_le hxu S.min_u.1)⟩)
    (fun h => h.1 S.min_u.1) (fun h => h.1 S.min_v.1) (x := x')
    ⟨hx', hx'A, hx'u, hx'v⟩ (Ne.symm hne)

/-! ### The second regime: neither entrance maximal -/

/-- **The region has one maximal point**: two would merge. -/
theorem regimeB_max_unique (hM : InKPMin M) (S : RootSplit M) (hu : ¬ IsMaxPt S.u)
    (hv : ¬ IsMaxPt S.v) {B B' : M} (hB : IsMaxPt B) (hBR : S.R.mem B)
    (hB' : IsMaxPt B') (hB'R : S.R.mem B') : B = B' := by
  refine Classical.byContradiction fun hne => ?_
  have hmemN : ∀ {x : M}, (x = B ∨ x = B') → S.R.mem x := by
    rintro x (h | h)
    · rw [h]; exact hBR
    · rw [h]; exact hB'R
  have hnot : ∀ {w : M}, ¬ IsMaxPt w → ¬ (w = B ∨ w = B') := by
    rintro w hw (h | h)
    · rw [h] at hw; exact hw hB
    · rw [h] at hw; exact hw hB'
  exact hM.no_collapse_single S (fun x => x = B ∨ x = B') B (Or.inl rfl)
    (Merger.max_pair_merges hB hB')
    (fun x hx => ⟨fun h => absurd h (S.not_neg_of_mem (hmemN hx)),
      fun h => absurd h (S.not_neg_of_mem hBR)⟩)
    (hnot hu) (hnot hv) (x := B') (Or.inr rfl) (fun h => hne h.symm)

/-- Everything in the region lies below its one maximal point. -/
theorem regimeB_le (hM : InKPMin M) (S : RootSplit M) (hu : ¬ IsMaxPt S.u)
    (hv : ¬ IsMaxPt S.v) {B : M} (hB : IsMaxPt B) (hBR : S.R.mem B) {x : M}
    (hx : S.R.mem x) : x ≼ B := by
  obtain ⟨m, hxm, hm⟩ := hM.exists_max_above x
  rw [hM.regimeB_max_unique S hu hv hB hBR hm (S.R.upward hxm hx)]
  exact hxm

/-- **`u` is covered by that point alone**: anything else strictly above `u`
would collapse onto it. -/
theorem regimeB_above_u (hM : InKPMin M) (S : RootSplit M) (hu : ¬ IsMaxPt S.u)
    (hv : ¬ IsMaxPt S.v) {B : M} (hB : IsMaxPt B) (hBR : S.R.mem B) {x : M}
    (hux : S.u ≼ x) : x = S.u ∨ x = B := by
  refine Classical.byContradiction fun hc => ?_
  have hxu : x ≠ S.u := fun h => hc (Or.inl h)
  have hxB : x ≠ B := fun h => hc (Or.inr h)
  have huB : S.u ≼ B := hM.regimeB_le S hu hv hB hBR S.min_u.1
  have hBu : B ≠ S.u := fun h => hu (h ▸ hB)
  exact hM.no_collapse_single S (fun y => S.u ≼ y ∧ y ≠ S.u) B ⟨huB, hBu⟩
    (fun hy _ hyz => Or.inl ⟨Frame.le_trans hy.1 hyz, fun hzu =>
      hy.2 (hM.antisymm _ _ (hzu ▸ hyz) hy.1)⟩)
    (fun y hy => ⟨fun h => absurd h (S.not_neg_of_mem (S.R.upward hy.1 S.min_u.1)),
      fun h => absurd h (S.not_neg_of_mem hBR)⟩)
    (fun h => h.2 rfl) (fun h => S.not_uv h.1) (x := x) ⟨hux, hxu⟩ hxB

/-- **The region is the two entrances and the point above them**: a third
minimal point would carry everything above it onto itself. -/
theorem regimeB_region (hM : InKPMin M) (S : RootSplit M) (hu : ¬ IsMaxPt S.u)
    (hv : ¬ IsMaxPt S.v) {B : M} (hB : IsMaxPt B) (hBR : S.R.mem B) (x : M) :
    S.R.mem x ↔ x = S.u ∨ x = S.v ∨ x = B := by
  constructor
  · intro hx
    obtain ⟨l, hl⟩ := hM.list.finite
    obtain ⟨z, ⟨hzR, hzx⟩, hzmin⟩ :=
      hasMinimal_of_list l hl (fun q => S.R.mem q ∧ q ≼ x) ⟨x, hx, Frame.le_refl x⟩
    have hzmin' : ∀ q, S.R.mem q → q ≼ z → z ≼ q :=
      fun q hq hqz => hzmin q ⟨hq, Frame.le_trans hqz hzx⟩ hqz
    by_cases hzu : z = S.u
    · rw [hzu] at hzx
      rcases hM.regimeB_above_u S hu hv hB hBR hzx with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    by_cases hzv : z = S.v
    · rw [hzv] at hzx
      rcases hM.regimeB_above_u S.swap hv hu hB hBR hzx with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    exfalso
    have hnu : ¬ z ≼ S.u := fun h => hzu (hM.eq_u_of_le S hzR h)
    have hnv : ¬ z ≼ S.v := fun h => hzv (hM.eq_u_of_le S.swap hzR h)
    have hzB : z ≠ B := fun h => hnu (hzmin' S.u S.min_u.1
      (by rw [h]; exact hM.regimeB_le S hu hv hB hBR S.min_u.1))
    exact hM.no_collapse_cone S z
      (fun y hy => ⟨fun h => absurd h (S.not_neg_of_mem (S.R.upward hy hzR)),
        fun h => absurd h (S.not_neg_of_mem hzR)⟩)
      hnu hnv (hM.regimeB_le S hu hv hB hBR hzR) (Ne.symm hzB)
  · rintro (h | h | h)
    · rw [h]; exact S.min_u.1
    · rw [h]; exact S.min_v.1
    · rw [h]; exact hBR

/-- **Every point off the region but `A` sees `B`**, as well as `A`: one that
did not would carry everything above it onto itself. -/
theorem regimeB_sees (hM : InKPMin M) (S : RootSplit M) (hu : ¬ IsMaxPt S.u)
    (hv : ¬ IsMaxPt S.v) {A B : M} (hA : IsMaxPt A) (hAR : ¬ S.R.mem A)
    (hB : IsMaxPt B) (hBR : S.R.mem B) {x : M} (hx : ¬ S.R.mem x) (hxA : x ≠ A) :
    x ≼ B := by
  refine Classical.byContradiction fun hxB => ?_
  have hle : ∀ {z : M}, S.R.mem z → z ≼ B := fun hz => hM.regimeB_le S hu hv hB hBR hz
  have hneg : ∀ {y : M}, x ≼ y → (neg S.R).mem y :=
    fun hxy _ hyz hz => hxB (Frame.le_trans hxy (Frame.le_trans hyz (hle hz)))
  exact hM.no_collapse_cone S x
    (fun y hy => ⟨fun _ => hneg (Frame.le_refl x), fun _ => hneg hy⟩)
    (fun h => hxB (Frame.le_trans h (hle S.min_u.1)))
    (fun h => hxB (Frame.le_trans h (hle S.min_v.1)))
    (hM.le_outside S hA hAR hx) (Ne.symm hxA)

/-- **Every other point sees at most one entrance**, in either regime: seeing
both is reserved for the root. -/
theorem sees_one (hM : InKPMin M) (S : RootSplit M) {x : M} (hxr : x ≠ S.root)
    (hsee : x ≼ S.u ∨ x ≼ S.v) : (x ≼ S.u ∧ ¬ x ≼ S.v) ∨ (x ≼ S.v ∧ ¬ x ≼ S.u) :=
  hsee.elim (fun h => Or.inl ⟨h, fun h' => hxr (hM.eq_root_of_le_both S h h')⟩)
    (fun h => Or.inr ⟨h, fun h' => hxr (hM.eq_root_of_le_both S h' h)⟩)

end InKPMin

namespace InKPMin

variable {M : Type} [Frame M]

/-! ### The first regime, point by point -/

/-- **The first regime, point by point.**  Besides the root, `A` and the two
entrances, every point sees exactly one entrance; `regimeA_side` allows at most
one such point for each, so there are at most six points in all. -/
theorem regimeA_points (hM : InKPMin M) (S : RootSplit M) (hu : IsMaxPt S.u)
    (hv : IsMaxPt S.v) {A : M} (hA : IsMaxPt A) (hAR : ¬ S.R.mem A) (x : M) :
    x = S.root ∨ x = A ∨ x = S.u ∨ x = S.v ∨
      (x ≼ A ∧ x ≼ S.u ∧ ¬ x ≼ S.v) ∨ (x ≼ A ∧ x ≼ S.v ∧ ¬ x ≼ S.u) := by
  by_cases hxR : S.R.mem x
  · rcases (hM.regimeA_region S hu hv x).mp hxR with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  by_cases hxA : x = A
  · exact Or.inr (Or.inl hxA)
  by_cases hxr : x = S.root
  · exact Or.inl hxr
  have hxA' := hM.le_outside S hA hAR hxR
  rcases hM.sees_one S hxr (hM.regimeA_sees S hu hv hA hAR hxR hxA) with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hxA', h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hxA', h⟩))))

end InKPMin

/-! ## The second regime, exactly -/

/-- **The shape of the second regime**: a root `r`; maximal points `A` and `B`;
entrances `u` and `v`, covered by `B` alone, which with `B` are exactly the
points not below `A`; `A` the only point not below `B`; and the root the only
point below both entrances. -/
structure RegimeB (M : Type) [Frame M] where
  r : M
  A : M
  B : M
  u : M
  v : M
  root : ∀ p, r ≼ p
  A_max : ∀ p, A ≼ p → p = A
  B_max : ∀ p, B ≼ p → p = B
  not_le_A : ∀ z, ¬ z ≼ A ↔ z = u ∨ z = v ∨ z = B
  not_le_B : ∀ z, ¬ z ≼ B ↔ z = A
  u_le : ∀ y, u ≼ y ↔ y = u ∨ y = B
  v_le : ∀ y, v ≼ y ↔ y = v ∨ y = B
  le_both : ∀ x, x ≼ u → x ≼ v → x = r
  not_uv : ¬ u ≼ v
  not_vu : ¬ v ≼ u

namespace RegimeB

variable {M : Type} [Frame M] (S : RegimeB M)

/-- The wiring: every point but `A`, `B` and the two entrances. -/
def Wiring (x : M) : Prop := x ≠ S.A ∧ x ≠ S.B ∧ x ≠ S.u ∧ x ≠ S.v

/-- **Reduced**: no wiring point takes part in an α- or β-pair. -/
def Reduced : Prop := ∀ x y : M, IsAlpha x y ∨ IsBeta x y → ¬ S.Wiring x ∧ ¬ S.Wiring y

/-- The same shape, entrances exchanged. -/
def swap : RegimeB M where
  r := S.r
  A := S.A
  B := S.B
  u := S.v
  v := S.u
  root := S.root
  A_max := S.A_max
  B_max := S.B_max
  not_le_A z := (S.not_le_A z).trans or_left_comm
  not_le_B := S.not_le_B
  u_le := S.v_le
  v_le := S.u_le
  le_both x hv hu := S.le_both x hu hv
  not_uv := S.not_vu
  not_vu := S.not_uv

/-! ### The order -/

theorem u_le_B : S.u ≼ S.B := (S.u_le _).mpr (Or.inr rfl)

theorem not_u_le_A : ¬ S.u ≼ S.A := (S.not_le_A _).mpr (Or.inl rfl)

theorem not_A_le_B : ¬ S.A ≼ S.B := (S.not_le_B _).mpr rfl

theorem u_ne_B : S.u ≠ S.B := fun h => S.not_vu (by rw [h]; exact S.swap.u_le_B)

theorem le_B_of_ne {z : M} (hz : z ≠ S.A) : z ≼ S.B :=
  Classical.byContradiction fun h => hz ((S.not_le_B z).mp h)

/-- Every point lies below one of the two maximal points. -/
theorem le_A_or_B (z : M) : z ≼ S.A ∨ z ≼ S.B := by
  by_cases h : z ≼ S.A
  · exact Or.inl h
  · right
    rcases (S.not_le_A z).mp h with rfl | rfl | rfl
    · exact S.u_le_B
    · exact S.swap.u_le_B
    · exact Frame.le_refl _

/-- A negation is fixed by which of the two maximal points the set holds. -/
theorem mem_neg_iff (a : Upset M) (z : M) :
    (neg a).mem z ↔ (z ≼ S.A → ¬ a.mem S.A) ∧ (z ≼ S.B → ¬ a.mem S.B) := by
  constructor
  · intro h
    exact ⟨fun hz ha => h _ hz ha, fun hz hb => h _ hz hb⟩
  · rintro ⟨hA, hB⟩ y hzy hay
    rcases S.le_A_or_B y with hy | hy
    · exact hA (Frame.le_trans hzy hy) (a.upward hy hay)
    · exact hB (Frame.le_trans hzy hy) (a.upward hy hay)

/-! ### The split at the root -/

theorem mem_region_iff (z : M) : (kpRegion S.r (Upset.up S.A)).mem z ↔ ¬ z ≼ S.A :=
  ⟨fun h hzA => h.2 S.A hzA (Frame.le_refl _),
   fun hzA => ⟨S.root z, fun y hzy hAy => hzA (S.A_max y hAy ▸ hzy)⟩⟩

theorem min_u : (kpRegion S.r (Upset.up S.A)).Minimal S.u := by
  refine ⟨(S.mem_region_iff _).mpr S.not_u_le_A, fun q hq hqu => ?_⟩
  rcases (S.not_le_A q).mp ((S.mem_region_iff q).mp hq) with rfl | rfl | rfl
  · exact Frame.le_refl _
  · exact absurd hqu S.not_vu
  · exact S.u_le_B

/-- The region at the root cut out by the set above `A`, entered at `u` and at
`v`. -/
def split : RootSplit M :=
  ⟨S.r, S.root, Upset.up S.A, S.u, S.v, S.min_u, S.swap.min_u, S.not_uv, S.not_vu⟩

/-- Only `A` fails to reach the region. -/
theorem mem_negR (z : M) : (neg S.split.R).mem z ↔ z = S.A := by
  constructor
  · intro h
    refine Classical.byContradiction fun hz => h S.B (S.le_B_of_ne hz) ?_
    exact (S.mem_region_iff _).mpr ((S.not_le_A _).mpr (Or.inr (Or.inr rfl)))
  · rintro rfl y hAy hy
    exact (S.mem_region_iff y).mp hy (S.A_max y hAy ▸ Frame.le_refl _)

/-! ### Regions -/

/-- **One entrance, except at a point seeing both entrances.**  The region cut
out at `r` by `a` has one entrance unless `r` sees both entrances and `a` holds
`A` but not `B`, which makes the region `{u, v, B}`. -/
theorem principal {r : M} {a : Upset M}
    (h : ¬ (r ≼ S.u ∧ r ≼ S.v ∧ a.mem S.A ∧ ¬ a.mem S.B)) : (kpRegion r a).Principal := by
  intro p hp
  have hn := (S.mem_neg_iff a p).mp hp.2
  by_cases hA : a.mem S.A <;> by_cases hB : a.mem S.B
  · -- both: the region is empty
    rcases S.le_A_or_B p with hpA | hpB
    · exact absurd hA (hn.1 hpA)
    · exact absurd hB (hn.2 hpB)
  · -- `A` alone: the region lies in `{u, v, B}`
    have hin : ∀ {z}, (kpRegion r a).mem z → z = S.u ∨ z = S.v ∨ z = S.B := fun hz =>
      (S.not_le_A _).mp fun hzA => ((S.mem_neg_iff a _).mp hz.2).1 hzA hA
    have hmem : ∀ {z}, r ≼ z → (z = S.u ∨ z = S.v ∨ z = S.B) → (kpRegion r a).mem z :=
      fun hrz hz => ⟨hrz, (S.mem_neg_iff a _).mpr
        ⟨fun hzA => absurd hzA ((S.not_le_A _).mpr hz), fun _ => hB⟩⟩
    by_cases hru : r ≼ S.u
    · have hrv : ¬ r ≼ S.v := fun hrv => h ⟨hru, hrv, hA, hB⟩
      refine ⟨S.u, hmem hru (Or.inl rfl), fun q hq => ?_⟩
      rcases hin hq with rfl | rfl | rfl
      · exact Frame.le_refl _
      · exact absurd hq.1 hrv
      · exact S.u_le_B
    by_cases hrv : r ≼ S.v
    · refine ⟨S.v, hmem hrv (Or.inr (Or.inl rfl)), fun q hq => ?_⟩
      rcases hin hq with rfl | rfl | rfl
      · exact absurd hq.1 hru
      · exact Frame.le_refl _
      · exact S.swap.u_le_B
    have hrB : r ≼ S.B := by
      rcases hin hp with rfl | rfl | rfl
      · exact absurd hp.1 hru
      · exact absurd hp.1 hrv
      · exact hp.1
    refine ⟨S.B, hmem hrB (Or.inr (Or.inr rfl)), fun q hq => ?_⟩
    rcases hin hq with rfl | rfl | rfl
    · exact absurd hq.1 hru
    · exact absurd hq.1 hrv
    · exact Frame.le_refl _
  · -- `B` alone: the region is at most `A`
    have hin : ∀ {z}, (kpRegion r a).mem z → z = S.A := fun hz =>
      (S.not_le_B _).mp fun hzB => ((S.mem_neg_iff a _).mp hz.2).2 hzB hB
    exact ⟨S.A, hin hp ▸ hp, fun q hq => by rw [hin hq]; exact Frame.le_refl _⟩
  · -- neither: the region is everything above `r`
    exact ⟨r, ⟨Frame.le_refl r, (S.mem_neg_iff a r).mpr ⟨fun _ => hA, fun _ => hB⟩⟩,
      fun _ hq => hq.1⟩

include S in
/-- **A finite frame of the shape is in `𝓛`**, split at the root. -/
theorem inKPList (hfin : ∃ l : List M, ∀ p, p ∈ l) : InKPList M :=
  ⟨hfin, ⟨S.r, S.root⟩, ⟨S.r, Upset.up S.A, S.u, S.v, S.min_u, S.swap.min_u, S.not_uv, S.not_vu⟩⟩

/-- **When the region `{u, v, B}` cannot be taken piecemeal, the axiom holds.**
Let `sat` be a property of upward closed sets that never separates `A` from `B`,
or puts `u` in every such set holding `v`, or `v` in every one holding `u`.
Then the axiom holds at every triple of such sets.  Every region but `{u, v, B}`
has one entrance (`principal`); and when `b ⊔ c` covers `{u, v, B}`, the
disjunct holding the right entrance holds the other entrance too, and so the
whole region. -/
theorem kp_top_of (sat : Upset M → Prop)
    (hsat : (∀ X, sat X → (X.mem S.A ↔ X.mem S.B)) ∨ (∀ X, sat X → X.mem S.v → X.mem S.u) ∨
      (∀ X, sat X → X.mem S.u → X.mem S.v))
    {a b c : Upset M} (ha : sat a) (hb : sat b) (hc : sat c) : kpAt a b c = ⊤ := by
  refine (BoundedLattice.eq_top_iff _).mpr fun x _ r _ hr => ?_
  by_cases hp : r ≼ S.u ∧ r ≼ S.v ∧ a.mem S.A ∧ ¬ a.mem S.B
  · obtain ⟨hru, hrv, hA, hB⟩ := hp
    have hin : ∀ s, (neg a).mem s → s = S.u ∨ s = S.v ∨ s = S.B := fun s hs =>
      (S.not_le_A s).mp fun hsA => ((S.mem_neg_iff a s).mp hs).1 hsA hA
    have hneg : ∀ s, (s = S.u ∨ s = S.v ∨ s = S.B) → (neg a).mem s := fun s hs =>
      (S.mem_neg_iff a s).mpr ⟨fun hsA => absurd hsA ((S.not_le_A s).mpr hs), fun _ => hB⟩
    -- a set holding both entrances holds the region
    have whole : ∀ X : Upset M, X.mem S.u → X.mem S.v → (neg a ⇨ X).mem r :=
      fun X hu hv s _ hs => by
        rcases hin s hs with rfl | rfl | rfl
        · exact hu
        · exact hv
        · exact X.upward S.u_le_B hu
    have hu := hr S.u hru (hneg _ (Or.inl rfl))
    have hv := hr S.v hrv (hneg _ (Or.inr (Or.inl rfl)))
    rcases hsat with hAB | hvu | huv
    · exact absurd ((hAB a ha).mp hA) hB
    · rcases hv with hbv | hcv
      · exact Or.inl (whole b (hvu b hb hbv) hbv)
      · exact Or.inr (whole c (hvu c hc hcv) hcv)
    · rcases hu with hbu | hcu
      · exact Or.inl (whole b hbu (huv b hb hbu))
      · exact Or.inr (whole c hcu (huv c hc hcu))
  · exact kp_step_of_principal (S.principal hp) b c hr

/-! ### The pairs -/

theorem not_alpha_from_A {y : M} : ¬ IsAlpha S.A y :=
  fun ⟨hne, hAy, _⟩ => hne (S.A_max y hAy).symm

theorem alpha_from_u {y : M} (h : IsAlpha S.u y) : y = S.B := by
  obtain ⟨hne, huy, _⟩ := h
  rcases (S.u_le y).mp huy with rfl | rfl
  · exact absurd rfl hne
  · rfl

theorem not_alpha_to_A {x : M} : ¬ IsAlpha x S.A := by
  rintro ⟨hne, hxA, hα⟩
  have hBx : S.B ≠ x := fun e =>
    (S.not_le_A S.B).mpr (Or.inr (Or.inr rfl)) (by rw [e]; exact hxA)
  exact S.not_A_le_B (hα S.B (S.le_B_of_ne hne) hBx)

theorem not_alpha_to_u {x : M} : ¬ IsAlpha x S.u := by
  rintro ⟨hne, hxu, hα⟩
  have hxA : x ≼ S.A := Classical.byContradiction fun h => by
    rcases (S.not_le_A x).mp h with rfl | rfl | rfl
    · exact hne rfl
    · exact S.not_vu hxu
    · exact S.u_ne_B (S.B_max _ hxu)
  have hAx : S.A ≠ x := fun e => by
    subst e
    exact S.not_u_le_A (by rw [S.A_max _ hxu]; exact Frame.le_refl _)
  exact S.not_u_le_A (hα S.A hxA hAx)

theorem beta_from_A {y : M} (h : IsBeta S.A y) : y = S.B := by
  obtain ⟨hne, hβ⟩ := h
  rcases S.le_A_or_B y with hyA | hyB
  · exact absurd ((hβ S.A).mpr ⟨hyA, hne⟩).2 (fun e => e rfl)
  · refine Classical.byContradiction fun hyB' => ?_
    exact S.not_A_le_B ((hβ S.B).mpr ⟨hyB, Ne.symm hyB'⟩).1

theorem beta_from_u {y : M} (h : IsBeta S.u y) : y = S.v := by
  obtain ⟨hne, hβ⟩ := h
  obtain ⟨hyB, hBy⟩ := (hβ S.B).mp ⟨S.u_le_B, Ne.symm S.u_ne_B⟩
  have hyA : ¬ y ≼ S.A := fun hyA => by
    have hAy : S.A ≠ y := fun e => S.not_A_le_B (by rw [e]; exact hyB)
    exact S.not_u_le_A ((hβ S.A).mpr ⟨hyA, hAy⟩).1
  rcases (S.not_le_A y).mp hyA with rfl | rfl | rfl
  · exact absurd rfl hne
  · rfl
  · exact absurd rfl hBy

/-- **The pairs of the shape.**  An α- or β-pair avoids `A` and both entrances;
or it is `A` with `B`; or it lies among `u`, `v` and `B`. -/
theorem pair_cases {x y : M} (h : IsAlpha x y ∨ IsBeta x y) :
    (x ≠ S.A ∧ x ≠ S.u ∧ x ≠ S.v ∧ y ≠ S.A ∧ y ≠ S.u ∧ y ≠ S.v) ∨
      ((x = S.A ∧ y = S.B) ∨ (x = S.B ∧ y = S.A)) ∨
      ((x = S.u ∨ x = S.v ∨ x = S.B) ∧ (y = S.u ∨ y = S.v ∨ y = S.B)) := by
  by_cases hx : x = S.A ∨ x = S.u ∨ x = S.v
  · right
    rcases h with hα | hβ
    · rcases hx with rfl | rfl | rfl
      · exact absurd hα S.not_alpha_from_A
      · exact Or.inr ⟨Or.inl rfl, Or.inr (Or.inr (S.alpha_from_u hα))⟩
      · exact Or.inr ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr (S.swap.alpha_from_u hα))⟩
    · rcases hx with rfl | rfl | rfl
      · exact Or.inl (Or.inl ⟨rfl, S.beta_from_A hβ⟩)
      · exact Or.inr ⟨Or.inl rfl, Or.inr (Or.inl (S.beta_from_u hβ))⟩
      · exact Or.inr ⟨Or.inr (Or.inl rfl), Or.inl (S.swap.beta_from_u hβ)⟩
  by_cases hy : y = S.A ∨ y = S.u ∨ y = S.v
  · right
    rcases h with hα | hβ
    · rcases hy with rfl | rfl | rfl
      · exact absurd hα S.not_alpha_to_A
      · exact absurd hα S.not_alpha_to_u
      · exact absurd hα S.swap.not_alpha_to_u
    · have hβ' := hβ.symm
      rcases hy with rfl | rfl | rfl
      · exact Or.inl (Or.inr ⟨S.beta_from_A hβ', rfl⟩)
      · exact Or.inr ⟨Or.inr (Or.inl (S.beta_from_u hβ')), Or.inl rfl⟩
      · exact Or.inr ⟨Or.inl (S.swap.beta_from_u hβ'), Or.inr (Or.inl rfl)⟩
  · exact Or.inl ⟨fun e => hx (Or.inl e), fun e => hx (Or.inr (Or.inl e)),
      fun e => hx (Or.inr (Or.inr e)), fun e => hy (Or.inl e),
      fun e => hy (Or.inr (Or.inl e)), fun e => hy (Or.inr (Or.inr e))⟩

theorem not_wiring {x : M} (hx : x = S.A ∨ x = S.B ∨ x = S.u ∨ x = S.v) : ¬ S.Wiring x :=
  fun ⟨h₁, h₂, h₃, h₄⟩ => by rcases hx with e | e | e | e <;> contradiction

/-- The last two kinds of pair in `pair_cases` stay out of the wiring. -/
theorem not_wiring_of_core {x y : M}
    (h : ((x = S.A ∧ y = S.B) ∨ (x = S.B ∧ y = S.A)) ∨
      ((x = S.u ∨ x = S.v ∨ x = S.B) ∧ (y = S.u ∨ y = S.v ∨ y = S.B))) :
    ¬ S.Wiring x ∧ ¬ S.Wiring y := by
  rcases h with (⟨hx, hy⟩ | ⟨hx, hy⟩) | ⟨hx, hy⟩
  · exact ⟨S.not_wiring (Or.inl hx), S.not_wiring (Or.inr (Or.inl hy))⟩
  · exact ⟨S.not_wiring (Or.inr (Or.inl hx)), S.not_wiring (Or.inl hy)⟩
  · have core : ∀ {z}, (z = S.u ∨ z = S.v ∨ z = S.B) → ¬ S.Wiring z := fun hz =>
      S.not_wiring (by rcases hz with e | e | e <;> simp [e])
    exact ⟨core hx, core hy⟩

theorem u_ne_r : S.u ≠ S.r := fun h => S.not_uv (by rw [h]; exact S.root _)

/-- The root takes part in no pair: everything lies above it, and it is the only
point below both entrances. -/
theorem not_pair_from_r {y : M} (h : IsAlpha S.r y ∨ IsBeta S.r y) : False := by
  rcases h with ⟨hne, _, hα⟩ | ⟨hne, hβ⟩
  · exact hne (S.le_both y (hα _ (S.root _) S.u_ne_r) (hα _ (S.root _) S.swap.u_ne_r)).symm
  · exact ((hβ y).mp ⟨S.root y, Ne.symm hne⟩).2 rfl

theorem not_pair_to_r {x : M} (h : IsAlpha x S.r ∨ IsBeta x S.r) : False := by
  rcases h with ⟨hne, hxr, _⟩ | hβ
  · exact hne (S.le_both x (Frame.le_trans hxr (S.root _)) (Frame.le_trans hxr (S.root _)))
  · exact S.not_pair_from_r (Or.inr hβ.symm)

/-- `B` pairs only with `A` and the entrances. -/
theorem pair_from_B {y : M} (h : IsAlpha S.B y ∨ IsBeta S.B y) : y = S.A := by
  rcases h with ⟨hne, hBy, _⟩ | ⟨hne, hβ⟩
  · exact absurd (S.B_max y hBy).symm hne
  · exact (S.not_le_B y).mp fun hyB => ((hβ S.B).mpr ⟨hyB, hne⟩).2 rfl

theorem pair_to_B {x : M} (h : IsAlpha x S.B ∨ IsBeta x S.B) :
    x = S.A ∨ x = S.u ∨ x = S.v := by
  rcases h with ⟨hne, hxB, hα⟩ | hβ
  · by_cases hxA : x ≼ S.A
    · have hAx : S.A ≠ x := fun e => S.not_A_le_B (by rw [e]; exact hxB)
      exact absurd (hα S.A hxA hAx) ((S.not_le_A _).mpr (Or.inr (Or.inr rfl)))
    · rcases (S.not_le_A x).mp hxA with e | e | e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr e)
      · exact absurd e hne
  · exact Or.inl (S.pair_from_B (Or.inr hβ.symm))

/-- **Reducedness is about the wiring alone**: it holds as soon as no two
wiring points but the root form a pair. -/
theorem reduced_of (h : ∀ x y : M, IsAlpha x y ∨ IsBeta x y → S.Wiring x → S.Wiring y →
    x ≠ S.r → y ≠ S.r → False) : S.Reduced := by
  intro x y hp
  rcases S.pair_cases hp with ⟨hxA, hxu, hxv, hyA, hyu, hyv⟩ | hc
  · exfalso
    have hxr : x ≠ S.r := fun e => by subst e; exact S.not_pair_from_r hp
    have hyr : y ≠ S.r := fun e => by subst e; exact S.not_pair_to_r hp
    have hxB : x ≠ S.B := fun e => by subst e; exact hyA (S.pair_from_B hp)
    have hyB : y ≠ S.B := fun e => by
      subst e
      rcases S.pair_to_B hp with e | e | e
      · exact hxA e
      · exact hxu e
      · exact hxv e
    exact h x y hp ⟨hxA, hxB, hxu, hxv⟩ ⟨hyA, hyB, hyu, hyv⟩ hxr hyr
  · exact S.not_wiring_of_core hc

/-! ### The theorem -/

/-- **A member is reduced**: a pair touching the wiring avoids `A` and both
entrances, so merging it keeps the split. -/
theorem reduced_of_inKPMin (hM : InKPMin M) : S.Reduced := by
  intro x y h
  rcases S.pair_cases h with ⟨hxA, hxu, hxv, hyA, hyu, hyv⟩ | hAB | ⟨hx, hy⟩
  · exfalso
    have hsat : ∀ z, (neg S.split.R).mem z ↔ (neg S.split.R).mem ((Merger.pair x y h).g z) :=
      Merger.collapse_sat (N := fun z => z = x ∨ z = y) (c := y)
        (Q := fun z => (neg S.split.R).mem z) fun z hz => by
          show (neg S.split.R).mem z ↔ (neg S.split.R).mem y
          rw [S.mem_negR, S.mem_negR]
          rcases hz with rfl | rfl
          · exact ⟨fun e => absurd e hxA, fun e => absurd e hyA⟩
          · exact Iff.rfl
    exact hM.no_merge_single S.split (Merger.pair x y h) hsat
      (fun w hw => Merger.collapse_eq_not (N := fun z => z = x ∨ z = y)
        (fun e => e.elim (fun e => hxu e.symm) (fun e => hyu e.symm)) w hw)
      (fun w hw => Merger.collapse_eq_not (N := fun z => z = x ∨ z = y)
        (fun e => e.elim (fun e => hxv e.symm) (fun e => hyv e.symm)) w hw)
      (Merger.pair_g_ne h)
  · exact S.not_wiring_of_core (Or.inl hAB)
  · exact S.not_wiring_of_core (Or.inr ⟨hx, hy⟩)

/-- **A reduced frame is a member.**  The axiom fails at the root, and only
there; and each α- or β-step, lying among `A`, `B`, `u` and `v`, validates it
(`kp_top_of`). -/
theorem inKPMin_of_reduced (hfin : ∃ l : List M, ∀ p, p ∈ l) (hA : Frame.Antisymm M)
    (hR : S.Reduced) : InKPMin M := by
  obtain ⟨l, hl⟩ := hfin
  refine inKPMin_iff.mpr ⟨S.inKPList ⟨l, hl⟩, hA, ?_, ?_⟩
  · -- a split lies at a point seeing both entrances, which is the root
    intro r a hs p
    by_cases hr : r ≼ S.u ∧ r ≼ S.v
    · rw [S.le_both r hr.1 hr.2]; exact S.root p
    · exact absurd (S.principal fun h => hr ⟨h.1, h.2.1⟩)
        ((Upset.not_principal_iff_splits (hasMinimal_of_list l hl) _).mpr hs)
  · -- each remaining step keeps the region `{u, v, B}` from being taken piecemeal
    intro x y h
    have hne : x ≠ y := h.elim (fun h => h.1) (fun h => h.1)
    have hgx : (Merger.pair x y h).g x = y :=
      Merger.collapse_mem (N := fun z => z = x ∨ z = y) (Or.inl rfl)
    have hdisj : (∀ X : Upset M, (X.mem x ↔ X.mem y) → (X.mem S.A ↔ X.mem S.B)) ∨
        (∀ X : Upset M, (X.mem x ↔ X.mem y) → X.mem S.v → X.mem S.u) ∨
        (∀ X : Upset M, (X.mem x ↔ X.mem y) → X.mem S.u → X.mem S.v) := by
      obtain ⟨hwx, hwy⟩ := hR x y h
      rcases S.pair_cases h with ⟨hxA, hxu, hxv, hyA, hyu, hyv⟩ | hAB | ⟨hx, hy⟩
      · -- both would be `B`
        have hxB : x = S.B := Classical.byContradiction fun e => hwx ⟨hxA, e, hxu, hxv⟩
        have hyB : y = S.B := Classical.byContradiction fun e => hwy ⟨hyA, e, hyu, hyv⟩
        exact absurd (hxB.trans hyB.symm) hne
      · left
        rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact fun _ hX => hX
        · exact fun _ hX => hX.symm
      · right
        have hvB := S.swap.u_le_B
        have huB := S.u_le_B
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        · exact absurd rfl hne
        · exact Or.inl fun _ hX hv => hX.mpr hv
        · exact Or.inl fun X hX hv => hX.mpr (X.upward hvB hv)
        · exact Or.inl fun _ hX hv => hX.mp hv
        · exact absurd rfl hne
        · exact Or.inr fun X hX hu => hX.mpr (X.upward huB hu)
        · exact Or.inl fun X hX hv => hX.mp (X.upward hvB hv)
        · exact Or.inr fun X hX hu => hX.mp (X.upward huB hu)
        · exact absurd rfl hne
    have key : ∀ X : Upset M, (∀ z, X.mem z ↔ X.mem ((Merger.pair x y h).g z)) →
        (X.mem x ↔ X.mem y) := fun X hX => (hX x).trans (by rw [hgx])
    exact (Merger.pair x y h).kp_top_of_sat fun a b c ha hb hc =>
      S.kp_top_of (fun X => X.mem x ↔ X.mem y) hdisj (key a ha) (key b hb) (key c hc)

/-- **Minimal exactly when reduced**, for a finite poset of the second regime's
shape. -/
theorem inKPMin_iff_reduced (hfin : ∃ l : List M, ∀ p, p ∈ l) (hA : Frame.Antisymm M) :
    InKPMin M ↔ S.Reduced :=
  ⟨S.reduced_of_inKPMin, S.inKPMin_of_reduced hfin hA⟩

end RegimeB

/-! ### The members of the second regime -/

/-- **A member with non-maximal entrances has the shape**, read off from the
clauses of the shape theorem. -/
theorem InKPMin.exists_regimeB {M : Type} [Frame M] (hM : InKPMin M) (S : RootSplit M)
    (hu : ¬ IsMaxPt S.u) : ∃ T : RegimeB M, T.u = S.u ∧ T.v = S.v := by
  have hv : ¬ IsMaxPt S.v := fun h => hu ((hM.max_iff S).mpr h)
  obtain ⟨A, hA, hAR⟩ := hM.exists_outside S
  obtain ⟨B, huB, hB⟩ := hM.exists_max_above S.u
  have hBR : S.R.mem B := S.R.upward huB S.min_u.1
  have hvB : S.v ≼ B := hM.regimeB_le S hu hv hB hBR S.min_v.1
  let T : RegimeB M :=
    { r := S.root
      A := A
      B := B
      u := S.u
      v := S.v
      root := S.isRoot
      A_max := hA
      B_max := hB
      not_le_A := fun z =>
        (hM.mem_iff S hA hAR z).symm.trans (hM.regimeB_region S hu hv hB hBR z)
      not_le_B := fun z => ⟨fun hz => Classical.byContradiction fun hzA => hz (by
          by_cases hzR : S.R.mem z
          · exact hM.regimeB_le S hu hv hB hBR hzR
          · exact hM.regimeB_sees S hu hv hA hAR hB hBR hzR hzA),
        fun hz hzB => hAR (by rw [hz] at hzB; rw [← hA B hzB]; exact hBR)⟩
      u_le := fun y => ⟨hM.regimeB_above_u S hu hv hB hBR, fun h => h.elim
        (fun e => by rw [e]; exact Frame.le_refl _) (fun e => by rw [e]; exact huB)⟩
      v_le := fun y => ⟨hM.regimeB_above_u S.swap hv hu hB hBR, fun h => h.elim
        (fun e => by rw [e]; exact Frame.le_refl _) (fun e => by rw [e]; exact hvB)⟩
      le_both := fun _ hxu hxv => hM.eq_root_of_le_both S hxu hxv
      not_uv := S.not_uv
      not_vu := S.not_vu }
  exact ⟨T, rfl, rfl⟩

/-- **The second regime of `𝓜`, exactly.**  The members of `𝓜` split at
non-maximal entrances are exactly the finite posets of the second regime's
shape that are reduced. -/
theorem inKPMin_regimeB_iff {M : Type} [Frame M] :
    (InKPMin M ∧ ∃ S : RootSplit M, ¬ IsMaxPt S.u) ↔
      (∃ l : List M, ∀ p, p ∈ l) ∧ Frame.Antisymm M ∧ ∃ T : RegimeB M, T.Reduced := by
  constructor
  · rintro ⟨hM, S, hu⟩
    obtain ⟨T, -, -⟩ := hM.exists_regimeB S hu
    exact ⟨hM.list.finite, hM.antisymm, T, T.reduced_of_inKPMin hM⟩
  · rintro ⟨hfin, hA, T, hT⟩
    exact ⟨T.inKPMin_of_reduced hfin hA hT, T.split, fun h => T.u_ne_B (h _ T.u_le_B).symm⟩

/-! ## The ladder -/

/-- The points of the ladder frame. -/
inductive LPt (n : Nat) where
  | root | A | B | u | v | c0
  | w : Fin (n + 1) → LPt n
  deriving DecidableEq

namespace LPt

variable {n : Nat}

def le : LPt n → LPt n → Prop
  | .root, _ => True
  | .A, y => y = .A
  | .B, y => y = .B
  | .u, y => y = .u ∨ y = .B
  | .v, y => y = .v ∨ y = .B
  | .c0, y => y = .c0 ∨ y = .A ∨ y = .B
  | .w _, .u => True
  | .w _, .A => True
  | .w _, .B => True
  | .w i, .c0 => 1 ≤ i.val
  | .w i, .w j => j.val = i.val ∨ j.val + 2 ≤ i.val
  | .w _, _ => False

instance : Frame (LPt n) where
  le := le
  le_refl x := by cases x <;> simp [le]
  le_trans {x y z} h₁ h₂ := by
    cases x <;> cases y <;> cases z <;> simp_all [le] <;> omega

theorem antisymm : Frame.Antisymm (LPt n) := by
  intro x y h₁ h₂
  cases x <;> cases y <;> simp_all [Frame.le, le] <;> (try apply Fin.ext) <;> omega

/-! ### Facts about the order -/

theorem root_le (x : LPt n) : LPt.root ≼ x := trivial

theorem eq_A_of_A_le {y : LPt n} (h : LPt.A ≼ y) : y = .A := h

theorem not_le_A_iff (x : LPt n) : ¬ x ≼ .A ↔ x = .u ∨ x = .v ∨ x = .B := by
  cases x <;> simp [Frame.le, le]

theorem eq_root_of_le_uv {x : LPt n} (hu : x ≼ .u) (hv : x ≼ .v) : x = .root := by
  cases x <;> simp_all [Frame.le, le]

theorem u_le_iff (y : LPt n) : LPt.u ≼ y ↔ y = .u ∨ y = .B := Iff.rfl
theorem v_le_iff (y : LPt n) : LPt.v ≼ y ↔ y = .v ∨ y = .B := Iff.rfl

theorem above_B {y : LPt n} (h : LPt.B ≼ y) : y = .B := h

/-! ### The list of points -/

/-- Every point, each once. -/
def all (n : Nat) : List (LPt n) :=
  [.root, .A, .B, .u, .v, .c0] ++ (List.finRange (n + 1)).map .w

theorem mem_all (x : LPt n) : x ∈ all n := by
  cases x <;> simp [all, List.mem_finRange]

theorem length_all : (all n).length = n + 7 := by
  simp [all]

theorem nodup_all : (all n).Nodup := by
  rw [all, List.nodup_append]
  refine ⟨by simp, List.Pairwise.map LPt.w (fun _ _ hab h => hab (LPt.w.inj h))
    (List.nodup_finRange _), ?_⟩
  intro a ha b hb
  simp only [List.mem_map] at hb
  obtain ⟨j, _, rfl⟩ := hb
  simp at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end LPt

namespace LPt

variable {n : Nat}

/-! ### The ladder has the second regime's shape -/

/-- The ladder frame, as a frame of the second regime's shape. -/
abbrev regimeB : RegimeB (LPt n) where
  r := .root
  A := .A
  B := .B
  u := .u
  v := .v
  root := root_le
  A_max _ h := eq_A_of_A_le h
  B_max _ h := above_B h
  not_le_A := not_le_A_iff
  not_le_B z := by cases z <;> simp [Frame.le, le]
  u_le := u_le_iff
  v_le := v_le_iff
  le_both _ hu hv := eq_root_of_le_uv hu hv
  not_uv := by simp [Frame.le, le]
  not_vu := by simp [Frame.le, le]

end LPt

namespace LPt

variable {n : Nat}

/-! ### The ladder is reduced -/

theorem w_ne {j k : Fin (n + 1)} (h : j.val ≠ k.val) : (LPt.w j : LPt n) ≠ .w k :=
  fun e => h (congrArg Fin.val (LPt.w.inj e))

/-- **Two rungs differ in what lies strictly above them.**  With `j` below `k`:
rung `j` lies strictly above rung `k` when `j + 2 ≤ k`; otherwise `k = j + 1`,
and rung `k` sees `c0` where rung `0` does not, or sees rung `j - 1`, which rung
`j` does not. -/
theorem not_beta_w {j k : Fin (n + 1)} (hjk : j.val < k.val) :
    ¬ IsBeta (LPt.w j : LPt n) (.w k) := by
  rintro ⟨-, hβ⟩
  by_cases h2 : j.val + 2 ≤ k.val
  · exact ((hβ (.w j)).mpr ⟨by simp only [Frame.le, le]; omega, w_ne (by omega)⟩).2 rfl
  by_cases hj : j.val = 0
  · have := ((hβ .c0).mpr ⟨by simp only [Frame.le, le]; omega, nofun⟩).1
    simp only [Frame.le, le] at this
    omega
  · have := ((hβ (.w ⟨j.val - 1, by omega⟩)).mpr
      ⟨by simp only [Frame.le, le]; omega, w_ne (by show j.val - 1 ≠ k.val; omega)⟩).1
    simp only [Frame.le, le] at this
    omega

theorem wiring_cases {x : LPt n} (hx : regimeB.Wiring x) (hxr : x ≠ .root) :
    x = .c0 ∨ ∃ k, x = .w k := by
  obtain ⟨hA, hB, hu, hv⟩ := hx
  cases x with
  | c0 => exact Or.inl rfl
  | w k => exact Or.inr ⟨k, rfl⟩
  | root => exact absurd rfl hxr
  | A => exact absurd rfl hA
  | B => exact absurd rfl hB
  | u => exact absurd rfl hu
  | v => exact absurd rfl hv

/-- **The ladder is reduced.**  The wiring is `c0` and the rungs.  `c0` sees
neither entrance and the rungs see `u`, so `c0` pairs with no rung.  Two rungs
differ in what lies strictly above them (`not_beta_w`).  And no rung collapses
into another: that one would lie below `c0`, so be rung `1` or higher, and
below the rungs two and three beneath the first, which no rung does. -/
theorem reduced : (regimeB : RegimeB (LPt n)).Reduced := by
  refine RegimeB.reduced_of _ fun x y hp hx hy hxr hyr => ?_
  rcases wiring_cases hx hxr with rfl | ⟨k, rfl⟩ <;>
    rcases wiring_cases hy hyr with rfl | ⟨j, rfl⟩
  · exact hp.elim (fun h => h.1 rfl) (fun h => h.1 rfl)
  · rcases hp with ⟨-, hc, -⟩ | ⟨-, hβ⟩
    · simp [Frame.le, le] at hc
    · have := ((hβ .u).mpr ⟨trivial, nofun⟩).1
      simp [Frame.le, le] at this
  · rcases hp with ⟨-, -, hα⟩ | ⟨-, hβ⟩
    · have := hα .u trivial nofun
      simp [Frame.le, le] at this
    · have := ((hβ .u).mp ⟨trivial, nofun⟩).1
      simp [Frame.le, le] at this
  · have hkj : k.val ≠ j.val := fun e =>
      hp.elim (fun h => h.1 (by rw [Fin.ext e])) (fun h => h.1 (by rw [Fin.ext e]))
    rcases hp with ⟨-, hle, hα⟩ | hβ
    · simp only [Frame.le, le] at hle
      have hc := hα .c0 (by simp only [Frame.le, le]; omega) nofun
      have h2 := hα (.w ⟨k.val - 2, by omega⟩) (by simp only [Frame.le, le]; omega)
        (w_ne (by show k.val - 2 ≠ k.val; omega))
      simp only [Frame.le, le] at hc h2
      have h3 := hα (.w ⟨k.val - 3, by omega⟩) (by simp only [Frame.le, le]; omega)
        (w_ne (by show k.val - 3 ≠ k.val; omega))
      simp only [Frame.le, le] at h3
      omega
    · rcases Nat.lt_or_gt_of_ne hkj with h | h
      · exact not_beta_w h hβ
      · exact not_beta_w h hβ.symm

/-- **Every ladder frame is a minimal refuter.** -/
theorem inKPMin (n : Nat) : InKPMin (LPt n) :=
  regimeB.inKPMin_of_reduced ⟨all n, mem_all⟩ antisymm reduced

/-- A ladder frame lies below another only if it has no more rungs. -/
theorem le_of_sh {n m : Nat} (h : SH (Upset (LPt m)) (Upset (LPt n))) : m ≤ n := by
  have := length_le_of_sh antisymm nodup_all mem_all mem_all h
  rw [length_all, length_all] at this
  omega

end LPt

/-- **`𝓜` is infinite.**  Every ladder frame is a minimal refuter, and no two
of them lie below each other both ways. -/
theorem kpMin_infinite :
    (∀ n, InKPMin (LPt n)) ∧
      ∀ n m, SH (Upset (LPt m)) (Upset (LPt n)) → SH (Upset (LPt n)) (Upset (LPt m)) →
        n = m :=
  ⟨LPt.inKPMin, fun _ _ h₁ h₂ => Nat.le_antisymm (LPt.le_of_sh h₂) (LPt.le_of_sh h₁)⟩
