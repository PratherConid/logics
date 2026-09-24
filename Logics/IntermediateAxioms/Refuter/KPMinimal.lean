import Logics.IntermediateAxioms.Refuter.KPRefuter

/-!
# The shape of the minimal refuters of Kreisel and Putnam's axiom

`𝓜` is the part of the list `𝓛` that is minimal in the Jankov order: frames
refuting the axiom below which nothing smaller refutes it (`InKPMin`).  It is
taken among posets.  That loses nothing, since a preorder has the same upward
closed sets as the poset of its equivalence classes, and it is needed, since
duplicating a point changes the frame without changing the algebra.

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

## The theorem

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
  covered by `B` alone (`regimeB_above_u`).  Every point off the region but `A`
  sees both `A` and `B` (`regimeB_sees`); at most one of them sees neither
  entrance (`regimeB_neither`), and it sees nothing else (`regimeB_neither_above`);
  the rest see exactly one (`sees_one`).  `regimeB_points` gathers these.

So the first regime is finite, and every other member lies in the second, whose
frames differ only in how the points seeing one entrance alone are wired to each
other, to the one point seeing neither, and to the root.

## What is not here

The theorem constrains the members of `𝓜` and produces none.  That the frames of
the first regime, and those of the second found by search, are each in `𝓜` is
checked by machine but not formalised; so is the count of members by size that
suggests there are infinitely many.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

/-- Homomorphisms carry the axiom's value along. -/
theorem Hom.map_kpAt {α β : Type} [HeytingAlgebra α] [HeytingAlgebra β] (f : Hom α β)
    (a b c : α) : f.toFun (kpAt a b c) = kpAt (f.toFun a) (f.toFun b) (f.toFun c) := by
  simp only [kpAt, f.map_himp, f.map_sup, f.map_neg]

/-! ## Two ways a merge keeps the axiom refuted -/

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
  antisymm : ∀ p q : M, p ≼ q → q ≼ p → p = q
  minimal : RefuterLB (Upset M) kreiselPutnamForm

/-- Nothing lies above `m` but `m` itself. -/
def IsMaxPt {M : Type} [Frame M] (m : M) : Prop := ∀ p, m ≼ p → p = m

namespace InKPMin

variable {M : Type} [Frame M]

theorem exists_nodup (hM : InKPMin M) : ∃ l : List M, l.Nodup ∧ ∀ p, p ∈ l := by
  obtain ⟨l, hl⟩ := hM.list.finite
  obtain ⟨l', hnd, hmem⟩ := ListCount.exists_nodup l
  exact ⟨l', hnd, fun p => (hmem p).mpr (hl p)⟩

theorem exists_max_above (hM : InKPMin M) (x : M) : ∃ m, x ≼ m ∧ IsMaxPt m := by
  obtain ⟨l, hl⟩ := hM.list.finite
  obtain ⟨m, hxm, hmax⟩ := hasMaximal_of_list l hl (fun p => x ≼ p) ⟨x, Frame.le_refl x⟩
  exact ⟨m, hxm, fun p hmp => hM.antisymm _ _ (hmax p (Frame.le_trans hxm hmp) hmp) hmp⟩

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
  have htop : Upset.up S.root = ⊤ :=
    Upset.ext fun p => ⟨fun _ => trivial, fun _ => S.isRoot p⟩
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

theorem exists_ne_above {x : M} (hx : ¬ IsMaxPt x) : ∃ p, x ≼ p ∧ p ≠ x :=
  Classical.byContradiction fun hc => hx fun p hxp =>
    Classical.byContradiction fun hne => hc ⟨p, hxp, hne⟩

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
  have hN : ∀ {x x' y : M}, (x = A ∨ x = A') → (x' = A ∨ x' = A') → x ≼ y →
      (y = A ∨ y = A') ∨ x' ≼ y := by
    intro x x' y hx _ hxy
    left
    rcases hx with rfl | rfl
    · exact Or.inl (hA y hxy)
    · exact Or.inr (hA' y hxy)
  have hout : ∀ {w : M}, S.R.mem w → ¬ (w = A ∨ w = A') := by
    rintro w hw (rfl | rfl)
    · exact hAR hw
    · exact hA'R hw
  exact hM.no_collapse_single S (fun x => x = A ∨ x = A') A (Or.inl rfl) hN
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
  have hN : ∀ {x x' y : M}, (x = S.u ∨ x = w) → (x' = S.u ∨ x' = w) → x ≼ y →
      (y = S.u ∨ y = w) ∨ x' ≼ y := by
    intro x x' y hx _ hxy
    left
    rcases hx with rfl | rfl
    · exact Or.inl (hu y hxy)
    · exact Or.inr (hw y hxy)
  have hvw : ¬ S.v ≼ w := fun h => hwv (hv w h)
  have hwv' : ¬ w ≼ S.v := fun h => hwv (hw S.v h).symm
  refine hM.no_collapse_triple S.swap (fun x => x = S.u ∨ x = w) S.u (Or.inl rfl) hN
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
  exact hM.no_collapse_single S (fun y => x ≼ y) x (Frame.le_refl x)
    (fun hy _ hyz => Or.inl (Frame.le_trans hy hyz))
    (fun y hy => ⟨fun _ => hneg (Frame.le_refl x), fun _ => hneg hy⟩)
    hnu hnv (x := A) (hM.le_outside S hA hAR hx) (Ne.symm hxA)

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
  have hN : ∀ {x x' y : M}, (x = B ∨ x = B') → (x' = B ∨ x' = B') → x ≼ y →
      (y = B ∨ y = B') ∨ x' ≼ y := by
    intro x x' y hx _ hxy
    left
    rcases hx with rfl | rfl
    · exact Or.inl (hB y hxy)
    · exact Or.inr (hB' y hxy)
  have hmemN : ∀ {x : M}, (x = B ∨ x = B') → S.R.mem x := by
    rintro x (h | h)
    · rw [h]; exact hBR
    · rw [h]; exact hB'R
  have hnot : ∀ {w : M}, ¬ IsMaxPt w → ¬ (w = B ∨ w = B') := by
    rintro w hw (h | h)
    · rw [h] at hw; exact hw hB
    · rw [h] at hw; exact hw hB'
  exact hM.no_collapse_single S (fun x => x = B ∨ x = B') B (Or.inl rfl) hN
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
    exact hM.no_collapse_single S (fun y => z ≼ y) z (Frame.le_refl z)
      (fun hy _ hyz => Or.inl (Frame.le_trans hy hyz))
      (fun y hy => ⟨fun h => absurd h (S.not_neg_of_mem (S.R.upward hy hzR)),
        fun h => absurd h (S.not_neg_of_mem hzR)⟩)
      hnu hnv (x := B) (hM.regimeB_le S hu hv hB hBR hzR) (Ne.symm hzB)
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
  exact hM.no_collapse_single S (fun y => x ≼ y) x (Frame.le_refl x)
    (fun hy _ hyz => Or.inl (Frame.le_trans hy hyz))
    (fun y hy => ⟨fun _ => hneg (Frame.le_refl x), fun _ => hneg hy⟩)
    (fun h => hxB (Frame.le_trans h (hle S.min_u.1)))
    (fun h => hxB (Frame.le_trans h (hle S.min_v.1)))
    (x := A) (hM.le_outside S hA hAR hx) (Ne.symm hxA)

/-- **At most one point sees neither entrance**: all of them would merge. -/
theorem regimeB_neither (hM : InKPMin M) (S : RootSplit M) (hu : ¬ IsMaxPt S.u)
    (hv : ¬ IsMaxPt S.v) {A B : M} (hA : IsMaxPt A) (hAR : ¬ S.R.mem A)
    (hB : IsMaxPt B) (hBR : S.R.mem B) {x x' : M}
    (hx : ¬ S.R.mem x) (hxA : x ≠ A) (hxu : ¬ x ≼ S.u) (hxv : ¬ x ≼ S.v)
    (hx' : ¬ S.R.mem x') (hx'A : x' ≠ A) (hx'u : ¬ x' ≼ S.u) (hx'v : ¬ x' ≼ S.v) :
    x = x' := by
  refine Classical.byContradiction fun hne => ?_
  have hsees : ∀ {y : M}, ¬ S.R.mem y → y ≠ A → y ≼ B :=
    fun hy hyA => hM.regimeB_sees S hu hv hA hAR hB hBR hy hyA
  have hN : ∀ {y y' z : M},
      (¬ S.R.mem y ∧ y ≠ A ∧ ¬ y ≼ S.u ∧ ¬ y ≼ S.v) →
      (¬ S.R.mem y' ∧ y' ≠ A ∧ ¬ y' ≼ S.u ∧ ¬ y' ≼ S.v) → y ≼ z →
      (¬ S.R.mem z ∧ z ≠ A ∧ ¬ z ≼ S.u ∧ ¬ z ≼ S.v) ∨ y' ≼ z := by
    intro y y' z hy hy' hyz
    by_cases hzR : S.R.mem z
    · rcases (hM.regimeB_region S hu hv hB hBR z).mp hzR with h | h | h
      · rw [h] at hyz; exact absurd hyz hy.2.2.1
      · rw [h] at hyz; exact absurd hyz hy.2.2.2
      · rw [h]; exact Or.inr (hsees hy'.1 hy'.2.1)
    · by_cases hzA : z = A
      · rw [hzA]; exact Or.inr (hM.le_outside S hA hAR hy'.1)
      · exact Or.inl ⟨hzR, hzA, fun h => hy.2.2.1 (Frame.le_trans hyz h),
          fun h => hy.2.2.2 (Frame.le_trans hyz h)⟩
  exact hM.no_collapse_single S (fun y => ¬ S.R.mem y ∧ y ≠ A ∧ ¬ y ≼ S.u ∧ ¬ y ≼ S.v) x
    ⟨hx, hxA, hxu, hxv⟩ hN
    (fun y hy => ⟨fun h => absurd h (S.not_neg_of_le (hsees hy.1 hy.2.1) hBR),
      fun h => absurd h (S.not_neg_of_le (hsees hx hxA) hBR)⟩)
    (fun h => h.1 S.min_u.1) (fun h => h.1 S.min_v.1) (x := x')
    ⟨hx', hx'A, hx'u, hx'v⟩ (Ne.symm hne)

/-- **Above the point seeing neither entrance lie only `A` and `B`.** -/
theorem regimeB_neither_above (hM : InKPMin M) (S : RootSplit M) (hu : ¬ IsMaxPt S.u)
    (hv : ¬ IsMaxPt S.v) {A B : M} (hA : IsMaxPt A) (hAR : ¬ S.R.mem A)
    (hB : IsMaxPt B) (hBR : S.R.mem B) {x : M}
    (hx : ¬ S.R.mem x) (hxA : x ≠ A) (hxu : ¬ x ≼ S.u) (hxv : ¬ x ≼ S.v)
    {y : M} (hxy : x ≼ y) : y = x ∨ y = A ∨ y = B := by
  by_cases hyR : S.R.mem y
  · rcases (hM.regimeB_region S hu hv hB hBR y).mp hyR with h | h | h
    · rw [h] at hxy; exact absurd hxy hxu
    · rw [h] at hxy; exact absurd hxy hxv
    · exact Or.inr (Or.inr h)
  · by_cases hyA : y = A
    · exact Or.inr (Or.inl hyA)
    · exact Or.inl (hM.regimeB_neither S hu hv hA hAR hB hBR hyR hyA
        (fun h => hxu (Frame.le_trans hxy h)) (fun h => hxv (Frame.le_trans hxy h))
        hx hxA hxu hxv)

/-- **Every other point sees at most one entrance**, in either regime: seeing
both is reserved for the root. -/
theorem sees_one (hM : InKPMin M) (S : RootSplit M) {x : M} (hxr : x ≠ S.root)
    (hsee : x ≼ S.u ∨ x ≼ S.v) : (x ≼ S.u ∧ ¬ x ≼ S.v) ∨ (x ≼ S.v ∧ ¬ x ≼ S.u) :=
  hsee.elim (fun h => Or.inl ⟨h, fun h' => hxr (hM.eq_root_of_le_both S h h')⟩)
    (fun h => Or.inr ⟨h, fun h' => hxr (hM.eq_root_of_le_both S h' h)⟩)

end InKPMin

namespace InKPMin

variable {M : Type} [Frame M]

/-! ### Every point, regime by regime -/

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

/-- **The second regime, point by point.**  Besides the root, `A`, `B` and the
two entrances, every point sees `A` and `B`, and either sees exactly one entrance
or is the one point, by `regimeB_neither`, seeing nothing but `A` and `B`. -/
theorem regimeB_points (hM : InKPMin M) (S : RootSplit M) (hu : ¬ IsMaxPt S.u)
    (hv : ¬ IsMaxPt S.v) {A B : M} (hA : IsMaxPt A) (hAR : ¬ S.R.mem A)
    (hB : IsMaxPt B) (hBR : S.R.mem B) (x : M) :
    x = S.root ∨ x = A ∨ x = S.u ∨ x = S.v ∨ x = B ∨
      (x ≼ A ∧ x ≼ B ∧
        ((∀ y, x ≼ y → y = x ∨ y = A ∨ y = B) ∨
          (x ≼ S.u ∧ ¬ x ≼ S.v) ∨ (x ≼ S.v ∧ ¬ x ≼ S.u))) := by
  by_cases hxR : S.R.mem x
  · rcases (hM.regimeB_region S hu hv hB hBR x).mp hxR with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  by_cases hxA : x = A
  · exact Or.inr (Or.inl hxA)
  by_cases hxr : x = S.root
  · exact Or.inl hxr
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hM.le_outside S hA hAR hxR,
    hM.regimeB_sees S hu hv hA hAR hB hBR hxR hxA, ?_⟩))))
  by_cases hsee : x ≼ S.u ∨ x ≼ S.v
  · exact Or.inr (hM.sees_one S hxr hsee)
  · exact Or.inl fun y hxy => hM.regimeB_neither_above S hu hv hA hAR hB hBR hxR hxA
      (fun h => hsee (Or.inl h)) (fun h => hsee (Or.inr h)) hxy

end InKPMin
