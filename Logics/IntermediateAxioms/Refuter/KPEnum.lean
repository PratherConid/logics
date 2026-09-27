import Logics.IntermediateAxioms.Refuter.KPMinimal

/-!
# The minimal refuters of Kreisel and Putnam's axiom, listed

`KPMinimal` gives the shape every member of `𝓜` has, decides the second regime
exactly, as the reduced frames of its shape, and builds the frames `BPt` of
that regime.  This file lists the members, up to isomorphism (`FrameIso`).
They fall into three families (`InKPMin.family`), and every member is on the
list (`InKPMin.classify`).

* **The first family** (`kpFirst`, frames `APt`): split at maximal entrances.
  Three frames: the three branch fork on `A`, `u` and `v`, with four points;
  that fork with a point below `A` and `u`; and with a point below `A` and each
  entrance.
* **The second family** (`kpSecond`, frames `BPt false`): split at entrances
  that are not maximal, with no point seeing neither entrance.  Three frames,
  of five, six and seven points: a root; `A`; `u` and `v` covered by `B`; and
  below each entrance nothing, or a single point below it, `A` and `B`.
* **The third family** (`kpEnum`, frames `BPt true`): as the second, but with a
  point `c0` below `A` and `B` alone.  Below each entrance lies a side of the
  Rieger--Nishimura ladder whose top rung is `c0`, and the frame is fixed by the
  two sides.  A side with `k` rungs is `I k`, the rungs `1, …, k`, or
  `J (k - 1)`, the rungs `1, …, k - 1` and `k + 1`, so there are two for each
  `k ≥ 1`.  `kpEnum n` lists the unordered pairs of sides giving `n` points,
  `2 (n - 6)` of them for odd `n ≥ 7` and one more for even `n ≥ 6` (checked by
  `decide` up to twelve points).  The ladder frames `LPt` are the pairs of an
  `I` side and the empty one.

For each family the listed frames are members (`kpFirst_sound`,
`kpSecond_sound`, `kpEnum_sound`) and every member is isomorphic to one of them
(`kpFirst_complete`, `kpSecond_complete`, `kpEnum_complete`).

## Membership

The frames of the second regime are members by `BPt.inKPMin`.  The frames of
the first regime go through `inKPMin_iff` directly: away from the root there
are too few points for a split (`not_splits_of_few`); only maximal points pair
(`APt.pair_max`); and after merging two of them every region is entered once
up to the merge (`APt.regions`, `kp_top_of_pair`).

## Exhaustiveness

The first regime is read off `regimeA_points` and `regimeA_side`
(`InKPMin.exists_iso_regimeA`).  In the second regime, reducedness makes the
points seeing neither entrance, and each side coloured by lying below such a
point, a reduced side (`ReducedSide.of_frame`): the points off it tell equally
coloured points apart by nothing.  A reduced side is a side of the ladder
(`ReducedSide.ladder`).  So there is at most one point seeing neither entrance
(`RegimeB.neither_unique`), and the member is a frame `BPt`
(`RegimeB.exists_iso`).

## What is not here

That distinct entries of the list give frames that are not isomorphic, and
that the families are disjoint, is not proved; nor is the count of `kpEnum n`
for every `n`.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

/-! ## A member of the second regime, point by point -/

namespace RegimeB

variable {M : Type} [Frame M] {T : RegimeB M}

/-- What a point seeing neither entrance lies below, off its own part. -/
theorem neither_le_iff (hA : Frame.Antisymm M) {x z : M} (hx : T.Neither x)
    (hz : ¬ T.Neither z) : x ≼ z ↔ z = T.A ∨ z = T.B := by
  constructor
  · intro hxz
    rcases T.cases_pt z with e | e | e | e | e | e | e | e
    · exact absurd (e ▸ hxz) (T.not_le_r hA hx.2.1)
    · exact Or.inl e
    · exact Or.inr e
    · exact absurd (e ▸ hxz) hx.2.2.1
    · exact absurd (e ▸ hxz) hx.2.2.2
    · exact absurd e hz
    · exact absurd (Frame.le_trans hxz e.2.2) hx.2.2.1
    · exact absurd (Frame.le_trans hxz e.2.2) hx.2.2.2
  · rintro (rfl | rfl)
    · exact T.wiring_le_A hx.1
    · exact T.wiring_le_B hx.1

/-- The points seeing neither entrance, all uncoloured, form a reduced side. -/
theorem neither_reduced (hM : InKPMin M) : ReducedSide T.Neither (fun _ => False) :=
  .of_frame hM.antisymm (fun _ _ _ h => h) (fun hx _ h => (T.reduced_of_inKPMin hM _ _ h).1 hx.1)
    fun hx hy hz _ hxz =>
      (neither_le_iff hM.antisymm hy hz).mpr ((neither_le_iff hM.antisymm hx hz).mp hxz)

/-- **At most one point sees neither entrance.** -/
theorem neither_unique (hM : InKPMin M) {x y : M} (hx : T.Neither x) (hy : T.Neither y) :
    x = y := by
  obtain ⟨l, _, hl⟩ := hM.exists_nodup
  exact (neither_reduced hM).eq_of_not_col hl hx hy id id

/-- The colour on the side of `u` is lying below the point seeing neither
entrance. -/
theorem colU_iff (hM : InKPMin M) {x c : M} (hc : T.Neither c) : T.ColU x ↔ x ≼ c :=
  ⟨fun ⟨c', hc', hxc'⟩ => by rw [neither_unique hM hc hc']; exact hxc', fun h => ⟨c, hc, h⟩⟩

/-- What a point on the side of `u` lies below, off its own side. -/
theorem sideU_le_iff (hM : InKPMin M) {x z : M} (hx : T.SideU x) (hz : ¬ T.SideU z) :
    x ≼ z ↔ z = T.A ∨ z = T.B ∨ z = T.u ∨ (T.Neither z ∧ T.ColU x) := by
  constructor
  · intro hxz
    rcases T.cases_pt z with e | e | e | e | e | e | e | e
    · exact absurd (e ▸ hxz) (T.not_le_r hM.antisymm hx.2.1)
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact absurd (e ▸ hxz) (T.sideU_not_le_v hx)
    · exact Or.inr (Or.inr (Or.inr ⟨e, z, e, hxz⟩))
    · exact absurd e hz
    · exact absurd (Frame.le_trans hxz e.2.2) (T.sideU_not_le_v hx)
  · rintro (rfl | rfl | rfl | ⟨hz', hc⟩)
    · exact T.wiring_le_A hx.1
    · exact T.wiring_le_B hx.1
    · exact hx.2.2
    · exact (colU_iff hM hz').mp hc

/-- **The side of `u` is a reduced side**, coloured by lying below the point
seeing neither entrance: off the side, points of it are told apart only by the
colour. -/
theorem sideU_reduced (hM : InKPMin M) : ReducedSide T.SideU T.ColU :=
  .of_frame hM.antisymm (fun _ _ hxy ⟨c, hc, hyc⟩ => ⟨c, hc, Frame.le_trans hxy hyc⟩)
    (fun hx _ h => (T.reduced_of_inKPMin hM _ _ h).1 hx.1)
    fun hx hy hz hcol hxz => (sideU_le_iff hM hy hz).mpr
      (by rw [← hcol]; exact (sideU_le_iff hM hx hz).mp hxz)

/-- **A member of the second regime is a frame `BPt`**, with `c0` present
exactly when some point sees neither entrance. -/
theorem exists_iso (hM : InKPMin M) (T : RegimeB M) {c : Bool}
    (hc : c = true ↔ ∃ x, T.Neither x) :
    ∃ σu σv : Side, BPt.Valid c σu σv ∧ Nonempty (FrameIso (BPt c σu σv) M) := by
  have hA := hM.antisymm
  haveI : Nonempty M := ⟨T.r⟩
  obtain ⟨l, hnd, hl⟩ := hM.exists_nodup
  -- each side is a side of the ladder, read off its rungs
  obtain ⟨σu, ψu, hmu, hsu, hleu, hcolu⟩ := (sideU_reduced (T := T) hM).ladder hnd hl
  obtain ⟨σv, ψv, hmv, hsv, hlev, hcolv⟩ := (sideU_reduced (T := T.swap) hM).ladder hnd hl
  -- the point seeing neither entrance, when there is one
  obtain ⟨n0, hn0⟩ : ∃ n0 : M, c = true → T.Neither n0 :=
    ⟨Classical.epsilon T.Neither, fun h => Classical.epsilon_spec (hc.mp h)⟩
  refine ⟨σu, σv, fun hcf => ?_, ⟨FrameIso.ofLeIff BPt.antisymm (fun p => match p with
    | .root => T.r
    | .A => T.A
    | .B => T.B
    | .u => T.u
    | .v => T.v
    | .c0 _ => n0
    | .wu i _ => ψu i
    | .wv i _ => ψv i) (fun z => ?_) fun p q => ?_⟩⟩
  · -- without a point seeing neither entrance nothing is coloured, so every rung is `1`
    have hno : ∀ x, ¬ T.Neither x := fun x hx => by
      have := hc.mpr ⟨x, hx⟩
      rw [hcf] at this
      exact Bool.false_ne_true this
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have h2 : ¬ 2 ≤ i := fun h => by
        obtain ⟨c', hc', _⟩ := (hcolu i hi).mpr h
        exact hno c' hc'
      have := Side.one_le hi
      omega
    · have h2 : ¬ 2 ≤ i := fun h => by
        obtain ⟨c', hc', _⟩ := (hcolv i hi).mpr h
        exact hno c' (T.neither_swap.mp hc')
      have := Side.one_le hi
      omega
  · -- every point is named
    rcases T.cases_pt z with rfl | rfl | rfl | rfl | rfl | hz | hz | hz
    · exact ⟨.root, rfl⟩
    · exact ⟨.A, rfl⟩
    · exact ⟨.B, rfl⟩
    · exact ⟨.u, rfl⟩
    · exact ⟨.v, rfl⟩
    · have h := hc.mpr ⟨z, hz⟩
      exact ⟨.c0 h, neither_unique hM (hn0 h) hz⟩
    · obtain ⟨i, hi, rfl⟩ := hsu z hz
      exact ⟨.wu i hi, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := hsv z hz
      exact ⟨.wv i hi, rfl⟩
  · -- the order, point by point, from what is known of each point
    have hnamed := T.le_named hA
    have hne := T.named_ne
    have hn := fun h => T.neither_facts (hn0 h)
    have hx := fun i h => T.sideU_facts (hmu i h)
    have hy : ∀ i, σv.mem i = true → ψv i ≠ T.A ∧ ψv i ≠ T.B ∧ ψv i ≠ T.v ∧ ψv i ≠ T.u ∧
        ψv i ≠ T.r ∧ ψv i ≼ T.A ∧ ψv i ≼ T.B ∧ ψv i ≼ T.v ∧ ¬ ψv i ≼ T.u :=
      fun i h => T.swap.sideU_facts (hmv i h)
    -- and how the parts lie against each other
    have n_x : ∀ i, c = true → σu.mem i = true → ¬ n0 ≼ ψu i :=
      fun i h h' hle => (hn0 h).2.2.1 (Frame.le_trans hle (hmu i h').2.2)
    have n_y : ∀ i, c = true → σv.mem i = true → ¬ n0 ≼ ψv i :=
      fun i h h' hle => (hn0 h).2.2.2 (Frame.le_trans hle (hmv i h').2.2)
    have x_n : ∀ i, σu.mem i = true → c = true → (ψu i ≼ n0 ↔ 2 ≤ i) :=
      fun i h h' => (colU_iff hM (hn0 h')).symm.trans (hcolu i h)
    have y_n : ∀ i, σv.mem i = true → c = true → (ψv i ≼ n0 ↔ 2 ≤ i) :=
      fun i h h' => (colU_iff (T := T.swap) hM (T.neither_swap.mpr (hn0 h'))).symm.trans
        (hcolv i h)
    have x_y : ∀ i j, σu.mem i = true → σv.mem j = true → ¬ ψu i ≼ ψv j :=
      fun i j h h' hle => T.sideU_not_le_v (hmu i h) (Frame.le_trans hle (hmv j h').2.2)
    have y_x : ∀ i j, σv.mem i = true → σu.mem j = true → ¬ ψv i ≼ ψu j :=
      fun i j h h' hle => T.swap.sideU_not_le_v (hmv i h) (Frame.le_trans hle (hmu j h').2.2)
    clear hsu hsv hcolu hcolv hc hl hnd
    cases p <;> cases q <;> simp [Frame.le, BPt.leb, Frame.le_refl, *]

end RegimeB

/-! ## The frames of the first regime

`APt hx hy` has a root and maximal points `A`, `u` and `v`; when `hx`, a point
`x` below `A` and `u` alone, and when `hy`, a point `y` below `A` and `v`
alone.  With no point added it is the three branch fork. -/

/-- The points of a frame of the first regime. -/
inductive APt (hx hy : Bool) where
  | root | A | u | v
  | x (h : hx = true)
  | y (h : hy = true)
  deriving DecidableEq

namespace APt

variable {hx hy : Bool}

/-- The order, as a test. -/
def leb : APt hx hy → APt hx hy → Bool
  | root, _ => true
  | A, A => true
  | u, u => true
  | v, v => true
  | x _, x _ => true
  | x _, A => true
  | x _, u => true
  | y _, y _ => true
  | y _, A => true
  | y _, v => true
  | _, _ => false

instance : Frame (APt hx hy) where
  le p q := leb p q = true
  le_refl p := by cases p <;> rfl
  le_trans {p q r} h₁ h₂ := by cases p <;> cases q <;> cases r <;> simp_all [leb]

theorem antisymm : Frame.Antisymm (APt hx hy) := by
  intro p q h₁ h₂
  cases p <;> cases q <;> simp_all [Frame.le, leb]

/-- Every point, each once. -/
def all (hx hy : Bool) : List (APt hx hy) :=
  [root, A, u, v] ++ ((if h : hx = true then [x h] else []) ++
    (if h : hy = true then [y h] else []))

theorem mem_all (p : APt hx hy) : p ∈ all hx hy := by
  cases p with
  | x h => simp [all, h]
  | y h => simp [all, h]
  | _ => simp [all]

theorem length_all :
    (all hx hy).length = 4 + (if hx = true then 1 else 0) + (if hy = true then 1 else 0) := by
  cases hx <;> cases hy <;> simp [all]

theorem nodup_all : (all hx hy).Nodup := by
  cases hx <;> cases hy <;> simp [all]

/-- Exchanging `u` and `v`. -/
def swap : APt hx hy → APt hy hx
  | root => root
  | A => A
  | u => v
  | v => u
  | x h => y h
  | y h => x h

theorem swap_swap (p : APt hx hy) : swap (swap p) = p := by
  cases p <;> rfl

def swapIso : FrameIso (APt hx hy) (APt hy hx) :=
  .ofInverse swap swap swap_swap swap_swap fun p q => by
    cases p <;> cases q <;> simp [Frame.le, leb, swap]

/-! ### The split -/

theorem mem_region_A (z : APt hx hy) : (kpRegion root (Upset.up A)).mem z ↔ ¬ z ≼ A :=
  ⟨fun h hzA => h.2 A hzA (Frame.le_refl _), fun hzA => ⟨rfl, fun w hzw hAw => hzA (by
    cases w <;> simp_all [Frame.le, leb, Upset.up])⟩⟩

theorem min_u : (kpRegion root (Upset.up A)).Minimal (u : APt hx hy) :=
  ⟨(mem_region_A _).mpr (by simp [Frame.le, leb]), fun q hq hqu => by
    rw [mem_region_A] at hq
    cases q <;> simp_all [Frame.le, leb]⟩

theorem min_v : (kpRegion root (Upset.up A)).Minimal (v : APt hx hy) :=
  ⟨(mem_region_A _).mpr (by simp [Frame.le, leb]), fun q hq hqv => by
    rw [mem_region_A] at hq
    cases q <;> simp_all [Frame.le, leb]⟩

/-- The split at the root cut out by the set above `A`, entered at the maximal
points `u` and `v`. -/
def split : RootSplit (APt hx hy) :=
  ⟨root, fun _ => rfl, Upset.up A, u, v, min_u, min_v, by simp [Frame.le, leb],
    by simp [Frame.le, leb]⟩

theorem u_max : IsMaxPt (u : APt hx hy) := fun p h => by cases p <;> simp_all [Frame.le, leb]

/-! ### Regions -/

/-- Every point lies below `A`, `u` or `v`. -/
theorem le_max (w : APt hx hy) : w ≼ A ∨ w ≼ u ∨ w ≼ v := by
  cases w <;> simp [Frame.le, leb]

/-- A negation is fixed by which of the three maximal points the set holds. -/
theorem mem_neg_iff (a : Upset (APt hx hy)) (z : APt hx hy) :
    (neg a).mem z ↔ (z ≼ A → ¬ a.mem A) ∧ (z ≼ u → ¬ a.mem u) ∧ (z ≼ v → ¬ a.mem v) := by
  rw [Upset.neg_mem_iff_of_cover [A, u, v] fun w => (le_max w).elim (⟨A, by simp, ·⟩)
    fun h => h.elim (⟨u, by simp, ·⟩) (⟨v, by simp, ·⟩)]
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]

theorem mem_root (a : Upset (APt hx hy)) (z : APt hx hy) :
    (kpRegion root a).mem z ↔ (z ≼ A → ¬ a.mem A) ∧ (z ≼ u → ¬ a.mem u) ∧ (z ≼ v → ¬ a.mem v) :=
  ⟨fun h => (mem_neg_iff a z).mp h.2, fun h => ⟨rfl, (mem_neg_iff a z).mpr h⟩⟩

/-- Above a point other than the root there are at most three points. -/
theorem few_above {r : APt hx hy} (hr : r ≠ root) :
    ∃ L : List (APt hx hy), (∀ z, r ≼ z → z ∈ L) ∧ L.length < 4 := by
  cases r with
  | root => exact absurd rfl hr
  | A => exact ⟨[A], fun z hz => by cases z <;> simp_all [Frame.le, leb], by simp⟩
  | u => exact ⟨[u], fun z hz => by cases z <;> simp_all [Frame.le, leb], by simp⟩
  | v => exact ⟨[v], fun z hz => by cases z <;> simp_all [Frame.le, leb], by simp⟩
  | x h => exact ⟨[x h, A, u], fun z hz => by cases z <;> simp_all [Frame.le, leb], by simp⟩
  | y h => exact ⟨[y h, A, v], fun z hz => by cases z <;> simp_all [Frame.le, leb], by simp⟩

/-- **The axiom fails only at the root.** -/
theorem root_of_splits {r : APt hx hy} {a : Upset (APt hx hy)} (hs : (kpRegion r a).Splits) :
    r = root := by
  refine Classical.byContradiction fun hr => ?_
  obtain ⟨L, hL, hlen⟩ := few_above hr
  exact not_splits_of_few L hL hlen hs

/-- **Only maximal points pair**: `A`, `u` and `v` have no strict successors,
and every other point has some that the other point of a pair would lack. -/
theorem pair_max {p q : APt hx hy} (h : IsAlpha p q ∨ IsBeta p q) :
    (p = A ∨ p = u ∨ p = v) ∧ (q = A ∨ q = u ∨ q = v) := by
  have key : ∀ {p q : APt hx hy}, IsAlpha p q ∨ IsBeta p q → p = A ∨ p = u ∨ p = v := by
    intro p q h
    rcases h with ⟨hne, hle, hα⟩ | ⟨hne, hβ⟩
    · have h₁ := hα A
      have h₂ := hα u
      have h₃ := hα v
      clear hα h
      cases p <;> cases q <;> simp_all [Frame.le, leb]
    · have h₁ := hβ A
      have h₂ := hβ u
      have h₃ := hβ v
      clear hβ h
      cases p <;> cases q <;> simp_all [Frame.le, leb]
  refine ⟨key h, ?_⟩
  rcases h with ⟨hne, hle, hα⟩ | hβ
  · rcases key (Or.inl ⟨hne, hle, hα⟩) with rfl | rfl | rfl <;> cases q <;>
      simp_all [Frame.le, leb]
  · exact key (Or.inr hβ.symm)

/-- **After merging two maximal points, the regions not separating them have
one entrance up to the merge.**  Away from the root there are too few points to
split.  At the root it depends on which maximal points the set holds: with
none, the root is in the region; with two or three, at most the third point is;
with one, the region is the other two, and those are the merged pair, unless a
point below both of them comes in too and is the entrance. -/
theorem regions (a : Upset (APt hx hy)) {p q : APt hx hy} (hp : p = A ∨ p = u ∨ p = v)
    (hq : q = A ∨ q = u ∨ q = v) (hpq : p ≠ q) (ha : a.mem p ↔ a.mem q) (r : APt hx hy) :
    (kpRegion r a).Principal ∨
      ((kpRegion r a).mem p ∧ ∀ z, (kpRegion r a).mem z → p ≼ z ∨ q ≼ z) := by
  by_cases hr : r = root
  · subst hr
    -- a point is in the region when no maximal point above it is in the set
    have hR := mem_root a
    have least : ∀ m : APt hx hy,
        ((m ≼ A → ¬ a.mem A) ∧ (m ≼ u → ¬ a.mem u) ∧ (m ≼ v → ¬ a.mem v)) →
        (∀ z, ((z ≼ A → ¬ a.mem A) ∧ (z ≼ u → ¬ a.mem u) ∧ (z ≼ v → ¬ a.mem v)) → m ≼ z) →
        (kpRegion root a).Principal :=
      fun m hm h => Upset.principal_of_least ⟨(hR m).mpr hm, fun z hz => h z ((hR z).mp hz)⟩
    have pair : ((p ≼ A → ¬ a.mem A) ∧ (p ≼ u → ¬ a.mem u) ∧ (p ≼ v → ¬ a.mem v)) →
        (∀ z, ((z ≼ A → ¬ a.mem A) ∧ (z ≼ u → ¬ a.mem u) ∧ (z ≼ v → ¬ a.mem v)) →
          p ≼ z ∨ q ≼ z) →
        (kpRegion root a).mem p ∧ ∀ z, (kpRegion root a).mem z → p ≼ z ∨ q ≼ z :=
      fun hp' h => ⟨(hR p).mpr hp', fun z hz => h z ((hR z).mp hz)⟩
    clear hR
    by_cases hA : a.mem A <;> by_cases hu : a.mem u <;> by_cases hv : a.mem v
    · -- all three: the region is empty
      refine Or.inl (Upset.principal_of_empty fun z hz => ?_)
      rw [mem_root] at hz
      cases z <;> (try contradiction) <;> simp [Frame.le, leb, hA, hu, hv] at hz
    · -- all but `v`: the region is `v`
      refine Or.inl (least v (by simp [Frame.le, leb, hv]) fun z hz => ?_)
      cases z <;> (try contradiction) <;> simp [Frame.le, leb, hA, hu, hv] at hz ⊢
    · -- all but `u`: the region is `u`
      refine Or.inl (least u (by simp [Frame.le, leb, hu]) fun z hz => ?_)
      cases z <;> (try contradiction) <;> simp [Frame.le, leb, hA, hu, hv] at hz ⊢
    · -- `A` alone: the region is `u` and `v`, the merged pair
      right
      have hpq' : (p = u ∧ q = v) ∨ (p = v ∧ q = u) := by
        clear least pair
        rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> simp_all
      rcases hpq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact pair (by simp [Frame.le, leb, hu, hv]) fun z hz => by
          cases z <;> (try contradiction) <;> simp [Frame.le, leb, hA, hu, hv] at hz ⊢
    · -- all but `A`: the region is `A`
      refine Or.inl (least A (by simp [Frame.le, leb, hA]) fun z hz => ?_)
      cases z <;> (try contradiction) <;> simp [Frame.le, leb, hA, hu, hv] at hz ⊢
    · -- `u` alone: the region is `A` and `v`, and `y` if present
      cases hy with
      | true =>
        refine Or.inl (least (y rfl) (by simp [Frame.le, leb, hA, hv]) fun z hz => ?_)
        cases z <;> (try contradiction) <;> simp [Frame.le, leb, hA, hu, hv] at hz ⊢
      | false =>
        right
        have hpq' : (p = A ∧ q = v) ∨ (p = v ∧ q = A) := by
          clear least pair
          rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> simp_all
        rcases hpq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          exact pair (by simp [Frame.le, leb, hA, hv]) fun z hz => by
            cases z <;> (try contradiction) <;> simp [Frame.le, leb, hA, hu, hv] at hz ⊢
    · -- `v` alone: the region is `A` and `u`, and `x` if present
      cases hx with
      | true =>
        refine Or.inl (least (x rfl) (by simp [Frame.le, leb, hA, hu]) fun z hz => ?_)
        cases z <;> (try contradiction) <;> simp [Frame.le, leb, hA, hu, hv] at hz ⊢
      | false =>
        right
        have hpq' : (p = A ∧ q = u) ∨ (p = u ∧ q = A) := by
          clear least pair
          rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> simp_all
        rcases hpq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          exact pair (by simp [Frame.le, leb, hA, hu]) fun z hz => by
            cases z <;> (try contradiction) <;> simp [Frame.le, leb, hA, hu, hv] at hz ⊢
    · -- none: the root is in the region
      exact Or.inl (least root (by simp [hA, hu, hv]) fun _ _ => rfl)
  · obtain ⟨L, hL, hlen⟩ := few_above hr
    exact Or.inl (Classical.byContradiction fun hnp => not_splits_of_few L hL hlen
      ((Upset.not_principal_iff_splits (hasMinimal_of_list _ mem_all) _).mp hnp))

/-- **Every frame of the first regime is a minimal refuter.** -/
theorem inKPMin : InKPMin (APt hx hy) := by
  refine inKPMin_iff.mpr ⟨⟨⟨all hx hy, mem_all⟩, ⟨root, fun _ => rfl⟩,
    ⟨root, Upset.up A, u, v, min_u, min_v, split.not_uv, split.not_vu⟩⟩, antisymm,
    fun r a hs p => by rw [root_of_splits hs]; rfl, fun p q h => ?_⟩
  obtain ⟨hp, hq⟩ := pair_max h
  have hpq : p ≠ q := h.elim (fun h => h.1) (fun h => h.1)
  refine (Merger.pair p q h).kp_top_of_sat fun a b c ha hb hc => ?_
  have key : ∀ X : Upset (APt hx hy), (∀ z, X.mem z ↔ X.mem ((Merger.pair p q h).g z)) →
      (X.mem p ↔ X.mem q) := fun X hX => (hX p).trans (by rw [Merger.pair_g_of_mem (Or.inl rfl)])
  exact kp_top_of_pair (key b hb) (key c hc) (regions a hp hq hpq (key a ha))

end APt

/-! ## A member of the first regime, point by point -/

namespace InKPMin

variable {M : Type} [Frame M]

/-- **A point below `A` and `u` alone**, in a frame split at maximal
entrances, is outside the region and none of the named points. -/
theorem sideA_facts (S : RootSplit M) (hu : IsMaxPt S.u) {A : M} (hAm : IsMaxPt A)
    (hAR : ¬ S.R.mem A) {z : M} (hz : z ≼ A ∧ z ≼ S.u ∧ ¬ z ≼ S.v) :
    ¬ S.R.mem z ∧ z ≠ A ∧ z ≠ S.u ∧ z ≠ S.v ∧ z ≠ S.root ∧ z ≼ A ∧ z ≼ S.u ∧ ¬ z ≼ S.v :=
  ⟨fun h => hAR (S.R.upward hz.1 h),
    fun e => hAR (by rw [← hAm S.u (e ▸ hz.2.1)]; exact S.min_u.1),
    fun e => hAR (by rw [hu A (e ▸ hz.1)]; exact S.min_u.1),
    fun e => hz.2.2 (e ▸ Frame.le_refl _), fun e => hz.2.2 (e ▸ S.isRoot _), hz⟩

/-- **A member of the first regime is a frame `APt`**: besides the root, `A` and
the two entrances there is at most one point below `A` and `u` alone, and at
most one below `A` and `v` alone (`regimeA_points`, `regimeA_side`). -/
theorem exists_iso_regimeA (hM : InKPMin M) (S : RootSplit M) (hu : IsMaxPt S.u) :
    ∃ hx hy : Bool, Nonempty (FrameIso (APt hx hy) M) := by
  have hA := hM.antisymm
  have hv : IsMaxPt S.v := (hM.max_iff S).mp hu
  obtain ⟨A, hAm, hAR⟩ := hM.exists_outside S
  -- the points below `A` and one entrance alone, and whether there are any
  obtain ⟨bx, xp, hbx, hxp⟩ : ∃ (bx : Bool) (xp : M),
      ((∃ z, z ≼ A ∧ z ≼ S.u ∧ ¬ z ≼ S.v) → bx = true) ∧
        (bx = true → xp ≼ A ∧ xp ≼ S.u ∧ ¬ xp ≼ S.v) :=
    ⟨truth _, @Classical.epsilon _ ⟨A⟩ fun z => z ≼ A ∧ z ≼ S.u ∧ ¬ z ≼ S.v,
      truth_eq_true.mpr, fun h => Classical.epsilon_spec (truth_eq_true.mp h)⟩
  obtain ⟨bY, yp, hbY, hyp⟩ : ∃ (bY : Bool) (yp : M),
      ((∃ z, z ≼ A ∧ z ≼ S.v ∧ ¬ z ≼ S.u) → bY = true) ∧
        (bY = true → yp ≼ A ∧ yp ≼ S.v ∧ ¬ yp ≼ S.u) :=
    ⟨truth _, @Classical.epsilon _ ⟨A⟩ fun z => z ≼ A ∧ z ≼ S.v ∧ ¬ z ≼ S.u,
      truth_eq_true.mpr, fun h => Classical.epsilon_spec (truth_eq_true.mp h)⟩
  have hx := fun h => sideA_facts S hu hAm hAR (hxp h)
  have hy : bY = true → ¬ S.R.mem yp ∧ yp ≠ A ∧ yp ≠ S.v ∧ yp ≠ S.u ∧ yp ≠ S.root ∧
      yp ≼ A ∧ yp ≼ S.v ∧ ¬ yp ≼ S.u := fun h => sideA_facts S.swap hv hAm hAR (hyp h)
  refine ⟨bx, bY, ⟨FrameIso.ofLeIff APt.antisymm (fun p => match p with
    | .root => S.root
    | .A => A
    | .u => S.u
    | .v => S.v
    | .x _ => xp
    | .y _ => yp) (fun z => ?_) fun p q => ?_⟩⟩
  · -- every point is named
    rcases hM.regimeA_points S hu hv hAm hAR z with rfl | rfl | rfl | rfl | hz | hz
    · exact ⟨.root, rfl⟩
    · exact ⟨.A, rfl⟩
    · exact ⟨.u, rfl⟩
    · exact ⟨.v, rfl⟩
    · have h := hbx ⟨z, hz⟩
      have hz' := sideA_facts S hu hAm hAR hz
      exact ⟨.x h, hM.regimeA_side S hu hv hAm hAR (hx h).1 (hx h).2.1 (hxp h).2.1 (hxp h).2.2
        hz'.1 hz'.2.1 hz.2.1 hz.2.2⟩
    · have h := hbY ⟨z, hz⟩
      have hz' := sideA_facts S.swap hv hAm hAR hz
      exact ⟨.y h, hM.regimeA_side S.swap hv hu hAm hAR (hy h).1 (hy h).2.1 (hyp h).2.1
        (hyp h).2.2 hz'.1 hz'.2.1 hz.2.1 hz.2.2⟩
  · -- the order, point by point, from what is known of each point
    have hnamed : (∀ z, S.root ≼ z) ∧ (∀ z, z ≼ S.root ↔ z = S.root) ∧ (∀ z, A ≼ z ↔ z = A) ∧
        (∀ z, S.u ≼ z ↔ z = S.u) ∧ (∀ z, S.v ≼ z ↔ z = S.v) :=
      ⟨S.isRoot, fun _ => le_root_iff hA S.isRoot, fun _ => hAm.le_iff, fun _ => hu.le_iff,
        fun _ => hv.le_iff⟩
    have hAu : A ≠ S.u := fun e => hAR (by rw [e]; exact S.min_u.1)
    have hAv : A ≠ S.v := fun e => hAR (by rw [e]; exact S.min_v.1)
    have huv : S.u ≠ S.v := fun e => S.not_uv (by rw [e]; exact Frame.le_refl _)
    have hrA : S.root ≠ A := fun e => hAu (hAm _ (by rw [← e]; exact S.isRoot S.u)).symm
    have hru : S.root ≠ S.u := fun e => S.not_uv (by rw [← e]; exact S.isRoot S.v)
    have hrv : S.root ≠ S.v := fun e => S.not_vu (by rw [← e]; exact S.isRoot S.u)
    have hne : S.u ≠ A ∧ S.v ≠ A ∧ S.v ≠ S.u ∧ A ≠ S.root ∧ S.u ≠ S.root ∧ S.v ≠ S.root :=
      ⟨hAu.symm, hAv.symm, huv.symm, hrA.symm, hru.symm, hrv.symm⟩
    have x_y : bx = true → bY = true → ¬ xp ≼ yp :=
      fun h h' hle => (hxp h).2.2 (Frame.le_trans hle (hyp h').2.1)
    have y_x : bx = true → bY = true → ¬ yp ≼ xp :=
      fun h h' hle => (hyp h').2.2 (Frame.le_trans hle (hxp h).2.1)
    clear hbx hbY
    cases p <;> cases q <;> simp [Frame.le, APt.leb, Frame.le_refl, *]

end InKPMin

/-! ## The list -/

namespace Side

/-- The sides with `k` rungs. -/
def ofSize : Nat → List Side
  | 0 => [I 0]
  | k + 1 => [I (k + 1), J k]

theorem mem_ofSize {σ : Side} {k : Nat} : σ ∈ ofSize k ↔ σ.size = k := by
  cases σ <;> cases k <;> simp [ofSize, size]

/-- Ordering the sides: by the number of rungs, `I` before `J`. -/
def key : Side → Nat
  | I k => 2 * k
  | J k => 2 * k + 3

end Side

/-- **The first family**: the three frames of the first regime, the three
branch fork and that fork with a point below `A` and `u`, or below `A` and each
entrance. -/
def kpFirst : List (Bool × Bool) := [(false, false), (true, false), (true, true)]

/-- **The second family**: the three frames of the second regime with no point
seeing neither entrance, each side empty or a single rung. -/
def kpSecond : List (Side × Side) := [(.I 0, .I 0), (.I 0, .I 1), (.I 1, .I 1)]

/-- **The third family, enumerated**: the pairs of sides whose frame of the
second regime, with `c0`, has `n` points, each unordered pair once. -/
def kpEnum (n : Nat) : List (Side × Side) :=
  ((List.range (n - 5)).flatMap fun k =>
    (Side.ofSize k).flatMap fun σ => (Side.ofSize (n - 6 - k)).map fun τ => (σ, τ)).filter
      fun p => decide (p.1.key ≤ p.2.key)

theorem mem_kpEnum {n : Nat} {σ τ : Side} :
    (σ, τ) ∈ kpEnum n ↔ σ.size + τ.size + 6 = n ∧ σ.key ≤ τ.key := by
  simp only [kpEnum, List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map,
    Side.mem_ofSize, Prod.mk.injEq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨k, hk, σ', hσ', τ', hτ', rfl, rfl⟩, hkey⟩
    exact ⟨by omega, hkey⟩
  · rintro ⟨hn, hkey⟩
    exact ⟨⟨σ.size, by omega, σ, rfl, τ, by omega, rfl, rfl⟩, hkey⟩

/-- The counts `2 (n - 6)`, and one more for even `n`, from six to twelve points. -/
example : (List.range' 6 7).map (fun n => (kpEnum n).length) = [1, 2, 5, 6, 9, 10, 13] := by
  decide

/-! ## The first family -/

section

variable {M : Type} [Frame M]

/-- The frames of the first family are minimal refuters split at maximal
entrances. -/
theorem kpFirst_sound {p : Bool × Bool} (_ : p ∈ kpFirst) :
    InKPMin (APt p.1 p.2) ∧ ∃ S : RootSplit (APt p.1 p.2), IsMaxPt S.u :=
  ⟨APt.inKPMin, APt.split, APt.u_max⟩

/-- **The first family has no other members**: a minimal refuter split at
maximal entrances is one of its frames. -/
theorem kpFirst_complete (hM : InKPMin M) (S : RootSplit M) (hu : IsMaxPt S.u) :
    ∃ p ∈ kpFirst, Nonempty (FrameIso (APt p.1 p.2) M) := by
  obtain ⟨hx, hy, ⟨e⟩⟩ := hM.exists_iso_regimeA S hu
  cases hx <;> cases hy
  · exact ⟨(false, false), by simp [kpFirst], ⟨e⟩⟩
  · exact ⟨(true, false), by simp [kpFirst], ⟨APt.swapIso.trans e⟩⟩
  · exact ⟨(true, false), by simp [kpFirst], ⟨e⟩⟩
  · exact ⟨(true, true), by simp [kpFirst], ⟨e⟩⟩

/-! ## The second family -/

/-- The frames of the second family are minimal refuters of the second regime
with no point seeing neither entrance. -/
theorem kpSecond_sound {p : Side × Side} (hp : p ∈ kpSecond) :
    InKPMin (BPt false p.1 p.2) ∧ ∀ x, ¬ (BPt.regimeB : RegimeB (BPt false p.1 p.2)).Neither x := by
  refine ⟨BPt.inKPMin fun _ => ?_, fun x ⟨⟨hA, hB, hu, hv⟩, hr, hxu, hxv⟩ => ?_⟩
  · simp only [kpSecond, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      exact ⟨fun i hi => by simp [Side.mem] at hi; omega,
        fun i hi => by simp [Side.mem] at hi; omega⟩
  · cases x with
    | root => exact hr rfl
    | A => exact hA rfl
    | B => exact hB rfl
    | u => exact hu rfl
    | v => exact hv rfl
    | c0 h => exact Bool.false_ne_true h
    | wu _ _ => exact hxu rfl
    | wv _ _ => exact hxv rfl

/-- **The second family has no other members**: a minimal refuter of the
second regime with no point seeing neither entrance is one of its frames. -/
theorem kpSecond_complete (hM : InKPMin M) (T : RegimeB M) (hT : ∀ x, ¬ T.Neither x) :
    ∃ p ∈ kpSecond, Nonempty (FrameIso (BPt false p.1 p.2) M) := by
  obtain ⟨σu, σv, hV, ⟨e⟩⟩ := RegimeB.exists_iso hM T (c := false)
    ⟨fun h => absurd h Bool.false_ne_true, fun ⟨x, hx⟩ => absurd hx (hT x)⟩
  rcases Side.eq_of_small (hV rfl).1 with rfl | rfl <;>
    rcases Side.eq_of_small (hV rfl).2 with rfl | rfl
  · exact ⟨(.I 0, .I 0), by simp [kpSecond], ⟨e⟩⟩
  · exact ⟨(.I 0, .I 1), by simp [kpSecond], ⟨e⟩⟩
  · exact ⟨(.I 0, .I 1), by simp [kpSecond], ⟨BPt.swapIso.trans e⟩⟩
  · exact ⟨(.I 1, .I 1), by simp [kpSecond], ⟨e⟩⟩

/-! ## The third family -/

/-- **The enumeration is sound**: every pair it lists gives a minimal refuter
of the second regime with a point seeing neither entrance, with `n` points. -/
theorem kpEnum_sound {n : Nat} {p : Side × Side} (hp : p ∈ kpEnum n) :
    InKPMin (BPt true p.1 p.2) ∧
      (∃ x, (BPt.regimeB : RegimeB (BPt true p.1 p.2)).Neither x) ∧
      (BPt.all true p.1 p.2).length = n := by
  obtain ⟨σ, τ⟩ := p
  obtain ⟨hn, -⟩ := mem_kpEnum.mp hp
  refine ⟨BPt.inKPMin nofun, ⟨.c0 rfl, ⟨nofun, nofun, nofun, nofun⟩, nofun, nofun, nofun⟩, ?_⟩
  rw [BPt.length_all]
  simp only [ite_true]
  omega

/-- **The enumeration is exhaustive**: a minimal refuter of the second regime
with a point seeing neither entrance is a frame the enumeration lists at its
number of points. -/
theorem kpEnum_complete (hM : InKPMin M) (T : RegimeB M) (hT : ∃ x, T.Neither x)
    {l : List M} (hnd : l.Nodup) (hl : ∀ x, x ∈ l) :
    ∃ p ∈ kpEnum l.length, Nonempty (FrameIso (BPt true p.1 p.2) M) := by
  obtain ⟨σu, σv, -, ⟨e⟩⟩ := RegimeB.exists_iso hM T (c := true) ⟨fun _ => hT, fun _ => rfl⟩
  have hlen := e.length_eq BPt.nodup_all BPt.mem_all hnd hl
  rw [BPt.length_all] at hlen
  simp only [ite_true] at hlen
  by_cases hk : σu.key ≤ σv.key
  · exact ⟨(σu, σv), mem_kpEnum.mpr ⟨by omega, hk⟩, ⟨e⟩⟩
  · exact ⟨(σv, σu), mem_kpEnum.mpr ⟨by omega, by omega⟩, ⟨BPt.swapIso.trans e⟩⟩

/-! ## Every minimal refuter is on the list -/

/-- **The three families cover `𝓜`.** -/
theorem InKPMin.family (hM : InKPMin M) :
    (∃ S : RootSplit M, IsMaxPt S.u) ∨ (∃ T : RegimeB M, ∀ x, ¬ T.Neither x) ∨
      (∃ T : RegimeB M, ∃ x, T.Neither x) := by
  obtain ⟨S⟩ := hM.exists_rootSplit
  by_cases hu : IsMaxPt S.u
  · exact Or.inl ⟨S, hu⟩
  · obtain ⟨T, -, -⟩ := hM.exists_regimeB S hu
    by_cases hN : ∃ x, T.Neither x
    · exact Or.inr (Or.inr ⟨T, hN⟩)
    · exact Or.inr (Or.inl ⟨T, fun x hx => hN ⟨x, hx⟩⟩)

/-- **Every minimal refuter is on the list**: a frame of the first family, of
the second, or of the enumeration at its number of points. -/
theorem InKPMin.classify (hM : InKPMin M) {l : List M} (hnd : l.Nodup) (hl : ∀ x, x ∈ l) :
    (∃ p ∈ kpFirst, Nonempty (FrameIso (APt p.1 p.2) M)) ∨
      (∃ p ∈ kpSecond, Nonempty (FrameIso (BPt false p.1 p.2) M)) ∨
      (∃ p ∈ kpEnum l.length, Nonempty (FrameIso (BPt true p.1 p.2) M)) := by
  rcases hM.family with ⟨S, hu⟩ | ⟨T, hT⟩ | ⟨T, hT⟩
  · exact Or.inl (kpFirst_complete hM S hu)
  · exact Or.inr (Or.inl (kpSecond_complete hM T hT))
  · exact Or.inr (Or.inr (kpEnum_complete hM T hT hnd hl))

end
