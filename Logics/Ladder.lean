import Logics.Reduction

/-!
# The Rieger--Nishimura ladder, and the reduced sides

The Rieger--Nishimura ladder has rungs `s₀, s₁, s₂, …`, with `sᵢ` below `sⱼ`
exactly when `j + 2 ≤ i`.  A *side* (`Side`) is a finite upward closed set of
rungs, the top rung `s₀` left out: `I k`, the rungs `1, …, k`, or `J k`, the
rungs `1, …, k` and `k + 2`.  A set of rungs missing none but perhaps the one
just under its highest is a side (`Side.exists_of_gaps`).

Sides are what reduction leaves of a set of coloured points.  Take a set `D` of
points of a finite poset, each coloured or not, the colour passing downwards,
with no α- or β-pair of equally coloured points (`ReducedSide`); such a set
arises from a frame with no α- or β-pair on it whenever the points off it tell
equally coloured points apart by nothing (`ReducedSide.of_frame`).  Then `D` is
a side of the ladder (`ReducedSide.ladder`): an uncoloured point is the rung
`1`, and a coloured point with `h` points of `D` strictly above it is the rung
`h + 2` (`ReducedSide.rung`).  This is de Jongh's description of the reduced
one-variable models, the colour being the variable's failure.

* At most one point is uncoloured (`eq_of_not_col`): of two, a maximal and the
  next would be a pair.
* Up a strict step the rung drops by at least two (`rung_add_two_le`): the
  points above the upper one and the upper one itself are among those above
  the lower, and if that were all, the two would be an α-pair.
* So the points strictly above a coloured point lie on rungs at least two
  lower.  Counting settles the rest: if rungs are one to one below `m`, a point
  on rung `m` has exactly `m - 2` points strictly above it, all on rungs `1`
  to `m - 2`, so they are all of those (`le_of_rung`).  Two points on rung `m`
  then have the same points strictly above them, a β-pair (`rung_inj`).
* The same count puts a point on every rung at least two below a point's
  (`exists_rung`), which makes the rungs taken a side.
-/

/-! ## Sides -/

/-- A side: `I k` holds the rungs `1, …, k`, and `J k` the rungs `1, …, k` and
`k + 2`. -/
inductive Side where
  | I (k : Nat)
  | J (k : Nat)
  deriving DecidableEq, Repr

namespace Side

/-- The rungs of a side. -/
def mem : Side → Nat → Bool
  | I k, i => decide (1 ≤ i ∧ i ≤ k)
  | J k, i => decide ((1 ≤ i ∧ i ≤ k) ∨ i = k + 2)

/-- The number of rungs. -/
def size : Side → Nat
  | I k => k
  | J k => k + 1

/-- The rungs, as a list. -/
def rungs : Side → List Nat
  | I k => List.range' 1 k
  | J k => List.range' 1 k ++ [k + 2]

theorem mem_rungs (σ : Side) (i : Nat) : i ∈ σ.rungs ↔ σ.mem i = true := by
  cases σ <;> simp [rungs, mem, List.mem_range'_1] <;> omega

theorem nodup_rungs (σ : Side) : σ.rungs.Nodup := by
  cases σ with
  | I k => exact List.nodup_range'
  | J k =>
    refine List.nodup_append.mpr ⟨List.nodup_range', (by simp), ?_⟩
    intro a ha b hb
    rw [List.mem_range'_1] at ha
    rw [List.mem_singleton] at hb
    omega

theorem length_rungs (σ : Side) : σ.rungs.length = σ.size := by
  cases σ <;> simp [rungs, size]

theorem one_le {σ : Side} {i : Nat} (h : σ.mem i = true) : 1 ≤ i := by
  cases σ <;> simp [mem] at h <;> omega

/-- A side is upward closed in the ladder. -/
theorem mem_of_le {σ : Side} {i j : Nat} (h : σ.mem i = true) (hj : 1 ≤ j) (hji : j + 2 ≤ i) :
    σ.mem j = true := by
  cases σ <;> simp [mem] at h ⊢ <;> omega

/-- A side of rungs no higher than `1` is empty or the rung `1`. -/
theorem eq_of_small {σ : Side} (h : ∀ i, σ.mem i = true → i = 1) : σ = I 0 ∨ σ = I 1 := by
  cases σ with
  | I k =>
    by_cases hk : 2 ≤ k
    · exact absurd (h 2 (by simp [mem]; omega)) (by decide)
    · by_cases hk0 : k = 0
      · exact Or.inl (by rw [hk0])
      · exact Or.inr (by rw [show k = 1 by omega])
  | J k => exact absurd (h (k + 2) (by simp [mem])) (by omega)

/-- **A set of rungs with no gap but the one under its top is a side**: with
`t` its highest rung, it is `I t` if it holds the rung `t - 1`, or `t` is the
rung `1`, and `J (t - 2)` otherwise. -/
theorem exists_of_gaps {V : Nat → Prop} {t : Nat} (ht : V t) (hV : ∀ i, V i → 1 ≤ i ∧ i ≤ t)
    (hdown : ∀ j, 1 ≤ j → j + 2 ≤ t → V j) : ∃ σ : Side, ∀ i, σ.mem i = true ↔ V i := by
  have ht1 := (hV t ht).1
  by_cases hI : t = 1 ∨ V (t - 1)
  · refine ⟨I t, fun i => ⟨fun hi => ?_, fun hi => by simp [mem]; exact hV i hi⟩⟩
    simp only [mem, decide_eq_true_eq] at hi
    by_cases hit : i = t
    · rw [hit]; exact ht
    by_cases hi2 : i + 2 ≤ t
    · exact hdown i hi.1 hi2
    rcases hI with h1 | h1
    · omega
    · rw [show i = t - 1 by omega]; exact h1
  · refine ⟨J (t - 2), fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
    · simp only [mem, decide_eq_true_eq] at hi
      rcases hi with hi | hi
      · exact hdown i hi.1 (by omega)
      · rw [show i = t by omega]; exact ht
    · have := hV i hi
      have hne : i ≠ t - 1 := fun e => hI (Or.inr (e ▸ hi))
      simp only [mem, decide_eq_true_eq]
      omega

end Side

/-! ## Reduced sides -/

/-- A set `D` of points, each coloured or not, the colour passing downwards,
with no α- or β-pair of equally coloured points. -/
structure ReducedSide {M : Type} [Frame M] (D col : M → Prop) : Prop where
  antisymm : ∀ {x y}, D x → D y → x ≼ y → y ≼ x → x = y
  col_down : ∀ {x y}, D x → D y → x ≼ y → col y → col x
  no_beta : ∀ {x y}, D x → D y → x ≠ y →
    (∀ z, D z → (x ≼ z ∧ z ≠ x ↔ y ≼ z ∧ z ≠ y)) → (col x ↔ col y) → False
  no_alpha : ∀ {x y}, D x → D y → x ≠ y → x ≼ y →
    (∀ z, D z → x ≼ z → z ≠ x → y ≼ z) → (col x → col y) → False

namespace ReducedSide

variable {M : Type} [Frame M] {D col : M → Prop}

/-- **A reduced side from a frame**: when the frame has no α- or β-pair on `D`,
and points off `D` tell equally coloured points of `D` apart by nothing, a pair
on `D` of equally coloured points would be a pair of the frame. -/
theorem of_frame (hA : Frame.Antisymm M) (hcol : ∀ {x y}, D x → D y → x ≼ y → col y → col x)
    (hpair : ∀ {x y}, D x → D y → (IsAlpha x y ∨ IsBeta x y) → False)
    (hoff : ∀ {x y z}, D x → D y → ¬ D z → (col x ↔ col y) → x ≼ z → y ≼ z) :
    ReducedSide D col where
  antisymm _ _ h₁ h₂ := hA _ _ h₁ h₂
  col_down := hcol
  no_beta {x y} hx hy hne h hc := hpair hx hy (Or.inr ⟨hne, fun z => by
    by_cases hz : D z
    · exact h z hz
    · exact ⟨fun ⟨hxz, _⟩ => ⟨hoff hx hy hz hc hxz, fun e => hz (e ▸ hy)⟩,
        fun ⟨hyz, _⟩ => ⟨hoff hy hx hz hc.symm hyz, fun e => hz (e ▸ hx)⟩⟩⟩)
  no_alpha {x y} hx hy hne hxy h hc := hpair hx hy (Or.inl ⟨hne, hxy, fun z hxz hzx => by
    by_cases hz : D z
    · exact h z hz hxz hzx
    · exact hoff hx hy hz ⟨hc, hcol hx hy hxy⟩ hxz⟩)

variable (l : List M)

/-- Whether `z` is a point of `D` strictly above `x`. -/
noncomputable def strict (D : M → Prop) (x z : M) : Bool := truth (D z ∧ x ≼ z ∧ z ≠ x)

/-- The number of points of `D` strictly above `x`. -/
noncomputable def height (D : M → Prop) (x : M) : Nat := l.countP (strict D x)

/-- **The rung of a point**: `1` if uncoloured, and two more than the number of
points strictly above it if coloured. -/
noncomputable def rung (D col : M → Prop) (x : M) : Nat :=
  if truth (col x) then height l D x + 2 else 1

theorem rung_of_col {x : M} (h : col x) : rung l D col x = height l D x + 2 := by
  rw [rung, ite_eq_left (truth_eq_true.mpr h)]

theorem rung_of_not_col {x : M} (h : ¬ col x) : rung l D col x = 1 := by
  rw [rung, ite_eq_right (fun e => h (truth_eq_true.mp e))]

theorem one_le_rung (x : M) : 1 ≤ rung l D col x := by
  by_cases h : col x
  · rw [rung_of_col l h]; omega
  · rw [rung_of_not_col l h]; exact Nat.le_refl 1

theorem col_iff (x : M) : col x ↔ 2 ≤ rung l D col x := by
  by_cases h : col x
  · rw [rung_of_col l h]; exact ⟨fun _ => by omega, fun _ => h⟩
  · rw [rung_of_not_col l h]; exact ⟨fun h' => absurd h' h, fun h' => by omega⟩

variable {l}

/-- **At most one point is uncoloured.**  Take one maximal among them; any
other, maximal among the rest, has at most that one strictly above it, and so
pairs with it. -/
theorem eq_of_not_col (hR : ReducedSide D col) (hl : ∀ x, x ∈ l) {x y : M} (hx : D x)
    (hy : D y) (hcx : ¬ col x) (hcy : ¬ col y) : x = y := by
  obtain ⟨m, ⟨hmD, hmc⟩, hmmax⟩ :=
    hasMaximal_of_list l hl (fun z => D z ∧ ¬ col z) ⟨x, hx, hcx⟩
  have hmtop : ∀ z, D z → m ≼ z → z = m := fun z hz hmz => by
    by_cases hcz : col z
    · exact absurd (hR.col_down hmD hz hmz hcz) hmc
    · exact hR.antisymm hz hmD (hmmax z ⟨hz, hcz⟩ hmz) hmz
  have key : ∀ p, D p → ¬ col p → p = m := by
    intro p hp hcp
    refine Classical.byContradiction fun hpm => ?_
    obtain ⟨q, ⟨⟨hqD, hqc⟩, hqm⟩, hqmax⟩ := hasMaximal_of_list l hl
      (fun z => (D z ∧ ¬ col z) ∧ z ≠ m) ⟨p, ⟨hp, hcp⟩, hpm⟩
    have hsucc : ∀ z, D z → q ≼ z → z ≠ q → z = m := fun z hz hqz hzq =>
      Classical.byContradiction fun hzm => by
        have hcz : ¬ col z := fun hcz => hqc (hR.col_down hqD hz hqz hcz)
        exact hzq (hR.antisymm hz hqD (hqmax z ⟨⟨hz, hcz⟩, hzm⟩ hqz) hqz)
    by_cases hqm' : q ≼ m
    · exact hR.no_alpha hqD hmD hqm hqm'
        (fun z hz hqz hzq => by rw [hsucc z hz hqz hzq]; exact Frame.le_refl m)
        (fun h => absurd h hqc)
    · refine hR.no_beta hqD hmD hqm (fun z hz => ⟨fun ⟨hqz, hzq⟩ => ?_, fun ⟨hmz, hzm⟩ => ?_⟩)
        ⟨fun h => absurd h hqc, fun h => absurd h hmc⟩
      · rw [hsucc z hz hqz hzq] at hqz
        exact absurd hqz hqm'
      · exact absurd (hmtop z hz hmz) hzm
  rw [key x hx hcx, key y hy hcy]

/-- Counting a point with those strictly above it adds one. -/
theorem height_add_one (hnd : l.Nodup) (hl : ∀ x, x ∈ l) {y : M} (hy : D y) :
    l.countP (strict D y) + 1 = l.countP fun z => truth (D z ∧ y ≼ z) :=
  ListCount.countP_succ hnd (hl y) (truth_eq_true.mpr ⟨hy, Frame.le_refl y⟩)
    (truth_eq_false.mpr fun h => h.2.2 rfl)
    (fun _ _ hzy => truth_congr ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hzy⟩⟩)

/-- **Up a strict step the rung drops by at least two.** -/
theorem rung_add_two_le (hR : ReducedSide D col) (hnd : l.Nodup) (hl : ∀ x, x ∈ l)
    {x y : M} (hx : D x) (hy : D y) (hxy : x ≼ y) (hne : x ≠ y) :
    rung l D col y + 2 ≤ rung l D col x := by
  have hcx : col x := Classical.byContradiction fun hcx =>
    hne (hR.eq_of_not_col hl hx hy hcx fun hcy => hcx (hR.col_down hx hy hxy hcy))
  rw [rung_of_col l hcx]
  by_cases hcy : col y
  · rw [rung_of_col l hcy]
    -- `y` and the points above it are strictly above `x`, and not all of those
    have hsub : ∀ z ∈ l, truth (D z ∧ y ≼ z) = true → strict D x z = true := fun z _ hz => by
      obtain ⟨hzD, hyz⟩ := truth_eq_true.mp hz
      exact truth_eq_true.mpr ⟨hzD, Frame.le_trans hxy hyz,
        fun e => hne (hR.antisymm hx hy hxy (e ▸ hyz))⟩
    by_cases hex : ∃ z ∈ l, strict D x z = true ∧ truth (D z ∧ y ≼ z) = false
    · have hlt := ListCount.countP_lt hsub hex
      have hsucc := height_add_one hnd hl hy
      show height l D y + 2 + 2 ≤ height l D x + 2
      unfold height
      omega
    · refine absurd (hR.no_alpha hx hy hne hxy (fun z hz hxz hzx => ?_) fun _ => hcy) id
      exact Classical.byContradiction fun hyz => hex ⟨z, hl z,
        truth_eq_true.mpr ⟨hz, hxz, hzx⟩, truth_eq_false.mpr fun h => hyz h.2⟩
  · rw [rung_of_not_col l hcy]
    have : 0 < l.countP (strict D x) :=
      List.countP_pos_iff.mpr ⟨y, hl y, truth_eq_true.mpr ⟨hy, hxy, Ne.symm hne⟩⟩
    show 1 + 2 ≤ height l D x + 2
    unfold height
    omega

/-- The points of `D` on rungs at least two below `m`. -/
noncomputable def below (l : List M) (D col : M → Prop) (m : Nat) (z : M) : Bool :=
  truth (D z ∧ rung l D col z + 2 ≤ m)

/-- If rungs are one to one below `m`, the points on rungs at least two below
`m` are at most as many as a list holding those rungs. -/
theorem count_below_le (hnd : l.Nodup) {m : Nat}
    (hinj : ∀ y y', D y → D y' → rung l D col y + 2 ≤ m → rung l D col y' = rung l D col y →
      y' = y)
    (w : List Nat) (hw : ∀ z, D z → rung l D col z + 2 ≤ m → rung l D col z ∈ w) :
    l.countP (below l D col m) ≤ w.length :=
  ListCount.countP_le_of_inj hnd
    (fun y _ y' _ hy hy' e => by
      obtain ⟨hyD, hym⟩ := truth_eq_true.mp hy
      obtain ⟨hy'D, _⟩ := truth_eq_true.mp hy'
      exact (hinj y y' hyD hy'D hym e.symm).symm)
    (fun z _ hz => by
      obtain ⟨hzD, hzm⟩ := truth_eq_true.mp hz
      exact hw z hzD hzm)

/-- The points strictly above a coloured point are among those on rungs at least
two below it. -/
theorem height_le_below (hR : ReducedSide D col) (hnd : l.Nodup) (hl : ∀ x, x ∈ l) {x : M}
    (hx : D x) : ∀ z ∈ l, strict D x z = true → below l D col (rung l D col x) z = true :=
  fun z _ hz => by
    obtain ⟨hzD, hxz, hzx⟩ := truth_eq_true.mp hz
    exact truth_eq_true.mpr ⟨hzD, hR.rung_add_two_le hnd hl hx hzD hxz (Ne.symm hzx)⟩

/-- **A coloured point lies below every point on a rung at least two lower**,
if rungs are one to one down there: those points are no more than the points
strictly above it. -/
theorem le_of_rung (hR : ReducedSide D col) (hnd : l.Nodup) (hl : ∀ x, x ∈ l) {x : M}
    (hx : D x) (hcx : col x)
    (hinj : ∀ y y', D y → D y' → rung l D col y + 2 ≤ rung l D col x →
      rung l D col y' = rung l D col y → y' = y)
    {y : M} (hy : D y) (hyx : rung l D col y + 2 ≤ rung l D col x) : x ≼ y := by
  refine Classical.byContradiction fun hxy => ?_
  have hlt : l.countP (strict D x) < l.countP (below l D col (rung l D col x)) :=
    ListCount.countP_lt (hR.height_le_below hnd hl hx)
      ⟨y, hl y, truth_eq_true.mpr ⟨hy, hyx⟩, truth_eq_false.mpr fun h => hxy h.2.1⟩
  have hle := count_below_le hnd hinj (List.range' 1 (rung l D col x - 2)) fun z _ hz =>
    List.mem_range'_1.mpr ⟨one_le_rung l z, by omega⟩
  rw [List.length_range', show rung l D col x - 2 = l.countP (strict D x) by
    rw [rung_of_col l hcx]; rfl] at hle
  omega

/-- **Rungs are one to one.** -/
theorem rung_inj (hR : ReducedSide D col) (hnd : l.Nodup) (hl : ∀ x, x ∈ l) :
    ∀ x y, D x → D y → rung l D col x = rung l D col y → x = y := by
  suffices h : ∀ n, ∀ x y, D x → D y → rung l D col x = n → rung l D col y = n → x = y from
    fun x y hx hy e => h _ x y hx hy rfl e.symm
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro x y hx hy hxn hyn
    have below_inj : ∀ y₁ y₂, D y₁ → D y₂ → rung l D col y₁ + 2 ≤ n →
        rung l D col y₂ = rung l D col y₁ → y₂ = y₁ :=
      fun y₁ y₂ h₁ h₂ hlt e => ih _ (by omega) y₂ y₁ h₂ h₁ e rfl
    by_cases hcx : col x
    · have hcy : col y := (col_iff l (D := D) y).mpr
        (by rw [hyn, ← hxn]; exact (col_iff l (D := D) x).mp hcx)
      refine Classical.byContradiction fun hne => hR.no_beta hx hy hne (fun z hz => ?_)
        ⟨fun _ => hcy, fun _ => hcx⟩
      constructor
      · rintro ⟨hxz, hzx⟩
        have hz2 := hR.rung_add_two_le hnd hl hx hz hxz (Ne.symm hzx)
        refine ⟨hR.le_of_rung hnd hl hy hcy (by rw [hyn]; exact below_inj) hz
          (by omega), fun e => ?_⟩
        rw [e] at hz2
        omega
      · rintro ⟨hyz, hzy⟩
        have hz2 := hR.rung_add_two_le hnd hl hy hz hyz (Ne.symm hzy)
        refine ⟨hR.le_of_rung hnd hl hx hcx (by rw [hxn]; exact below_inj) hz
          (by omega), fun e => ?_⟩
        rw [e] at hz2
        omega
    · have hcy : ¬ col y := fun hcy => by
        have h2 := (col_iff l (D := D) y).mp hcy
        rw [rung_of_not_col l hcx] at hxn
        omega
      exact hR.eq_of_not_col hl hx hy hcx hcy

/-- **The order, read on rungs.** -/
theorem le_iff (hR : ReducedSide D col) (hnd : l.Nodup) (hl : ∀ x, x ∈ l) {x y : M}
    (hx : D x) (hy : D y) :
    x ≼ y ↔ rung l D col y = rung l D col x ∨ rung l D col y + 2 ≤ rung l D col x := by
  constructor
  · intro hxy
    by_cases hne : x = y
    · exact Or.inl (by rw [hne])
    · exact Or.inr (hR.rung_add_two_le hnd hl hx hy hxy hne)
  · rintro (e | h)
    · rw [hR.rung_inj hnd hl x y hx hy e.symm]
      exact Frame.le_refl y
    · have hcx : col x := (col_iff l (D := D) x).mpr
        (by have := one_le_rung l (D := D) (col := col) y; omega)
      exact hR.le_of_rung hnd hl hx hcx
        (fun y₁ y₂ h₁ h₂ _ e => hR.rung_inj hnd hl y₂ y₁ h₂ h₁ e) hy h

/-- **Every rung at least two below a point's is taken**: an empty one would
leave too few rungs for the points strictly above it. -/
theorem exists_rung (hR : ReducedSide D col) (hnd : l.Nodup) (hl : ∀ x, x ∈ l) {x : M}
    (hx : D x) {j : Nat} (hj : 1 ≤ j) (hjx : j + 2 ≤ rung l D col x) :
    ∃ y, D y ∧ rung l D col y = j := by
  refine Classical.byContradiction fun hno => ?_
  have hcx : col x := (col_iff l (D := D) x).mpr (by omega)
  have hle := count_below_le hnd (m := rung l D col x)
    (fun y₁ y₂ h₁ h₂ _ e => hR.rung_inj hnd hl y₂ y₁ h₂ h₁ e)
    ((List.range' 1 (rung l D col x - 2)).erase j) fun z hz hzx => by
      refine (List.mem_erase_of_ne fun e => hno ⟨z, hz, e⟩).mpr ?_
      exact List.mem_range'_1.mpr ⟨one_le_rung l z, by omega⟩
  rw [List.length_erase_of_mem (List.mem_range'_1.mpr ⟨hj, by omega⟩), List.length_range'] at hle
  have hge : l.countP (strict D x) ≤ l.countP (below l D col (rung l D col x)) :=
    List.countP_mono_left (hR.height_le_below hnd hl hx)
  have hh : rung l D col x = l.countP (strict D x) + 2 := rung_of_col l hcx
  omega

/-- **A reduced side is a side of the ladder**: its points are the rungs of a
side, one to one, with the order and the colour read off the rungs. -/
theorem ladder [Nonempty M] (hR : ReducedSide D col) (hnd : l.Nodup) (hl : ∀ x, x ∈ l) :
    ∃ (σ : Side) (ψ : Nat → M), (∀ i, σ.mem i = true → D (ψ i)) ∧
      (∀ x, D x → ∃ i, σ.mem i = true ∧ ψ i = x) ∧
      (∀ i j, σ.mem i = true → σ.mem j = true → (ψ i ≼ ψ j ↔ j = i ∨ j + 2 ≤ i)) ∧
      (∀ i, σ.mem i = true → (col (ψ i) ↔ 2 ≤ i)) := by
  -- the rungs taken form a side
  obtain ⟨σ, hσ⟩ : ∃ σ : Side, ∀ i, σ.mem i = true ↔ ∃ x, D x ∧ rung l D col x = i := by
    by_cases hex : ∃ x, D x
    · obtain ⟨t, htD, htmax⟩ := ListCount.exists_max hl D (rung l D col) hex
      exact Side.exists_of_gaps ⟨t, htD, rfl⟩
        (fun i ⟨x, hx, e⟩ => e ▸ ⟨one_le_rung l x, htmax x hx⟩)
        (fun j hj hjt => hR.exists_rung hnd hl htD hj hjt)
    · exact ⟨.I 0, fun i => ⟨fun h => by simp [Side.mem] at h; omega,
        fun ⟨x, hx, _⟩ => absurd ⟨x, hx⟩ hex⟩⟩
  -- each rung taken, read back as its point
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Nat → M, ∀ i, σ.mem i = true → D (ψ i) ∧ rung l D col (ψ i) = i :=
    ⟨fun i => Classical.epsilon fun x => D x ∧ rung l D col x = i,
      fun i h => Classical.epsilon_spec ((hσ i).mp h)⟩
  refine ⟨σ, ψ, fun i h => (hψ i h).1, fun x hx => ?_, fun i j hi hj => ?_, fun i hi => ?_⟩
  · have hi := (hσ _).mpr ⟨x, hx, rfl⟩
    exact ⟨_, hi, hR.rung_inj hnd hl _ _ (hψ _ hi).1 hx (hψ _ hi).2⟩
  · rw [hR.le_iff hnd hl (hψ i hi).1 (hψ j hj).1, (hψ i hi).2, (hψ j hj).2]
  · rw [col_iff l (D := D) (col := col) (ψ i), (hψ i hi).2]

end ReducedSide
