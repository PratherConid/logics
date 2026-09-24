import Logics.IntermediateAxioms.Refuter.KPMinimal
import Logics.Birkhoff

/-!
# The minimal refuters of Kreisel and Putnam's axiom are infinitely many

`kpMin_infinite`: for every `n` the ladder frame `LPt n` is in `𝓜`, and no two
ladder frames lie below each other both ways.  So `𝓜` has infinitely many
members, no two of them equivalent in the Jankov order.

## The frames

`LPt n` has a root; two maximal points `A` and `B`; `u` and `v`, each covered by
`B` alone; a point `c0` covered by `A` and `B`; and a Rieger--Nishimura ladder
`w 0, …, w n` on the side of `u`.  Every rung sees `u`, `A` and `B` but not `v`;
rung `i` sees rung `j` exactly when `j + 2 ≤ i`; and every rung but the bottom
one sees `c0`.  There are `n + 7` points (`length_all`).

The axiom fails at the root, where the points not seeing `A` form the region
`{u, v, B}`, entered at `u` and at `v` (`inKPList`).  Everywhere else it holds
(`kp_mem_ne_root`): only four sets arise as a negation (`neg_cases`), and away
from the root each of them is entered at one point.

## Why nothing smaller lies below

Minimality is proved on the algebra directly.

* **A homomorphic image that merges anything validates the axiom.**  The
  axiom's value always contains every point but the root, which is the
  algebra's coatom; an image identifying two elements sends the coatom to the
  top, and with it every value of the axiom (`valid_of_collapse`).
* **So what lies below is a subalgebra, and a subalgebra refuting the axiom is
  the whole algebra** (`surjective_of_refutes`).  The failure has to be at the
  root, where the failing negation is `{u, v, B}` and the two disjuncts split
  it; meeting each disjunct with it puts the sets above `u` and above `v` in the
  subalgebra (`img_uv_of_fail`).  From those two, every point's set follows in
  turn (`img_up_all`): `B` lies above both entrances, `A` is what is not below
  `B`, `c0` is what is below neither entrance, the bottom rung is what is below
  neither `c0` nor `v`, and each higher rung is what is below neither the rung
  beneath it nor `v` (`wsucc_le_iff`).  This last step is where the ladder's
  shape is used.  Every upward closed set is a join of the sets points
  generate, so the subalgebra is everything.

Two ladders of different lengths are told apart by counting points
(`le_of_sh`).
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

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

theorem antisymm (x y : LPt n) (h₁ : x ≼ y) (h₂ : y ≼ x) : x = y := by
  cases x <;> cases y <;> simp_all [Frame.le, le] <;> (try apply Fin.ext) <;> omega

/-! ### Facts about the order -/

theorem root_le (x : LPt n) : LPt.root ≼ x := trivial

theorem eq_root_of_le_root {x : LPt n} (h : x ≼ .root) : x = .root := by
  cases x <;> simp_all [Frame.le, le]

theorem le_A_or_B (x : LPt n) : x ≼ .A ∨ x ≼ .B := by
  cases x <;> simp [Frame.le, le]

theorem le_B {x : LPt n} (hx : x ≠ .A) : x ≼ .B := by
  cases x <;> simp_all [Frame.le, le]

theorem eq_A_of_A_le {y : LPt n} (h : LPt.A ≼ y) : y = .A := h

theorem not_le_A_iff (x : LPt n) : ¬ x ≼ .A ↔ x = .u ∨ x = .v ∨ x = .B := by
  cases x <;> simp [Frame.le, le]

theorem eq_root_of_le_uv {x : LPt n} (hu : x ≼ .u) (hv : x ≼ .v) : x = .root := by
  cases x <;> simp_all [Frame.le, le]

theorem u_le_iff (y : LPt n) : LPt.u ≼ y ↔ y = .u ∨ y = .B := Iff.rfl
theorem v_le_iff (y : LPt n) : LPt.v ≼ y ↔ y = .v ∨ y = .B := Iff.rfl

theorem A_le_iff (y : LPt n) : LPt.A ≼ y ↔ ¬ y ≼ .B := by
  cases y <;> simp [Frame.le, le]

theorem B_le_iff (y : LPt n) : LPt.B ≼ y ↔ LPt.u ≼ y ∧ LPt.v ≼ y := by
  cases y <;> simp [Frame.le, le]

theorem c0_le_iff (y : LPt n) : LPt.c0 ≼ y ↔ ¬ y ≼ .u ∧ ¬ y ≼ .v := by
  cases y <;> simp [Frame.le, le]

theorem w0_le_iff (y : LPt n) : LPt.w 0 ≼ y ↔ ¬ y ≼ .c0 ∧ ¬ y ≼ .v := by
  cases y <;> simp [Frame.le, le] <;> omega

theorem wsucc_le_iff {k : Nat} (hk : k + 1 ≤ n) (y : LPt n) :
    LPt.w ⟨k + 1, by omega⟩ ≼ y ↔ ¬ y ≼ .w ⟨k, by omega⟩ ∧ ¬ y ≼ .v := by
  cases y <;> simp [Frame.le, le] <;> omega

theorem above_B {y : LPt n} (h : LPt.B ≼ y) : y = .B := h

theorem above_u {y : LPt n} (h : LPt.u ≼ y) (hne : y ≠ .u) : y = .B := by
  rcases h with h | h
  · exact absurd h hne
  · exact h

theorem above_v {y : LPt n} (h : LPt.v ≼ y) (hne : y ≠ .v) : y = .B := by
  rcases h with h | h
  · exact absurd h hne
  · exact h

theorem above_c0 {y : LPt n} (h : LPt.c0 ≼ y) (hne : y ≠ .c0) : y = .A ∨ y = .B := by
  rcases h with h | h | h
  · exact absurd h hne
  · exact Or.inl h
  · exact Or.inr h

theorem above_w {k : Fin (n + 1)} {y : LPt n} (h : LPt.w k ≼ y) (hne : y ≠ .w k) :
    y = .u ∨ y = .A ∨ y = .B ∨ y = .c0 ∨ ∃ j : Fin (n + 1), y = .w j ∧ j.val + 2 ≤ k.val := by
  cases y with
  | w j =>
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨j, rfl, ?_⟩)))
    have hjk : j ≠ k := fun hjk => hne (by rw [hjk])
    have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    simp only [Frame.le, le] at h
    omega
  | _ => simp_all [Frame.le, le]

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

/-! ### The four possible negations -/

/-- **Only four sets arise as a negation**: nothing, `{A}`, `{u, v, B}` or
everything, according to which of the two maximal points the set reaches. -/
theorem neg_cases (a : Upset (LPt n)) :
    (∀ x, ¬ (neg a).mem x) ∨ (∀ x, (neg a).mem x ↔ x = .A) ∨
      (∀ x, (neg a).mem x ↔ (x = .u ∨ x = .v ∨ x = .B)) ∨ (∀ x, (neg a).mem x) := by
  by_cases hA : a.mem .A
  · by_cases hB : a.mem .B
    · refine Or.inl fun x hx => ?_
      rcases le_A_or_B x with h | h
      · exact hx _ h hA
      · exact hx _ h hB
    · refine Or.inr (Or.inr (Or.inl fun x => ?_))
      rw [← not_le_A_iff]
      refine ⟨fun h hxA => h _ hxA hA, fun hxA y hxy hay => ?_⟩
      by_cases hyA : y = .A
      · rw [hyA] at hxy; exact hxA hxy
      · exact hB (a.upward (le_B hyA) hay)
  · by_cases hB : a.mem .B
    · refine Or.inr (Or.inl fun x => ⟨fun h => ?_, fun hx => ?_⟩)
      · exact Classical.byContradiction fun hxA => h _ (le_B hxA) hB
      · rw [hx]
        intro y hAy hay
        rw [eq_A_of_A_le hAy] at hay
        exact hA hay
    · refine Or.inr (Or.inr (Or.inr fun x y _ hay => ?_))
      rcases le_A_or_B y with h | h
      · exact hA (a.upward h hay)
      · exact hB (a.upward h hay)

/-! ### The axiom holds away from the root -/

/-- Pointwise form of `kp_top_of_principal`: if every region above `x` has one
entrance, the axiom holds at `x`. -/
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

/-- Away from the root every region has one entrance: a point other than the
root sees at most one of `u` and `v`. -/
theorem principal_of_ne_root {r : LPt n} (hr : r ≠ .root) (a : Upset (LPt n)) :
    (kpRegion r a).Principal := by
  intro p hp
  rcases neg_cases a with h | h | h | h
  · exact absurd hp.2 (h p)
  · have hpA := (h p).mp hp.2
    rw [hpA] at hp
    exact ⟨.A, hp, fun q hq => by rw [(h q).mp hq.2]; exact Frame.le_refl _⟩
  · by_cases hru : r ≼ .u
    · refine ⟨.u, ⟨hru, (h _).mpr (Or.inl rfl)⟩, fun q hq => ?_⟩
      rcases (h q).mp hq.2 with hq' | hq' | hq'
      · rw [hq']; exact Frame.le_refl _
      · rw [hq'] at hq; exact absurd (eq_root_of_le_uv hru hq.1) hr
      · rw [hq']; exact Or.inr rfl
    by_cases hrv : r ≼ .v
    · refine ⟨.v, ⟨hrv, (h _).mpr (Or.inr (Or.inl rfl))⟩, fun q hq => ?_⟩
      rcases (h q).mp hq.2 with hq' | hq' | hq'
      · rw [hq'] at hq; exact absurd (eq_root_of_le_uv hq.1 hrv) hr
      · rw [hq']; exact Frame.le_refl _
      · rw [hq']; exact Or.inr rfl
    · have onlyB : ∀ q, (kpRegion r a).mem q → q = .B := by
        intro q hq
        rcases (h q).mp hq.2 with hq' | hq' | hq'
        · rw [hq'] at hq; exact absurd hq.1 hru
        · rw [hq'] at hq; exact absurd hq.1 hrv
        · exact hq'
      have hpB := onlyB p hp
      rw [hpB] at hp
      exact ⟨.B, hp, fun q hq => by rw [onlyB q hq]; exact Frame.le_refl _⟩
  · exact ⟨r, ⟨Frame.le_refl _, h r⟩, fun _ hq => hq.1⟩

/-- **The axiom holds at every point but the root.** -/
theorem kp_mem_ne_root {x : LPt n} (hx : x ≠ .root) (a b c : Upset (LPt n)) :
    (kpAt a b c).mem x :=
  kp_mem_of_principal (fun _ hxr => principal_of_ne_root
    (fun hr => hx (eq_root_of_le_root (hr ▸ hxr))) a) b c

/-! ### A frame of the list -/

theorem region_A_iff (q : LPt n) :
    (kpRegion .root (Upset.up (.A : LPt n))).mem q ↔ ¬ q ≼ .A :=
  ⟨fun h hqA => h.2 .A hqA (Frame.le_refl _),
   fun hqA => ⟨root_le q, fun _ hqy hAy => hqA (eq_A_of_A_le hAy ▸ hqy)⟩⟩

theorem minimal_u : (kpRegion .root (Upset.up (.A : LPt n))).Minimal .u := by
  refine ⟨(region_A_iff _).mpr (by simp [Frame.le, le]), fun q hq hqu => ?_⟩
  have := (region_A_iff q).mp hq
  cases q <;> simp_all [Frame.le, le]

theorem minimal_v : (kpRegion .root (Upset.up (.A : LPt n))).Minimal .v := by
  refine ⟨(region_A_iff _).mpr (by simp [Frame.le, le]), fun q hq hqv => ?_⟩
  have := (region_A_iff q).mp hq
  cases q <;> simp_all [Frame.le, le]

/-- **The ladder frame is in `𝓛`**: finite, rooted, and split at the root by
`u` and `v`. -/
theorem inKPList : InKPList (LPt n) :=
  ⟨⟨all n, mem_all⟩, ⟨.root, root_le⟩,
    ⟨.root, Upset.up .A, .u, .v, minimal_u, minimal_v,
      by simp [Frame.le, le], by simp [Frame.le, le]⟩⟩

end LPt

namespace LPt

variable {n : Nat}

/-! ### Step A: a homomorphic image that merges anything validates the axiom -/

/-- Everything but the root: the largest upward closed set short of the top. -/
def coatom : Upset (LPt n) :=
  ⟨fun x => x ≠ .root, fun {x y} hxy hx hy => hx (eq_root_of_le_root (by rw [hy] at hxy; exact hxy))⟩

theorem le_coatom (U : Upset (LPt n)) (hU : U ≠ ⊤) : U ⊑ coatom := by
  intro x hx hxr
  apply hU
  refine Upset.ext fun y => ⟨fun _ => trivial, fun _ => U.upward ?_ hx⟩
  rw [hxr]
  exact root_le y

theorem coatom_le_kp (v : Nat → Upset (LPt n)) : coatom ⊑ kreiselPutnamForm.eval v :=
  fun _ hx => kp_mem_ne_root hx (v 0) (v 1) (v 2)

/-! ### Step B: a subalgebra refuting the axiom is everything -/

section Generate

variable {γ : Type} [HeytingAlgebra γ] (e : Hom γ (Upset (LPt n)))

/-- In the image of `e`. -/
def InImg (U : Upset (LPt n)) : Prop := ∃ a, e.toFun a = U

variable {e}

theorem img_inf {U V : Upset (LPt n)} : InImg e U → InImg e V → InImg e (U ⊓ V)
  | ⟨a, ha⟩, ⟨b, hb⟩ => ⟨a ⊓ b, by rw [e.map_inf, ha, hb]⟩

theorem img_sup {U V : Upset (LPt n)} : InImg e U → InImg e V → InImg e (U ⊔ V)
  | ⟨a, ha⟩, ⟨b, hb⟩ => ⟨a ⊔ b, by rw [e.map_sup, ha, hb]⟩

theorem img_himp {U V : Upset (LPt n)} : InImg e U → InImg e V → InImg e (U ⇨ V)
  | ⟨a, ha⟩, ⟨b, hb⟩ => ⟨a ⇨ b, by rw [e.map_himp, ha, hb]⟩

theorem img_bot : InImg e (⊥ : Upset (LPt n)) := ⟨⊥, e.map_bot⟩

theorem img_top : InImg e (⊤ : Upset (LPt n)) := ⟨⊤, e.map_top⟩

theorem img_neg {U : Upset (LPt n)} (h : InImg e U) : InImg e (neg U) := img_himp h img_bot

theorem img_supList : ∀ {L : List (Upset (LPt n))}, (∀ U ∈ L, InImg e U) →
    InImg e (Birkhoff.supList L)
  | [], _ => img_bot
  | U :: _, h => img_sup (h U (List.mem_cons.mpr (Or.inl rfl)))
      (img_supList fun V hV => h V (List.mem_cons_of_mem U hV))

end Generate

theorem mem_supList : ∀ {L : List (Upset (LPt n))} {z : LPt n},
    (Birkhoff.supList L).mem z ↔ ∃ U ∈ L, U.mem z
  | [], _ => ⟨fun h => h.elim, fun ⟨_, hU, _⟩ => by cases hU⟩
  | U :: t, z => by
    show U.mem z ∨ (Birkhoff.supList t).mem z ↔ _
    rw [mem_supList]
    constructor
    · rintro (h | ⟨V, hV, hz⟩)
      · exact ⟨U, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact ⟨V, List.mem_cons_of_mem U hV, hz⟩
    · rintro ⟨V, hV, hz⟩
      rcases List.mem_cons.mp hV with rfl | hV
      · exact Or.inl hz
      · exact Or.inr ⟨V, hV, hz⟩

/-- The points strictly above `x`, as the join of the sets they generate. -/
noncomputable def strictUp (x : LPt n) : Upset (LPt n) :=
  Birkhoff.supList (((all n).filter fun y => truth (x ≼ y ∧ y ≠ x)).map Upset.up)

theorem mem_strictUp (x z : LPt n) : (strictUp x).mem z ↔ x ≼ z ∧ z ≠ x := by
  rw [strictUp, mem_supList]
  constructor
  · rintro ⟨U, hU, hz⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hU
    obtain ⟨hxy, hyx⟩ := truth_eq_true.mp (List.mem_filter.mp hy).2
    exact ⟨Frame.le_trans hxy hz, fun hzx => hyx (antisymm _ _ (hzx ▸ hz) hxy)⟩
  · rintro ⟨hxz, hzx⟩
    exact ⟨Upset.up z, List.mem_map.mpr ⟨z, List.mem_filter.mpr
      ⟨mem_all z, truth_eq_true.mpr ⟨hxz, hzx⟩⟩, rfl⟩, Frame.le_refl z⟩

/-- The points not below `x`. -/
theorem mem_notBelow (x y : LPt n) : (Upset.up x ⇨ strictUp x).mem y ↔ ¬ y ≼ x := by
  constructor
  · intro h hyx
    exact ((mem_strictUp x x).mp (h x hyx (Frame.le_refl x))).2 rfl
  · intro hyx z hyz hxz
    exact (mem_strictUp x z).mpr ⟨hxz, fun hzx => hyx (hzx ▸ hyz)⟩

section Generate

variable {γ : Type} [HeytingAlgebra γ] {e : Hom γ (Upset (LPt n))}

theorem img_strictUp {x : LPt n} (h : ∀ y, x ≼ y → y ≠ x → InImg e (Upset.up y)) :
    InImg e (strictUp x) :=
  img_supList fun U hU => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hU
    obtain ⟨hxy, hyx⟩ := truth_eq_true.mp (List.mem_filter.mp hy).2
    exact h y hxy hyx

theorem img_notBelow {x : LPt n} (hx : InImg e (Upset.up x))
    (h : ∀ y, x ≼ y → y ≠ x → InImg e (Upset.up y)) :
    InImg e (Upset.up x ⇨ strictUp x) :=
  img_himp hx (img_strictUp h)

/-- **Every point is generated from `u` and `v`.**  `B` lies above both; `A` is
what is not below `B`; `c0` is what is below neither `u` nor `v`; the bottom rung
is what is below neither `c0` nor `v`; and each higher rung is what is below
neither the rung beneath it nor `v`. -/
theorem img_up_all (hu : InImg e (Upset.up (.u : LPt n)))
    (hv : InImg e (Upset.up (.v : LPt n))) (x : LPt n) : InImg e (Upset.up x) := by
  have hB : InImg e (Upset.up (.B : LPt n)) := by
    rw [show Upset.up (.B : LPt n) = Upset.up .u ⊓ Upset.up .v from
      Upset.ext fun y => B_le_iff y]
    exact img_inf hu hv
  have hA : InImg e (Upset.up (.A : LPt n)) := by
    rw [show Upset.up (.A : LPt n) = Upset.up .B ⇨ strictUp .B from
      Upset.ext fun y => (A_le_iff y).trans (mem_notBelow _ y).symm]
    exact img_notBelow hB fun y hBy hne => absurd (above_B hBy) hne
  have aboveU : ∀ y, LPt.u ≼ y → y ≠ .u → InImg e (Upset.up y) :=
    fun y h hne => by rw [above_u h hne]; exact hB
  have aboveV : ∀ y, LPt.v ≼ y → y ≠ .v → InImg e (Upset.up y) :=
    fun y h hne => by rw [above_v h hne]; exact hB
  have hc0 : InImg e (Upset.up (.c0 : LPt n)) := by
    rw [show Upset.up (.c0 : LPt n) =
        (Upset.up .u ⇨ strictUp .u) ⊓ (Upset.up .v ⇨ strictUp .v) from
      Upset.ext fun y => (c0_le_iff y).trans
        (and_congr (mem_notBelow _ y).symm (mem_notBelow _ y).symm)]
    exact img_inf (img_notBelow hu aboveU) (img_notBelow hv aboveV)
  have hnotV := img_notBelow hv aboveV
  have hw : ∀ m, ∀ j : Fin (n + 1), j.val < m → InImg e (Upset.up (.w j)) := by
    intro m
    induction m with
    | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ m ih =>
      intro j hj
      by_cases hjm : j.val < m
      · exact ih j hjm
      have hjv : j.val = m := by omega
      have aboveW : ∀ i : Fin (n + 1), i.val < m →
          ∀ y, LPt.w i ≼ y → y ≠ .w i → InImg e (Upset.up y) := by
        intro i hi y hiy hne
        rcases above_w hiy hne with h | h | h | h | ⟨i', rfl, hi'⟩
        · rw [h]; exact hu
        · rw [h]; exact hA
        · rw [h]; exact hB
        · rw [h]; exact hc0
        · exact ih i' (by omega)
      cases m with
      | zero =>
        have hj0 : j = 0 := Fin.ext hjv
        rw [hj0, show Upset.up (.w 0 : LPt n) =
            (Upset.up .c0 ⇨ strictUp .c0) ⊓ (Upset.up .v ⇨ strictUp .v) from
          Upset.ext fun y => (w0_le_iff y).trans
            (and_congr (mem_notBelow _ y).symm (mem_notBelow _ y).symm)]
        refine img_inf (img_notBelow hc0 fun y h hne => ?_) hnotV
        rcases above_c0 h hne with h' | h'
        · rw [h']; exact hA
        · rw [h']; exact hB
      | succ k =>
        have hkn : k + 1 ≤ n := by have := j.isLt; omega
        have hjk : j = ⟨k + 1, by omega⟩ := Fin.ext hjv
        rw [hjk, show Upset.up (.w ⟨k + 1, by omega⟩ : LPt n) =
            (Upset.up (.w ⟨k, by omega⟩) ⇨ strictUp (.w ⟨k, by omega⟩)) ⊓
              (Upset.up .v ⇨ strictUp .v) from
          Upset.ext fun y => (wsucc_le_iff hkn y).trans
            (and_congr (mem_notBelow _ y).symm (mem_notBelow _ y).symm)]
        exact img_inf (img_notBelow (ih ⟨k, by omega⟩ (Nat.lt_succ_self k))
          (aboveW ⟨k, by omega⟩ (Nat.lt_succ_self k))) hnotV
  cases x with
  | root =>
    rw [show Upset.up (.root : LPt n) = ⊤ from
      Upset.ext fun y => ⟨fun _ => trivial, fun _ => root_le y⟩]
    exact img_top
  | A => exact hA
  | B => exact hB
  | u => exact hu
  | v => exact hv
  | c0 => exact hc0
  | w j => exact hw (j.val + 1) j (Nat.lt_succ_self _)

/-- **A failure at the root puts `u` and `v` in the image.**  The failing
negation must be `{u, v, B}`, the two disjuncts split it, and meeting each
disjunct with it gives the set above one entrance. -/
theorem img_uv_of_fail {a b c : Upset (LPt n)} (ha : InImg e a) (hb : InImg e b)
    (hc : InImg e c) (h : ¬ (kpAt a b c).mem .root) :
    InImg e (Upset.up (.u : LPt n)) ∧ InImg e (Upset.up (.v : LPt n)) := by
  have H : (neg a ⇨ (b ⊔ c)).mem (.root : LPt n) ∧ ¬ (neg a ⇨ b).mem (.root : LPt n) ∧
      ¬ (neg a ⇨ c).mem (.root : LPt n) := by
    have hex : ∃ r : LPt n, (neg a ⇨ (b ⊔ c)).mem r ∧
        ¬ ((neg a ⇨ b) ⊔ (neg a ⇨ c)).mem r :=
      Classical.byContradiction fun hc' => h fun r _ hr =>
        Classical.byContradiction fun hr' => hc' ⟨r, hr, hr'⟩
    obtain ⟨r, hr1, hr2⟩ := hex
    by_cases hr : r = .root
    · rw [hr] at hr1 hr2
      exact ⟨hr1, fun h' => hr2 (Or.inl h'), fun h' => hr2 (Or.inr h')⟩
    · exact absurd (kp_mem_ne_root hr a b c r (Frame.le_refl r) hr1) hr2
  obtain ⟨H1, H2, H3⟩ := H
  rcases neg_cases a with hN | hN | hN | hN
  · exact absurd (fun s _ hs => absurd hs (hN s)) H2
  · rcases H1 .A (root_le _) ((hN _).mpr rfl) with hbA | hcA
    · exact absurd (fun s _ hs => by rw [(hN s).mp hs]; exact hbA) H2
    · exact absurd (fun s _ hs => by rw [(hN s).mp hs]; exact hcA) H3
  · have hcover : ∀ X : Upset (LPt n), X.mem .u → X.mem .v → (neg a ⇨ X).mem .root :=
      fun X hu hv s _ hs => by
        rcases (hN s).mp hs with hs' | hs' | hs'
        · rw [hs']; exact hu
        · rw [hs']; exact hv
        · rw [hs']; exact X.upward (Or.inr rfl : (LPt.u : LPt n) ≼ .B) hu
    have hb2 : ¬ (b.mem .u ∧ b.mem .v) := fun h' => H2 (hcover b h'.1 h'.2)
    have hc2 : ¬ (c.mem .u ∧ c.mem .v) := fun h' => H3 (hcover c h'.1 h'.2)
    have H1u : b.mem .u ∨ c.mem .u := H1 .u (root_le _) ((hN _).mpr (Or.inl rfl))
    have H1v : b.mem .v ∨ c.mem .v := H1 .v (root_le _) ((hN _).mpr (Or.inr (Or.inl rfl)))
    have hNi : InImg e (neg a) := img_neg ha
    have upU : ∀ X : Upset (LPt n), X.mem .u → ¬ X.mem .v → X ⊓ neg a = Upset.up .u :=
      fun X hu hv => Upset.ext fun y => ⟨fun ⟨hX, hn⟩ => by
          rcases (hN y).mp hn with hy | hy | hy
          · rw [hy]; exact Frame.le_refl _
          · rw [hy] at hX; exact absurd hX hv
          · rw [hy]; exact Or.inr rfl,
        fun huy => ⟨X.upward huy hu, (hN y).mpr (by
          rcases huy with hy | hy
          · exact Or.inl hy
          · exact Or.inr (Or.inr hy))⟩⟩
    have upV : ∀ X : Upset (LPt n), X.mem .v → ¬ X.mem .u → X ⊓ neg a = Upset.up .v :=
      fun X hv hu => Upset.ext fun y => ⟨fun ⟨hX, hn⟩ => by
          rcases (hN y).mp hn with hy | hy | hy
          · rw [hy] at hX; exact absurd hX hu
          · rw [hy]; exact Frame.le_refl _
          · rw [hy]; exact Or.inr rfl,
        fun hvy => ⟨X.upward hvy hv, (hN y).mpr (by
          rcases hvy with hy | hy
          · exact Or.inr (Or.inl hy)
          · exact Or.inr (Or.inr hy))⟩⟩
    constructor
    · by_cases hbv : b.mem .v
      · have hcu : c.mem .u := H1u.resolve_left fun hbu => hb2 ⟨hbu, hbv⟩
        rw [← upU c hcu fun hcv => hc2 ⟨hcu, hcv⟩]
        exact img_inf hc hNi
      · have hcv : c.mem .v := H1v.resolve_left hbv
        have hbu : b.mem .u := H1u.resolve_right fun hcu => hc2 ⟨hcu, hcv⟩
        rw [← upU b hbu hbv]
        exact img_inf hb hNi
    · by_cases hbu : b.mem .u
      · have hcv : c.mem .v := H1v.resolve_left fun hbv => hb2 ⟨hbu, hbv⟩
        rw [← upV c hcv fun hcu => hc2 ⟨hcu, hcv⟩]
        exact img_inf hc hNi
      · have hcu : c.mem .u := H1u.resolve_left hbu
        have hbv : b.mem .v := H1v.resolve_right fun hcv => hc2 ⟨hcu, hcv⟩
        rw [← upV b hbv hbu]
        exact img_inf hb hNi
  · rcases H1 .root (root_le _) (hN _) with hbr | hcr
    · exact absurd (fun s _ _ => b.upward (root_le s) hbr) H2
    · exact absurd (fun s _ _ => c.upward (root_le s) hcr) H3

/-- **An embedding of an algebra refuting the axiom is onto.** -/
theorem surjective_of_refutes (he : Function.Injective e.toFun)
    (hnv : ¬ ∀ v : Nat → γ, kreiselPutnamForm.eval v = ⊤) :
    Function.Surjective e.toFun := by
  have hex : ∃ a b c : γ, kpAt a b c ≠ ⊤ := Classical.byContradiction fun hc =>
    hnv (kreiselPutnamForm_valid_iff.mpr fun a b c =>
      Classical.byContradiction fun h => hc ⟨a, b, c, h⟩)
  obtain ⟨a, b, c, habc⟩ := hex
  have hroot : ¬ (kpAt (e.toFun a) (e.toFun b) (e.toFun c)).mem (.root : LPt n) := by
    intro h
    apply habc
    apply he
    rw [e.map_top, Hom.map_kpAt]
    exact Upset.ext fun x => ⟨fun _ => trivial, fun _ =>
      (kpAt (e.toFun a) (e.toFun b) (e.toFun c)).upward (root_le x) h⟩
  obtain ⟨hu, hv⟩ := img_uv_of_fail ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ hroot
  intro U
  have hU : U = Birkhoff.supList (((all n).filter fun x => truth (U.mem x)).map Upset.up) :=
    Upset.ext fun z => by
      rw [mem_supList]
      constructor
      · intro hz
        exact ⟨Upset.up z, List.mem_map.mpr ⟨z, List.mem_filter.mpr
          ⟨mem_all z, truth_eq_true.mpr hz⟩, rfl⟩, Frame.le_refl z⟩
      · rintro ⟨V, hV, hzV⟩
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hV
        exact U.upward hzV (truth_eq_true.mp (List.mem_filter.mp hx).2)
  rw [hU]
  exact img_supList fun V hV => by
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hV
    exact img_up_all hu hv x

end Generate

/-! ### The frames are minimal refuters -/

/-- **Nothing smaller below refutes the axiom.**  A homomorphic image that merges
anything validates the axiom, since the axiom's value always contains every
point but the root; and an embedding of an algebra refuting it is onto. -/
theorem refuterLB : RefuterLB (Upset (LPt n)) kreiselPutnamForm := by
  intro γ iγ hsh hnv
  obtain ⟨δ, iδ, ⟨f, hfs⟩, ⟨g, hgi⟩⟩ := hsh
  by_cases hinj : Function.Injective f.toFun
  · obtain ⟨k, hk⟩ := @embeds_of_iso γ (Upset (LPt n)) δ iγ _ iδ f hinj hfs g hgi
    exact @sh_of_bijective γ (Upset (LPt n)) iγ _ k
      ⟨hk, @surjective_of_refutes n γ iγ k hk hnv⟩
  · obtain ⟨a, b, hab, hne⟩ := exists_collapse f hinj
    exact absurd (@valid_of_embeds γ δ iγ iδ ⟨g, hgi⟩ _
      (valid_of_collapse f hfs hab hne le_coatom coatom_le_kp)) hnv

/-- **Every ladder frame is a minimal refuter.** -/
theorem inKPMin (n : Nat) : InKPMin (LPt n) := ⟨inKPList, antisymm, refuterLB⟩

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
