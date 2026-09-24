import Logics.Homomorphism

/-!
# Finite frames: counting points, and shrinking a frame

Two ways of turning a frame into a smaller one whose algebra sits below the
original in the Jankov order, and the count that makes "smaller" bite.

* **The points above a point** (`Above`) form a frame whose algebra is a
  homomorphic image: restricting upward closed sets is onto.
* **Merging points** (`Merger`) along a map that respects the order as a
  p-morphism must gives a frame whose algebra is a subalgebra: pulling upward
  closed sets back is one to one.  Collapsing a set onto one of its members
  (`Merger.collapse`) is the case that comes up, and an upward closed set can
  always be collapsed (`Merger.collapseUp`).
* **Counting** (`length_le_of_sh`).  A finite poset with `n` points has a chain
  of `n` strict steps down through its upward closed sets, removing one minimal
  point at a time, and a frame whose points a list of length `m` names has none
  longer than `m`.  Chains travel up the Jankov order, so the upward closed sets
  of a finite poset lie below those of a finite frame only if the poset has at
  most as many points.

Finiteness is a list naming every point.  Minimal points exist in a finite
frame, and so, turning the order round (`Op`), do maximal ones
(`hasMaximal_of_list`).
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

universe u

/-! ## Lists -/

namespace ListCount

/-- Dropping repeats from a list keeps its members. -/
theorem exists_nodup {α : Type u} :
    ∀ l : List α, ∃ l' : List α, l'.Nodup ∧ ∀ a, a ∈ l' ↔ a ∈ l
  | [] => ⟨[], List.nodup_nil, fun _ => Iff.rfl⟩
  | x :: t => by
    obtain ⟨t', hnd, hmem⟩ := exists_nodup t
    by_cases hx : x ∈ t'
    · refine ⟨t', hnd, fun a => ⟨fun h => List.mem_cons_of_mem x ((hmem a).mp h),
        fun h => ?_⟩⟩
      rcases List.mem_cons.mp h with rfl | ht
      · exact hx
      · exact (hmem a).mpr ht
    · refine ⟨x :: t', List.nodup_cons.mpr ⟨hx, hnd⟩, fun a => ?_⟩
      rw [List.mem_cons, List.mem_cons, hmem a]

/-- A predicate implying another, and failing at a member where the other
holds, counts strictly fewer. -/
theorem countP_lt {α : Type u} {p q : α → Bool} {l : List α}
    (hle : ∀ x ∈ l, p x = true → q x = true)
    (hex : ∃ x ∈ l, q x = true ∧ p x = false) :
    l.countP p < l.countP q := by
  induction l with
  | nil => obtain ⟨_, hx, _⟩ := hex; cases hx
  | cons a t ih =>
    have hle' : ∀ x ∈ t, p x = true → q x = true :=
      fun x hx => hle x (List.mem_cons_of_mem a hx)
    obtain ⟨x, hx, hqx, hpx⟩ := hex
    rw [List.countP_cons, List.countP_cons]
    rcases List.mem_cons.mp hx with rfl | hxt
    · have := List.countP_mono_left hle'
      rw [ite_eq_right (by simp [hpx]), ite_eq_left hqx]
      omega
    · have ih' := ih hle' ⟨x, hxt, hqx, hpx⟩
      have hpa : (if p a = true then 1 else 0) ≤ (if q a = true then 1 else 0) := by
        cases hp : p a <;> cases hq : q a <;> simp_all
      omega

/-- In a list without repeats, a predicate agreeing with another except at one
member, where only the other holds, counts exactly one fewer. -/
theorem countP_succ {α : Type u} {p q : α → Bool} {x : α} {l : List α}
    (hnd : l.Nodup) (hx : x ∈ l) (hpx : p x = true) (hqx : q x = false)
    (hsame : ∀ y ∈ l, y ≠ x → q y = p y) : l.countP q + 1 = l.countP p := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    rw [List.countP_cons, List.countP_cons]
    rcases List.mem_cons.mp hx with rfl | hxt
    · have : t.countP q = t.countP p :=
        List.countP_congr fun y hy => by
          rw [hsame y (List.mem_cons_of_mem _ hy) (fun h => hnd.1 (h ▸ hy))]
      rw [this, ite_eq_left hpx, ite_eq_right (by simp [hqx])]
    · have hax : a ≠ x := fun h => hnd.1 (h ▸ hxt)
      have ih' := ih hnd.2 hxt (fun y hy hyx => hsame y (List.mem_cons_of_mem _ hy) hyx)
      rw [hsame a (List.mem_cons.mpr (Or.inl rfl)) hax]
      omega

/-- Dropping a member leaves a shorter list. -/
theorem length_filterMap_lt {α β : Type u} (f : α → Option β) {l : List α}
    (h : ∃ x ∈ l, f x = none) : (l.filterMap f).length < l.length := by
  induction l with
  | nil => obtain ⟨_, hx, _⟩ := h; cases hx
  | cons a t ih =>
    obtain ⟨x, hx, hfx⟩ := h
    rcases List.mem_cons.mp hx with rfl | hxt
    · rw [List.filterMap_cons_none hfx, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filterMap_le f t)
    · cases hfa : f a with
      | none =>
        rw [List.filterMap_cons_none hfa, List.length_cons]
        exact Nat.lt_succ_of_lt (ih ⟨x, hxt, hfx⟩)
      | some b =>
        rw [List.filterMap_cons_some hfa, List.length_cons, List.length_cons]
        exact Nat.succ_lt_succ (ih ⟨x, hxt, hfx⟩)

end ListCount

/-! ## Chains -/

/-- A chain of `n` strict steps down. -/
def HasChain (α : Type u) [PartialOrder α] (n : Nat) : Prop :=
  ∃ c : Nat → α, ∀ i, i < n → c (i + 1) ⊑ c i ∧ c (i + 1) ≠ c i

/-- The meet of the first `k + 1` values of a sequence. -/
def meetUpTo {β : Type u} [Lattice β] (b : Nat → β) : Nat → β
  | 0 => b 0
  | k + 1 => meetUpTo b k ⊓ b (k + 1)

/-- A chain goes into any algebra the first embeds in. -/
theorem HasChain.of_embeds {α β : Type u} [HeytingAlgebra α] [HeytingAlgebra β]
    (h : Embeds α β) {n : Nat} (hc : HasChain α n) : HasChain β n := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨c, hc⟩ := hc
  exact ⟨fun i => f.toFun (c i), fun i hi =>
    ⟨f.mono (hc i hi).1, fun heq => (hc i hi).2 (hf heq)⟩⟩

/-- A chain in a homomorphic image lifts: take preimages and meet them in turn,
which keeps each image in place because the chain descends. -/
theorem HasChain.of_onto {α β : Type u} [HeytingAlgebra α] [HeytingAlgebra β]
    (h : Onto α β) {n : Nat} (hc : HasChain α n) : HasChain β n := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨c, hc⟩ := hc
  let b : Nat → β := fun i => Classical.choose (hf (c i))
  have hb : ∀ i, f.toFun (b i) = c i := fun i => Classical.choose_spec (hf (c i))
  have himg : ∀ k, k ≤ n → f.toFun (meetUpTo b k) = c k := by
    intro k
    induction k with
    | zero => intro _; exact hb 0
    | succ k ih =>
      intro hk
      show f.toFun (meetUpTo b k ⊓ b (k + 1)) = c (k + 1)
      rw [f.map_inf, ih (Nat.le_of_succ_le hk), hb, inf_comm]
      exact inf_eq_left_iff.mpr (hc k hk).1
  refine ⟨meetUpTo b, fun i hi => ⟨inf_le_left _ _, fun heq => (hc i hi).2 ?_⟩⟩
  rw [← himg (i + 1) hi, ← himg i (Nat.le_of_lt hi), heq]

/-- Chains travel up the Jankov order. -/
theorem HasChain.of_sh {α β : Type} [iα : HeytingAlgebra α] [iβ : HeytingAlgebra β]
    (h : SH α β) {n : Nat} (hc : HasChain α n) : HasChain β n := by
  obtain ⟨γ, iγ, hon, hem⟩ := h
  exact @HasChain.of_onto γ β iγ iβ hon n (@HasChain.of_embeds α γ iα iγ hem n hc)

/-! ## Counting points -/

/-- A proposition as a boolean, by excluded middle.  Going through one fixed
decision keeps counts from depending on how decidability was found. -/
noncomputable def truth (q : Prop) : Bool := @decide q (Classical.propDecidable q)

theorem truth_eq_true {q : Prop} : truth q = true ↔ q :=
  @decide_eq_true_iff q (Classical.propDecidable q)

theorem truth_eq_false {q : Prop} : truth q = false ↔ ¬ q :=
  @decide_eq_false_iff_not q (Classical.propDecidable q)

theorem truth_congr {q q' : Prop} (h : q ↔ q') : truth q = truth q' :=
  congrArg truth (propext h)

namespace Upset

variable {P : Type} [Frame P]

/-- How many entries of `l` lie in `U`. -/
noncomputable def count (l : List P) (U : Upset P) : Nat :=
  l.countP fun p => truth (U.mem p)

/-- A strictly larger upward closed set has strictly more points of any list
naming them all. -/
theorem count_lt {l : List P} (hl : ∀ p, p ∈ l) {U V : Upset P} (h : U ⊑ V)
    (hne : U ≠ V) : count l U < count l V := by
  have hex : ∃ p, V.mem p ∧ ¬ U.mem p := Classical.byContradiction fun hc =>
    hne (le_antisymm h fun p hv => Classical.byContradiction fun hu => hc ⟨p, hv, hu⟩)
  obtain ⟨p, hv, hu⟩ := hex
  exact ListCount.countP_lt
    (fun x _ hx => truth_eq_true.mpr (h x (truth_eq_true.mp hx)))
    ⟨p, hl p, truth_eq_true.mpr hv, truth_eq_false.mpr hu⟩

theorem count_le_length (l : List P) (U : Upset P) : count l U ≤ l.length :=
  List.countP_le_length

end Upset

/-- **No chain outlasts the points.**  Each strict step down loses a point, so a
frame whose points a list of length `m` names has no chain of more than `m`
steps. -/
theorem length_ge_of_hasChain {Q : Type} [Frame Q] {l : List Q} (hl : ∀ q, q ∈ l)
    {n : Nat} (h : HasChain (Upset Q) n) : n ≤ l.length := by
  obtain ⟨c, hc⟩ := h
  have key : ∀ i, i ≤ n → i + Upset.count l (c i) ≤ Upset.count l (c 0) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (Nat.le_of_succ_le hk)
      have h2 := Upset.count_lt hl (hc k hk).1 (hc k hk).2
      omega
  have := key n (Nat.le_refl n)
  have := Upset.count_le_length l (c 0)
  omega

/-- **A poset has a chain as long as its points.**  Starting from the whole
frame, remove one minimal point at a time; what is left stays upward closed
because nothing in it lay below the removed point, and each step loses exactly
one entry of a list without repeats. -/
theorem hasChain_of_nodup {M : Type} [Frame M]
    (antisymm : ∀ p q : M, p ≼ q → q ≼ p → p = q)
    {l : List M} (hnd : l.Nodup) (hl : ∀ p, p ∈ l) : HasChain (Upset M) l.length := by
  suffices H : ∀ k, k ≤ l.length → ∃ c : Nat → Upset M,
      (∀ i, i < k → c (i + 1) ⊑ c i ∧ c (i + 1) ≠ c i) ∧
        Upset.count l (c k) + k = l.length by
    obtain ⟨c, hc, _⟩ := H l.length (Nat.le_refl _)
    exact ⟨c, hc⟩
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun _ => ⊤, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    rw [Nat.add_zero]
    unfold Upset.count
    rw [List.countP_eq_length]
    intro _ _
    exact truth_eq_true.mpr True.intro
  | succ k ih =>
    intro hk
    obtain ⟨c, hc, hcount⟩ := ih (Nat.le_of_succ_le hk)
    have hpos : 0 < Upset.count l (c k) := by omega
    obtain ⟨p, _, hpc⟩ := List.countP_pos_iff.mp hpos
    obtain ⟨x, hx, hxmin⟩ :=
      hasMinimal_of_list l hl (c k).mem ⟨p, truth_eq_true.mp hpc⟩
    let W : Upset M := ⟨fun y => (c k).mem y ∧ y ≠ x, fun {y z} hyz hy =>
      ⟨(c k).upward hyz hy.1, fun hzx => hy.2
        (antisymm y x (hzx ▸ hyz) (hxmin y hy.1 (hzx ▸ hyz)))⟩⟩
    have hWle : W ⊑ c k := fun _ hy => hy.1
    have hWne : W ≠ c k := fun heq => by
      have : W.mem x := heq ▸ hx
      exact this.2 rfl
    refine ⟨fun i => if i ≤ k then c i else W, fun i hi => ?_, ?_⟩
    · dsimp only
      by_cases hik : i < k
      · rw [ite_eq_left (Nat.succ_le_of_lt hik), ite_eq_left (Nat.le_of_lt hik)]
        exact hc i hik
      · have hik' : i = k := by omega
        subst hik'
        rw [ite_eq_right (Nat.not_succ_le_self i), ite_eq_left (Nat.le_refl i)]
        exact ⟨hWle, hWne⟩
    · dsimp only
      rw [ite_eq_right (Nat.not_succ_le_self k)]
      have hstep : Upset.count l W + 1 = Upset.count l (c k) :=
        ListCount.countP_succ hnd (hl x) (truth_eq_true.mpr hx)
          (truth_eq_false.mpr fun hw => hw.2 rfl)
          (fun y _ hyx => truth_congr ⟨fun h => h.1, fun h => ⟨h, hyx⟩⟩)
      omega

/-- **Counting through the Jankov order.**  If the upward closed sets of a
finite poset lie below those of a finite frame, the poset has at most as many
points: its chain of that length would travel up to the frame, which has no
chain longer than its own points. -/
theorem length_le_of_sh {M Q : Type} [Frame M] [Frame Q]
    (antisymm : ∀ p q : M, p ≼ q → q ≼ p → p = q)
    {lM : List M} (hnd : lM.Nodup) (hlM : ∀ p, p ∈ lM)
    {lQ : List Q} (hlQ : ∀ q, q ∈ lQ)
    (h : SH (Upset M) (Upset Q)) : lM.length ≤ lQ.length :=
  length_ge_of_hasChain hlQ (HasChain.of_sh h (hasChain_of_nodup antisymm hnd hlM))

/-! ## Maximal points -/

/-- A frame with its order turned round. -/
structure Op (P : Type u) where
  pt : P

instance {P : Type u} [Frame P] : Frame (Op P) where
  le p q := q.pt ≼ p.pt
  le_refl p := Frame.le_refl p.pt
  le_trans h₁ h₂ := Frame.le_trans h₂ h₁

/-- Every inhabited set of points of a finite frame has a maximal one: a
minimal one of the frame turned round. -/
theorem hasMaximal_of_list {P : Type u} [Frame P] (l : List P) (hl : ∀ p, p ∈ l)
    (S : P → Prop) (hS : ∃ p, S p) : ∃ m, S m ∧ ∀ q, S q → m ≼ q → q ≼ m := by
  obtain ⟨p, hp⟩ := hS
  obtain ⟨m, hSm, hmax⟩ := hasMinimal_of_list (l.map Op.mk)
    (fun q => List.mem_map.mpr ⟨q.pt, hl q.pt, rfl⟩) (fun q => S q.pt) ⟨⟨p⟩, hp⟩
  exact ⟨m.pt, hSm, fun q hSq hmq => hmax ⟨q⟩ hSq hmq⟩

/-! ## The points above a point

Passing to the points above one of them is a homomorphic image: restricting
upward closed sets is onto. -/

/-- The points above `r`, as a frame of their own. -/
structure Above {P : Type} [Frame P] (r : P) where
  pt : P
  above : r ≼ pt

namespace Above

variable {P : Type} [Frame P] {r : P}

instance : Frame (Above r) where
  le p q := p.pt ≼ q.pt
  le_refl p := Frame.le_refl p.pt
  le_trans h₁ h₂ := Frame.le_trans h₁ h₂

/-- The root of the points above `r`, which is `r` itself. -/
def root (r : P) : Above r := ⟨r, Frame.le_refl r⟩

open Classical in
/-- The entries of `l` lying above `r`. -/
noncomputable def cover (r : P) (l : List P) : List (Above r) :=
  l.filterMap fun p => if h : r ≼ p then some ⟨p, h⟩ else none

theorem mem_cover {l : List P} (hl : ∀ p, p ∈ l) (q : Above r) : q ∈ cover r l := by
  unfold cover
  rw [List.mem_filterMap]
  refine ⟨q.pt, hl q.pt, ?_⟩
  split
  · rfl
  · exact absurd q.above ‹_›

/-- A point not above `r` is lost, so fewer entries remain. -/
theorem length_cover_lt {l : List P} {p : P} (hpl : p ∈ l) (hrp : ¬ r ≼ p) :
    (cover r l).length < l.length :=
  ListCount.length_filterMap_lt _ ⟨p, hpl, by simp [hrp]⟩

/-- Restricting an upward closed set to the points above `r`. -/
def restrict (U : Upset P) : Upset (Above r) :=
  ⟨fun q => U.mem q.pt, fun h hq => U.upward h hq⟩

/-- Extending back: the points above `r` that `V` contains. -/
def extend (V : Upset (Above r)) : Upset P :=
  ⟨fun p => ∃ h : r ≼ p, V.mem ⟨p, h⟩,
   fun {_ _} hpp' ⟨h, hv⟩ => ⟨Frame.le_trans h hpp', V.upward hpp' hv⟩⟩

theorem restrict_extend (V : Upset (Above r)) : restrict (extend V) = V :=
  Upset.ext fun q => ⟨fun ⟨_, hv⟩ => hv, fun hv => ⟨q.above, hv⟩⟩

/-- Restriction is a homomorphism: everything above a point above `r` is above
`r` too, so the arrow looks at the same points either way. -/
def restrictHom (r : P) : Hom (Upset P) (Upset (Above r)) where
  toFun := restrict
  map_bot := Upset.ext fun _ => Iff.rfl
  map_top := Upset.ext fun _ => Iff.rfl
  map_inf _ _ := Upset.ext fun _ => Iff.rfl
  map_sup _ _ := Upset.ext fun _ => Iff.rfl
  map_himp _ _ := Upset.ext fun q =>
    ⟨fun h q' hqq' hu => h q'.pt hqq' hu,
     fun h p hqp hu => h ⟨p, Frame.le_trans q.above hqp⟩ hqp hu⟩

theorem onto (r : P) : Onto (Upset (Above r)) (Upset P) :=
  ⟨restrictHom r, fun V => ⟨extend V, restrict_extend V⟩⟩

theorem sh (r : P) : SH (Upset (Above r)) (Upset P) :=
  ⟨Upset (Above r), inferInstance, onto r, embeds_refl _⟩

end Above

/-! ## Merging points

Merging points along a map that respects the order the way a p-morphism must is
a subalgebra: pulling upward closed sets back along the merge is one to one. -/

/-- A way of merging points: each goes to a representative that the same map
fixes, and whatever lies above a point lies, up to merging, above every point
merged with it. -/
structure Merger (P : Type) [Frame P] where
  g : P → P
  idem : ∀ x, g (g x) = g x
  bisim : ∀ {x x' y : P}, g x = g x' → x ≼ y → ∃ y', g y' = g y ∧ x' ≼ y'

/-- The representatives, which are what is left after merging. -/
structure Merger.Pt {P : Type} [Frame P] (m : Merger P) where
  pt : P
  fixed : m.g pt = pt

namespace Merger

variable {P : Type} [Frame P] (m : Merger P)

theorem Pt.ext {q q' : m.Pt} (h : q.pt = q'.pt) : q = q' := by
  cases q; cases q'; cases h; rfl

/-- One representative lies below another when something merged into the
second lies above the first. -/
instance : Frame m.Pt where
  le q q' := ∃ y, m.g y = q'.pt ∧ q.pt ≼ y
  le_refl q := ⟨q.pt, q.fixed, Frame.le_refl _⟩
  le_trans {q₁ q₂ q₃} h₁ h₂ := by
    obtain ⟨y₁, hy₁, h₁⟩ := h₁
    obtain ⟨y₂, hy₂, h₂⟩ := h₂
    obtain ⟨y', hy', h'⟩ := m.bisim (x := q₂.pt) (x' := y₁) (by rw [q₂.fixed, hy₁]) h₂
    exact ⟨y', hy'.trans hy₂, Frame.le_trans h₁ h'⟩

/-- Sending a point to its representative. -/
def proj (x : P) : m.Pt := ⟨m.g x, m.idem x⟩

theorem proj_fixed (q : m.Pt) : m.proj q.pt = q := Pt.ext m q.fixed

theorem proj_mono {x y : P} (h : x ≼ y) : m.proj x ≼ m.proj y :=
  m.bisim (x := x) (x' := m.g x) (m.idem x).symm h

theorem proj_back {x : P} {q : m.Pt} (h : m.proj x ≼ q) :
    ∃ y, x ≼ y ∧ m.proj y = q := by
  obtain ⟨z, hz, hxz⟩ := h
  obtain ⟨y, hy, hxy⟩ := m.bisim (x := m.g x) (x' := x) (m.idem x) hxz
  exact ⟨y, hxy, Pt.ext m (hy.trans hz)⟩

/-- Pulling an upward closed set back along the merge. -/
def pull (V : Upset m.Pt) : Upset P :=
  ⟨fun x => V.mem (m.proj x), fun h hv => V.upward (m.proj_mono h) hv⟩

/-- Pulling back is a homomorphism, the arrow surviving because the merge
lifts every step up the order. -/
def pullHom : Hom (Upset m.Pt) (Upset P) where
  toFun := m.pull
  map_bot := Upset.ext fun _ => Iff.rfl
  map_top := Upset.ext fun _ => Iff.rfl
  map_inf _ _ := Upset.ext fun _ => Iff.rfl
  map_sup _ _ := Upset.ext fun _ => Iff.rfl
  map_himp _ _ := Upset.ext fun x =>
    ⟨fun h y hxy hv => h (m.proj y) (m.proj_mono hxy) hv,
     fun h q hq hv => by
       obtain ⟨y, hxy, rfl⟩ := m.proj_back hq
       exact h y hxy hv⟩

theorem pull_injective : Function.Injective m.pull := by
  intro V W h
  refine Upset.ext fun q => ?_
  have := congrArg (fun U : Upset P => U.mem q.pt) h
  simp only [pull, m.proj_fixed] at this
  exact Iff.of_eq this

theorem sh : SH (Upset m.Pt) (Upset P) :=
  ⟨Upset P, inferInstance, onto_refl _, ⟨m.pullHom, m.pull_injective⟩⟩

open Classical in
/-- The entries of `l` that are representatives. -/
noncomputable def cover (l : List P) : List m.Pt :=
  l.filterMap fun x => if h : m.g x = x then some ⟨x, h⟩ else none

theorem mem_cover {l : List P} (hl : ∀ p, p ∈ l) (q : m.Pt) : q ∈ m.cover l := by
  unfold cover
  rw [List.mem_filterMap]
  refine ⟨q.pt, hl q.pt, ?_⟩
  split
  · rfl
  · exact absurd q.fixed ‹_›

/-- A point merged into another is lost, so fewer entries remain. -/
theorem length_cover_lt {l : List P} {x : P} (hxl : x ∈ l) (hx : m.g x ≠ x) :
    (m.cover l).length < l.length :=
  ListCount.length_filterMap_lt _ ⟨x, hxl, by simp [hx]⟩

/-- An upward closed set that never separates merged points, read on the
representatives. -/
def lift (U : Upset P) (hU : ∀ x, U.mem x ↔ U.mem (m.g x)) : Upset m.Pt :=
  ⟨fun q => U.mem q.pt, fun {_ _} ⟨y, hy, hqy⟩ hu => by
    rw [← hy]; exact (hU y).mp (U.upward hqy hu)⟩

theorem pull_lift (U : Upset P) (hU : ∀ x, U.mem x ↔ U.mem (m.g x)) :
    m.pull (m.lift U hU) = U :=
  Upset.ext fun x => (hU x).symm

open Classical in
/-- Collapsing a set `N` onto one of its members `c`.  This merges correctly
when whatever lies above a member of `N` lies in `N` or above every member. -/
noncomputable def collapse (N : P → Prop) (c : P) (hc : N c)
    (h : ∀ {x x' y : P}, N x → N x' → x ≼ y → N y ∨ x' ≼ y) : Merger P where
  g x := if N x then c else x
  idem x := by
    by_cases hx : N x
    · rw [ite_eq_left hx, ite_eq_left hc]
    · rw [ite_eq_right hx, ite_eq_right hx]
  bisim {x x' y} hxx' hxy := by
    by_cases hx : N x
    · have hx' : N x' := by
        by_cases hx' : N x'
        · exact hx'
        · rw [ite_eq_left hx, ite_eq_right hx'] at hxx'
          exact hxx' ▸ hc
      rcases h hx hx' hxy with hy | hy
      · exact ⟨x', by rw [ite_eq_left hx', ite_eq_left hy], Frame.le_refl _⟩
      · exact ⟨y, rfl, hy⟩
    · have hx' : x' = x := by
        by_cases hx' : N x'
        · rw [ite_eq_right hx, ite_eq_left hx'] at hxx'
          exact absurd (hxx' ▸ hc) hx
        · rw [ite_eq_right hx, ite_eq_right hx'] at hxx'
          exact hxx'.symm
      exact ⟨y, rfl, hx' ▸ hxy⟩

section collapse

variable {N : P → Prop} {c : P} {hc : N c}
  {h : ∀ {x x' y : P}, N x → N x' → x ≼ y → N y ∨ x' ≼ y}

theorem collapse_mem {x : P} (hx : N x) : (collapse N c hc h).g x = c := by
  classical
  exact ite_eq_left hx

theorem collapse_not {x : P} (hx : ¬ N x) : (collapse N c hc h).g x = x := by
  classical
  exact ite_eq_right hx

/-- A point outside `N` is merged with nothing else. -/
theorem collapse_eq_not {w : P} (hw : ¬ N w) (y : P) :
    (collapse N c hc h).g y = (collapse N c hc h).g w → y = w := by
  rw [collapse_not hw]
  intro hy
  by_cases hyN : N y
  · rw [collapse_mem hyN] at hy
    exact absurd (hy ▸ hc) hw
  · rwa [collapse_not hyN] at hy

/-- A property that takes the same value on every member of `N` as on `c`
never separates merged points. -/
theorem collapse_sat {Q : P → Prop} (hQ : ∀ x, N x → (Q x ↔ Q c)) :
    ∀ x, Q x ↔ Q ((collapse N c hc h).g x) := by
  intro x
  by_cases hx : N x
  · rw [collapse_mem hx]; exact hQ x hx
  · rw [collapse_not hx]

end collapse

/-- Collapsing an upward closed set onto one of its members, which always
merges correctly: the set becomes a single maximal point. -/
noncomputable abbrev collapseUp (N : P → Prop) (c : P) (hc : N c)
    (hup : ∀ {x y : P}, N x → x ≼ y → N y) : Merger P :=
  collapse N c hc (fun hx _ hxy => Or.inl (hup hx hxy))

end Merger
