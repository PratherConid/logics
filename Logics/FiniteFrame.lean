import Logics.Homomorphism

/-!
# Finite frames: counting points, and shrinking a frame

Two ways of turning a frame into a smaller one whose algebra sits below the
original in the Jankov order, and the count that makes "smaller" bite.

* **The points above a point** (`Above`), and more generally the points of an
  upward closed set (`Within`), form a frame whose algebra is a homomorphic
  image: restricting upward closed sets is onto.
* **Merging points** (`Merger`) along a map that respects the order as a
  p-morphism must gives a frame whose algebra is a subalgebra: pulling upward
  closed sets back is one to one.  Collapsing a set onto one of its members
  (`Merger.collapse`) is the case that comes up, and an upward closed set can
  always be collapsed (`Merger.collapseUp`).
* **Every complete subalgebra comes from a merge.**  What a merge pulls back is
  closed under arbitrary unions and intersections (`Merger.range`), and every
  subalgebra so closed is what some merge pulls back
  (`CompleteSub.mem_iff_pull`).  On a finite frame every subalgebra is complete,
  so there every subalgebra comes from a merge (`Merger.exists_of_hom`) and is
  the algebra of the merged frame (`Merger.sh_iff_of_hom`).
* **Every homomorphic image comes from an upward closed set.**  On a finite
  frame a homomorphism identifies two upward closed sets exactly when they agree
  on the least set it sends to the top (`Upset.map_eq_iff_ker`), so its image is
  the algebra of the points of that set (`Within.sh_iff_of_onto`).  Together:
  what lies below the algebra of a finite frame is the algebra of a merge of the
  points of an upward closed set (`sh_iff_merge`).
* **Counting** (`length_le_of_sh`).  A finite poset with `n` points has a chain
  of `n` strict steps down through its upward closed sets, removing one minimal
  point at a time, and a frame whose points a list of length `m` names has none
  longer than `m`.  Chains travel up the Jankov order, so the upward closed sets
  of a finite poset lie below those of a finite frame only if the poset has at
  most as many points.

Finiteness is a list naming every point.  Minimal points exist in a finite
frame, and so, turning the order round (`Op`), do maximal ones
(`hasMaximal_of_list`).  Also here: the upward closed set a finite set of points
generates, as a finite join (`Upset.gen`), and the coatom of a rooted frame
(`Upset.coatom`).
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
    (antisymm : Frame.Antisymm M)
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
    (antisymm : Frame.Antisymm M)
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

/-- Nothing lies above `m` but `m` itself. -/
def IsMaxPt {P : Type u} [Frame P] (m : P) : Prop := ∀ p, m ≼ p → p = m

/-- In a finite poset every point lies below a maximal one. -/
theorem exists_max_above {P : Type u} [Frame P] (antisymm : Frame.Antisymm P)
    {l : List P} (hl : ∀ p, p ∈ l) (x : P) : ∃ m, x ≼ m ∧ IsMaxPt m := by
  obtain ⟨m, hxm, hmax⟩ := hasMaximal_of_list l hl (fun p => x ≼ p) ⟨x, Frame.le_refl x⟩
  exact ⟨m, hxm, fun p hmp => antisymm _ _ (hmax p (Frame.le_trans hxm hmp) hmp) hmp⟩

/-- A point that is not maximal has another point above it. -/
theorem exists_ne_above {P : Type u} [Frame P] {x : P} (hx : ¬ IsMaxPt x) :
    ∃ p, x ≼ p ∧ p ≠ x :=
  Classical.byContradiction fun hc => hx fun p hxp =>
    Classical.byContradiction fun hne => hc ⟨p, hxp, hne⟩

/-! ## Upward closed sets generated by points

In a finite frame the upward closed set generated by some points is a finite
join, of the sets each of them generates.  Keeping the list of those sets
around lets an argument about joins reach the individual generators. -/

namespace Upset

variable {P : Type} [Frame P]

/-- The sets generated by the entries of `l` satisfying `S`, one per entry. -/
noncomputable def generators (l : List P) (S : P → Prop) : List (Upset P) :=
  (l.filter fun x => truth (S x)).map up

theorem up_mem_generators {l : List P} (hl : ∀ x, x ∈ l) {S : P → Prop} {x : P}
    (hx : S x) : up x ∈ generators l S :=
  List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hl x, truth_eq_true.mpr hx⟩, rfl⟩

theorem mem_of_generators {l : List P} {S : P → Prop} {V : Upset P}
    (hV : V ∈ generators l S) : ∃ x, S x ∧ V = up x := by
  obtain ⟨x, hxl, hxV⟩ := List.mem_map.mp hV
  exact ⟨x, truth_eq_true.mp (List.mem_filter.mp hxl).2, hxV.symm⟩

/-- The upward closed set generated by the points satisfying `S`. -/
noncomputable def gen (l : List P) (S : P → Prop) : Upset P := supList (generators l S)

theorem mem_gen {l : List P} (hl : ∀ x, x ∈ l) {S : P → Prop} {z : P} :
    (gen l S).mem z ↔ ∃ y, S y ∧ y ≼ z := by
  rw [gen, mem_supList]
  constructor
  · rintro ⟨V, hV, hz⟩
    obtain ⟨y, hy, rfl⟩ := mem_of_generators hV
    exact ⟨y, hy, hz⟩
  · rintro ⟨y, hy, hyz⟩
    exact ⟨up y, up_mem_generators hl hy, hyz⟩

/-- Every upward closed set is generated by its own points. -/
theorem gen_mem {l : List P} (hl : ∀ x, x ∈ l) (U : Upset P) : gen l U.mem = U :=
  ext fun _ => (mem_gen hl).trans
    ⟨fun ⟨_, hy, hyz⟩ => U.upward hyz hy, fun hz => ⟨_, hz, Frame.le_refl _⟩⟩

end Upset

/-! ## Rooted frames

When one point lies below every other and nothing else lies below it, the other
points form an upward closed set, and every upward closed set short of the
whole frame lies inside it. -/

namespace Upset

variable {P : Type} [Frame P] {r : P}

/-- Every point but `r`, upward closed when nothing else lies below `r`. -/
def coatom (r : P) (hr : ∀ x, x ≼ r → x = r) : Upset P :=
  ⟨fun x => x ≠ r, fun {x _} hxy hx hy => hx (hr x (hy ▸ hxy))⟩

/-- An upward closed set short of the whole frame misses the root, since one
holding the root holds everything. -/
theorem le_coatom (hroot : ∀ x, r ≼ x) (hr : ∀ x, x ≼ r → x = r) (U : Upset P)
    (hU : U ≠ ⊤) : U ⊑ coatom r hr := by
  intro x hx hxr
  apply hU
  refine ext fun y => ⟨fun _ => trivial, fun _ => U.upward ?_ hx⟩
  rw [hxr]
  exact hroot y

end Upset

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

/-! ## The points of an upward closed set

The same goes for the points of any upward closed set `U`: with a point they
hold everything above it, so restricting upward closed sets to them is onto.
Two sets restrict to the same one exactly when they agree on `U`. -/

/-- The points of an upward closed set `U`, as a frame of their own. -/
structure Within {P : Type} [Frame P] (U : Upset P) where
  pt : P
  mem : U.mem pt

namespace Within

variable {P : Type} [Frame P] {U : Upset P}

instance : Frame (Within U) where
  le p q := p.pt ≼ q.pt
  le_refl p := Frame.le_refl p.pt
  le_trans h₁ h₂ := Frame.le_trans h₁ h₂

open Classical in
/-- The entries of `l` in `U`. -/
noncomputable def cover (U : Upset P) (l : List P) : List (Within U) :=
  l.filterMap fun p => if h : U.mem p then some ⟨p, h⟩ else none

theorem mem_cover {l : List P} (hl : ∀ p, p ∈ l) (q : Within U) : q ∈ cover U l := by
  unfold cover
  rw [List.mem_filterMap]
  refine ⟨q.pt, hl q.pt, ?_⟩
  split
  · rfl
  · exact absurd q.mem ‹_›

/-- A point outside `U` is lost, so fewer entries remain. -/
theorem length_cover_lt {l : List P} {p : P} (hpl : p ∈ l) (hp : ¬ U.mem p) :
    (cover U l).length < l.length :=
  ListCount.length_filterMap_lt _ ⟨p, hpl, by simp [hp]⟩

/-- Restricting an upward closed set to the points of `U`. -/
def restrict (V : Upset P) : Upset (Within U) :=
  ⟨fun q => V.mem q.pt, fun h hq => V.upward h hq⟩

/-- Extending back: the points of `U` that `W` contains. -/
def extend (W : Upset (Within U)) : Upset P :=
  ⟨fun p => ∃ h : U.mem p, W.mem ⟨p, h⟩,
   fun {_ _} hpp' ⟨h, hw⟩ => ⟨U.upward hpp' h, W.upward hpp' hw⟩⟩

theorem restrict_extend (W : Upset (Within U)) : restrict (extend W) = W :=
  Upset.ext fun q => ⟨fun ⟨_, hw⟩ => hw, fun hw => ⟨q.mem, hw⟩⟩

/-- Two upward closed sets restrict to the same one exactly when they agree on
`U`. -/
theorem restrict_eq_iff {V W : Upset P} :
    (restrict V : Upset (Within U)) = restrict W ↔ ∀ x, U.mem x → (V.mem x ↔ W.mem x) :=
  ⟨fun h x hx => Iff.of_eq (congrArg (fun R : Upset (Within U) => R.mem ⟨x, hx⟩) h),
   fun h => Upset.ext fun q => h q.pt q.mem⟩

/-- Restriction is a homomorphism: everything above a point of `U` is in `U`,
so the arrow looks at the same points either way. -/
def restrictHom (U : Upset P) : Hom (Upset P) (Upset (Within U)) where
  toFun := restrict
  map_bot := Upset.ext fun _ => Iff.rfl
  map_top := Upset.ext fun _ => Iff.rfl
  map_inf _ _ := Upset.ext fun _ => Iff.rfl
  map_sup _ _ := Upset.ext fun _ => Iff.rfl
  map_himp _ _ := Upset.ext fun q =>
    ⟨fun h q' hqq' hv => h q'.pt hqq' hv,
     fun h p hqp hv => h ⟨p, U.upward hqp q.mem⟩ hqp hv⟩

theorem onto (U : Upset P) : Onto (Upset (Within U)) (Upset P) :=
  ⟨restrictHom U, fun W => ⟨extend W, restrict_extend W⟩⟩

theorem sh (U : Upset P) : SH (Upset (Within U)) (Upset P) :=
  ⟨Upset (Within U), inferInstance, onto U, embeds_refl _⟩

end Within

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

/-! ## Every complete subalgebra comes from a merge

Pulling back along a merge gives more than a subalgebra.  The upward closed sets
it produces are those that never separate merged points, and they are closed
under unions and intersections of arbitrary families: a *complete* subalgebra
(`Merger.range`).  Conversely a complete subalgebra comes from a merge
(`CompleteSub.mem_iff_pull`): merge two points when no member separates them.

Completeness is what makes the converse work.  Each point `y` then has a least
member containing it, `least y`, and a union of the members missing it,
`missing y`, and the points no member separates from `y` are those in the first
and not in the second.  So `least y ⇨ missing y`, a member, holds exactly where
nothing above is merged with `y` (`mem_gap_iff`), which gives the condition a
merge needs (`back`), and lets every upward closed set that never separates
merged points be built as a union of `least`s.

On a finite frame every subalgebra is complete, a union or an intersection of a
family being that of finitely many of its members (`CompleteSub.ofHom`).  So
there every subalgebra comes from a merge (`Merger.exists_of_hom`), and the
algebra is that of the merged frame (`Merger.sh_iff_of_hom`).  Without
finiteness this fails: the finite and cofinite sets of a discrete infinite frame
form a subalgebra that is not complete. -/

namespace Upset

variable {P : Type} [Frame P]

/-- The union of a family of upward closed sets. -/
def sUnion (F : Upset P → Prop) : Upset P :=
  ⟨fun x => ∃ U, F U ∧ U.mem x, fun h ⟨U, hU, hx⟩ => ⟨U, hU, U.upward h hx⟩⟩

/-- The intersection of a family of upward closed sets. -/
def sInter (F : Upset P → Prop) : Upset P :=
  ⟨fun x => ∀ U, F U → U.mem x, fun h hx U hU => U.upward h (hx U hU)⟩

/-- A point is in the meet of a list exactly when it is in all of its entries. -/
theorem mem_infList : ∀ {L : List (Upset P)} {p : P},
    (infList L).mem p ↔ ∀ U ∈ L, U.mem p
  | [], _ => ⟨(fun _ _ h => nomatch h), fun _ => trivial⟩
  | U :: t, p => by
    show U.mem p ∧ (infList t).mem p ↔ _
    rw [mem_infList]
    constructor
    · rintro ⟨h, ht⟩ V hV
      rcases List.mem_cons.mp hV with rfl | hV
      · exact h
      · exact ht V hV
    · intro h
      exact ⟨h U (List.mem_cons_self ..), fun V hV => h V (List.mem_cons_of_mem _ hV)⟩

/-- **On a finite frame a union is a finite join**, of one member of the family
per point it contains. -/
theorem exists_supList (l : List P) (hl : ∀ x, x ∈ l) (F : Upset P → Prop) :
    ∃ L : List (Upset P), (∀ U ∈ L, F U) ∧ sUnion F = supList L := by
  let pick : P → Upset P := fun x => @Classical.epsilon _ ⟨⊤⟩ fun U => F U ∧ U.mem x
  have hpick : ∀ x, (∃ U, F U ∧ U.mem x) → F (pick x) ∧ (pick x).mem x :=
    fun x => Classical.epsilon_spec (p := fun U => F U ∧ U.mem x)
  have hmem : ∀ {y}, y ∈ l.filter (fun x => truth (∃ U, F U ∧ U.mem x)) →
      F (pick y) ∧ (pick y).mem y :=
    fun hy => hpick _ (truth_eq_true.mp (List.mem_filter.mp hy).2)
  refine ⟨(l.filter fun x => truth (∃ U, F U ∧ U.mem x)).map pick, fun U hU => ?_,
    ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hU
    exact (hmem hy).1
  · exact mem_supList.mpr ⟨pick x,
      List.mem_map_of_mem (List.mem_filter.mpr ⟨hl x, truth_eq_true.mpr hx⟩), (hpick x hx).2⟩
  · obtain ⟨U, hU, hxU⟩ := mem_supList.mp hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hU
    exact ⟨pick y, (hmem hy).1, hxU⟩

/-- **On a finite frame an intersection is a finite meet**, of one member of
the family per point it misses. -/
theorem exists_infList (l : List P) (hl : ∀ x, x ∈ l) (F : Upset P → Prop) :
    ∃ L : List (Upset P), (∀ U ∈ L, F U) ∧ sInter F = infList L := by
  let pick : P → Upset P := fun x => @Classical.epsilon _ ⟨⊤⟩ fun U => F U ∧ ¬ U.mem x
  have hpick : ∀ x, (∃ U, F U ∧ ¬ U.mem x) → F (pick x) ∧ ¬ (pick x).mem x :=
    fun x => Classical.epsilon_spec (p := fun U => F U ∧ ¬ U.mem x)
  have hmem : ∀ {y}, y ∈ l.filter (fun x => truth (∃ U, F U ∧ ¬ U.mem x)) →
      F (pick y) ∧ ¬ (pick y).mem y :=
    fun hy => hpick _ (truth_eq_true.mp (List.mem_filter.mp hy).2)
  refine ⟨(l.filter fun x => truth (∃ U, F U ∧ ¬ U.mem x)).map pick, fun U hU => ?_,
    ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hU
    exact (hmem hy).1
  · refine mem_infList.mpr fun W hW => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hW
    exact hx _ (hmem hy).1
  · intro U hU
    refine Classical.byContradiction fun hxU => ?_
    have hex : ∃ U, F U ∧ ¬ U.mem x := ⟨U, hU, hxU⟩
    exact (hpick x hex).2 (mem_infList.mp hx _
      (List.mem_map_of_mem (List.mem_filter.mpr ⟨hl x, truth_eq_true.mpr hex⟩)))

end Upset

/-- A *complete* subalgebra of the upward closed sets: closed under the arrow,
and under unions and intersections of arbitrary families, the empty ones giving
`⊥` and `⊤`. -/
structure CompleteSub (P : Type) [Frame P] where
  mem : Upset P → Prop
  himp : ∀ {U V : Upset P}, mem U → mem V → mem (U ⇨ V)
  sUnion : ∀ F : Upset P → Prop, (∀ U, F U → mem U) → mem (Upset.sUnion F)
  sInter : ∀ F : Upset P → Prop, (∀ U, F U → mem U) → mem (Upset.sInter F)

namespace Merger

variable {P : Type} [Frame P] (m : Merger P)

/-- An upward closed set is pulled back along a merge exactly when it never
separates merged points. -/
theorem pulled_iff (U : Upset P) : (∃ V, m.pull V = U) ↔ ∀ x, U.mem x ↔ U.mem (m.g x) := by
  constructor
  · rintro ⟨V, rfl⟩ x
    show V.mem (m.proj x) ↔ V.mem (m.proj (m.g x))
    rw [show m.proj (m.g x) = m.proj x from Pt.ext m (m.idem x)]
  · intro hU
    exact ⟨m.lift U hU, m.pull_lift U hU⟩

/-- **A merge gives a complete subalgebra**, the upward closed sets pulled back
along it: never separating merged points survives any union and intersection,
and the arrow is pulled back with the rest. -/
def range : CompleteSub P where
  mem U := ∃ V, m.pull V = U
  himp := fun ⟨V, hV⟩ ⟨W, hW⟩ => ⟨V ⇨ W, by rw [← hV, ← hW]; exact m.pullHom.map_himp V W⟩
  sUnion F hF := (m.pulled_iff _).mpr fun x =>
    ⟨fun ⟨U, hU, hx⟩ => ⟨U, hU, ((m.pulled_iff U).mp (hF U hU) x).mp hx⟩,
     fun ⟨U, hU, hx⟩ => ⟨U, hU, ((m.pulled_iff U).mp (hF U hU) x).mpr hx⟩⟩
  sInter F hF := (m.pulled_iff _).mpr fun x =>
    ⟨fun hx U hU => ((m.pulled_iff U).mp (hF U hU) x).mp (hx U hU),
     fun hx U hU => ((m.pulled_iff U).mp (hF U hU) x).mpr (hx U hU)⟩

end Merger

namespace CompleteSub

variable {P : Type} [Frame P] (S : CompleteSub P)

/-- Two points that no member of `S` separates. -/
def Equiv (x y : P) : Prop := ∀ U, S.mem U → (U.mem x ↔ U.mem y)

theorem equiv_refl (x : P) : S.Equiv x x := fun _ _ => Iff.rfl

theorem equiv_symm {x y : P} (h : S.Equiv x y) : S.Equiv y x := fun U hU => (h U hU).symm

theorem equiv_trans {x y z : P} (h₁ : S.Equiv x y) (h₂ : S.Equiv y z) : S.Equiv x z :=
  fun U hU => (h₁ U hU).trans (h₂ U hU)

/-- The least member containing `y`. -/
def least (y : P) : Upset P := Upset.sInter fun U => S.mem U ∧ U.mem y

/-- The union of the members missing `y`. -/
def missing (y : P) : Upset P := Upset.sUnion fun U => S.mem U ∧ ¬ U.mem y

theorem least_mem (y : P) : S.mem (S.least y) := S.sInter _ fun _ h => h.1

theorem missing_mem (y : P) : S.mem (S.missing y) := S.sUnion _ fun _ h => h.1

theorem self_mem_least (y : P) : (S.least y).mem y := fun _ h => h.2

theorem self_not_mem_missing (y : P) : ¬ (S.missing y).mem y := fun ⟨_, h, hy⟩ => h.2 hy

/-- The points no member separates from `y` are those in `least y` and not in
`missing y`. -/
theorem equiv_iff (y z : P) : S.Equiv z y ↔ (S.least y).mem z ∧ ¬ (S.missing y).mem z := by
  constructor
  · intro h
    exact ⟨fun U hU => (h U hU.1).mpr hU.2, fun ⟨U, hU, hz⟩ => hU.2 ((h U hU.1).mp hz)⟩
  · rintro ⟨hl, hm⟩ U hU
    rcases Classical.em (U.mem y) with hy | hy
    · exact ⟨fun _ => hy, fun _ => hl U ⟨hU, hy⟩⟩
    · exact ⟨fun hz => absurd ⟨U, ⟨hU, hy⟩, hz⟩ hm, fun h => absurd h hy⟩

/-- **The gap of `y`**, the member `least y ⇨ missing y`, holds at a point
exactly when nothing above it is merged with `y`. -/
theorem mem_gap_iff (y x : P) :
    (S.least y ⇨ S.missing y).mem x ↔ ∀ z, x ≼ z → ¬ S.Equiv z y := by
  show (∀ z, x ≼ z → (S.least y).mem z → (S.missing y).mem z) ↔ _
  constructor
  · intro h z hxz hz
    exact ((S.equiv_iff y z).mp hz).2 (h z hxz ((S.equiv_iff y z).mp hz).1)
  · intro h z hxz hl
    exact Classical.byContradiction fun hm => h z hxz ((S.equiv_iff y z).mpr ⟨hl, hm⟩)

/-- **The condition a merge needs.**  If `x` and `x'` are not separated and `y`
lies above `x`, something not separated from `y` lies above `x'`: otherwise the
gap of `y` would hold at `x'` and not at `x`. -/
theorem back {x x' y : P} (hxx' : S.Equiv x x') (hxy : x ≼ y) :
    ∃ y', S.Equiv y' y ∧ x' ≼ y' := by
  refine Classical.byContradiction fun hne => ?_
  have hx' : (S.least y ⇨ S.missing y).mem x' :=
    (S.mem_gap_iff y x').mpr fun z hz hzy => hne ⟨z, hzy, hz⟩
  have hx : (S.least y ⇨ S.missing y).mem x :=
    (hxx' _ (S.himp (S.least_mem y) (S.missing_mem y))).mpr hx'
  exact (S.mem_gap_iff y x).mp hx y hxy (S.equiv_refl y)

/-- `least x` holds at `z` exactly when something not separated from `z` lies
above `x`: were there none, the gap of `z`, a member holding at `x`, would
contain `least x` and so `z`. -/
theorem mem_least_iff (x z : P) : (S.least x).mem z ↔ ∃ z', x ≼ z' ∧ S.Equiv z' z := by
  constructor
  · intro hz
    refine Classical.byContradiction fun hne => ?_
    have hgap : (S.least z ⇨ S.missing z).mem x :=
      (S.mem_gap_iff z x).mpr fun z' hxz' hz' => hne ⟨z', hxz', hz'⟩
    have hle : (S.least z ⇨ S.missing z).mem z :=
      hz _ ⟨S.himp (S.least_mem z) (S.missing_mem z), hgap⟩
    exact S.self_not_mem_missing z (hle z (Frame.le_refl z) (S.self_mem_least z))
  · rintro ⟨z', hxz', hz'⟩
    exact (hz' _ (S.least_mem x)).mp ((S.least x).upward hxz' (S.self_mem_least x))

/-- A chosen point not separated from `x`, the same for all such points. -/
noncomputable def rep (x : P) : P := @Classical.epsilon P ⟨x⟩ fun y => S.Equiv y x

theorem rep_equiv (x : P) : S.Equiv (S.rep x) x :=
  Classical.epsilon_spec (p := fun y => S.Equiv y x) ⟨x, S.equiv_refl x⟩

theorem rep_eq {x x' : P} (h : S.Equiv x x') : S.rep x = S.rep x' := by
  have : (fun y => S.Equiv y x) = (fun y => S.Equiv y x') :=
    funext fun y => propext
      ⟨fun h' => S.equiv_trans h' h, fun h' => S.equiv_trans h' (S.equiv_symm h)⟩
  unfold rep
  rw [this]

/-- **The merge**: each point goes to the chosen point of its class. -/
noncomputable def merger : Merger P where
  g := S.rep
  idem x := S.rep_eq (S.rep_equiv x)
  bisim {x x' y} hxx' hxy := by
    have h : S.Equiv x x' :=
      S.equiv_trans (S.equiv_symm (S.rep_equiv x)) (hxx' ▸ S.rep_equiv x')
    obtain ⟨y', hy', hxy'⟩ := S.back h hxy
    exact ⟨y', S.rep_eq hy', hxy'⟩

/-- **Every complete subalgebra comes from a merge**: its members are exactly
the upward closed sets pulled back along `merger`.  A member never separates
merged points by definition; and an upward closed set that never does is the
union of the `least x` over its points `x`, a member. -/
theorem mem_iff_pull (U : Upset P) : S.mem U ↔ ∃ V, S.merger.pull V = U := by
  rw [S.merger.pulled_iff]
  constructor
  · intro hU x
    exact (S.rep_equiv x U hU).symm
  · intro hU
    have hsat : ∀ {z z'}, S.Equiv z z' → U.mem z → U.mem z' := fun {z z'} h hz => by
      have h₁ : U.mem (S.rep z) := (hU z).mp hz
      rw [S.rep_eq h] at h₁
      exact (hU z').mpr h₁
    have : U = Upset.sUnion fun W => ∃ x, U.mem x ∧ W = S.least x := by
      refine Upset.ext fun z => ⟨fun hz => ⟨_, ⟨z, hz, rfl⟩, S.self_mem_least z⟩, ?_⟩
      rintro ⟨_, ⟨x, hx, rfl⟩, hz⟩
      obtain ⟨z', hxz', hz'⟩ := (S.mem_least_iff x z).mp hz
      exact hsat hz' (U.upward hxz' hx)
    rw [this]
    exact S.sUnion _ fun _ ⟨x, _, hW⟩ => hW ▸ S.least_mem x

/-- **On a finite frame every subalgebra is complete.**  The image of a
homomorphism into the upward closed sets of a frame whose points a list names:
a union of members is the join of one member per point it contains, and an
intersection the meet of one member per point it misses. -/
noncomputable def ofHom {α : Type} [HeytingAlgebra α] (l : List P) (hl : ∀ x, x ∈ l)
    (f : Hom α (Upset P)) : CompleteSub P where
  mem U := f.InImg U
  himp := Hom.img_himp
  sUnion F hF := by
    obtain ⟨L, hL, h⟩ := Upset.exists_supList l hl F
    rw [h]
    exact Hom.img_supList fun U hU => hF U (hL U hU)
  sInter F hF := by
    obtain ⟨L, hL, h⟩ := Upset.exists_infList l hl F
    rw [h]
    exact Hom.img_infList fun U hU => hF U (hL U hU)

end CompleteSub

namespace Merger

variable {P : Type} [Frame P]

/-- **On a finite frame every subalgebra comes from a merge**: the image of any
homomorphism into the upward closed sets is exactly what is pulled back along
some merge. -/
theorem exists_of_hom {α : Type} [HeytingAlgebra α] (l : List P) (hl : ∀ x, x ∈ l)
    (f : Hom α (Upset P)) : ∃ m : Merger P, ∀ U, f.InImg U ↔ ∃ V, m.pull V = U :=
  ⟨(CompleteSub.ofHom l hl f).merger, (CompleteSub.ofHom l hl f).mem_iff_pull⟩

/-- A map into the upward closed sets of a merged frame is a homomorphism when
pulling it back gives one: pulling back is a one to one homomorphism, so every
equation it satisfies after pulling back, it satisfies already. -/
def homOfPull {α : Type} [HeytingAlgebra α] (m : Merger P) (f : Hom α (Upset P))
    (e : α → Upset m.Pt) (he : ∀ a, m.pull (e a) = f.toFun a) : Hom α (Upset m.Pt) where
  toFun := e
  map_bot := m.pull_injective ((he _).trans (f.map_bot.trans m.pullHom.map_bot.symm))
  map_top := m.pull_injective ((he _).trans (f.map_top.trans m.pullHom.map_top.symm))
  map_inf a b := m.pull_injective ((he _).trans ((f.map_inf a b).trans
    ((congr (congrArg (· ⊓ ·) (he a)) (he b)).symm.trans (m.pullHom.map_inf _ _).symm)))
  map_sup a b := m.pull_injective ((he _).trans ((f.map_sup a b).trans
    ((congr (congrArg (· ⊔ ·) (he a)) (he b)).symm.trans (m.pullHom.map_sup _ _).symm)))
  map_himp a b := m.pull_injective ((he _).trans ((f.map_himp a b).trans
    ((congr (congrArg (· ⇨ ·) (he a)) (he b)).symm.trans (m.pullHom.map_himp _ _).symm)))

/-- **And the algebra is that of the merged frame.**  For an embedding `f`,
sending `a` to `f a` read on the representatives of the merge of
`exists_of_hom` is an isomorphism, since pulling back is one to one and has the
same image as `f`. -/
theorem exists_iso_of_hom {α : Type} [HeytingAlgebra α] (l : List P) (hl : ∀ x, x ∈ l)
    (f : Hom α (Upset P)) (hf : Function.Injective f.toFun) :
    ∃ m : Merger P, ∃ e : Hom α (Upset m.Pt),
      Function.Injective e.toFun ∧ Function.Surjective e.toFun := by
  obtain ⟨m, hm⟩ := exists_of_hom l hl f
  have hsat : ∀ a x, (f.toFun a).mem x ↔ (f.toFun a).mem (m.g x) :=
    fun a => (m.pulled_iff _).mp ((hm _).mp ⟨a, rfl⟩)
  have hpull : ∀ a, m.pull (m.lift (f.toFun a) (hsat a)) = f.toFun a :=
    fun a => m.pull_lift _ _
  let e := m.homOfPull f _ hpull
  have he_inj : Function.Injective e.toFun := fun a b h =>
    hf (by rw [← hpull a, ← hpull b]; exact congrArg m.pull h)
  have he_surj : Function.Surjective e.toFun := fun V => by
    obtain ⟨a, ha⟩ := (hm (m.pull V)).mpr ⟨V, rfl⟩
    exact ⟨a, m.pull_injective ((hpull a).trans ha)⟩
  exact ⟨m, e, he_inj, he_surj⟩

/-- So the merge of `exists_of_hom` puts `α` and the upward closed sets of the
merged frame below each other. -/
theorem sh_iff_of_hom {α : Type} [HeytingAlgebra α] (l : List P) (hl : ∀ x, x ∈ l)
    (f : Hom α (Upset P)) (hf : Function.Injective f.toFun) :
    ∃ m : Merger P, SH α (Upset m.Pt) ∧ SH (Upset m.Pt) α := by
  obtain ⟨m, e, he⟩ := exists_iso_of_hom l hl f hf
  exact ⟨m, sh_of_embeds ⟨e, he.1⟩, sh_of_bijective e he⟩

end Merger

/-! ## Every homomorphic image comes from an upward closed set

Dually, a homomorphism `f` out of the upward closed sets identifies two of them
exactly when it sends both arrows between them to the top.  On a finite frame
the sets it sends to the top have a least one, `ker f`, their intersection
being that of finitely many (`Upset.map_ker`), and an arrow between two sets
contains `ker f` exactly when the two agree on it.  So `f` identifies two sets
exactly when they agree on `ker f` (`Upset.map_eq_iff_ker`), which is when they
restrict to the same upward closed set of its points.  The image of `f` is then
the algebra of the points of `ker f` (`Within.exists_iso_of_onto`).  Without
finiteness this fails: on an infinite discrete frame, of the sets whose
complements are finite none is least.

Combined with merges: what lies below the algebra of a finite frame is a
subalgebra of a homomorphic image, so the algebra of a merge of the points of an
upward closed set, and conversely (`sh_iff_merge`). -/

namespace Upset

variable {P : Type} [Frame P] {α : Type} [HeytingAlgebra α]

/-- The intersection of the upward closed sets that `f` sends to the top. -/
def ker (f : Hom (Upset P) α) : Upset P := sInter fun V => f.toFun V = ⊤

/-- On a finite frame `f` sends `ker f` itself to the top: it is the
intersection of finitely many sets that `f` sends there. -/
theorem map_ker (l : List P) (hl : ∀ x, x ∈ l) (f : Hom (Upset P) α) :
    f.toFun (ker f) = ⊤ := by
  obtain ⟨L, hL, h⟩ := exists_infList l hl fun V => f.toFun V = ⊤
  rw [ker, h, f.map_infList]
  refine (BoundedLattice.eq_top_iff _).mpr (le_infList fun a ha => ?_)
  obtain ⟨V, hV, rfl⟩ := List.mem_map.mp ha
  have hV' : f.toFun V = ⊤ := hL V hV
  rw [hV']
  exact le_rfl

/-- **`f` identifies two upward closed sets exactly when they agree on
`ker f`**, on a finite frame.  If `f` identifies them it sends both arrows
between them to the top, so both arrows contain `ker f`; if they agree on
`ker f` their meets with it are equal, and `f` sends each set to the same value
as its meet with `ker f`. -/
theorem map_eq_iff_ker (l : List P) (hl : ∀ x, x ∈ l) (f : Hom (Upset P) α)
    {V W : Upset P} : f.toFun V = f.toFun W ↔ ∀ x, (ker f).mem x → (V.mem x ↔ W.mem x) := by
  constructor
  · intro h x hx
    have hVW : f.toFun (V ⇨ W) = ⊤ := by rw [f.map_himp, h]; exact himp_eq_top_of_le le_rfl
    have hWV : f.toFun (W ⇨ V) = ⊤ := by rw [f.map_himp, h]; exact himp_eq_top_of_le le_rfl
    exact ⟨hx _ hVW x (Frame.le_refl x), hx _ hWV x (Frame.le_refl x)⟩
  · intro h
    have hKV : ker f ⊓ V = ker f ⊓ W :=
      ext fun x => ⟨fun hx => ⟨hx.1, (h x hx.1).mp hx.2⟩, fun hx => ⟨hx.1, (h x hx.1).mpr hx.2⟩⟩
    rw [← top_inf (f.toFun V), ← top_inf (f.toFun W), ← map_ker l hl f, ← f.map_inf,
      ← f.map_inf, hKV]

/-- When `ker f` is everything, `f` identifies nothing. -/
theorem injective_of_ker (l : List P) (hl : ∀ x, x ∈ l) (f : Hom (Upset P) α)
    (h : ker f = ⊤) : Function.Injective f.toFun := fun _ _ hVW =>
  ext fun x => (map_eq_iff_ker l hl f).mp hVW x (by rw [h]; trivial)

end Upset

namespace Within

variable {P : Type} [Frame P] {α : Type} [HeytingAlgebra α]

/-- **On a finite frame every homomorphic image is the algebra of the points of
an upward closed set**, namely of `ker f`: restricting to it identifies the same
upward closed sets as `f` does, so sending `f V` to the restriction of `V` is an
isomorphism. -/
theorem exists_iso_of_onto (l : List P) (hl : ∀ x, x ∈ l) (f : Hom (Upset P) α)
    (hf : Function.Surjective f.toFun) :
    ∃ e : Hom α (Upset (Within (Upset.ker f))),
      Function.Injective e.toFun ∧ Function.Surjective e.toFun := by
  have h : ∀ V W, f.toFun V = f.toFun W ↔
      (restrictHom (Upset.ker f)).toFun V = (restrictHom (Upset.ker f)).toFun W :=
    fun _ _ => (Upset.map_eq_iff_ker l hl f).trans restrict_eq_iff.symm
  exact ⟨f.descend hf _ fun V W => (h V W).mp,
    Hom.descend_injective fun V W => (h V W).mpr,
    Hom.descend_surjective fun W => ⟨extend W, restrict_extend W⟩⟩

/-- So the points of `ker f` put `α` and their upward closed sets below each
other. -/
theorem sh_iff_of_onto (l : List P) (hl : ∀ x, x ∈ l) (f : Hom (Upset P) α)
    (hf : Function.Surjective f.toFun) :
    ∃ U : Upset P, SH α (Upset (Within U)) ∧ SH (Upset (Within U)) α := by
  obtain ⟨e, he⟩ := exists_iso_of_onto l hl f hf
  exact ⟨_, sh_of_embeds ⟨e, he.1⟩, sh_of_bijective e he⟩

end Within

/-- **What lies below the algebra of a finite frame is the algebra of a merge of
the points of an upward closed set.**  An algebra below is a subalgebra of a
homomorphic image; the image is the algebra of the points of an upward closed
set (`Within.exists_iso_of_onto`), and a subalgebra of that the algebra of one
of its merges (`Merger.exists_iso_of_hom`).  Conversely the algebra of such a
merge embeds in that of the points, a homomorphic image. -/
theorem sh_iff_merge {P : Type} [Frame P] {α : Type} [HeytingAlgebra α] (l : List P)
    (hl : ∀ x, x ∈ l) :
    SH α (Upset P) ↔ ∃ (U : Upset P) (m : Merger (Within U)) (e : Hom α (Upset m.Pt)),
      Function.Injective e.toFun ∧ Function.Surjective e.toFun := by
  constructor
  · rintro ⟨γ, iγ, ⟨f, hf⟩, ⟨g, hg⟩⟩
    obtain ⟨e, he⟩ := Within.exists_iso_of_onto l hl f hf
    obtain ⟨m, e', he'⟩ := Merger.exists_iso_of_hom (Within.cover _ l) (Within.mem_cover hl)
      (e.comp g) fun _ _ h => hg (he.1 h)
    exact ⟨_, m, e', he'⟩
  · rintro ⟨U, m, e, he, -⟩
    exact ⟨Upset (Within U), inferInstance, Within.onto U,
      m.pullHom.comp e, fun _ _ h => he (m.pull_injective h)⟩
