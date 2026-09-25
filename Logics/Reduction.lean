import Logics.FiniteFrame

/-!
# Merging a finite poset one step at a time

A merge of a frame (`Merger`) gives a frame whose algebra lies below the
original's.  Two merges identify just two points:

* an *α-pair* (`IsAlpha x y`): `y` is the only immediate successor of `x`, so
  that everything strictly above `x` lies above `y`, and `x` collapses into `y`;
* a *β-pair* (`IsBeta x y`): two points with the same strict successors, which
  merge into one.

Merging an α- or a β-pair is always a merge (`Merger.pair`), and every merge
that identifies anything, on a finite poset, identifies some α- or β-pair
(`Merger.exists_pair`).  Merging that pair alone therefore merges less, and its
algebra lies between the two (`Merger.exists_step`).  So an algebra reached by
merging is already below that of a single step: to see that no merge of a
finite poset keeps a formula refuted, it is enough to try the α- and β-pairs.

Repeating the step, every merge of a finite poset is a chain of α- and β-steps
(`Merger.isChain`): merging a pair leaves a poset with one point fewer
(`Merger.pair_antisymm`), on which the rest of the merge can be read
(`Merger.after`).

With the other way down, passing to the points of an upward closed set, this
makes being a minimal refuter a condition on the frame: the algebra of a finite
poset is a minimal refuter of a formula exactly when the formula holds on the
points of every proper upward closed set and after every α- and β-step
(`refuterLB_iff_steps`).

## Finding the pair

Call a point *merged* when the merge identifies it with another.  Take `x`
maximal among the merged points, so that nothing strictly above `x` is merged;
then `y` maximal among the other points identified with `x`.  Whatever lies
above `y` is identified, by the merge's back condition, with something above
`x`: with `x` itself, or with a point strictly above `x`, which being unmerged
is that very point.  So everything strictly above `y` is `x` or lies above `x`.
If `y` lies below `x`, then `x` is its only immediate successor, an α-pair.
Otherwise the two are unrelated, and the back condition run the other way puts
every strict successor of `x` above `y`: a β-pair.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

variable {P : Type} [Frame P]

/-- An α-pair: `y` is the only immediate successor of `x`, everything strictly
above `x` lying above `y`. -/
def IsAlpha (x y : P) : Prop := x ≠ y ∧ x ≼ y ∧ ∀ z, x ≼ z → z ≠ x → y ≼ z

/-- A β-pair: two distinct points with the same strict successors. -/
def IsBeta (x y : P) : Prop := x ≠ y ∧ ∀ z, (x ≼ z ∧ z ≠ x) ↔ (y ≼ z ∧ z ≠ y)

namespace Merger

/-- Collapsing an α- or β-pair onto `y` merges correctly: whatever lies above
either point, and is not one of them, lies above both. -/
theorem pair_merges {x y : P} (h : IsAlpha x y ∨ IsBeta x y) {a a' b : P}
    (ha : a = x ∨ a = y) (ha' : a' = x ∨ a' = y) (hab : a ≼ b) :
    (b = x ∨ b = y) ∨ a' ≼ b := by
  refine (Classical.em (b = x ∨ b = y)).imp id fun hb => ?_
  have hbx : b ≠ x := fun e => hb (Or.inl e)
  have hby : b ≠ y := fun e => hb (Or.inr e)
  have hxb_hyb : x ≼ b ∧ y ≼ b := by
    rcases h with ⟨_, hxy, hα⟩ | ⟨_, hβ⟩
    · rcases ha with rfl | rfl
      · exact ⟨hab, hα b hab hbx⟩
      · exact ⟨Frame.le_trans hxy hab, hab⟩
    · rcases ha with rfl | rfl
      · exact ⟨hab, ((hβ b).mp ⟨hab, hbx⟩).1⟩
      · exact ⟨((hβ b).mpr ⟨hab, hby⟩).1, hab⟩
  rcases ha' with rfl | rfl
  · exact hxb_hyb.1
  · exact hxb_hyb.2

/-- **The merge of an α- or β-pair**, collapsing `x` onto `y`. -/
noncomputable def pair (x y : P) (h : IsAlpha x y ∨ IsBeta x y) : Merger P :=
  collapse (fun z => z = x ∨ z = y) y (Or.inr rfl) (pair_merges h)

/-- The pair's merge moves `x`. -/
theorem pair_g_ne {x y : P} (h : IsAlpha x y ∨ IsBeta x y) : (pair x y h).g x ≠ x := by
  have hgx : (pair x y h).g x = y := collapse_mem (N := fun z => z = x ∨ z = y) (Or.inl rfl)
  rw [hgx]
  rcases h with ⟨hne, _⟩ | ⟨hne, _⟩ <;> exact Ne.symm hne

/-- The pair's merge identifies nothing but the pair. -/
theorem pair_classes {x y : P} {h : IsAlpha x y ∨ IsBeta x y} {a b : P}
    (hab : (pair x y h).g a = (pair x y h).g b) :
    a = b ∨ ((a = x ∨ a = y) ∧ (b = x ∨ b = y)) := by
  rcases Classical.em (a = x ∨ a = y) with ha | ha
  · rcases Classical.em (b = x ∨ b = y) with hb | hb
    · exact Or.inr ⟨ha, hb⟩
    · exact Or.inl (collapse_eq_not (N := fun z => z = x ∨ z = y) hb a hab)
  · exact Or.inl (collapse_eq_not (N := fun z => z = x ∨ z = y) ha b hab.symm).symm

/-- The pair's merge identifies only what `m` does, when `m` identifies the pair. -/
theorem pair_refines {x y : P} {h : IsAlpha x y ∨ IsBeta x y} {m : Merger P}
    (hxy : m.g x = m.g y) (a b : P) (hab : (pair x y h).g a = (pair x y h).g b) :
    m.g a = m.g b := by
  rcases pair_classes hab with rfl | ⟨ha, hb⟩
  · rfl
  · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      first | rfl | exact hxy | exact hxy.symm

/-- **Merging less puts the algebra higher.**  If `m` identifies whatever `s`
does, what `m` pulls back `s` pulls back too, so `m`'s algebra embeds in
`s`'s. -/
theorem sh_of_refines (s m : Merger P) (h : ∀ a b, s.g a = s.g b → m.g a = m.g b) :
    SH (Upset m.Pt) (Upset s.Pt) := by
  have hsat : ∀ (V : Upset m.Pt) x, (m.pull V).mem x ↔ (m.pull V).mem (s.g x) := fun V x => by
    show V.mem (m.proj x) ↔ V.mem (m.proj (s.g x))
    rw [show m.proj (s.g x) = m.proj x from Pt.ext m (h _ _ (s.idem x))]
  have hpull : ∀ V, s.pull (s.lift (m.pull V) (hsat V)) = m.pull V := fun V => s.pull_lift _ _
  exact sh_of_embeds ⟨s.homOfPull m.pullHom _ hpull, fun V W hVW =>
    m.pull_injective (by rw [← hpull V, ← hpull W]; exact congrArg s.pull hVW)⟩

/-- **A merge of a finite poset that identifies anything identifies an α- or a
β-pair.**  See the module documentation for the choice of the pair. -/
theorem exists_pair (hA : Frame.Antisymm P) (l : List P) (hl : ∀ x, x ∈ l) (m : Merger P)
    (hm : ∃ x, m.g x ≠ x) : ∃ x y : P, m.g x = m.g y ∧ (IsAlpha x y ∨ IsBeta x y) := by
  obtain ⟨x₀, hx₀⟩ := hm
  -- `x`, maximal among the merged points
  obtain ⟨x, hMx, hxmax⟩ := hasMaximal_of_list l hl (fun a => ∃ b, b ≠ a ∧ m.g b = m.g a)
    ⟨x₀, m.g x₀, hx₀, m.idem x₀⟩
  have single : ∀ z, x ≼ z → z ≠ x → ∀ b, m.g b = m.g z → b = z := fun z hxz hzx b hb =>
    Classical.byContradiction fun hbz => hzx (hA _ _ (hxmax z ⟨b, hbz, hb⟩ hxz) hxz)
  -- `y`, maximal among the other points identified with `x`
  obtain ⟨y, ⟨hyx, hy⟩, hymax⟩ := hasMaximal_of_list l hl (fun b => b ≠ x ∧ m.g b = m.g x) hMx
  have strict_y : ∀ z, y ≼ z → z ≠ y → x ≼ z := fun z hyz hzy => by
    obtain ⟨z', hz', hxz'⟩ := m.bisim (x := y) (x' := x) hy hyz
    rcases Classical.em (z' = x) with hz'x | hz'x
    · -- `z` is identified with `x`, so it is `x`, `y` being maximal among the others
      have hzx : m.g z = m.g x := hz'.symm.trans (congrArg m.g hz'x)
      rcases Classical.em (z = x) with e | hzne
      · rw [e]; exact Frame.le_refl x
      · exact absurd (hA _ _ (hymax z ⟨hzne, hzx⟩ hyz) hyz) hzy
    · -- `z` is identified with a point strictly above `x`, so it is that point
      rw [single z' hxz' hz'x z hz'.symm]
      exact hxz'
  rcases Classical.em (y ≼ x) with hyx' | hyx'
  · -- `x` is the only immediate successor of `y`
    exact ⟨y, x, hy, Or.inl ⟨hyx, hyx', strict_y⟩⟩
  · -- `x` and `y` have the same strict successors
    refine ⟨x, y, hy.symm, Or.inr ⟨Ne.symm hyx, fun z => ⟨?_, ?_⟩⟩⟩
    · rintro ⟨hxz, hzx⟩
      obtain ⟨z', hz', hyz'⟩ := m.bisim (x := x) (x' := y) hy.symm hxz
      rw [single z hxz hzx z' hz'] at hyz'
      exact ⟨hyz', fun hzy =>
        hyx ((single z hxz hzx x (by rw [hzy]; exact hy.symm)).trans hzy).symm⟩
    · rintro ⟨hyz, hzy⟩
      exact ⟨strict_y z hyz hzy, fun hzx => hyx' (hzx ▸ hyz)⟩

/-- **Every merge of a finite poset that identifies anything factors through a
single step**: it identifies an α- or β-pair, and its algebra lies below the
algebra of merging that pair alone. -/
theorem exists_step (hA : Frame.Antisymm P) (l : List P) (hl : ∀ x, x ∈ l) (m : Merger P)
    (hm : ∃ x, m.g x ≠ x) :
    ∃ x y : P, ∃ h : IsAlpha x y ∨ IsBeta x y, SH (Upset m.Pt) (Upset (pair x y h).Pt) := by
  obtain ⟨x, y, hxy, h⟩ := exists_pair hA l hl m hm
  exact ⟨x, y, h, sh_of_refines (pair x y h) m (pair_refines hxy)⟩

/-! ## Every merge is a chain of steps

Merging an α- or β-pair leaves a poset with one point fewer (`pair_antisymm`),
on which a merge identifying the pair can be read (`after`).  Repeating the
step, a merge of a finite poset is a chain of α- and β-steps (`isChain`). -/

/-- An α- or β-pair never has `y` below `x`. -/
theorem not_le_of_pair (hA : Frame.Antisymm P) {x y : P} (h : IsAlpha x y ∨ IsBeta x y) :
    ¬ y ≼ x := by
  intro hyx
  rcases h with ⟨hne, hxy, _⟩ | ⟨hne, hβ⟩
  · exact hne (hA _ _ hxy hyx)
  · exact ((hβ x).mpr ⟨hyx, hne⟩).2 rfl

/-- **Merging a pair leaves a poset.**  In the merged frame `q` lies below `r`
when `q` lies below `r`'s point, or `r`'s point is `y` and `q` lies below `x`;
two points below each other are then equal, or put `y` below `x`. -/
theorem pair_antisymm (hA : Frame.Antisymm P) {x y : P} (h : IsAlpha x y ∨ IsBeta x y) :
    Frame.Antisymm (pair x y h).Pt := by
  have key : ∀ {q r : (pair x y h).Pt}, q ≼ r → q.pt ≼ r.pt ∨ (r.pt = y ∧ q.pt ≼ x) := by
    rintro q r ⟨w, hw, hqw⟩
    rcases Classical.em (w = x ∨ w = y) with hN | hN
    · have hwy : (pair x y h).g w = y := collapse_mem (N := fun z => z = x ∨ z = y) hN
      have hry : r.pt = y := hw.symm.trans hwy
      rcases hN with hwx | hwy'
      · exact Or.inr ⟨hry, hwx ▸ hqw⟩
      · exact Or.inl ((hwy'.trans hry.symm) ▸ hqw)
    · have hww : (pair x y h).g w = w := collapse_not (N := fun z => z = x ∨ z = y) hN
      exact Or.inl (by rw [← hw, hww]; exact hqw)
  have hyx := not_le_of_pair hA h
  intro q r hqr hrq
  apply Pt.ext (pair x y h)
  rcases key hqr with h₁ | ⟨h₁, h₁'⟩ <;> rcases key hrq with h₂ | ⟨h₂, h₂'⟩
  · exact hA _ _ h₁ h₂
  · exact absurd (by rw [← h₂]; exact Frame.le_trans h₁ h₂') hyx
  · exact absurd (by rw [← h₁]; exact Frame.le_trans h₂ h₁') hyx
  · exact h₂.trans h₁.symm

/-- **A merge identifying a pair, read after merging the pair.** -/
noncomputable def after (m : Merger P) {x y : P} (h : IsAlpha x y ∨ IsBeta x y)
    (hxy : m.g x = m.g y) : Merger (pair x y h).Pt where
  g q := (pair x y h).proj (m.g q.pt)
  idem q := by
    show (pair x y h).proj (m.g ((pair x y h).g (m.g q.pt))) = (pair x y h).proj (m.g q.pt)
    rw [pair_refines hxy _ _ ((pair x y h).idem _), m.idem]
  bisim {q q₁ r} hqq hqr := by
    have hm : m.g q.pt = m.g q₁.pt := by
      have := pair_refines (h := h) hxy _ _ (congrArg Pt.pt hqq)
      rwa [m.idem, m.idem] at this
    obtain ⟨w, hw, hqw⟩ := hqr
    obtain ⟨w', hw', hqw'⟩ := m.bisim hm hqw
    refine ⟨(pair x y h).proj w', ?_, w', rfl, hqw'⟩
    show (pair x y h).proj (m.g ((pair x y h).g w')) = (pair x y h).proj (m.g r.pt)
    rw [← hw, pair_refines hxy _ _ ((pair x y h).idem w'),
      pair_refines hxy _ _ ((pair x y h).idem w), hw']

/-- `after` identifies exactly what `m` does. -/
theorem after_classes (m : Merger P) {x y : P} (h : IsAlpha x y ∨ IsBeta x y)
    (hxy : m.g x = m.g y) (a b : P) :
    m.g a = m.g b ↔
      (m.after h hxy).g ((pair x y h).proj a) = (m.after h hxy).g ((pair x y h).proj b) := by
  show m.g a = m.g b ↔ (pair x y h).proj (m.g ((pair x y h).g a)) =
    (pair x y h).proj (m.g ((pair x y h).g b))
  rw [pair_refines hxy _ _ ((pair x y h).idem a), pair_refines hxy _ _ ((pair x y h).idem b)]
  refine ⟨fun e => by rw [e], fun e => ?_⟩
  have := pair_refines (h := h) hxy _ _ (congrArg Pt.pt e)
  rwa [m.idem, m.idem] at this

/-- **A chain of α- and β-steps.**  A merge that identifies nothing; or one that
merges an α- or β-pair first and then, on the result, merges by such a chain,
the two together identifying exactly what it does. -/
inductive IsChain : {P : Type} → [Frame P] → Merger P → Prop
  | nil {P : Type} [Frame P] {m : Merger P} : (∀ x, m.g x = x) → IsChain m
  | cons {P : Type} [Frame P] {m : Merger P} {x y : P} (h : IsAlpha x y ∨ IsBeta x y)
      {m' : Merger (pair x y h).Pt} :
      (∀ a b, m.g a = m.g b ↔ m'.g ((pair x y h).proj a) = m'.g ((pair x y h).proj b)) →
      IsChain m' → IsChain m

/-- Every merge of a poset with at most `n` points is a chain of steps. -/
theorem isChain_of_length (n : Nat) : ∀ {P : Type} [Frame P], Frame.Antisymm P →
    ∀ l : List P, (∀ x, x ∈ l) → l.length ≤ n → ∀ m : Merger P, IsChain m := by
  induction n with
  | zero =>
    intro P _ _ l hl hn m
    have hnil : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)
    exact .nil fun x => by have := hl x; rw [hnil] at this; exact nomatch this
  | succ n ih =>
    intro P _ hA l hl hn m
    rcases Classical.em (∀ x, m.g x = x) with hfix | hfix
    · exact .nil hfix
    have hm : ∃ x, m.g x ≠ x :=
      Classical.byContradiction fun hc =>
        hfix fun x => Classical.byContradiction fun hx => hc ⟨x, hx⟩
    obtain ⟨x, y, hxy, h⟩ := exists_pair hA l hl m hm
    have hlen : ((pair x y h).cover l).length ≤ n :=
      Nat.le_of_lt_succ (Nat.lt_of_lt_of_le ((pair x y h).length_cover_lt (hl x) (pair_g_ne h)) hn)
    exact .cons h (after_classes m h hxy)
      (ih (pair_antisymm hA h) _ ((pair x y h).mem_cover hl) hlen (m.after h hxy))

/-- **Every merge of a finite poset is a chain of α- and β-steps.** -/
theorem isChain (hA : Frame.Antisymm P) (l : List P) (hl : ∀ x, x ∈ l) (m : Merger P) :
    IsChain m :=
  isChain_of_length l.length hA l hl (Nat.le_refl _) m

end Merger

/-! ## Minimal refuters, one step at a time

What lies below the algebra of a finite poset is a subalgebra of a homomorphic
image.  An image identifying anything is the algebra of the points of an upward
closed set short of everything (`Within.exists_iso_of_onto`); one identifying
nothing is the algebra itself, whose subalgebras come from merges
(`Merger.exists_iso_of_hom`), and a merge identifying anything lies below a
single α- or β-step (`Merger.exists_step`).  Both shrinkings lose points, so by
counting (`length_le_of_sh`) the algebra is a minimal refuter of a formula
exactly when the formula holds on the points of every proper upward closed set
and after every α- and β-step (`refuterLB_iff_steps`), a condition on the frame
alone. -/

/-- **A finite poset's algebra is a minimal refuter exactly when no single step
down refutes.**  The steps are passing to the points of a proper upward closed
set, and merging an α- or β-pair. -/
theorem refuterLB_iff_steps (hA : Frame.Antisymm P) (l : List P) (hl : ∀ x, x ∈ l)
    (p : Form) :
    RefuterLB (Upset P) p ↔
      (∀ U : Upset P, U ≠ ⊤ → ∀ v : Nat → Upset (Within U), p.eval v = ⊤) ∧
      ∀ (x y : P) (h : IsAlpha x y ∨ IsBeta x y), ∀ v : Nat → Upset (Merger.pair x y h).Pt,
        p.eval v = ⊤ := by
  obtain ⟨l', hnd, hl'⟩ : ∃ l' : List P, l'.Nodup ∧ ∀ x, x ∈ l' := by
    obtain ⟨l', hnd, hmem⟩ := ListCount.exists_nodup l
    exact ⟨l', hnd, fun x => (hmem x).mpr (hl x)⟩
  constructor
  · -- a smaller frame refuting the formula would put the algebra below itself
    intro hLB
    have small : ∀ {Q : Type} [Frame Q] {lQ : List Q}, (∀ q, q ∈ lQ) →
        lQ.length < l'.length → SH (Upset Q) (Upset P) → ∀ v : Nat → Upset Q, p.eval v = ⊤ :=
      fun hlQ hlt hsh => Classical.byContradiction fun hv => absurd
        (length_le_of_sh hA hnd hl' hlQ (hLB _ inferInstance hsh hv)) (Nat.not_le.mpr hlt)
    refine ⟨fun U hU => small (Within.mem_cover hl') ?_ (Within.sh U), fun x y h =>
      small (Merger.mem_cover _ hl') (Merger.length_cover_lt _ (hl' x) (Merger.pair_g_ne h))
        (Merger.pair x y h).sh⟩
    obtain ⟨z, hz⟩ : ∃ z, ¬ U.mem z := Classical.byContradiction fun hc =>
      hU (Upset.ext fun z => ⟨fun _ => trivial, fun _ =>
        Classical.byContradiction fun hz => hc ⟨z, hz⟩⟩)
    exact Within.length_cover_lt (hl' z) hz
  · rintro ⟨hU, hstep⟩ γ iγ ⟨δ, iδ, ⟨f, hf⟩, ⟨g, hg⟩⟩ hnv
    by_cases hinj : Function.Injective f.toFun
    · -- `γ` is a subalgebra of the algebra itself, the algebra of a merge
      obtain ⟨e₀, he₀⟩ := embeds_of_iso f hinj hf g hg
      obtain ⟨m, e, he⟩ := Merger.exists_iso_of_hom l hl e₀ he₀
      by_cases hm : ∃ x, m.g x ≠ x
      · obtain ⟨x, y, h, hsh⟩ := Merger.exists_step hA l hl m hm
        exact absurd (valid_of_sh (sh_of_embeds ⟨e, he.1⟩) (valid_of_sh hsh (hstep x y h))) hnv
      · -- a merge identifying nothing gives the algebra back
        have hfix : ∀ x, m.g x = x := fun x => Classical.byContradiction fun hx => hm ⟨x, hx⟩
        refine sh_of_bijective (m.pullHom.comp e) ⟨fun _ _ hab => he.1 (m.pull_injective hab),
          fun U => ?_⟩
        obtain ⟨V, hV⟩ := (m.pulled_iff U).mpr fun x => by rw [hfix x]
        obtain ⟨a, ha⟩ := he.2 V
        exact ⟨a, show m.pull (e.toFun a) = U by rw [ha, hV]⟩
    · -- `δ` identifies something: the points of a proper upward closed set
      obtain ⟨e, he⟩ := Within.exists_iso_of_onto l hl f hf
      exact absurd (valid_of_embeds ⟨g, hg⟩ (valid_of_sh (sh_of_embeds ⟨e, he.1⟩)
        (hU _ fun hK => hinj (Upset.injective_of_ker l hl f hK)))) hnv
