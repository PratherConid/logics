import Logics.Filter

/-!
# Embedding a finite algebra through its points

The elements of a finite Heyting algebra `A` whose frame has a root are the
upward closed sets of that frame, and each is the join of the principal upsets
of the points it contains: the join irreducible elements.  To embed `A` in
another algebra `B` it is enough to say where each point goes, and to send an
element to the join of the images of the points below it (`ext`).  This file
finds the conditions on those images under which that map is an embedding, and
there are few of them (`Images`).

* **Order and meets.**  Comparable points have comparable images, and the images
  of two incomparable points meet in the image of their meet.  Then the map
  keeps meets, by distributivity, and joins, since a point below a join lies
  below one side of it.
* **Arrows.**  For each point `k` let `co k` be the largest element not above
  it.  The image of `k`, implied into the image of `co k`, gives nothing beyond
  the image of `co k`.  Every arrow of `A` is a meet of such `co k`, so the map
  keeps arrows.
* **Injectivity.**  The coatom's image misses the top.  A homomorphism that
  identifies two elements sends the arrows between them to the top, and with
  them the coatom.

The facts these rest on about `A` itself -- every element is the join of the
points below it, points are join prime, and so on -- are recorded in `Points`;
for a concrete algebra each is a finite check.

The last section reads the conditions through formulas.  When the image of each
point is the value of a formula and each condition is a derivation under a
premise `P`, a refutation of `P → C` puts `A` below the refuting algebra
(`sh_of_refutes`).  In the quotient by the filter above `P`'s value, `P` holds
and the derivations apply, while the refutation keeps `C`, and with it the
coatom's image, below the top.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

/-- The disjunction of a list of formulas, `⊥` for the empty one. -/
def Form.disj : List Form → Form
  | [] => .fls
  | p :: ps => .or p (Form.disj ps)

theorem Form.eval_disj {α : Type u} [HeytingAlgebra α] (v : Nat → α) :
    ∀ ps : List Form, (Form.disj ps).eval v = supList (ps.map fun p => p.eval v)
  | [] => rfl
  | p :: ps => by
    show p.eval v ⊔ (Form.disj ps).eval v = _
    rw [Form.eval_disj v ps]
    rfl

/-- Every variable of the formula is `.var 0` or `.var 1`. -/
def Form.inTwo : Form → Bool
  | .var n => decide (n < 2)
  | .fls => true
  | .and p q | .or p q | .imp p q => p.inTwo && q.inTwo

namespace PointEmbed

/-- The valuation sending `.var 0` to `a` and every other variable to `b`. -/
def valPair {α : Type u} (a b : α) : Nat → α := fun n => if n = 0 then a else b

/-- A formula in `.var 0` and `.var 1` sees a valuation only through those two
values. -/
theorem eval_pair {α : Type u} [HeytingAlgebra α] (v : Nat → α) :
    ∀ {p : Form}, p.inTwo = true → p.eval v = p.eval (valPair (v 0) (v 1))
  | .var n, h => by
    simp only [Form.inTwo, decide_eq_true_eq] at h
    rcases n with _ | _ | n
    · rfl
    · rfl
    · omega
  | .fls, _ => rfl
  | .and p q, h => by
    simp only [Form.inTwo, Bool.and_eq_true] at h
    show p.eval v ⊓ q.eval v = p.eval _ ⊓ q.eval _
    rw [eval_pair v h.1, eval_pair v h.2]
  | .or p q, h => by
    simp only [Form.inTwo, Bool.and_eq_true] at h
    show p.eval v ⊔ q.eval v = p.eval _ ⊔ q.eval _
    rw [eval_pair v h.1, eval_pair v h.2]
  | .imp p q, h => by
    simp only [Form.inTwo, Bool.and_eq_true] at h
    show (p.eval v ⇨ q.eval v) = (p.eval _ ⇨ q.eval _)
    rw [eval_pair v h.1, eval_pair v h.2]

/-- **A refuter with a coatom is minimal once every refutation in it generates
it**: at each refuting pair every element is the value of one of the formulas
`ts`.  For a formula in two variables, and a concrete algebra, every hypothesis
is a finite check. -/
theorem refuterLB_of_generates {A : Type} [HeytingAlgebra A] {p : Form} {c : A}
    (ts : List Form) (hp2 : p.inTwo = true) (hts : ∀ t ∈ ts, t.inTwo = true)
    (hc : ∀ x : A, x ≠ ⊤ → x ⊑ c) (hp : ∀ a b : A, c ⊑ p.eval (valPair a b))
    (hgen : ∀ a b : A, p.eval (valPair a b) ≠ ⊤ → ∀ z : A, ∃ t ∈ ts, z = t.eval (valPair a b)) :
    RefuterLB A p := by
  refine refuterLB_of_coatom hc (fun v => by rw [eval_pair v hp2]; exact hp _ _) ?_
  intro γ _ h _ v hv z
  rw [eval_pair _ hp2] at hv
  obtain ⟨t, ht, hz⟩ := hgen _ _ hv z
  refine ⟨t.eval (valPair (v 0) (v 1)), ?_⟩
  rw [hz, ← h.eval, eval_pair _ (hts t ht)]
  rfl

variable {A : Type} [HeytingAlgebra A] [∀ x y : A, Decidable (x ⊑ y)]

/-- The points of `J` below an element. -/
def below (J : List A) (a : A) : List A := J.filter fun j => decide (j ⊑ a)

theorem mem_below {J : List A} {a j : A} : j ∈ below J a ↔ j ∈ J ∧ j ⊑ a := by
  simp [below]

/-- A finite Heyting algebra presented by its points.  `J` lists the join
irreducible elements, `co j` is the largest element not above `j`, and `c` is
the coatom.  For a concrete algebra every field is a finite check. -/
structure Points (A : Type) [HeytingAlgebra A] [∀ x y : A, Decidable (x ⊑ y)] where
  J : List A
  co : A → A
  c : A
  top_mem : ⊤ ∈ J
  not_le_bot : ∀ j ∈ J, ¬ j ⊑ ⊥
  le_supList : ∀ a : A, a ⊑ supList (below J a)
  prime : ∀ j ∈ J, ∀ a b : A, j ⊑ a ⊔ b → j ⊑ a ∨ j ⊑ b
  le_co : ∀ j ∈ J, ∀ a : A, ¬ j ⊑ a → a ⊑ co j
  infList_le_himp : ∀ a b : A,
    infList ((J.filter fun k => decide (k ⊑ a ∧ ¬ k ⊑ b)).map co) ⊑ (a ⇨ b)
  le_coatom : ∀ x : A, x ≠ ⊤ → x ⊑ c

variable {B : Type} [HeytingAlgebra B]

/-- The candidate embedding: an element goes to the join of the images of the
points below it. -/
def ext (J : List A) (g : A → B) (a : A) : B := supList ((below J a).map g)

/-- What the images of the points must satisfy. -/
structure Images (S : Points A) (g : A → B) : Prop where
  top : g ⊤ = ⊤
  mono : ∀ j ∈ S.J, ∀ k ∈ S.J, j ⊑ k → j ≠ k → k ≠ ⊤ → g j ⊑ g k
  meet : ∀ j ∈ S.J, ∀ k ∈ S.J, ¬ j ⊑ k → ¬ k ⊑ j → g j ⊓ g k ⊑ ext S.J g (j ⊓ k)
  arrow : ∀ k ∈ S.J, k ≠ ⊤ → (g k ⇨ ext S.J g (S.co k)) ⊑ ext S.J g (S.co k)

variable {S : Points A} {g : A → B}

theorem g_le_ext {j a : A} (hj : j ∈ S.J) (h : j ⊑ a) : g j ⊑ ext S.J g a :=
  le_supList (List.mem_map.mpr ⟨j, mem_below.mpr ⟨hj, h⟩, rfl⟩)

theorem ext_mono {a b : A} (h : a ⊑ b) : ext S.J g a ⊑ ext S.J g b :=
  supList_le fun x hx => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hjJ, hja⟩ := mem_below.mp hj
    exact g_le_ext hjJ (le_trans hja h)

theorem ext_of_mem (hg : Images S g) {j : A} (hj : j ∈ S.J) : ext S.J g j = g j := by
  refine le_antisymm (supList_le fun x hx => ?_) (g_le_ext hj le_rfl)
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hkJ, hkj⟩ := mem_below.mp hk
  by_cases hkeq : k = j
  · rw [hkeq]; exact le_rfl
  by_cases hjt : j = ⊤
  · rw [hjt, hg.top]; exact le_top _
  exact hg.mono k hkJ j hj hkj hkeq hjt

theorem ext_bot : ext S.J g (⊥ : A) = ⊥ :=
  (eq_bot_iff _).mpr (supList_le fun x hx => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hjJ, hjb⟩ := mem_below.mp hj
    exact absurd hjb (S.not_le_bot j hjJ))

theorem ext_top (hg : Images S g) : ext S.J g (⊤ : A) = ⊤ :=
  (eq_top_iff _).mpr (le_trans (le_of_eq hg.top.symm) (g_le_ext S.top_mem le_rfl))

theorem ext_sup (a b : A) : ext S.J g (a ⊔ b) = ext S.J g a ⊔ ext S.J g b := by
  refine le_antisymm (supList_le fun x hx => ?_)
    (sup_le (ext_mono (le_sup_left a b)) (ext_mono (le_sup_right a b)))
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hjJ, hjab⟩ := mem_below.mp hj
  rcases S.prime j hjJ a b hjab with h | h
  · exact le_trans (g_le_ext hjJ h) (le_sup_left _ _)
  · exact le_trans (g_le_ext hjJ h) (le_sup_right _ _)

/-- The meet condition for every pair of points, comparable ones included. -/
theorem meet_le (hg : Images S g) {j k : A} (hj : j ∈ S.J) (hk : k ∈ S.J) :
    g j ⊓ g k ⊑ ext S.J g (j ⊓ k) := by
  by_cases hjk : j ⊑ k
  · rw [inf_eq_left_iff.mpr hjk]
    exact le_trans (inf_le_left _ _) (g_le_ext hj le_rfl)
  by_cases hkj : k ⊑ j
  · have h : j ⊓ k = k := by rw [inf_comm]; exact inf_eq_left_iff.mpr hkj
    rw [h]
    exact le_trans (inf_le_right _ _) (g_le_ext hk le_rfl)
  exact hg.meet j hj k hk hjk hkj

theorem ext_inf (hg : Images S g) (a b : A) :
    ext S.J g (a ⊓ b) = ext S.J g a ⊓ ext S.J g b := by
  refine le_antisymm (le_inf (ext_mono (inf_le_left a b)) (ext_mono (inf_le_right a b))) ?_
  refine supList_inf_supList_le fun x hx y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
  obtain ⟨hjJ, hja⟩ := mem_below.mp hj
  obtain ⟨hkJ, hkb⟩ := mem_below.mp hk
  exact le_trans (meet_le hg hjJ hkJ) (ext_mono (inf_le_inf hja hkb))

theorem ext_infList (hg : Images S g) :
    ∀ L : List A, ext S.J g (infList L) = infList (L.map (ext S.J g))
  | [] => ext_top hg
  | x :: L => by
    show ext S.J g (x ⊓ infList L) = _
    rw [ext_inf hg, ext_infList hg L]
    rfl

theorem ext_himp (hg : Images S g) (a b : A) :
    ext S.J g (a ⇨ b) = (ext S.J g a ⇨ ext S.J g b) := by
  refine le_antisymm (le_himp_of_inf_le ?_) ?_
  · rw [← ext_inf hg]
    exact ext_mono (himp_inf_le a b)
  refine le_trans ?_ (ext_mono (S.infList_le_himp a b))
  rw [ext_infList hg]
  refine le_infList fun y hy => ?_
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
  simp only [List.mem_filter, decide_eq_true_eq] at hk
  obtain ⟨hkJ, hka, hkb⟩ := hk
  have h₁ : (ext S.J g a ⇨ ext S.J g b) ⊑ (g k ⇨ ext S.J g (S.co k)) :=
    le_trans (himp_le_himp_left (g_le_ext hkJ hka))
      (le_himp_of_inf_le (le_trans (himp_inf_le _ _) (ext_mono (S.le_co k hkJ b hkb))))
  refine le_trans h₁ ?_
  by_cases hkt : k = ⊤
  · rw [hkt, hg.top, himp_top_left]; exact le_rfl
  exact hg.arrow k hkJ hkt

/-- The map, as a homomorphism. -/
def hom (hg : Images S g) : Hom A B where
  toFun := ext S.J g
  map_bot := ext_bot
  map_top := ext_top hg
  map_inf := ext_inf hg
  map_sup := ext_sup
  map_himp := ext_himp hg

/-- **It is injective once the coatom's image misses the top.** -/
theorem injective (hg : Images S g) (hc : ext S.J g S.c ≠ ⊤) :
    Function.Injective (ext S.J g) := by
  intro x y hxy
  refine eq_of_himp_inf_eq_top (Classical.byContradiction fun hne => hc ?_)
  have h : ext S.J g ((x ⇨ y) ⊓ (y ⇨ x)) = ⊤ := by
    rw [ext_inf hg, ext_himp hg, ext_himp hg, hxy, himp_eq_top_of_le le_rfl, inf_top]
  exact (eq_top_iff _).mpr (le_trans (le_of_eq h.symm) (ext_mono (S.le_coatom _ hne)))

/-- **The images of the points embed `A`.** -/
theorem embeds (hg : Images S g) (hc : ext S.J g S.c ≠ ⊤) : Embeds A B :=
  ⟨hom hg, injective hg hc⟩

/-! ## Through formulas -/

/-- An inequality from a derivation, under a premise that holds. -/
theorem le_of_derives {w : Nat → B} {P X Y : Form} (hP : P.eval w = ⊤)
    (d : [X, P] ⊢ Y) : X.eval w ⊑ Y.eval w := by
  have h := Derives.soundness w d
  simp only [evalCtx, hP, inf_top] at h
  exact h

/-- **A refutation of `P → C` puts `A` below the refuting algebra**, when the
images of the points are the values of formulas `T` and every condition is a
derivation under `P`, the coatom's image deriving `C`. -/
theorem sh_of_refutes (S : Points A) (T : A → Form) {P C : Form}
    (htop : [P] ⊢ T ⊤)
    (hmono : ∀ j ∈ S.J, ∀ k ∈ S.J, j ⊑ k → j ≠ k → k ≠ ⊤ → [T j, P] ⊢ T k)
    (hmeet : ∀ j ∈ S.J, ∀ k ∈ S.J, ¬ j ⊑ k → ¬ k ⊑ j →
      [.and (T j) (T k), P] ⊢ Form.disj ((below S.J (j ⊓ k)).map T))
    (harrow : ∀ k ∈ S.J, k ≠ ⊤ →
      [.imp (T k) (Form.disj ((below S.J (S.co k)).map T)), P] ⊢
        Form.disj ((below S.J (S.co k)).map T))
    (hcon : [Form.disj ((below S.J S.c).map T), P] ⊢ C)
    (v : Nat → B) (hv : (Form.imp P C).eval v ≠ ⊤) : SH A B := by
  let F := Filter.up (P.eval v)
  let w : Nat → FilterQuot F := fun n => FilterQuot.mk F (v n)
  have hw : ∀ p : Form, p.eval w = FilterQuot.mk F (p.eval v) := (FilterQuot.mkHom F).eval v
  have hP : P.eval w = ⊤ := by rw [hw]; exact (FilterQuot.mk_eq_top_iff _ _).mpr le_rfl
  let g : A → FilterQuot F := fun a => (T a).eval w
  have hext : ∀ a, ext S.J g a = (Form.disj ((below S.J a).map T)).eval w := by
    intro a
    rw [Form.eval_disj, List.map_map]
    rfl
  have hg : Images S g :=
    { top := by
        have h := Derives.soundness w htop
        simp only [evalCtx, hP, inf_top] at h
        exact (eq_top_iff _).mpr h
      mono := fun j hj k hk h₁ h₂ h₃ => le_of_derives hP (hmono j hj k hk h₁ h₂ h₃)
      meet := fun j hj k hk h₁ h₂ => by
        rw [hext]; exact le_of_derives hP (hmeet j hj k hk h₁ h₂)
      arrow := fun k hk h₁ => by
        rw [hext]; exact le_of_derives hP (harrow k hk h₁) }
  have hc : ext S.J g S.c ≠ ⊤ := by
    intro h
    have h₁ : ext S.J g S.c ⊑ C.eval w := by rw [hext]; exact le_of_derives hP hcon
    rw [h, hw] at h₁
    have h₂ := (FilterQuot.mk_eq_top_iff F _).mp ((eq_top_iff _).mpr h₁)
    exact hv (himp_eq_top_of_le h₂)
  exact ⟨FilterQuot F, inferInstance, FilterQuot.onto F, embeds hg hc⟩

end PointEmbed
