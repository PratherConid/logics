import Logics.FiniteFrame

/-!
# Birkhoff's representation theorem

**Finite distributive lattices and finite posets correspond one to one.**  A
finite distributive lattice `L` gives the poset `Pt L` of its join irreducible
elements, ordered upside down; a finite poset `P` gives the lattice `Upset P`
of its upward closed sets.  The two constructions undo each other:

* `birkhoff_lattice`: `L` is isomorphic to `Upset (Pt L)`, by `rep`, which sends
  an element to the points below it;
* `birkhoff_poset`: `P` is isomorphic to `Pt (Upset P)`, by `ptOf`, which sends
  a point to the upward closed set it generates.

So up to isomorphism every finite distributive lattice is an `Upset P`, and
every finite poset is a `Pt L`.  For a finite Heyting algebra `rep` also keeps
the arrow (`birkhoff_heyting`), so the algebra and `Upset (Pt L)` lie below each
other in the Jankov order (`sh_upset`, `sh_of_upset`).

## Why `rep` is an isomorphism

* **Join irreducibles are join prime** (`JoinIrred.le_or_le`): a join
  irreducible below `a ⊔ b` is below `a` or below `b`.  This is the one use of
  distributivity, and it makes `rep` keep joins.
* **Every element is the join of the join irreducibles below it**
  (`le_of_irred`), so `rep` reflects the order.  This is the use of finiteness:
  by induction up the order, an element neither `⊥` nor join irreducible splits
  into two strictly smaller ones.
* **Every upward closed set of points is the set below its join**
  (`rep_surjective`), by primeness again.

## Why `ptOf` is an isomorphism

The upward closed set a point generates is join irreducible, since it holds that
point and so lies inside any upward closed set of a join containing it.
Conversely a join irreducible upward closed set lies below the join of the sets
its own points generate, so by primeness below one of them, which it therefore
equals.  Antisymmetry of the poset makes the correspondence one to one.

Finiteness is a list naming every element, as it is for frames.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

namespace Birkhoff

/-! ## Induction up a finite order -/

section Induction

variable {β : Type} [PartialOrder β]

/-- How many entries of `l` lie strictly below `a`. -/
noncomputable def rank (l : List β) (a : β) : Nat :=
  l.countP fun x => truth (x ⊑ a ∧ x ≠ a)

theorem rank_lt {l : List β} (hl : ∀ a, a ∈ l) {a b : β} (hba : b ⊑ a) (hne : b ≠ a) :
    rank l b < rank l a :=
  ListCount.countP_lt
    (fun x _ hx => by
      obtain ⟨hxb, _⟩ := truth_eq_true.mp hx
      exact truth_eq_true.mpr ⟨le_trans hxb hba, fun hxa =>
        hne (le_antisymm hba (hxa ▸ hxb))⟩)
    ⟨b, hl b, truth_eq_true.mpr ⟨hba, hne⟩, truth_eq_false.mpr fun h => h.2 rfl⟩

/-- **Strong induction up a finite order**: a property holding of each element
once it holds of everything strictly below it holds everywhere. -/
theorem induction {l : List β} (hl : ∀ a, a ∈ l) {P : β → Prop}
    (h : ∀ a, (∀ b, b ⊑ a → b ≠ a → P b) → P a) (a : β) : P a := by
  suffices H : ∀ n, ∀ a, rank l a < n → P a from H _ a (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro a ha; exact absurd ha (Nat.not_lt_zero _)
  | succ n ih =>
    intro a ha
    exact h a fun b hba hne =>
      ih b (Nat.lt_of_lt_of_le (rank_lt hl hba hne) (Nat.le_of_lt_succ ha))

end Induction

variable {α : Type} [BoundedLattice α]

/-! ## Join irreducible elements -/

/-- Nonzero, and not the join of two elements different from it. -/
def JoinIrred (j : α) : Prop := j ≠ ⊥ ∧ ∀ a b : α, a ⊔ b = j → a = j ∨ b = j

/-- **Join irreducibles are join prime.**  Below `a ⊔ b`, `j` is the join of its
meets with `a` and with `b`, and one of those must be `j` itself. -/
theorem JoinIrred.le_or_le [Distrib α] {j : α} (hj : JoinIrred j) {a b : α}
    (h : j ⊑ a ⊔ b) : j ⊑ a ∨ j ⊑ b := by
  have hle : j ⊑ (j ⊓ a) ⊔ (j ⊓ b) :=
    le_trans (le_inf le_rfl h) (Distrib.inf_sup_le j a b)
  have heq : (j ⊓ a) ⊔ (j ⊓ b) = j :=
    le_antisymm (sup_le (inf_le_left _ _) (inf_le_left _ _)) hle
  rcases hj.2 _ _ heq with h1 | h1
  · exact Or.inl (le_trans (le_of_eq h1.symm) (inf_le_right j a))
  · exact Or.inr (le_trans (le_of_eq h1.symm) (inf_le_right j b))

/-- **Every element is the join of the join irreducibles below it**: anything
above all of them is above it.  An element neither `⊥` nor join irreducible is
the join of two strictly smaller ones, which the induction covers. -/
theorem le_of_irred {l : List α} (hl : ∀ a, a ∈ l) {a x : α}
    (h : ∀ j, JoinIrred j → j ⊑ a → j ⊑ x) : a ⊑ x := by
  refine induction hl (P := fun a => ∀ x, (∀ j, JoinIrred j → j ⊑ a → j ⊑ x) → a ⊑ x)
    ?_ a x h
  intro a ih x h
  by_cases hbot : a = ⊥
  · rw [hbot]; exact bot_le x
  by_cases hirr : JoinIrred a
  · exact h a hirr le_rfl
  have hsplit : ∃ b c : α, b ⊔ c = a ∧ b ≠ a ∧ c ≠ a :=
    Classical.byContradiction fun hc => hirr ⟨hbot, fun b c hbc =>
      Classical.byContradiction fun hbc' =>
        hc ⟨b, c, hbc, fun hb => hbc' (Or.inl hb), fun hc' => hbc' (Or.inr hc')⟩⟩
  obtain ⟨b, c, hbc, hb, hc⟩ := hsplit
  have hba : b ⊑ a := hbc ▸ le_sup_left b c
  have hca : c ⊑ a := hbc ▸ le_sup_right b c
  rw [← hbc]
  exact sup_le (ih b hba hb x fun j hj hjb => h j hj (le_trans hjb hba))
    (ih c hca hc x fun j hj hjc => h j hj (le_trans hjc hca))

/-! ## Joins of lists -/

/-- A join irreducible below the join of a list lies below one of its entries. -/
theorem JoinIrred.le_supList [Distrib α] {j : α} (hj : JoinIrred j) :
    ∀ {L : List α}, j ⊑ supList L → ∃ x ∈ L, j ⊑ x
  | [], h => absurd (le_antisymm h (bot_le _)) hj.1
  | x :: t, h => by
    rcases hj.le_or_le h with hx | ht
    · exact ⟨x, List.mem_cons.mpr (Or.inl rfl), hx⟩
    · obtain ⟨y, hy, hjy⟩ := hj.le_supList ht
      exact ⟨y, List.mem_cons_of_mem x hy, hjy⟩

/-! ## From a lattice to a poset and back -/

/-- The poset of a lattice: its join irreducible elements. -/
structure Pt (α : Type) [BoundedLattice α] where
  val : α
  irred : JoinIrred val

theorem Pt.ext {j k : Pt α} (h : j.val = k.val) : j = k := by
  cases j; cases k; cases h; rfl

/-- Ordered upside down, so that the points below an element form an upward
closed set. -/
instance : Frame (Pt α) where
  le j k := k.val ⊑ j.val
  le_refl _ := le_rfl
  le_trans h₁ h₂ := le_trans h₂ h₁

theorem Pt.antisymm (j k : Pt α) (h₁ : j ≼ k) (h₂ : k ≼ j) : j = k :=
  Pt.ext (le_antisymm h₂ h₁)

/-- Finitely many points: the join irreducible entries of `l`. -/
theorem Pt.finite {l : List α} (hl : ∀ a, a ∈ l) : ∃ l' : List (Pt α), ∀ j, j ∈ l' := by
  classical
  refine ⟨l.filterMap (fun x => if h : JoinIrred x then some ⟨x, h⟩ else none),
    fun j => ?_⟩
  rw [List.mem_filterMap]
  refine ⟨j.val, hl j.val, ?_⟩
  split
  · rfl
  · exact absurd j.irred ‹_›

/-- An element read as the upward closed set of points below it. -/
def rep (a : α) : Upset (Pt α) := ⟨fun j => j.val ⊑ a, fun hjk hj => le_trans hjk hj⟩

theorem rep_bot : rep (⊥ : α) = ⊥ :=
  Upset.ext fun j => ⟨fun h => j.irred.1 (le_antisymm h (bot_le _)), fun h => h.elim⟩

theorem rep_top : rep (⊤ : α) = ⊤ := Upset.ext fun _ => ⟨fun _ => trivial, fun _ => le_top _⟩

theorem rep_inf (a b : α) : rep (a ⊓ b) = rep a ⊓ rep b :=
  Upset.ext fun _ => le_inf_iff

theorem rep_sup [Distrib α] (a b : α) : rep (a ⊔ b) = rep a ⊔ rep b :=
  Upset.ext fun j =>
    ⟨fun h => j.irred.le_or_le h,
     fun h => h.elim (fun h => le_trans h (le_sup_left _ _))
       (fun h => le_trans h (le_sup_right _ _))⟩

/-- `rep` reflects the order as well as keeping it. -/
theorem rep_le_iff {l : List α} (hl : ∀ a, a ∈ l) (a b : α) : rep a ⊑ rep b ↔ a ⊑ b :=
  ⟨fun h => le_of_irred hl fun j hj hja => h ⟨j, hj⟩ hja,
   fun h _ hja => le_trans hja h⟩

theorem rep_injective {l : List α} (hl : ∀ a, a ∈ l) :
    Function.Injective (rep : α → Upset (Pt α)) := fun a b h =>
  le_antisymm ((rep_le_iff hl a b).mp (le_of_eq h)) ((rep_le_iff hl b a).mp (le_of_eq h.symm))

/-- Every upward closed set of points is the set below its join. -/
theorem rep_surjective [Distrib α] {l : List α} (hl : ∀ a, a ∈ l) :
    Function.Surjective (rep : α → Upset (Pt α)) := by
  intro U
  refine ⟨supList (l.filter fun x => truth (∃ h : JoinIrred x, U.mem ⟨x, h⟩)),
    Upset.ext fun j => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨x, hxL, hjx⟩ := j.irred.le_supList h
    obtain ⟨hx, hU⟩ := truth_eq_true.mp (List.mem_filter.mp hxL).2
    exact U.upward (p := ⟨x, hx⟩) hjx hU
  · exact le_supList (List.mem_filter.mpr ⟨hl j.val, truth_eq_true.mpr ⟨j.irred, h⟩⟩)

/-- **Birkhoff, from the lattice side.**  A finite distributive lattice is
isomorphic to the upward closed sets of its poset of join irreducibles: `rep`
is a bijection keeping and reflecting the order, and so keeping meets, joins
and the bounds. -/
theorem birkhoff_lattice [Distrib α] {l : List α} (hl : ∀ a, a ∈ l) :
    (∃ l' : List (Pt α), ∀ j, j ∈ l') ∧ (∀ j k : Pt α, j ≼ k → k ≼ j → j = k) ∧
      Function.Injective (rep : α → Upset (Pt α)) ∧
      Function.Surjective (rep : α → Upset (Pt α)) ∧
      ∀ a b : α, rep a ⊑ rep b ↔ a ⊑ b :=
  ⟨Pt.finite hl, Pt.antisymm, rep_injective hl, rep_surjective hl, rep_le_iff hl⟩

/-! ## From a poset to a lattice and back -/

section Poset

variable {P : Type} [Frame P]

/-- The upward closed set a point generates is join irreducible: it holds the
point, so a join equal to it has a part holding the point, and that part then
holds everything the point generates. -/
theorem joinIrred_up (x : P) : JoinIrred (Upset.up x) := by
  refine ⟨fun h => ?_, fun U V hUV => ?_⟩
  · have : (⊥ : Upset P).mem x := h ▸ Frame.le_refl x
    exact this
  · have hx : (U ⊔ V).mem x := hUV ▸ Frame.le_refl x
    rcases hx with hU | hV
    · exact Or.inl (le_antisymm (hUV ▸ le_sup_left U V) fun _ hxy => U.upward hxy hU)
    · exact Or.inr (le_antisymm (hUV ▸ le_sup_right U V) fun _ hxy => V.upward hxy hV)

/-- A point read as the join irreducible it generates. -/
def ptOf (x : P) : Pt (Upset P) := ⟨Upset.up x, joinIrred_up x⟩

theorem ptOf_le_iff (x y : P) : ptOf x ≼ ptOf y ↔ x ≼ y :=
  ⟨fun h => h y (Frame.le_refl y), fun h _ hyz => Frame.le_trans h hyz⟩

theorem ptOf_injective (antisymm : Frame.Antisymm P) :
    Function.Injective (ptOf : P → Pt (Upset P)) := fun x y h =>
  antisymm x y ((ptOf_le_iff x y).mp (h ▸ Frame.le_refl _))
    ((ptOf_le_iff y x).mp (h ▸ Frame.le_refl _))

/-- Every join irreducible upward closed set is generated by one of its points:
it lies below the join of the sets its points generate, so by primeness below
one of them. -/
theorem ptOf_surjective {l : List P} (hl : ∀ x, x ∈ l) :
    Function.Surjective (ptOf : P → Pt (Upset P)) := by
  intro j
  have hle : j.val ⊑ Upset.gen l j.val.mem := le_of_eq (Upset.gen_mem hl j.val).symm
  obtain ⟨U, hUL, hjU⟩ := j.irred.le_supList hle
  obtain ⟨x, hxj, rfl⟩ := Upset.mem_of_generators hUL
  exact ⟨x, Pt.ext (le_antisymm (fun _ hxy => j.val.upward hxy hxj) hjU)⟩

/-- **Birkhoff, from the poset side.**  A finite poset is isomorphic to the poset
of join irreducibles of its lattice of upward closed sets: `ptOf` is a bijection
keeping and reflecting the order. -/
theorem birkhoff_poset (antisymm : Frame.Antisymm P)
    {l : List P} (hl : ∀ x, x ∈ l) :
    Function.Injective (ptOf : P → Pt (Upset P)) ∧
      Function.Surjective (ptOf : P → Pt (Upset P)) ∧
      ∀ x y : P, ptOf x ≼ ptOf y ↔ x ≼ y :=
  ⟨ptOf_injective antisymm, ptOf_surjective hl, ptOf_le_iff⟩

end Poset

/-! ## Heyting algebras -/

section Heyting

variable {H : Type} [HeytingAlgebra H]

/-- For a Heyting algebra `rep` also keeps the arrow: whether a point lies below
`a ⇨ b` is decided by the points below it and `a`, each element being the join
of the points below it. -/
def repHom {l : List H} (hl : ∀ a, a ∈ l) : Hom H (Upset (Pt H)) where
  toFun := rep
  map_bot := rep_bot
  map_top := rep_top
  map_inf := rep_inf
  map_sup := rep_sup
  map_himp _ _ := Upset.ext fun _ =>
    ⟨fun h _ hjk hka => le_trans (le_inf hjk hka) (inf_le_of_le_himp h),
     fun h => le_himp_of_inf_le (le_of_irred hl fun k hk hkja =>
       h ⟨k, hk⟩ (le_trans hkja (inf_le_left _ _)) (le_trans hkja (inf_le_right _ _)))⟩

/-- **Birkhoff for Heyting algebras.**  A finite Heyting algebra is isomorphic,
as a Heyting algebra, to the upward closed sets of its poset of join
irreducibles. -/
theorem birkhoff_heyting {l : List H} (hl : ∀ a, a ∈ l) :
    ∃ f : Hom H (Upset (Pt H)), Function.Injective f.toFun ∧ Function.Surjective f.toFun :=
  ⟨repHom hl, rep_injective hl, rep_surjective hl⟩

/-- So each lies below the other in the Jankov order. -/
theorem sh_upset {l : List H} (hl : ∀ a, a ∈ l) : SH (Upset (Pt H)) H :=
  sh_of_bijective (repHom hl) ⟨rep_injective hl, rep_surjective hl⟩

theorem sh_of_upset {l : List H} (hl : ∀ a, a ∈ l) : SH H (Upset (Pt H)) :=
  sh_of_bijective ((repHom hl).inv ⟨rep_injective hl, rep_surjective hl⟩)
    ⟨Hom.inv_injective _ _, fun a => ⟨rep a, rep_injective hl
      ((repHom hl).invFun_spec ⟨rep_injective hl, rep_surjective hl⟩ (rep a))⟩⟩

end Heyting

end Birkhoff
