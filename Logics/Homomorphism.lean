import Logics.Heyting

/-!
# Homomorphisms, and how validity travels

A separation argument exhibits an algebra validating one principle and refuting
another.  This file answers which algebras can serve: validity is inherited by
subalgebras and by homomorphic images, so an algebra that separates carries
smaller ones that separate too, and it is enough to look at the small ones.

The order that governs this is the one Jankov's theory uses.  Write `SH α β`
for "`α` is a subalgebra of a homomorphic image of `β`".  The main theorem,
`valid_of_sh`, says that whatever is valid in `β` is valid in `α`, so
refutation travels the other way: a refutation in `α` forces one in `β`.

Everything here is generic: nothing names a particular algebra.  The concrete
embeddings that put named algebras below others are built separately, on top of
this.
-/

open PartialOrder Lattice BoundedLattice HeytingAlgebra

/-! ## Homomorphisms -/

/-- A map preserving the Heyting operations. -/
structure Hom (α : Type u) (β : Type u) [HeytingAlgebra α] [HeytingAlgebra β] where
  toFun : α → β
  map_bot : toFun ⊥ = ⊥
  map_top : toFun ⊤ = ⊤
  map_inf : ∀ a b, toFun (a ⊓ b) = toFun a ⊓ toFun b
  map_sup : ∀ a b, toFun (a ⊔ b) = toFun a ⊔ toFun b
  map_himp : ∀ a b, toFun (a ⇨ b) = toFun a ⇨ toFun b

namespace Hom

variable {α β : Type u} [HeytingAlgebra α] [HeytingAlgebra β]

/-- Evaluation commutes with a homomorphism: pushing a valuation forward and
evaluating is the same as evaluating and pushing the value forward. -/
theorem eval (f : Hom α β) (v : Nat → α) :
    ∀ p : Form, p.eval (fun n => f.toFun (v n)) = f.toFun (p.eval v)
  | .var _ => rfl
  | .fls => f.map_bot.symm
  | .and p q => by
      show p.eval _ ⊓ q.eval _ = f.toFun (p.eval v ⊓ q.eval v)
      rw [eval f v p, eval f v q, f.map_inf]
  | .or p q => by
      show p.eval _ ⊔ q.eval _ = f.toFun (p.eval v ⊔ q.eval v)
      rw [eval f v p, eval f v q, f.map_sup]
  | .imp p q => by
      show (p.eval _ ⇨ q.eval _) = f.toFun (p.eval v ⇨ q.eval v)
      rw [eval f v p, eval f v q, f.map_himp]

end Hom

/-! ## The two ways one algebra sits inside another -/

/-- `α` embeds into `β`: it is, up to isomorphism, a subalgebra. -/
def Embeds (α β : Type u) [HeytingAlgebra α] [HeytingAlgebra β] : Prop :=
  ∃ f : Hom α β, Function.Injective f.toFun

/-- `β` maps onto `α`: `α` is a homomorphic image. -/
def Onto (α β : Type u) [HeytingAlgebra α] [HeytingAlgebra β] : Prop :=
  ∃ f : Hom β α, Function.Surjective f.toFun

/-- Validity passes to a subalgebra.  A valuation into the subalgebra is one
into the whole algebra, and an injection reflects being at the top. -/
theorem valid_of_embeds {α β : Type u} [HeytingAlgebra α] [HeytingAlgebra β]
    (h : Embeds α β) {p : Form} (hβ : ∀ v : Nat → β, p.eval v = ⊤) :
    ∀ v : Nat → α, p.eval v = ⊤ := by
  obtain ⟨f, hf⟩ := h
  intro v
  refine hf ?_
  rw [f.map_top, ← f.eval v p]
  exact hβ _

/-- Validity passes to a homomorphic image.  Every valuation into the image
lifts along the surjection. -/
theorem valid_of_onto {α β : Type u} [HeytingAlgebra α] [HeytingAlgebra β]
    (h : Onto α β) {p : Form} (hβ : ∀ v : Nat → β, p.eval v = ⊤) :
    ∀ w : Nat → α, p.eval w = ⊤ := by
  obtain ⟨f, hf⟩ := h
  intro w
  have hrep : ∀ n, ∃ b, f.toFun b = w n := fun n => hf (w n)
  have hw : w = fun n => f.toFun (Classical.choose (hrep n)) :=
    funext (fun n => (Classical.choose_spec (hrep n)).symm)
  rw [hw, f.eval, hβ, f.map_top]

/-! ## The Jankov order -/

/-- `α` is a subalgebra of a homomorphic image of `β`.  This is the order along
which Jankov's characteristic formulas classify algebras. -/
def SH (α β : Type) [iα : HeytingAlgebra α] [iβ : HeytingAlgebra β] : Prop :=
  ∃ (γ : Type) (iγ : HeytingAlgebra γ), @Onto γ β iγ iβ ∧ @Embeds α γ iα iγ

/-- **Validity travels down the Jankov order.**  Equivalently, a refutation in
`α` forces a refutation in every `β` above it, which is why a separating
algebra can always be replaced by a minimal one. -/
theorem valid_of_sh {α β : Type} [HeytingAlgebra α] [HeytingAlgebra β]
    (h : SH α β) {p : Form} (hβ : ∀ v : Nat → β, p.eval v = ⊤) :
    ∀ v : Nat → α, p.eval v = ⊤ := by
  obtain ⟨γ, iγ, hon, hem⟩ := h
  exact @valid_of_embeds α γ _ iγ hem p (@valid_of_onto γ β iγ _ hon p hβ)

/-- Contrapositive: a refutation travels up. -/
theorem exists_ne_top_of_sh {α β : Type} [HeytingAlgebra α] [HeytingAlgebra β]
    (h : SH α β) {p : Form} {v : Nat → α} (hv : p.eval v ≠ ⊤) :
    ¬ ∀ w : Nat → β, p.eval w = ⊤ := fun hβ => hv (valid_of_sh h hβ v)

/-- The identity homomorphism. -/
def Hom.id (α : Type u) [HeytingAlgebra α] : Hom α α :=
  ⟨_root_.id, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem embeds_refl (α : Type u) [HeytingAlgebra α] : Embeds α α :=
  ⟨Hom.id α, by intro x y hxy; exact hxy⟩

theorem onto_refl (α : Type u) [HeytingAlgebra α] : Onto α α :=
  ⟨Hom.id α, fun b => ⟨b, rfl⟩⟩

/-- Every algebra is trivially above itself. -/
theorem sh_refl (α : Type) [HeytingAlgebra α] : SH α α :=
  ⟨α, inferInstance, onto_refl α, embeds_refl α⟩


/-! ## Composition, monotonicity and inverses -/

namespace Hom

variable {α β γ : Type u} [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra γ]

/-- A homomorphism preserves the order. -/
theorem mono (f : Hom α β) {a b : α} (h : a ⊑ b) : f.toFun a ⊑ f.toFun b := by
  have he : f.toFun a = f.toFun a ⊓ f.toFun b := by
    rw [← f.map_inf, inf_eq_left_iff.mpr h]
  exact he ▸ inf_le_right _ _

def comp (g : Hom β γ) (f : Hom α β) : Hom α γ where
  toFun := fun a => g.toFun (f.toFun a)
  map_bot := by rw [f.map_bot, g.map_bot]
  map_top := by rw [f.map_top, g.map_top]
  map_inf a b := by rw [f.map_inf, g.map_inf]
  map_sup a b := by rw [f.map_sup, g.map_sup]
  map_himp a b := by rw [f.map_himp, g.map_himp]

/-- A homomorphism commutes with negation. -/
theorem map_neg (f : Hom α β) (a : α) : f.toFun (neg a) = neg (f.toFun a) := by
  show f.toFun (a ⇨ ⊥) = f.toFun a ⇨ ⊥
  rw [f.map_himp, f.map_bot]

noncomputable def invFun (f : Hom α β) (hf : Function.Injective f.toFun ∧ Function.Surjective f.toFun) (b : β) : α :=
  Classical.choose (hf.2 b)

theorem invFun_spec (f : Hom α β) (hf : Function.Injective f.toFun ∧ Function.Surjective f.toFun) (b : β) :
    f.toFun (f.invFun hf b) = b := Classical.choose_spec (hf.2 b)

/-- The inverse of a bijective homomorphism is one. -/
noncomputable def inv (f : Hom α β) (hf : Function.Injective f.toFun ∧ Function.Surjective f.toFun) : Hom β α where
  toFun := f.invFun hf
  map_bot := hf.1 (by rw [f.invFun_spec, f.map_bot])
  map_top := hf.1 (by rw [f.invFun_spec, f.map_top])
  map_inf a b := hf.1 (by rw [f.invFun_spec, f.map_inf, f.invFun_spec, f.invFun_spec])
  map_sup a b := hf.1 (by rw [f.invFun_spec, f.map_sup, f.invFun_spec, f.invFun_spec])
  map_himp a b := hf.1 (by rw [f.invFun_spec, f.map_himp, f.invFun_spec, f.invFun_spec])

theorem inv_injective (f : Hom α β)
    (hf : Function.Injective f.toFun ∧ Function.Surjective f.toFun) :
    Function.Injective (f.inv hf).toFun := by
  intro x y hxy
  have h2 : f.toFun (f.invFun hf x) = f.toFun (f.invFun hf y) := congrArg f.toFun hxy
  rwa [f.invFun_spec, f.invFun_spec] at h2

end Hom

/-! ## The image of a homomorphism

The values of a homomorphism are closed under the operations, so whatever is
built from values is a value again. -/

namespace Hom

variable {α β : Type u} [HeytingAlgebra α] [HeytingAlgebra β]

/-- `b` is a value of `f`. -/
def InImg (f : Hom α β) (b : β) : Prop := ∃ a, f.toFun a = b

variable {f : Hom α β}

theorem img_inf {x y : β} : f.InImg x → f.InImg y → f.InImg (x ⊓ y)
  | ⟨a, ha⟩, ⟨b, hb⟩ => ⟨a ⊓ b, by rw [f.map_inf, ha, hb]⟩

theorem img_sup {x y : β} : f.InImg x → f.InImg y → f.InImg (x ⊔ y)
  | ⟨a, ha⟩, ⟨b, hb⟩ => ⟨a ⊔ b, by rw [f.map_sup, ha, hb]⟩

theorem img_himp {x y : β} : f.InImg x → f.InImg y → f.InImg (x ⇨ y)
  | ⟨a, ha⟩, ⟨b, hb⟩ => ⟨a ⇨ b, by rw [f.map_himp, ha, hb]⟩

theorem img_bot : f.InImg ⊥ := ⟨⊥, f.map_bot⟩

theorem img_top : f.InImg ⊤ := ⟨⊤, f.map_top⟩

theorem img_neg {x : β} (h : f.InImg x) : f.InImg (neg x) := img_himp h img_bot

theorem img_supList : ∀ {L : List β}, (∀ x ∈ L, f.InImg x) → f.InImg (supList L)
  | [], _ => img_bot
  | x :: _, h => img_sup (h x (List.mem_cons.mpr (Or.inl rfl)))
      (img_supList fun y hy => h y (List.mem_cons_of_mem x hy))

end Hom

/-- An isomorphism puts each algebra below the other. -/
theorem sh_of_bijective {α β : Type} [HeytingAlgebra α] [HeytingAlgebra β]
    (f : Hom α β) (hf : Function.Injective f.toFun ∧ Function.Surjective f.toFun) : SH β α :=
  ⟨β, inferInstance, ⟨f, hf.2⟩, embeds_refl β⟩

/-- Validity need only be checked on the image of an embedding. -/
theorem valid_of_embeds_of_valid_on {α β : Type u} [HeytingAlgebra α] [HeytingAlgebra β]
    (f : Hom α β) (hf : Function.Injective f.toFun) {p : Form}
    (h : ∀ v : Nat → α, p.eval (fun n => f.toFun (v n)) = ⊤) :
    ∀ v : Nat → α, p.eval v = ⊤ := by
  intro v
  refine hf ?_
  rw [f.map_top, ← f.eval v p]
  exact h v

/-- An embedding already puts an algebra below: take the identity quotient. -/
theorem sh_of_embeds {A α : Type} [HeytingAlgebra A] [HeytingAlgebra α]
    (h : Embeds A α) : SH A α :=
  ⟨α, inferInstance, onto_refl α, h⟩

/-- A map that is not injective identifies two distinct elements. -/
theorem exists_collapse {α β : Type u} [HeytingAlgebra α] [HeytingAlgebra β]
    (f : Hom α β) (h : ¬ Function.Injective f.toFun) :
    ∃ a b : α, f.toFun a = f.toFun b ∧ a ≠ b := by
  refine Classical.byContradiction fun hne => h ?_
  intro a b hab
  exact Classical.byContradiction fun hab' => hne ⟨a, b, hab, hab'⟩

/-- A refutation survives being pushed along an embedding. -/
theorem ne_top_of_embeds {α β : Type u} [HeytingAlgebra α] [HeytingAlgebra β]
    (f : Hom α β) (hf : Function.Injective f.toFun) {p : Form} {v : Nat → α}
    (hv : p.eval v ≠ ⊤) : p.eval (fun n => f.toFun (v n)) ≠ ⊤ := by
  rw [f.eval v]
  intro hc
  exact hv (hf (by rw [hc, f.map_top]))

/-- When a quotient map is injective it is an isomorphism, so anything
embedding in the quotient already embeds in the algebra. -/
theorem embeds_of_iso {γ α β : Type u} [HeytingAlgebra γ] [HeytingAlgebra α]
    [HeytingAlgebra β] (f : Hom α β) (hinj : Function.Injective f.toFun)
    (hsurj : Function.Surjective f.toFun) (g : Hom γ β)
    (hg : Function.Injective g.toFun) : ∃ h : Hom γ α, Function.Injective h.toFun :=
  ⟨Hom.comp (f.inv ⟨hinj, hsurj⟩) g,
   fun _ _ hxy => hg (Hom.inv_injective f ⟨hinj, hsurj⟩ hxy)⟩

/-- A quotient that identifies two elements validates every formula whose
values all lie above the largest non-top element: the collapse sends that
element to the top, and so every value with it. -/
theorem valid_of_collapse {α β : Type u} [HeytingAlgebra α] [HeytingAlgebra β]
    (f : Hom α β) (hsurj : Function.Surjective f.toFun)
    {a b : α} (hab : f.toFun a = f.toFun b) (hne : a ≠ b)
    {c : α} (hc : ∀ x : α, x ≠ ⊤ → x ⊑ c)
    {p : Form} (hp : ∀ v : Nat → α, c ⊑ p.eval v) :
    ∀ w : Nat → β, p.eval w = ⊤ := by
  have hx : f.toFun ((a ⇨ b) ⊓ (b ⇨ a)) = ⊤ := by
    rw [f.map_inf, f.map_himp, f.map_himp, hab, himp_eq_top_of_le le_rfl, inf_top]
  have hxne : (a ⇨ b) ⊓ (b ⇨ a) ≠ ⊤ := by
    intro h
    have h1 : (a ⇨ b) = ⊤ := (eq_top_iff _).mpr (h ▸ inf_le_left (a ⇨ b) (b ⇨ a))
    have h2 : (b ⇨ a) = ⊤ := (eq_top_iff _).mpr (h ▸ inf_le_right (a ⇨ b) (b ⇨ a))
    exact hne (le_antisymm (le_of_himp_eq_top h1) (le_of_himp_eq_top h2))
  have hfc : f.toFun c = ⊤ :=
    (eq_top_iff _).mpr (le_trans (le_of_eq hx.symm) (f.mono (hc _ hxne)))
  intro w
  have hrep : ∀ n, ∃ x, f.toFun x = w n := fun n => hsurj (w n)
  have hw : w = fun n => f.toFun (Classical.choose (hrep n)) :=
    funext (fun n => (Classical.choose_spec (hrep n)).symm)
  rw [hw, f.eval]
  exact (eq_top_iff _).mpr (le_trans (le_of_eq hfc.symm) (f.mono (hp _)))

/-! ## Lower bounds among refuters

A separating algebra is worth more when nothing smaller would do.  `RefuterLB`
records that: anything below `A` in the order that still refutes `p` is back
above it, so `A` is minimal among the refuters of `p`.  It does not itself say
that `A` refutes `p` — that is a separate fact, and without it the property
holds vacuously. -/

def RefuterLB (A : Type) [iA : HeytingAlgebra A] (p : Form) : Prop :=
  ∀ (γ : Type) (iγ : HeytingAlgebra γ),
    @SH γ A iγ iA → (¬ ∀ v : Nat → γ, p.eval v = ⊤) → @SH A γ iA iγ

/-- **A refuter with a coatom is minimal once its refuting subalgebras are all
of it.**  Let `c` be the largest element short of the top, with `p` never
dropping below it.  A homomorphic image that merges two elements sends `c` to
the top, and `p` with it (`valid_of_collapse`).  One that merges nothing is `A`
itself, so what lies below it is a subalgebra of `A`, and a refutation there is
a refutation in `A` at values of the embedding.  It is then enough that such an
embedding is onto. -/
theorem refuterLB_of_coatom {A : Type} [HeytingAlgebra A] {p : Form} {c : A}
    (hc : ∀ x : A, x ≠ ⊤ → x ⊑ c) (hp : ∀ v : Nat → A, c ⊑ p.eval v)
    (honto : ∀ (γ : Type) [HeytingAlgebra γ] (h : Hom γ A), Function.Injective h.toFun →
      ∀ v : Nat → γ, p.eval (fun n => h.toFun (v n)) ≠ ⊤ → Function.Surjective h.toFun) :
    RefuterLB A p := by
  intro γ iγ hsh hnv
  obtain ⟨Q, iQ, ⟨f, hfs⟩, ⟨g, hgi⟩⟩ := hsh
  by_cases hinj : Function.Injective f.toFun
  · obtain ⟨h, hhi⟩ := embeds_of_iso f hinj hfs g hgi
    obtain ⟨v, hvne⟩ := exists_ne_top hnv
    exact sh_of_bijective h ⟨hhi, honto γ h hhi v (ne_top_of_embeds h hhi hvne)⟩
  · obtain ⟨a, b, hab, hne⟩ := exists_collapse f hinj
    exact absurd (valid_of_embeds ⟨g, hgi⟩ (valid_of_collapse f hfs hab hne hc hp)) hnv
