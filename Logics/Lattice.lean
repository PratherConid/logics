/-!
# Partial orders, lattices and bounded lattices

A small self-contained order theoretic hierarchy, `PartialOrder → Lattice →
BoundedLattice`, together with the usual identities: the universal properties of
`⊓` and `⊔`, idempotence, commutativity, associativity, monotonicity, the two
absorption laws, and the behaviour of the bounds.

The order is written `⊑` rather than `≤` so that a carrier type may keep its own
`LE` instance.

Nothing here depends on Mathlib.
-/

universe u

/-! ## Partial orders -/

/-- A reflexive, transitive, antisymmetric relation. -/
class PartialOrder (α : Type u) where
  le : α → α → Prop
  le_refl (a : α) : le a a
  le_trans {a b c : α} : le a b → le b c → le a c
  le_antisymm {a b : α} : le a b → le b a → a = b

infix:50 " ⊑ " => PartialOrder.le

namespace PartialOrder

variable {α : Type u} [PartialOrder α]

theorem le_of_eq {a b : α} (h : a = b) : a ⊑ b := h ▸ le_refl a

theorem le_rfl {a : α} : a ⊑ a := le_refl a

end PartialOrder

/-! ## Lattices -/

open PartialOrder

/-- A partial order with binary meets and joins. -/
class Lattice (α : Type u) extends PartialOrder α where
  inf : α → α → α
  sup : α → α → α
  inf_le_left (a b : α) : le (inf a b) a
  inf_le_right (a b : α) : le (inf a b) b
  le_inf {a b c : α} : le a b → le a c → le a (inf b c)
  le_sup_left (a b : α) : le a (sup a b)
  le_sup_right (a b : α) : le b (sup a b)
  sup_le {a b c : α} : le a c → le b c → le (sup a b) c

infixl:68 " ⊓ " => Lattice.inf
infixl:65 " ⊔ " => Lattice.sup

namespace Lattice

export PartialOrder (le_refl le_trans le_antisymm le_rfl le_of_eq)

variable {α : Type u} [Lattice α] (a b c : α)

/-! ### Meets -/

theorem le_inf_iff {a b c : α} : a ⊑ b ⊓ c ↔ a ⊑ b ∧ a ⊑ c :=
  ⟨fun h => ⟨le_trans h (inf_le_left b c), le_trans h (inf_le_right b c)⟩,
   fun h => le_inf h.1 h.2⟩

theorem inf_idem : a ⊓ a = a :=
  le_antisymm (inf_le_left a a) (le_inf le_rfl le_rfl)

theorem inf_comm : a ⊓ b = b ⊓ a :=
  le_antisymm
    (le_inf (inf_le_right a b) (inf_le_left a b))
    (le_inf (inf_le_right b a) (inf_le_left b a))

theorem inf_assoc : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) := by
  refine le_antisymm (le_inf ?_ ?_) (le_inf (le_inf ?_ ?_) ?_)
  · exact le_trans (inf_le_left _ c) (inf_le_left a b)
  · exact le_inf (le_trans (inf_le_left _ c) (inf_le_right a b)) (inf_le_right _ c)
  · exact inf_le_left a _
  · exact le_trans (inf_le_right a _) (inf_le_left b c)
  · exact le_trans (inf_le_right a _) (inf_le_right b c)

theorem inf_le_inf {a b c d : α} (h₁ : a ⊑ c) (h₂ : b ⊑ d) : a ⊓ b ⊑ c ⊓ d :=
  le_inf (le_trans (inf_le_left a b) h₁) (le_trans (inf_le_right a b) h₂)

theorem inf_eq_left_iff {a b : α} : a ⊓ b = a ↔ a ⊑ b :=
  ⟨fun h => h ▸ inf_le_right a b, fun h => le_antisymm (inf_le_left a b) (le_inf le_rfl h)⟩

/-! ### Joins -/

theorem sup_le_iff {a b c : α} : a ⊔ b ⊑ c ↔ a ⊑ c ∧ b ⊑ c :=
  ⟨fun h => ⟨le_trans (le_sup_left a b) h, le_trans (le_sup_right a b) h⟩,
   fun h => sup_le h.1 h.2⟩

theorem sup_idem : a ⊔ a = a :=
  le_antisymm (sup_le le_rfl le_rfl) (le_sup_left a a)

theorem sup_comm : a ⊔ b = b ⊔ a :=
  le_antisymm
    (sup_le (le_sup_right b a) (le_sup_left b a))
    (sup_le (le_sup_right a b) (le_sup_left a b))

theorem sup_assoc : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  refine le_antisymm (sup_le (sup_le ?_ ?_) ?_) (sup_le ?_ (sup_le ?_ ?_))
  · exact le_sup_left a _
  · exact le_trans (le_sup_left b c) (le_sup_right a _)
  · exact le_trans (le_sup_right b c) (le_sup_right a _)
  · exact le_trans (le_sup_left a b) (le_sup_left _ c)
  · exact le_trans (le_sup_right a b) (le_sup_left _ c)
  · exact le_sup_right _ c

theorem sup_le_sup {a b c d : α} (h₁ : a ⊑ c) (h₂ : b ⊑ d) : a ⊔ b ⊑ c ⊔ d :=
  sup_le (le_trans h₁ (le_sup_left c d)) (le_trans h₂ (le_sup_right c d))

theorem sup_eq_right_iff {a b : α} : a ⊔ b = b ↔ a ⊑ b :=
  ⟨fun h => h ▸ le_sup_left a b, fun h => le_antisymm (sup_le h le_rfl) (le_sup_right a b)⟩

/-! ### Absorption -/

theorem inf_sup_self : a ⊓ (a ⊔ b) = a :=
  le_antisymm (inf_le_left _ _) (le_inf le_rfl (le_sup_left a b))

theorem sup_inf_self : a ⊔ a ⊓ b = a :=
  le_antisymm (sup_le le_rfl (inf_le_left a b)) (le_sup_left _ _)

end Lattice

/-! ## Bounded lattices -/

open Lattice

/-- A lattice with a greatest and a least element. -/
class BoundedLattice (α : Type u) extends Lattice α where
  top : α
  bot : α
  le_top (a : α) : le a top
  bot_le (a : α) : le bot a

notation "⊤" => BoundedLattice.top
notation "⊥" => BoundedLattice.bot

namespace BoundedLattice

variable {α : Type u} [BoundedLattice α] (a : α)

theorem eq_top_iff : a = ⊤ ↔ (⊤ : α) ⊑ a :=
  ⟨fun h => h ▸ le_rfl, fun h => le_antisymm (le_top a) h⟩

theorem eq_bot_iff : a = ⊥ ↔ a ⊑ (⊥ : α) :=
  ⟨fun h => h ▸ le_rfl, fun h => le_antisymm h (bot_le a)⟩

theorem inf_top : a ⊓ ⊤ = a := inf_eq_left_iff.mpr (le_top a)

theorem top_inf : ⊤ ⊓ a = a := by rw [inf_comm]; exact inf_top a

theorem sup_bot : a ⊔ ⊥ = a := by
  rw [sup_comm]; exact sup_eq_right_iff.mpr (bot_le a)

theorem bot_sup : ⊥ ⊔ a = a := sup_eq_right_iff.mpr (bot_le a)

theorem inf_bot : a ⊓ ⊥ = ⊥ := (eq_bot_iff _).mpr (inf_le_right a ⊥)

theorem sup_top : a ⊔ ⊤ = ⊤ := (eq_top_iff _).mpr (le_sup_right a ⊤)

theorem top_sup : (⊤ : α) ⊔ a = ⊤ := by rw [sup_comm]; exact sup_top a

end BoundedLattice

/-! ## Distributive lattices

A lattice is distributive when meet distributes over join.  One inequality is
enough, the other holding in every lattice.  Being distributive is a property of
a lattice rather than more structure on it, so it is a class of propositions
over `Lattice`. -/

/-- Meet distributes over join. -/
class Distrib (α : Type u) [Lattice α] : Prop where
  inf_sup_le : ∀ a b c : α, a ⊓ (b ⊔ c) ⊑ (a ⊓ b) ⊔ (a ⊓ c)

/-! ## Products

Two orders side by side, compared componentwise.  Nothing here is specific to
this development; the product of partial orders is a partial order, and meets,
joins and bounds are all taken in each component separately. -/

namespace HProd

variable {α β : Type u}

instance [PartialOrder α] [PartialOrder β] : PartialOrder (α × β) where
  le p q := p.1 ⊑ q.1 ∧ p.2 ⊑ q.2
  le_refl _ := ⟨PartialOrder.le_rfl, PartialOrder.le_rfl⟩
  le_trans h₁ h₂ :=
    ⟨PartialOrder.le_trans h₁.1 h₂.1, PartialOrder.le_trans h₁.2 h₂.2⟩
  le_antisymm h₁ h₂ :=
    Prod.ext (PartialOrder.le_antisymm h₁.1 h₂.1) (PartialOrder.le_antisymm h₁.2 h₂.2)

/-- The order on a product is decidable when each component's is.  Instance
resolution cannot see this for itself, since `⊑` is a class field. -/
instance decLe [PartialOrder α] [PartialOrder β]
    [∀ a b : α, Decidable (a ⊑ b)] [∀ a b : β, Decidable (a ⊑ b)]
    (p q : α × β) : Decidable (p ⊑ q) :=
  inferInstanceAs (Decidable (p.1 ⊑ q.1 ∧ p.2 ⊑ q.2))

instance [Lattice α] [Lattice β] : Lattice (α × β) where
  inf p q := (p.1 ⊓ q.1, p.2 ⊓ q.2)
  sup p q := (p.1 ⊔ q.1, p.2 ⊔ q.2)
  inf_le_left _ _ := ⟨Lattice.inf_le_left _ _, Lattice.inf_le_left _ _⟩
  inf_le_right _ _ := ⟨Lattice.inf_le_right _ _, Lattice.inf_le_right _ _⟩
  le_inf h₁ h₂ := ⟨Lattice.le_inf h₁.1 h₂.1, Lattice.le_inf h₁.2 h₂.2⟩
  le_sup_left _ _ := ⟨Lattice.le_sup_left _ _, Lattice.le_sup_left _ _⟩
  le_sup_right _ _ := ⟨Lattice.le_sup_right _ _, Lattice.le_sup_right _ _⟩
  sup_le h₁ h₂ := ⟨Lattice.sup_le h₁.1 h₂.1, Lattice.sup_le h₁.2 h₂.2⟩

instance [BoundedLattice α] [BoundedLattice β] : BoundedLattice (α × β) where
  top := (⊤, ⊤)
  bot := (⊥, ⊥)
  le_top _ := ⟨BoundedLattice.le_top _, BoundedLattice.le_top _⟩
  bot_le _ := ⟨BoundedLattice.bot_le _, BoundedLattice.bot_le _⟩

/-- Deciding a property of every pair, one component at a time. -/
instance (p : α × β → Prop) [DecidablePred p]
    [Decidable (∀ a : α, ∀ b : β, p (a, b))] : Decidable (∀ x : α × β, p x) :=
  if h : ∀ a : α, ∀ b : β, p (a, b) then
    isTrue (fun x => by cases x; exact h _ _)
  else isFalse (fun hall => h (fun a b => hall (a, b)))

end HProd
