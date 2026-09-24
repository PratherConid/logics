import Logics.Heyting

/-!
# Building Heyting algebras from smaller ones

`ForkUp`, `KiteUp` and `ForkUp3` are each written out by hand, with their own
lattice and Heyting instances, although they are all the same construction
applied to different arguments.  This file supplies that construction, so that
further algebras cost a line rather than a page.

Two operations on *frames* generate all of them:

* putting two frames side by side and adding a new point **below** everything;
* putting two frames side by side and adding a new point **above** everything.

On the algebra of upward closed sets these come out simpler than they sound.
Side by side is a product, since an upset of a disjoint union is an upset of
each part independently.  A new point below everything is reachable only by the
whole frame, so it contributes exactly one new upset, sitting above all the
others: the algebra gains a **top**.  A new point above everything lies in
every nonempty upset, so the old bottom is no longer empty and a fresh empty
set appears underneath: the algebra gains a **bottom**.

So the two frame operations are `AdjoinTop (α × β)` and `AdjoinBot (α × β)`.
The product is ordinary order theory and lives with the classes it belongs to,
in `Logics/Lattice.lean` and `Logics/Heyting.lean`; this file supplies the two
adjunctions, which are not.
-/

universe u

open PartialOrder Lattice BoundedLattice HeytingAlgebra

/-! ## A new top

Adding a point below everything in the frame adds one upset, the whole frame,
above all the others. -/

/-- The algebra with one new value adjoined above all of `α`. -/
inductive AdjoinTop (α : Type u) where
  | of : α → AdjoinTop α
  | top : AdjoinTop α
  deriving DecidableEq, Repr

namespace AdjoinTop

variable {α : Type u}

instance [DecidableEq α] (p : AdjoinTop α → Prop) [DecidablePred p]
    [Decidable (∀ a : α, p (.of a))] : Decidable (∀ x, p x) :=
  if h : p .top ∧ ∀ a : α, p (.of a) then
    isTrue (by
      intro x
      cases x with
      | of a => exact h.2 a
      | top => exact h.1)
  else isFalse (fun hall => h ⟨hall _, fun _ => hall _⟩)

def le [PartialOrder α] : AdjoinTop α → AdjoinTop α → Prop
  | _, .top => True
  | .top, .of _ => False
  | .of a, .of b => a ⊑ b

instance decLe [PartialOrder α] [∀ a b : α, Decidable (a ⊑ b)] :
    ∀ x y : AdjoinTop α, Decidable (le x y)
  | _, .top => isTrue True.intro
  | .top, .of _ => isFalse (fun h => h)
  | .of a, .of b => inferInstanceAs (Decidable (a ⊑ b))

def inf [Lattice α] : AdjoinTop α → AdjoinTop α → AdjoinTop α
  | .top, y => y
  | x, .top => x
  | .of a, .of b => .of (a ⊓ b)

def sup [Lattice α] : AdjoinTop α → AdjoinTop α → AdjoinTop α
  | .top, _ => .top
  | _, .top => .top
  | .of a, .of b => .of (a ⊔ b)

/-- The new value is reached exactly when the hypothesis already lies inside
the conclusion; otherwise the old arrow does. -/
def himp [HeytingAlgebra α] [∀ a b : α, Decidable (a ⊑ b)] :
    AdjoinTop α → AdjoinTop α → AdjoinTop α
  | _, .top => .top
  | .top, y => y
  | .of a, .of b => if a ⊑ b then .top else .of (a ⇨ b)

variable [HeytingAlgebra α] [∀ a b : α, Decidable (a ⊑ b)]

instance : PartialOrder (AdjoinTop α) where
  le := le
  le_refl a := by
    cases a with
    | of _ => exact le_rfl
    | top => trivial
  le_trans {a b c} h₁ h₂ := by
    cases a <;> cases b <;> cases c <;>
      first
        | trivial
        | exact h₁.elim
        | exact h₂.elim
        | exact le_trans h₁ h₂
  le_antisymm {a b} h₁ h₂ := by
    cases a <;> cases b <;>
      first
        | rfl
        | exact h₁.elim
        | exact h₂.elim
        | exact congrArg AdjoinTop.of (le_antisymm h₁ h₂)

/-- The same decision, now phrased for the class field, which is what instance
resolution looks for when `AdjoinTop` is iterated. -/
instance decLeOrd (x y : AdjoinTop α) : Decidable (x ⊑ y) := decLe x y

instance : Lattice (AdjoinTop α) where
  inf := inf
  sup := sup
  inf_le_left a b := by
    cases a <;> cases b <;>
      first
        | trivial
        | exact le_rfl
        | exact inf_le_left _ _
  inf_le_right a b := by
    cases a <;> cases b <;>
      first
        | trivial
        | exact le_rfl
        | exact inf_le_right _ _
  le_inf {a b c} h₁ h₂ := by
    cases a <;> cases b <;> cases c <;>
      first
        | trivial
        | exact h₁.elim
        | exact h₂.elim
        | exact h₁
        | exact h₂
        | exact le_inf h₁ h₂
  le_sup_left a b := by
    cases a <;> cases b <;>
      first
        | trivial
        | exact le_sup_left _ _
  le_sup_right a b := by
    cases a <;> cases b <;>
      first
        | trivial
        | exact le_sup_right _ _
  sup_le {a b c} h₁ h₂ := by
    cases a <;> cases b <;> cases c <;>
      first
        | trivial
        | exact h₁.elim
        | exact h₂.elim
        | exact sup_le h₁ h₂

instance : BoundedLattice (AdjoinTop α) where
  top := .top
  bot := .of ⊥
  le_top a := by cases a <;> trivial
  bot_le a := by
    cases a with
    | of _ => exact bot_le _
    | top => trivial

instance : HeytingAlgebra (AdjoinTop α) where
  himp := himp
  himp_adj a b c := by
    cases a with
    | top =>
      cases b with
      | top =>
        cases c with
        | top => exact ⟨fun _ => True.intro, fun _ => True.intro⟩
        | of _ => exact Iff.rfl
      | of y =>
        cases c with
        | top => exact ⟨fun _ => True.intro, fun _ => True.intro⟩
        | of z =>
          show (y ⊑ z) ↔ le (.top : AdjoinTop α)
            (if y ⊑ z then .top else .of (y ⇨ z))
          split
          · rename_i h
            exact ⟨fun _ => True.intro, fun _ => h⟩
          · rename_i h
            exact ⟨fun hh => absurd hh h, fun hh => hh.elim⟩
    | of x =>
      cases b with
      | top =>
        cases c with
        | top => exact ⟨fun _ => True.intro, fun _ => True.intro⟩
        | of _ => exact Iff.rfl
      | of y =>
        cases c with
        | top => exact ⟨fun _ => True.intro, fun _ => True.intro⟩
        | of z =>
          show (x ⊓ y ⊑ z) ↔ le (.of x : AdjoinTop α)
            (if y ⊑ z then .top else .of (y ⇨ z))
          split
          · rename_i h
            exact ⟨fun _ => True.intro,
                   fun _ => le_trans (inf_le_right x y) h⟩
          · exact himp_adj x y z

end AdjoinTop

/-! ## A new bottom

Adding a point above everything in the frame puts that point in every nonempty
upset, so a fresh empty one appears below the old bottom. -/

/-- The algebra with one new value adjoined below all of `α`. -/
inductive AdjoinBot (α : Type u) where
  | of : α → AdjoinBot α
  | bot : AdjoinBot α
  deriving DecidableEq, Repr

namespace AdjoinBot

variable {α : Type u}

instance [DecidableEq α] (p : AdjoinBot α → Prop) [DecidablePred p]
    [Decidable (∀ a : α, p (.of a))] : Decidable (∀ x, p x) :=
  if h : p .bot ∧ ∀ a : α, p (.of a) then
    isTrue (by
      intro x
      cases x with
      | of a => exact h.2 a
      | bot => exact h.1)
  else isFalse (fun hall => h ⟨hall _, fun _ => hall _⟩)

def le [PartialOrder α] : AdjoinBot α → AdjoinBot α → Prop
  | .bot, _ => True
  | .of _, .bot => False
  | .of a, .of b => a ⊑ b

instance decLe [PartialOrder α] [∀ a b : α, Decidable (a ⊑ b)] :
    ∀ x y : AdjoinBot α, Decidable (le x y)
  | .bot, _ => isTrue True.intro
  | .of _, .bot => isFalse (fun h => h)
  | .of a, .of b => inferInstanceAs (Decidable (a ⊑ b))

def inf [Lattice α] : AdjoinBot α → AdjoinBot α → AdjoinBot α
  | .bot, _ => .bot
  | _, .bot => .bot
  | .of a, .of b => .of (a ⊓ b)

def sup [Lattice α] : AdjoinBot α → AdjoinBot α → AdjoinBot α
  | .bot, y => y
  | x, .bot => x
  | .of a, .of b => .of (a ⊔ b)

/-- The new value implies everything, and is implied only by itself. -/
def himp [HeytingAlgebra α] : AdjoinBot α → AdjoinBot α → AdjoinBot α
  | .bot, _ => .of ⊤
  | .of _, .bot => .bot
  | .of a, .of b => .of (a ⇨ b)

variable [HeytingAlgebra α]

instance : PartialOrder (AdjoinBot α) where
  le := le
  le_refl a := by
    cases a with
    | of _ => exact le_rfl
    | bot => trivial
  le_trans {a b c} h₁ h₂ := by
    cases a <;> cases b <;> cases c <;>
      first
        | trivial
        | exact h₁.elim
        | exact h₂.elim
        | exact le_trans h₁ h₂
  le_antisymm {a b} h₁ h₂ := by
    cases a <;> cases b <;>
      first
        | rfl
        | exact h₁.elim
        | exact h₂.elim
        | exact congrArg AdjoinBot.of (le_antisymm h₁ h₂)

instance decLeOrd [∀ a b : α, Decidable (a ⊑ b)] (x y : AdjoinBot α) :
    Decidable (x ⊑ y) := decLe x y

instance : Lattice (AdjoinBot α) where
  inf := inf
  sup := sup
  inf_le_left a b := by
    cases a <;> cases b <;>
      first
        | trivial
        | exact inf_le_left _ _
  inf_le_right a b := by
    cases a <;> cases b <;>
      first
        | trivial
        | exact inf_le_right _ _
  le_inf {a b c} h₁ h₂ := by
    cases a <;> cases b <;> cases c <;>
      first
        | trivial
        | exact h₁.elim
        | exact h₂.elim
        | exact le_inf h₁ h₂
  le_sup_left a b := by
    cases a <;> cases b <;>
      first
        | trivial
        | exact le_rfl
        | exact le_sup_left _ _
  le_sup_right a b := by
    cases a <;> cases b <;>
      first
        | trivial
        | exact le_rfl
        | exact le_sup_right _ _
  sup_le {a b c} h₁ h₂ := by
    cases a <;> cases b <;> cases c <;>
      first
        | trivial
        | exact h₁.elim
        | exact h₂.elim
        | exact h₁
        | exact h₂
        | exact sup_le h₁ h₂

instance : BoundedLattice (AdjoinBot α) where
  top := .of ⊤
  bot := .bot
  le_top a := by
    cases a with
    | of _ => exact le_top _
    | bot => trivial
  bot_le a := by cases a <;> trivial

instance : HeytingAlgebra (AdjoinBot α) where
  himp := himp
  himp_adj a b c := by
    cases a with
    | bot => exact ⟨fun _ => True.intro, fun _ => True.intro⟩
    | of x =>
      cases b with
      | bot => exact ⟨fun _ => le_top x, fun _ => True.intro⟩
      | of y =>
        cases c with
        | bot =>
          show le (.of (x ⊓ y) : AdjoinBot α) .bot ↔ le (.of x : AdjoinBot α) .bot
          exact Iff.rfl
        | of z => exact himp_adj x y z

end AdjoinBot
