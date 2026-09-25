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

Not every finite frame is built this way.  The zig-zag `a ≼ t ≽ s ≼ b` is
connected, so it is not two frames side by side, and no point lies above or
below all of it.  A third operation reaches it and the frames built on it: take
two frames, a maximal point `t` of the first and a minimal point `s` of the
second, and glue them by putting `s` below `t`.  On the algebras this is
`ZigGlue`, the pairs of the product meeting one condition that ties the two
points together.
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

/-! ## Gluing a maximal point to a minimal one

Take a frame `A` with a maximal point `t` and a frame `B` with a minimal point
`s`, and put them side by side with the one further relation `s ≼ t`.  Nothing
lies above `t` in `A` or below `s` in `B`, so that relation needs no others to
stay transitive.

An upset of the result is an upset of each part, with one condition: if it
contains `s`, it contains `t`.  On the algebras `α` of `A` and `β` of `B` both
points are elements.  `t` is maximal exactly when `{t}` is an upset, an atom
`a` of `α`, and `s` is minimal exactly when everything but `s` is an upset, a
coatom `c` of `β`.  An upset contains `t` when its first part lies above `a`,
and misses `s` when its second part lies below `c`.  So the algebra is the set
of pairs `(x, y)` of `α × β` with `y ⊑ c` or `a ⊑ x`.

Nothing in the construction needs `a` to be an atom or `c` a coatom; the frame
reading is the case where they are.  For any `a` and `c` the pairs satisfying
the condition contain both bounds and are closed under meets and joins, so
those are taken in the product.  The arrow of the product can leave them, but
below any pair there is a largest one satisfying the condition: the pair itself
when its first part lies above `a`, and otherwise the pair with its second part
cut down to `c`.  The arrow is the product's, cut down in this way.

A new point above everything is maximal, its atom being `.of ⊥` in
`AdjoinBot α`, and a new point below everything is minimal, its coatom being
`.of ⊤` in `AdjoinTop β`.  Gluing at those two places the new bottom of the
second frame below the new top of the first. -/

/-- The algebra of two frames glued at an element `a` of the first algebra and
an element `c` of the second: the pairs whose second part lies below `c` or
whose first part lies above `a`.  When `a` is the atom of a maximal point `t`
and `c` the coatom of a minimal point `s`, these are the upsets of the two
frames side by side with `s` placed below `t`. -/
structure ZigGlue {α β : Type u} [PartialOrder α] [PartialOrder β] (a : α) (c : β) where
  fst : α
  snd : β
  glued : snd ⊑ c ∨ a ⊑ fst

namespace ZigGlue

variable {α β : Type u} [HeytingAlgebra α] [HeytingAlgebra β] {a : α} {c : β}

theorem ext {p q : ZigGlue a c} (h₁ : p.fst = q.fst) (h₂ : p.snd = q.snd) : p = q := by
  cases p; cases q; cases h₁; cases h₂; rfl

instance [DecidableEq α] [DecidableEq β] : DecidableEq (ZigGlue a c) := fun p q =>
  if h : p.fst = q.fst ∧ p.snd = q.snd then isTrue (ext h.1 h.2)
  else isFalse (fun e => h (e ▸ ⟨rfl, rfl⟩))

instance (P : ZigGlue a c → Prop) [DecidablePred P]
    [Decidable (∀ x : α, ∀ y : β, ∀ h : y ⊑ c ∨ a ⊑ x, P ⟨x, y, h⟩)] :
    Decidable (∀ p, P p) :=
  if h : ∀ x y h, P ⟨x, y, h⟩ then isTrue (fun p => h p.fst p.snd p.glued)
  else isFalse (fun hall => h (fun _ _ _ => hall _))

/-- An element as its pair of parts. -/
def toProd (p : ZigGlue a c) : α × β := (p.fst, p.snd)

def inf (p q : ZigGlue a c) : ZigGlue a c where
  fst := p.fst ⊓ q.fst
  snd := p.snd ⊓ q.snd
  glued := by
    rcases p.glued with hp | hp
    · exact Or.inl (le_trans (inf_le_left _ _) hp)
    · rcases q.glued with hq | hq
      · exact Or.inl (le_trans (inf_le_right _ _) hq)
      · exact Or.inr (le_inf hp hq)

def sup (p q : ZigGlue a c) : ZigGlue a c where
  fst := p.fst ⊔ q.fst
  snd := p.snd ⊔ q.snd
  glued := by
    rcases p.glued with hp | hp
    · rcases q.glued with hq | hq
      · exact Or.inl (sup_le hp hq)
      · exact Or.inr (le_trans hq (le_sup_right _ _))
    · exact Or.inr (le_trans hp (le_sup_left _ _))

instance : PartialOrder (ZigGlue a c) where
  le p q := toProd p ⊑ toProd q
  le_refl _ := le_rfl
  le_trans h₁ h₂ := le_trans h₁ h₂
  le_antisymm h₁ h₂ :=
    have h := le_antisymm h₁ h₂
    ext (congrArg Prod.fst h) (congrArg Prod.snd h)

instance decLe [∀ x y : α, Decidable (x ⊑ y)] [∀ x y : β, Decidable (x ⊑ y)]
    (p q : ZigGlue a c) : Decidable (p ⊑ q) :=
  inferInstanceAs (Decidable (toProd p ⊑ toProd q))

instance : Lattice (ZigGlue a c) where
  inf := inf
  sup := sup
  inf_le_left p q := inf_le_left (toProd p) (toProd q)
  inf_le_right p q := inf_le_right (toProd p) (toProd q)
  le_inf {p q r} h₁ h₂ := show toProd p ⊑ toProd q ⊓ toProd r from le_inf h₁ h₂
  le_sup_left p q := le_sup_left (toProd p) (toProd q)
  le_sup_right p q := le_sup_right (toProd p) (toProd q)
  sup_le {p q r} h₁ h₂ := show toProd p ⊔ toProd q ⊑ toProd r from sup_le h₁ h₂

instance : BoundedLattice (ZigGlue a c) where
  top := ⟨⊤, ⊤, Or.inr (le_top a)⟩
  bot := ⟨⊥, ⊥, Or.inl (bot_le c)⟩
  le_top p := show toProd p ⊑ (⊤, ⊤) from le_top (toProd p)
  bot_le p := show (⊥, ⊥) ⊑ toProd p from bot_le (toProd p)

variable [∀ x y : α, Decidable (x ⊑ y)]

/-- The largest element below a pair: the pair itself when its first part lies
above `a`, and otherwise the pair with its second part cut down to `c`. -/
def ofProd (r : α × β) : ZigGlue a c :=
  if h : a ⊑ r.1 then ⟨r.1, r.2, Or.inr h⟩ else ⟨r.1, r.2 ⊓ c, Or.inl (inf_le_right _ _)⟩

theorem le_ofProd_iff (p : ZigGlue a c) (r : α × β) :
    toProd p ⊑ r ↔ p ⊑ ofProd r := by
  show toProd p ⊑ r ↔ toProd p ⊑ toProd (ofProd r)
  unfold ofProd
  split
  · exact Iff.rfl
  · rename_i ha
    refine ⟨fun h => ⟨h.1, le_inf h.2 ?_⟩, fun h => ⟨h.1, le_trans h.2 (inf_le_left _ _)⟩⟩
    rcases p.glued with hp | hp
    · exact hp
    · exact absurd (le_trans hp h.1) ha

def himp (p q : ZigGlue a c) : ZigGlue a c := ofProd (toProd p ⇨ toProd q)

instance : HeytingAlgebra (ZigGlue a c) where
  himp := himp
  himp_adj p q r := by
    show toProd p ⊓ toProd q ⊑ toProd r ↔ p ⊑ ofProd (toProd q ⇨ toProd r)
    exact (himp_adj _ _ _).trans (le_ofProd_iff p _)

end ZigGlue

/-! ## The diamond with a hair

In the chain `Fin 3`, the algebra of a two point chain, the middle element `1`
is both the atom of the top point and the coatom of the bottom point.  Gluing
the top of one two point chain to the bottom of another therefore gives the
zig-zag `u ≼ m ≽ v ≼ z`, and a new root below it gives the diamond with a
hair: a root, two points `u` and `v` above it with a common successor `m`, and
one more maximal point `z` above `v` alone.  Without `z` it would be the
diamond. -/

/-- The algebra of upsets of the diamond with a hair, nine elements. -/
abbrev DiamondHair := AdjoinTop (ZigGlue (1 : Fin 3) (1 : Fin 3))
