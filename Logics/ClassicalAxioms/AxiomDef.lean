import Logics.Heyting

/-!
# The classical principles

Each principle is stated as a predicate on propositions rather than as a rule,
so that it can be assumed *at particular arguments*: `ExcludedMiddleF a` says
excluded middle holds at `a`, and says nothing about any other proposition.
That is what makes it possible to ask which instances of one principle suffice
to prove an instance of another.

The first group collects the familiar principles.  The second combines one of
them disjunctively with Lukasiewicz's; within that group the primed members
take Lukasiewicz at swapped arguments, which for some of them is a genuine
change and for others only a transposition.

The file closes with the same material built as formulas of `Form`.  A
predicate on propositions can only ever be assumed at arguments one writes
down; a formula can be quantified over all of its substitution instances at
once, which is what statements about a whole schema require.
-/

def ExcludedMiddleF := fun (a : Prop) => a ∨ ¬a

def PeirceF := fun a b : Prop => ((a → b) → a) → a

def NotNotF := fun a : Prop => ¬ ¬ a → a

def DeMorganNotAndNotF := fun a b : Prop => ¬ (¬ a ∧ ¬ b) → a ∨ b

def ImpOrF := fun a b : Prop => (a → b) → (¬ a ∨ b)

def ConsequentiaMirabilisF := fun a : Prop => (¬ a → a) → a

def LukasiewiczF := fun a b : Prop => (¬ a → ¬ b) → (b → a)

def PierceOrLukasiewiczF := fun (a b : Prop) => (((a → b) → a) → a) ∨ ((¬ a → ¬ b) → (b → a))

def PeirceOrImpOrF := fun (a b : Prop) => (((a → b) → a) → a) ∨ ((a → b) → (¬ a ∨ b))

def DeMorganOrLukasiewiczF := fun (a b : Prop) => (¬ (¬ a ∧ ¬ b) → a ∨ b) ∨ ((¬ a → ¬ b) → (b → a))

def ImpOrOrLukasiewiczF := fun (a b : Prop) => ((a → b) → (¬ a ∨ b)) ∨ ((¬ a → ¬ b) → (b → a))

def PierceOrLukasiewiczF' := fun (a b : Prop) => (((a → b) → a) → a) ∨ ((¬ b → ¬ a) → (a → b))

def DeMorganOrLukasiewiczF' := fun (a b : Prop) => (¬ (¬ a ∧ ¬ b) → a ∨ b) ∨ ((¬ b → ¬ a) → (a → b))

def ImpOrOrLukasiewiczF' := fun (a b : Prop) => ((a → b) → (¬ a ∨ b)) ∨ ((¬ b → ¬ a) → (a → b))

/-! ### The same principles as formulas

Each of the seven basic principles becomes a formula former, taking the
formulas to be substituted for its arguments.  These are the building blocks;
they are parameterised because they are used at many different arguments. -/

def excludedMiddleForm (p : Form) : Form := .or p (Form.neg p)

def peirceForm (p q : Form) : Form := .imp (.imp (.imp p q) p) p

def notNotForm (p : Form) : Form := .imp (Form.neg (Form.neg p)) p

def demorganForm (p q : Form) : Form :=
  .imp (Form.neg (.and (Form.neg p) (Form.neg q))) (.or p q)

def impOrForm (p q : Form) : Form := .imp (.imp p q) (.or (Form.neg p) q)

def consequentiaMirabilisForm (p : Form) : Form := .imp (.imp (Form.neg p) p) p

def lukForm (p q : Form) : Form := .imp (.imp (Form.neg p) (Form.neg q)) (.imp q p)

def pierceOrLukForm : Form := .or (peirceForm (.var 0) (.var 1)) (lukForm (.var 0) (.var 1))

def demorganOrLukForm : Form := .or (demorganForm (.var 0) (.var 1)) (lukForm (.var 0) (.var 1))

def impOrOrLukForm : Form := .or (impOrForm (.var 0) (.var 1)) (lukForm (.var 0) (.var 1))

def pierceOrLukForm' : Form := .or (peirceForm (.var 0) (.var 1)) (lukForm (.var 1) (.var 0))

def demorganOrLukForm' : Form := .or (demorganForm (.var 0) (.var 1)) (lukForm (.var 1) (.var 0))

def impOrOrLukForm' : Form := .or (impOrForm (.var 0) (.var 1)) (lukForm (.var 1) (.var 0))

def peirceOrImpOrForm : Form := .or (peirceForm (.var 0) (.var 1)) (impOrForm (.var 0) (.var 1))
