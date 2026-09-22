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

def EmAOrNotBF := fun (a b : Prop) => a ∨ ¬ b ∨ ¬ (b → a)

def EmAOrBF := fun (a b : Prop) => a ∨ b ∨ ¬ (¬ b → a)

def PeirceF := fun a b : Prop => ((a → b) → a) → a

def NotNotF := fun a : Prop => ¬ ¬ a → a

def DeMorganNotAndNotF := fun a b : Prop => ¬ (¬ a ∧ ¬ b) → a ∨ b

def ImpOrF := fun a b : Prop => (a → b) → (¬ a ∨ b)

def ConsequentiaMirabilisF := fun a : Prop => (¬ a → a) → a

def LukasiewiczF := fun a b : Prop => (¬ a → ¬ b) → (b → a)

def Pierce₁₂OrPierce₂₁F := fun (a b : Prop) => (((a → b) → a) → a) ∨ (((b → a) → b) → b)

def ImpOr₁₂OrImpOr₂₁F := fun (a b : Prop) =>
  ((a → b) → (¬ a ∨ b)) ∨ ((b → a) → (¬ b ∨ a))

def Lukasiewicz₁₂OrLukasiewicz₂₁F := fun (a b : Prop) =>
  ((¬ a → ¬ b) → (b → a)) ∨ ((¬ b → ¬ a) → (a → b))

def Pierce₁₂OrDeMorgan₁₂F := fun (a b : Prop) =>
  (((a → b) → a) → a) ∨ (¬ (¬ a ∧ ¬ b) → a ∨ b)

def DeMorgan₁₂OrImpOr₁₂F := fun (a b : Prop) =>
  (¬ (¬ a ∧ ¬ b) → a ∨ b) ∨ ((a → b) → (¬ a ∨ b))

def Peirce₁₂OrImpOr₁₂F := fun (a b : Prop) => (((a → b) → a) → a) ∨ ((a → b) → (¬ a ∨ b))

def Peirce₁₂OrImpOr₂₁F := fun (a b : Prop) => (((a → b) → a) → a) ∨ ((b → a) → (¬ b ∨ a))

def Pierce₁₂OrLukasiewicz₁₂F := fun (a b : Prop) => (((a → b) → a) → a) ∨ ((¬ a → ¬ b) → (b → a))

def DeMorgan₁₂OrLukasiewicz₁₂F := fun (a b : Prop) => (¬ (¬ a ∧ ¬ b) → a ∨ b) ∨ ((¬ a → ¬ b) → (b → a))

def ImpOr₁₂OrLukasiewicz₁₂F := fun (a b : Prop) => ((a → b) → (¬ a ∨ b)) ∨ ((¬ a → ¬ b) → (b → a))

def Pierce₁₂OrLukasiewicz₂₁F := fun (a b : Prop) => (((a → b) → a) → a) ∨ ((¬ b → ¬ a) → (a → b))

def ImpOr₁₂OrLukasiewicz₂₁F := fun (a b : Prop) => ((a → b) → (¬ a ∨ b)) ∨ ((¬ b → ¬ a) → (a → b))

/-! Mixing a one argument principle with a two argument one.  The pairing is
only interesting when the two argument principle is taken at `(b, a)`: at
`(a, b)` the one argument disjunct already implies it and the disjunction
collapses. -/

def Em₁OrPeirce₂₁F := fun (a b : Prop) => (a ∨ ¬ a) ∨ (((b → a) → b) → b)

def NotNot₁OrPeirce₂₁F := fun (a b : Prop) => (¬ ¬ a → a) ∨ (((b → a) → b) → b)

def CM₁OrPeirce₂₁F := fun (a b : Prop) => ((¬ a → a) → a) ∨ (((b → a) → b) → b)

def Em₁OrLuk₂₁F := fun (a b : Prop) => (a ∨ ¬ a) ∨ ((¬ b → ¬ a) → (a → b))

def NotNot₁OrLuk₂₁F := fun (a b : Prop) => (¬ ¬ a → a) ∨ ((¬ b → ¬ a) → (a → b))

def CM₁OrLuk₂₁F := fun (a b : Prop) => ((¬ a → a) → a) ∨ ((¬ b → ¬ a) → (a → b))

/-! ### The same principles as formulas

Each of the seven basic principles becomes a formula former, taking the
formulas to be substituted for its arguments.  These are the building blocks;
they are parameterised because they are used at many different arguments. -/

def excludedMiddleForm (p : Form) : Form := .or p (Form.neg p)

def emAOrNotBForm (p q : Form) : Form :=
  .or p (.or (Form.neg q) (Form.neg (.imp q p)))

def emAOrBForm (p q : Form) : Form :=
  .or p (.or q (Form.neg (.imp (Form.neg q) p)))

def peirceForm (p q : Form) : Form := .imp (.imp (.imp p q) p) p

def notNotForm (p : Form) : Form := .imp (Form.neg (Form.neg p)) p

def demorganForm (p q : Form) : Form :=
  .imp (Form.neg (.and (Form.neg p) (Form.neg q))) (.or p q)

def impOrForm (p q : Form) : Form := .imp (.imp p q) (.or (Form.neg p) q)

def consequentiaMirabilisForm (p : Form) : Form := .imp (.imp (Form.neg p) p) p

def lukForm (p q : Form) : Form := .imp (.imp (Form.neg p) (Form.neg q)) (.imp q p)

def pierce₁₂OrPierce₂₁Form : Form := .or (peirceForm (.var 0) (.var 1)) (peirceForm (.var 1) (.var 0))

def impOr₁₂OrImpOr₂₁Form : Form := .or (impOrForm (.var 0) (.var 1)) (impOrForm (.var 1) (.var 0))

def luk₁₂OrLuk₂₁Form : Form := .or (lukForm (.var 0) (.var 1)) (lukForm (.var 1) (.var 0))

def pierce₁₂OrDeMorgan₁₂Form : Form := .or (peirceForm (.var 0) (.var 1)) (demorganForm (.var 0) (.var 1))

def demorgan₁₂OrImpOr₁₂Form : Form := .or (demorganForm (.var 0) (.var 1)) (impOrForm (.var 0) (.var 1))

def peirce₁₂OrImpOr₁₂Form : Form := .or (peirceForm (.var 0) (.var 1)) (impOrForm (.var 0) (.var 1))

def peirce₁₂OrImpOr₂₁Form : Form := .or (peirceForm (.var 0) (.var 1)) (impOrForm (.var 1) (.var 0))

def pierce₁₂OrLuk₁₂Form : Form := .or (peirceForm (.var 0) (.var 1)) (lukForm (.var 0) (.var 1))

def demorgan₁₂OrLuk₁₂Form : Form := .or (demorganForm (.var 0) (.var 1)) (lukForm (.var 0) (.var 1))

def impOr₁₂OrLuk₁₂Form : Form := .or (impOrForm (.var 0) (.var 1)) (lukForm (.var 0) (.var 1))

def pierce₁₂OrLuk₂₁Form : Form := .or (peirceForm (.var 0) (.var 1)) (lukForm (.var 1) (.var 0))

def impOr₁₂OrLuk₂₁Form : Form := .or (impOrForm (.var 0) (.var 1)) (lukForm (.var 1) (.var 0))

def em₁OrPeirce₂₁Form : Form :=
  .or (excludedMiddleForm (.var 0)) (peirceForm (.var 1) (.var 0))

def notNot₁OrPeirce₂₁Form : Form :=
  .or (notNotForm (.var 0)) (peirceForm (.var 1) (.var 0))

def cm₁OrPeirce₂₁Form : Form :=
  .or (consequentiaMirabilisForm (.var 0)) (peirceForm (.var 1) (.var 0))

def em₁OrLuk₂₁Form : Form :=
  .or (excludedMiddleForm (.var 0)) (lukForm (.var 1) (.var 0))

def notNot₁OrLuk₂₁Form : Form :=
  .or (notNotForm (.var 0)) (lukForm (.var 1) (.var 0))

def cm₁OrLuk₂₁Form : Form :=
  .or (consequentiaMirabilisForm (.var 0)) (lukForm (.var 1) (.var 0))
