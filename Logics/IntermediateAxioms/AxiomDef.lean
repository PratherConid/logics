import Logics.Heyting

/-!
# The principles of the intermediate logics

Each principle is stated as a predicate on propositions rather than as a rule,
so that it can be assumed *at particular arguments*: `ExcludedMiddleF a` says
excluded middle holds at `a`, and says nothing about any other proposition.
That is what makes it possible to ask which instances of one principle suffice
to prove an instance of another.

The first group collects the familiar principles, every one of which is
classical on its own.  The rest are not: combining two of them disjunctively,
or weakening one, gives axioms of logics that sit strictly between the
intuitionistic calculus and the classical one.  Within the combined group the
primed members take Lukasiewicz at
swapped arguments, which for some of them is a genuine change and for others
only a transposition.

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

/-- Smetanich's axiom: Peirce's law, granted that `a` already follows from the
failure of `b`. -/
def SmetanichF := fun (a b : Prop) => (¬ b → a) → (((a → b) → a) → a)

/-- Bounded depth two: either `a`, or `a` settles excluded middle at `b`. -/
def BD2F := fun (a b : Prop) => a ∨ (a → (b ∨ ¬ b))

/-- Either argument settles excluded middle at the other.  This is `BD2F` with
its bare left disjunct replaced by the mirror image of its right one.

The name records the shape of the smallest algebra that refutes it, a diamond:
two incomparable values between a bottom and a top.  Chains, however long,
cannot produce one. -/
def NoDiamondF := fun (a b : Prop) => (a → (b ∨ ¬ b)) ∨ (b → (a ∨ ¬ a))

/-- Linearity, guarded: the two arguments are comparable as soon as they are
jointly consistent.  Dropping the guard would give the linearity axiom itself,
which is stronger. -/
def NotNotAndF := fun (a b : Prop) => ¬ ¬ (a ∧ b) → ((a → b) ∨ (b → a))

/-- **Linearity**, the Godel--Dummett axiom: any two propositions are
comparable.  Its algebras are the chains. -/
def LinearityF := fun (a b : Prop) => (a → b) ∨ (b → a)

/-- **Weak excluded middle**, Jankov's axiom: excluded middle for a negation,
which unlike excluded middle itself leaves room below the classical logic. -/
def WeakEmF := fun (a : Prop) => ¬ a ∨ ¬ ¬ a

/-- **Kreisel and Putnam's axiom**: a disjunction established from a negation
splits, one of its disjuncts already following from that negation alone. -/
def KreiselPutnamF := fun (a b c : Prop) =>
  (¬ a → b ∨ c) → ((¬ a → b) ∨ (¬ a → c))

/-- **Scott's axiom**: weak excluded middle, granted that double negation
elimination at `a` would already settle excluded middle there. -/
def ScottF := fun (a : Prop) => ((¬ ¬ a → a) → (a ∨ ¬ a)) → (¬ a ∨ ¬ ¬ a)

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

def EmAOrNotB₁₂OrPeirce₁₂F := fun (a b : Prop) =>
  (a ∨ ¬ b ∨ ¬ (b → a)) ∨ (((a → b) → a) → a)

def EmAOrNotB₁₂OrPeirce₂₁F := fun (a b : Prop) =>
  (a ∨ ¬ b ∨ ¬ (b → a)) ∨ (((b → a) → b) → b)

def EmAOrB₁₂OrLuk₁₂F := fun (a b : Prop) =>
  (a ∨ b ∨ ¬ (¬ b → a)) ∨ ((¬ a → ¬ b) → (b → a))

def EmAOrB₁₂OrLuk₂₁F := fun (a b : Prop) =>
  (a ∨ b ∨ ¬ (¬ b → a)) ∨ ((¬ b → ¬ a) → (a → b))

def EmAOrNotB₁₂OrLuk₂₁F := fun (a b : Prop) =>
  (a ∨ ¬ b ∨ ¬ (b → a)) ∨ ((¬ b → ¬ a) → (a → b))

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

def smetanichForm : Form :=
  .imp (.imp (Form.neg (.var 1)) (.var 0)) (peirceForm (.var 0) (.var 1))

def bd2Form : Form :=
  .or (.var 0) (.imp (.var 0) (.or (.var 1) (Form.neg (.var 1))))

def noDiamondForm : Form :=
  .or (.imp (.var 0) (excludedMiddleForm (.var 1)))
      (.imp (.var 1) (excludedMiddleForm (.var 0)))

def notNotAndForm : Form :=
  .imp (Form.neg (Form.neg (.and (.var 0) (.var 1))))
    (.or (.imp (.var 0) (.var 1)) (.imp (.var 1) (.var 0)))

def linearityForm : Form := .or (.imp (.var 0) (.var 1)) (.imp (.var 1) (.var 0))

def weakEmForm : Form :=
  .or (Form.neg (.var 0)) (Form.neg (Form.neg (.var 0)))

def kreiselPutnamForm : Form :=
  .imp (.imp (Form.neg (.var 0)) (.or (.var 1) (.var 2)))
    (.or (.imp (Form.neg (.var 0)) (.var 1)) (.imp (Form.neg (.var 0)) (.var 2)))

def scottForm : Form :=
  .imp (.imp (notNotForm (.var 0)) (excludedMiddleForm (.var 0))) weakEmForm

def pierce₁₂OrLuk₁₂Form : Form := .or (peirceForm (.var 0) (.var 1)) (lukForm (.var 0) (.var 1))

def demorgan₁₂OrLuk₁₂Form : Form := .or (demorganForm (.var 0) (.var 1)) (lukForm (.var 0) (.var 1))

def impOr₁₂OrLuk₁₂Form : Form := .or (impOrForm (.var 0) (.var 1)) (lukForm (.var 0) (.var 1))

def pierce₁₂OrLuk₂₁Form : Form := .or (peirceForm (.var 0) (.var 1)) (lukForm (.var 1) (.var 0))

def impOr₁₂OrLuk₂₁Form : Form := .or (impOrForm (.var 0) (.var 1)) (lukForm (.var 1) (.var 0))

def emAOrNotB₁₂OrPeirce₁₂Form : Form :=
  .or (emAOrNotBForm (.var 0) (.var 1)) (peirceForm (.var 0) (.var 1))

def emAOrNotB₁₂OrPeirce₂₁Form : Form :=
  .or (emAOrNotBForm (.var 0) (.var 1)) (peirceForm (.var 1) (.var 0))

def emAOrB₁₂OrLuk₁₂Form : Form :=
  .or (emAOrBForm (.var 0) (.var 1)) (lukForm (.var 0) (.var 1))

def emAOrB₁₂OrLuk₂₁Form : Form :=
  .or (emAOrBForm (.var 0) (.var 1)) (lukForm (.var 1) (.var 0))

def emAOrNotB₁₂OrLuk₂₁Form : Form :=
  .or (emAOrNotBForm (.var 0) (.var 1)) (lukForm (.var 1) (.var 0))

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
