import Logics.Heyting

/-!
# The principles of the intermediate logics

Each principle is a formula of `Form`.  Substituting for its variables takes it
at particular arguments, and a statement about the principle as an axiom
*schema* quantifies over all of those substitution instances at once.  Which
instances of one principle suffice to derive an instance of another is what
places the principles relative to each other.

The basic principles come first, as formula formers taking the formulas to be
substituted for their arguments, since they are used at many different
arguments.  Every one of them is classical on its own.

The rest are formulas in `.var 0` and `.var 1` (and `.var 2`, for Kreisel and
Putnam's axiom), which the descriptions call `a` and `b` (and `c`).  Most join
two basic principles by a disjunction, the subscripts recording the order in
which each disjunct takes the arguments: `pierce₁₂OrLuk₂₁Form` is Peirce's law
at `a, b` or Łukasiewicz's at `b, a`.  Joining or weakening classical principles
this way need not stay classical: many of the results are axioms of logics
strictly between the intuitionistic calculus and the classical one.
-/

/-! ### The basic principles -/

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

/-! ### Joined and named principles -/

def pierce₁₂OrPierce₂₁Form : Form := .or (peirceForm (.var 0) (.var 1)) (peirceForm (.var 1) (.var 0))

def impOr₁₂OrImpOr₂₁Form : Form := .or (impOrForm (.var 0) (.var 1)) (impOrForm (.var 1) (.var 0))

def luk₁₂OrLuk₂₁Form : Form := .or (lukForm (.var 0) (.var 1)) (lukForm (.var 1) (.var 0))

def pierce₁₂OrDeMorgan₁₂Form : Form := .or (peirceForm (.var 0) (.var 1)) (demorganForm (.var 0) (.var 1))

def demorgan₁₂OrImpOr₁₂Form : Form := .or (demorganForm (.var 0) (.var 1)) (impOrForm (.var 0) (.var 1))

def peirce₁₂OrImpOr₁₂Form : Form := .or (peirceForm (.var 0) (.var 1)) (impOrForm (.var 0) (.var 1))

def peirce₁₂OrImpOr₂₁Form : Form := .or (peirceForm (.var 0) (.var 1)) (impOrForm (.var 1) (.var 0))

/-- Smetanich's axiom: Peirce's law, granted that `a` already follows from the
failure of `b`. -/
def smetanichForm : Form :=
  .imp (.imp (Form.neg (.var 1)) (.var 0)) (peirceForm (.var 0) (.var 1))

/-- Bounded depth two: either `a`, or `a` settles excluded middle at `b`. -/
def bd2Form : Form :=
  .or (.var 0) (.imp (.var 0) (.or (.var 1) (Form.neg (.var 1))))

/-- Either argument settles excluded middle at the other.  This is `bd2Form`
with its bare left disjunct replaced by the mirror image of its right one.

The name records the shape of the smallest algebra that refutes it, a diamond:
two incomparable values between a bottom and a top.  Chains, however long,
cannot produce one. -/
def noDiamondForm : Form :=
  .or (.imp (.var 0) (excludedMiddleForm (.var 1)))
      (.imp (.var 1) (excludedMiddleForm (.var 0)))

/-- Linearity, guarded: the two arguments are comparable as soon as they are
jointly consistent.  Dropping the guard would give the linearity axiom itself,
which is stronger. -/
def notNotAndForm : Form :=
  .imp (Form.neg (Form.neg (.and (.var 0) (.var 1))))
    (.or (.imp (.var 0) (.var 1)) (.imp (.var 1) (.var 0)))

/-- **Linearity**, the Godel--Dummett axiom: any two formulas are
comparable.  Its algebras are the chains. -/
def linearityForm : Form := .or (.imp (.var 0) (.var 1)) (.imp (.var 1) (.var 0))

/-- **Weak excluded middle**, Jankov's axiom: excluded middle for a negation,
which unlike excluded middle itself leaves room below the classical logic. -/
def weakEmForm : Form :=
  .or (Form.neg (.var 0)) (Form.neg (Form.neg (.var 0)))

/-- **Kreisel and Putnam's axiom**: a disjunction established from a negation
splits, one of its disjuncts already following from that negation alone. -/
def kreiselPutnamForm : Form :=
  .imp (.imp (Form.neg (.var 0)) (.or (.var 1) (.var 2)))
    (.or (.imp (Form.neg (.var 0)) (.var 1)) (.imp (Form.neg (.var 0)) (.var 2)))

/-- **Scott's axiom**: weak excluded middle, granted that double negation
elimination at `a` would already settle excluded middle there. -/
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

/-! Mixing a one argument principle with a two argument one.  The pairing is
only interesting when the two argument principle is taken at `(b, a)`: at
`(a, b)` the one argument disjunct already implies it and the disjunction
collapses. -/

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
