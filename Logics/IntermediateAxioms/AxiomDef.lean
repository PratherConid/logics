import Logics.Heyting

/-!
# The principles of the intermediate logics

Each principle is a formula former: it takes the formulas for its arguments and
builds a formula of `Form`.  Taken at distinct variables it is an axiom
*schema*, and a statement about the schema quantifies over all of its
substitution instances at once.  Which instances of one principle suffice to
derive an instance of another is what places the principles relative to each
other.

Most principles take two arguments, which the descriptions call `a` and `b`;
weak excluded middle and Scott's axiom take one, and Kreisel and Putnam's axiom
and `noForkUp2x2Var3Form` a third, `c`.  The basic principles come first, and
every one of them is classical on its own.  Most of the rest join two basic
principles by a disjunction, the subscripts recording the order in which each
disjunct takes the arguments: `pierce₁₂OrLuk₂₁Form` is Peirce's law at `a, b`
or Łukasiewicz's at `b, a`.  Joining or weakening classical principles this way
need not stay classical: many of the results are axioms of logics strictly
between the intuitionistic calculus and the classical one.
-/

/-! ### The basic principles -/

/-- `a ∨ ¬ a` -/
def excludedMiddleForm (p : Form) : Form := .or p (Form.neg p)

/-- `a ∨ (¬ b ∨ ¬ (b → a))` -/
def emAOrNotBForm (p q : Form) : Form := .or p (.or (Form.neg q) (Form.neg (.imp q p)))

/-- `a ∨ (b ∨ ¬ (¬ b → a))` -/
def emAOrBForm (p q : Form) : Form := .or p (.or q (Form.neg (.imp (Form.neg q) p)))

/-- `((a → b) → a) → a` -/
def peirceForm (p q : Form) : Form := .imp (.imp (.imp p q) p) p

/-- `¬ ¬ a → a` -/
def notNotForm (p : Form) : Form := .imp (Form.neg (Form.neg p)) p

/-- `¬ (¬ a ∧ ¬ b) → (a ∨ b)` -/
def demorganForm (p q : Form) : Form := .imp (Form.neg (.and (Form.neg p) (Form.neg q))) (.or p q)

/-- `(a → b) → (¬ a ∨ b)` -/
def impOrForm (p q : Form) : Form := .imp (.imp p q) (.or (Form.neg p) q)

/-- `(¬ a → a) → a` -/
def consequentiaMirabilisForm (p : Form) : Form := .imp (.imp (Form.neg p) p) p

/-- `(¬ a → ¬ b) → (b → a)` -/
def lukForm (p q : Form) : Form := .imp (.imp (Form.neg p) (Form.neg q)) (.imp q p)

/-! ### Joined and named principles -/

/-- `(((a → b) → a) → a) ∨ (((b → a) → b) → b)` -/
def pierce₁₂OrPierce₂₁Form (p q : Form) : Form := .or (peirceForm p q) (peirceForm q p)

/-- `((a → b) → (¬ a ∨ b)) ∨ ((b → a) → (¬ b ∨ a))` -/
def impOr₁₂OrImpOr₂₁Form (p q : Form) : Form := .or (impOrForm p q) (impOrForm q p)

/-- `((¬ a → ¬ b) → (b → a)) ∨ ((¬ b → ¬ a) → (a → b))` -/
def luk₁₂OrLuk₂₁Form (p q : Form) : Form := .or (lukForm p q) (lukForm q p)

/-- `(((a → b) → a) → a) ∨ (¬ (¬ a ∧ ¬ b) → (a ∨ b))` -/
def pierce₁₂OrDeMorgan₁₂Form (p q : Form) : Form := .or (peirceForm p q) (demorganForm p q)

/-- `(¬ (¬ a ∧ ¬ b) → (a ∨ b)) ∨ ((a → b) → (¬ a ∨ b))` -/
def demorgan₁₂OrImpOr₁₂Form (p q : Form) : Form := .or (demorganForm p q) (impOrForm p q)

/-- `(((a → b) → a) → a) ∨ ((a → b) → (¬ a ∨ b))` -/
def peirce₁₂OrImpOr₁₂Form (p q : Form) : Form := .or (peirceForm p q) (impOrForm p q)

/-- `(((a → b) → a) → a) ∨ ((b → a) → (¬ b ∨ a))` -/
def peirce₁₂OrImpOr₂₁Form (p q : Form) : Form := .or (peirceForm p q) (impOrForm q p)

/-- `(¬ b → a) → (((a → b) → a) → a)`

Smetanich's axiom: Peirce's law, granted that `a` already follows from the
failure of `b`. -/
def smetanichForm (p q : Form) : Form := .imp (.imp (Form.neg q) p) (peirceForm p q)

/-- `a ∨ (a → (b ∨ ¬ b))`

Bounded depth two: either `a`, or `a` settles excluded middle at `b`. -/
def bd2Form (p q : Form) : Form := .or p (.imp p (.or q (Form.neg q)))

/-- `(a → (b ∨ ¬ b)) ∨ (b → (a ∨ ¬ a))`

Either argument settles excluded middle at the other.  This is `bd2Form`
with its bare left disjunct replaced by the mirror image of its right one.

The name records the shape of the smallest algebra that refutes it, a diamond:
two incomparable values between a bottom and a top.  Chains, however long,
cannot produce one. -/
def noDiamondForm (p q : Form) : Form :=
  .or (.imp p (excludedMiddleForm q)) (.imp q (excludedMiddleForm p))

/-- `¬ ¬ (a ∧ b) → ((a → b) ∨ (b → a))`

Linearity, guarded: the two arguments are comparable as soon as they are
jointly consistent.  Dropping the guard would give the linearity axiom itself,
which is stronger. -/
def notNotAndForm (p q : Form) : Form :=
  .imp (Form.neg (Form.neg (.and p q))) (.or (.imp p q) (.imp q p))

/-- `(a → b) ∨ (b → a)`

**Linearity**, the Godel--Dummett axiom: any two formulas are
comparable.  Its algebras are the chains. -/
def linearityForm (p q : Form) : Form := .or (.imp p q) (.imp q p)

/-- `¬ a ∨ ¬ ¬ a`

**Weak excluded middle**, Jankov's axiom: excluded middle for a negation,
which unlike excluded middle itself leaves room below the classical logic. -/
def weakEmForm (p : Form) : Form := .or (Form.neg p) (Form.neg (Form.neg p))

/-- `(¬ a → (b ∨ c)) → ((¬ a → b) ∨ (¬ a → c))`

**Kreisel and Putnam's axiom**: a disjunction established from a negation
splits, one of its disjuncts already following from that negation alone. -/
def kreiselPutnamForm (p q r : Form) : Form :=
  .imp (.imp (Form.neg p) (.or q r)) (.or (.imp (Form.neg p) q) (.imp (Form.neg p) r))

/-- `((¬ ¬ a → a) → (a ∨ ¬ a)) → (¬ a ∨ ¬ ¬ a)`

**Scott's axiom**: weak excluded middle, granted that double negation
elimination at `a` would already settle excluded middle there. -/
def scottForm (p : Form) : Form := .imp (.imp (notNotForm p) (excludedMiddleForm p)) (weakEmForm p)

/-- `(((a → b) → a) → a) ∨ ((¬ a → ¬ b) → (b → a))` -/
def pierce₁₂OrLuk₁₂Form (p q : Form) : Form := .or (peirceForm p q) (lukForm p q)

/-- `(¬ (¬ a ∧ ¬ b) → (a ∨ b)) ∨ ((¬ a → ¬ b) → (b → a))` -/
def demorgan₁₂OrLuk₁₂Form (p q : Form) : Form := .or (demorganForm p q) (lukForm p q)

/-- `((a → b) → (¬ a ∨ b)) ∨ ((¬ a → ¬ b) → (b → a))` -/
def impOr₁₂OrLuk₁₂Form (p q : Form) : Form := .or (impOrForm p q) (lukForm p q)

/-- `(((a → b) → a) → a) ∨ ((¬ b → ¬ a) → (a → b))` -/
def pierce₁₂OrLuk₂₁Form (p q : Form) : Form := .or (peirceForm p q) (lukForm q p)

/-- `((a → b) → (¬ a ∨ b)) ∨ ((¬ b → ¬ a) → (a → b))` -/
def impOr₁₂OrLuk₂₁Form (p q : Form) : Form := .or (impOrForm p q) (lukForm q p)

/-- `(a ∨ (¬ b ∨ ¬ (b → a))) ∨ (((a → b) → a) → a)` -/
def emAOrNotB₁₂OrPeirce₁₂Form (p q : Form) : Form := .or (emAOrNotBForm p q) (peirceForm p q)

/-- `(a ∨ (¬ b ∨ ¬ (b → a))) ∨ (((b → a) → b) → b)` -/
def emAOrNotB₁₂OrPeirce₂₁Form (p q : Form) : Form := .or (emAOrNotBForm p q) (peirceForm q p)

/-- `(a ∨ (b ∨ ¬ (¬ b → a))) ∨ ((¬ a → ¬ b) → (b → a))` -/
def emAOrB₁₂OrLuk₁₂Form (p q : Form) : Form := .or (emAOrBForm p q) (lukForm p q)

/-- `(a ∨ (b ∨ ¬ (¬ b → a))) ∨ ((¬ b → ¬ a) → (a → b))` -/
def emAOrB₁₂OrLuk₂₁Form (p q : Form) : Form := .or (emAOrBForm p q) (lukForm q p)

/-- `(a ∨ (¬ b ∨ ¬ (b → a))) ∨ ((¬ b → ¬ a) → (a → b))` -/
def emAOrNotB₁₂OrLuk₂₁Form (p q : Form) : Form := .or (emAOrNotBForm p q) (lukForm q p)

/-! Mixing a one argument principle with a two argument one.  The pairing is
only interesting when the two argument principle is taken at `(b, a)`: at
`(a, b)` the one argument disjunct already implies it and the disjunction
collapses. -/

/-- `(a ∨ ¬ a) ∨ (((b → a) → b) → b)` -/
def em₁OrPeirce₂₁Form (p q : Form) : Form := .or (excludedMiddleForm p) (peirceForm q p)

/-- `(¬ ¬ a → a) ∨ (((b → a) → b) → b)` -/
def notNot₁OrPeirce₂₁Form (p q : Form) : Form := .or (notNotForm p) (peirceForm q p)

/-- `((¬ a → a) → a) ∨ (((b → a) → b) → b)` -/
def cm₁OrPeirce₂₁Form (p q : Form) : Form := .or (consequentiaMirabilisForm p) (peirceForm q p)

/-- `(a ∨ ¬ a) ∨ ((¬ b → ¬ a) → (a → b))` -/
def em₁OrLuk₂₁Form (p q : Form) : Form := .or (excludedMiddleForm p) (lukForm q p)

/-- `(¬ ¬ a → a) ∨ ((¬ b → ¬ a) → (a → b))` -/
def notNot₁OrLuk₂₁Form (p q : Form) : Form := .or (notNotForm p) (lukForm q p)

/-- `((¬ a → a) → a) ∨ ((¬ b → ¬ a) → (a → b))` -/
def cm₁OrLuk₂₁Form (p q : Form) : Form := .or (consequentiaMirabilisForm p) (lukForm q p)

/-! Principles each refuted, among the finite frames, by a single smallest one,
which their names record.  The first two are bounded depth two behind a premise
concluding `a ∨ b`; the last two are one principle, written in two variables and
in three. -/

/-- `((((a → (b ∨ ¬ b)) → a) → a) → (a ∨ b)) → (b ∨ (b → (a ∨ ¬ a)))`

Bounded depth two at `b, a`, granted that `a ∨ b` follows from Peirce's law
at `a` and `b ∨ ¬ b`.  The name records the smallest frame refuting it, the
uneven kite: a root and a top joined by one path through a single point and
another through two. -/
def noKiteUp1x2Form (p q : Form) : Form :=
  .imp (.imp (peirceForm p (excludedMiddleForm q)) (.or p q))
    (.or q (.imp q (excludedMiddleForm p)))

/-- `((b → (¬ a ∨ (¬ a → a))) → (a ∨ b)) → (a ∨ (a → (b ∨ ¬ b)))`

Bounded depth two at `a, b`, granted that `a ∨ b` follows from
`b → (¬ a ∨ (¬ a → a))`.  The name records the smallest frame refuting it, the
diamond with a hair: the diamond with one more maximal point, above one of its
two middle points only. -/
def noDiamondHairForm (p q : Form) : Form :=
  .imp (.imp (.imp q (.or (Form.neg p) (.imp (Form.neg p) p))) (.or p q)) (bd2Form p q)

/-- `((((¬ a → b) ∨ (a → b)) → (a ∨ ¬ a)) ∧ ¬ ¬ b) → (a ∨ ¬ a)`

Excluded middle at `a`, granted `¬ ¬ b` and that it follows from
`(¬ a → b) ∨ (a → b)`.  The name records the smallest frame refuting it, the
tall fork: a root with two branches of two points each. -/
def noForkUp2x2Form (p q : Form) : Form :=
  .imp
    (.and (.imp (.or (.imp (Form.neg p) q) (.imp p q)) (excludedMiddleForm p))
      (Form.neg (Form.neg q)))
    (excludedMiddleForm p)

/-- `((((a → c) ∨ (b → c)) → (a ∨ b)) ∧ ¬ (c → (a ∧ b))) → (a ∨ b)`

`a ∨ b`, granted that `c → (a ∧ b)` is refuted and that `a ∨ b` follows from
`(a → c) ∨ (b → c)`.  The tall fork's principle again, in three variables:
`noForkUp2x2Form` is this one at `a, ¬ a, b`, up to the order of a
disjunction and the refutation of `b → (a ∧ ¬ a)` being `¬ ¬ b`. -/
def noForkUp2x2Var3Form (p q r : Form) : Form :=
  .imp (.and (.imp (.or (.imp p r) (.imp q r)) (.or p q)) (Form.neg (.imp r (.and p q)))) (.or p q)
