import Logics.IntermediateAxioms.Model

/-!
# What the principles do not prove

Soundness, read backwards, turns the measurements of the previous file into
underivability: anything with a proof takes the top value under every
valuation, so a formula that misses the top value somewhere has no proof.

The first theorem applies this to bare intuitionistic logic, where the tall
fork refutes `Pierce₁₂OrPierce₂₁F` outright.  One such statement covers the whole
development, because every other principle here derives that one.

The rest say something stronger, about a principle assumed as an *axiom
schema*.  `DerivesFromSchema X p` holds when some finite list of substitution
instances of `X` derives `p`, and `DerivesFromSchema.valid` says an algebra
validating `X` validates everything the schema derives.  So a single algebra
validating `X` but refuting `p` rules out every instantiation of `X` at once,
which is what "strictly weaker" needs.

Such a statement is named `X_nderiv_Y` for `¬ DerivesFromSchema X_Form Y_Form`,
which reads left to right the way `⊢` does: the schema on the left does not
derive the formula on the right.  A bare `X_nderiv` has no schema on the left
and says that `X` is not derivable from nothing at all.

## The hierarchy

The derivations in `Logics/IntermediateAxioms/Implication.lean` and the
non-derivations here order every principle of this development into the poset
below.  Each node is one *representative*; an edge downwards means the upper
derives the lower and the lower does not derive the upper; and nodes joined by
no downward path are incomparable, neither deriving the other.

```
                     ExcludedMiddleF
                            |
                       SmetanichF
                        /       \
                    BD2F         LinearityF
                        \        /         \
                         NoDiamondF         WeakEmF
                             |
                 Pierce₁₂OrLukasiewicz₁₂F
                             |
                    Pierce₁₂OrPierce₂₁F
```

The spine on the left is the chain the combined principles fall into: every
disjunction of two basic principles studied here lands on one of its nodes.
The two nodes on the right are the axioms that are not such disjunctions, and
neither lies on the spine: `LinearityF` is incomparable with `BD2F` beside it,
and `WeakEmF` is incomparable with every node from `BD2F` downwards.  The last
section of this file proves both.

Each node stands for a class of principles that derive one another:

```
ExcludedMiddleF           ≡ EmAOrNotBF ≡ EmAOrBF ≡ Pierce₁₂OrDeMorgan₁₂F
                          ≡ DeMorgan₁₂OrImpOr₁₂F ≡ ImpOr₁₂OrImpOr₂₁F
SmetanichF                ≡ Peirce₁₂OrImpOr₂₁F ≡ Em₁OrPeirce₂₁F
                          ≡ EmAOrNotB₁₂OrPeirce₁₂F ≡ EmAOrNotB₁₂OrPeirce₂₁F
BD2F                      ≡ DeMorgan₁₂OrLukasiewicz₁₂F ≡ ImpOr₁₂OrLukasiewicz₁₂F
                          ≡ Pierce₁₂OrLukasiewicz₂₁F ≡ Em₁OrLuk₂₁F
                          ≡ NotNot₁OrLuk₂₁F ≡ CM₁OrLuk₂₁F
                          ≡ NotNot₁OrPeirce₂₁F ≡ CM₁OrPeirce₂₁F
                          ≡ EmAOrB₁₂OrLuk₁₂F ≡ EmAOrB₁₂OrLuk₂₁F
                          ≡ EmAOrNotB₁₂OrLuk₂₁F
LinearityF                (alone)
NoDiamondF                ≡ NotNotAndF ≡ ImpOr₁₂OrLukasiewicz₂₁F
                          ≡ Lukasiewicz₁₂OrLukasiewicz₂₁F
WeakEmF                   (alone)
Pierce₁₂OrLukasiewicz₁₂F  ≡ Peirce₁₂OrImpOr₁₂F
Pierce₁₂OrPierce₂₁F       (alone)
```

Each `≡` is a pair of derivations at shifted instances, not an identity: the
principles so related are different formulas that prove each other.  One `≡` is
weaker than the rest: `SmetanichF` needs *two* instances of itself to recover
`Peirce₁₂OrImpOr₂₁F`, and no single instantiation suffices.  Swapping
Lukasiewicz's arguments in the Peirce principle lands inside a class; doing it
in the `ImpOrF` principle drops a level; swapping `ImpOrF`'s own arguments in
`Peirce₁₂OrImpOr₁₂F` climbs three.

Four of the nodes carry names from the literature: `SmetanichF`,
`(¬ b → a) → (((a → b) → a) → a)`; `BD2F`, `a ∨ (a → (b ∨ ¬ b))`, bounded depth
two; `LinearityF`, `(a → b) ∨ (b → a)`, the Godel--Dummett axiom; and
`WeakEmF`, `¬ a ∨ ¬ ¬ a`, Jankov's.  Smetanich's axiom is linearity together
with bounded depth two, which is what the branching under it records, and why
it needs two separating algebras where `BD2F` needs one.

`NoDiamondF`, `(a → (b ∨ ¬ b)) ∨ (b → (a ∨ ¬ a))`, is shorter than either
combined principle at its node.  It is `BD2F` with the bare disjunct `a`
replaced by the mirror image of the other disjunct, so the step down from
`BD2F` is that one substitution, and `bd2F_noDiamondF` makes it at the plain
arguments.  The name records what separates it from the node below: the
diamond refutes it, while every chain, of whatever length, validates it.
`NotNotAndF`, `¬ ¬ (a ∧ b) → ((a → b) ∨ (b → a))`, is the same level said
differently, that the two arguments are comparable as soon as they are jointly
consistent.

The algebras listed below separate the nodes of the spine, but separating is
not the same as exhausting.  Showing that one of them is also the *complete* list of minimal
refuters, so that a schema derives the level precisely when it fails there,
takes a further argument, made where a single axiom is studied on its own
rather than the whole chain at once.

Not every such disjunction is intermediate.  `Pierce₁₂OrDeMorgan₁₂F` and
`DeMorgan₁₂OrImpOr₁₂F` avoid Lukasiewicz, and both land back on excluded
middle: at arguments built from `a ∨ ¬ a` each of their disjuncts collapses to
it on its own.  Every principle that stays below the top has `PeirceF` or
`LukasiewiczF` on at least one side, though that is not enough by itself, as
`Pierce₁₂OrDeMorgan₁₂F` shows: De Morgan is classical in any company but
Lukasiewicz's.

`EmAOrNotBF` and `EmAOrBF` reach the top by a different route.  Neither of
their disjuncts implies excluded middle; instead a substitution makes one of
the three *refutable*, and the remaining two are excluded middle exactly.
`EmAOrNotBF` needs its arguments aligned, at `b := a`, while `EmAOrBF` gives
way to the constant `b := False`.

Paired with a two-argument axiom they need not stay at the top, since the
substitution that collapses them need not be available.  Of the seventy two
such pairings, twenty four are degenerate and thirty eight are classical; the
five listed above are the rest, and every one lands on a level the hierarchy
already had.  Pairing a split with Peirce reaches the `Peirce₁₂OrImpOr₂₁F`
level, and pairing either with Lukasiewicz reaches the De Morgan level.

Joining a one-argument axiom to a two-argument one adds nothing new, but it
does not always collapse.  At the *same* argument it does: excluded middle,
double negation and consequentia mirabilis at `a` each imply `PeirceF a b`,
`ImpOrF a b` and `LukasiewiczF a b`, so the disjunction is the two-argument
principle again.  Crossed, at `(b, a)`, they do not, and the six `Em₁`,
`NotNot₁` and `CM₁` principles above are the result.

Two families never produce anything below the top.  A disjunction of two
one-argument axioms is classical, since taking both arguments to be the same
proposition collapses it to a single one; and a *conjunction* of any of these
is classical too, being at least as strong as each conjunct, every one of which
is already excluded middle.  Only disjunction, and only with a two-argument
axiom on at least one side, leaves room below.

## The separating algebras

Each step is witnessed by one algebra, which validates every instance of the
weaker principle and refutes one instance of the stronger.  All four are built
in `Logics/Heyting.lean`.

| step                                         | algebra   | theorem                             |
| -------------------------------------------- | --------- | ----------------------------------- |
| `ExcludedMiddleF` over `Peirce₁₂OrImpOr₂₁F`     | `Fin 3`   | `peirce₁₂OrImpOr₂₁_nderiv_em`          |
| `Peirce₁₂OrImpOr₂₁F` over `DeMorgan₁₂OrLukasiewicz₁₂F` | `ForkUp 1 1` | `demorgan₁₂OrLuk₁₂_nderiv_peirce₁₂OrImpOr₂₁` |
| `DeMorgan₁₂OrLukasiewicz₁₂F` over `NoDiamondF` | `Fin 4` | `noDiamond_nderiv_demorgan₁₂OrLuk₁₂` |
| `NoDiamondF` over `Pierce₁₂OrLukasiewicz₁₂F` | `KiteUp 1 1` | `pierce₁₂OrLuk₁₂_nderiv_noDiamond` |
| `Pierce₁₂OrLukasiewicz₁₂F` over `Pierce₁₂OrPierce₂₁F` | `KiteUp 1 2` | `pierce₁₂OrPierce₂₁_nderiv_pierce₁₂OrLuk₁₂` |

The shape of each algebra is what it contributes.  The chains `Fin 3` and
`Fin 4` are linear, and length is what tells the middle principles apart: the
lower classes survive every chain, while the De Morgan class dies once a chain
has two intermediate values.  The other three are not linear, and each differs
from the next in one parameter.  All three are `ForkUp m n` or `KiteUp m n`: a
root with two branches of the given lengths, the kite closing them off with a
tip.  `KiteUp 1 1` has that tip above its two incomparable middles, so the join
of those middles reaches the top; `ForkUp 1 1` has no tip, so it does not, and
that is why the fork separates the step the kite cannot.  `KiteUp 1 2` has a
tip again but reaches it by paths of different lengths, and that unevenness is
what the bottom step needs.
-/

/-- Nothing in this development is a theorem of bare intuitionistic logic.  It
is enough to say so for `Pierce₁₂OrPierce₂₁F`, since every other principle here
derives it: the fork with two long branches refutes it, so no derivation from no hypotheses
exists. -/
theorem pierce₁₂OrPierce₂₁F_nderiv : ¬ ([] ⊢ pierce₁₂OrPierce₂₁Form) := by
  intro d
  exact pierce₁₂OrPierce₂₁Form_nvalid_tallFork
    (Derives.valid_of_derives d (ForkUp 2 2)
      (fun n => if n = 0 then (ForkUp.tails 1 2 : ForkUp 2 2) else ForkUp.tails 2 1))

/-- Strictness below: no instantiation of `Pierce₁₂OrLukasiewicz₁₂F` derives
`NoDiamondF`.  The diamond validates every instance of the former and refutes
one of the latter. -/
theorem pierce₁₂OrLuk₁₂_nderiv_noDiamond :
    ¬ DerivesFromSchema pierce₁₂OrLuk₁₂Form noDiamondForm := fun h =>
  noDiamondForm_nvalid_diamond (DerivesFromSchema.valid pierce₁₂OrLuk₁₂Form_valid h _)

/-- Strictness above: no instantiation of `NoDiamondF` derives
`DeMorgan₁₂OrLukasiewicz₁₂F`.  Every chain validates the former, and the four
value chain refutes the latter. -/
theorem noDiamond_nderiv_demorgan₁₂OrLuk₁₂ :
    ¬ DerivesFromSchema noDiamondForm demorgan₁₂OrLuk₁₂Form := fun h =>
  demorgan₁₂OrLuk₁₂Form_nvalid_four (DerivesFromSchema.valid noDiamondForm_valid_chain h _)

/-- Strong as it is, `Peirce₁₂OrImpOr₂₁F` still does not reach excluded middle: it
holds throughout `Fin 3`, where excluded middle does not. -/
theorem peirce₁₂OrImpOr₂₁_nderiv_em :
    ¬ DerivesFromSchema peirce₁₂OrImpOr₂₁Form (excludedMiddleForm (.var 0)) := fun h =>
  excludedMiddleForm_nvalid_three (DerivesFromSchema.valid peirce₁₂OrImpOr₂₁Form_valid_three h _)

/-- The step from `DeMorgan₁₂OrLukasiewicz₁₂F` up to `Peirce₁₂OrImpOr₂₁F` is strict: no
instantiation of the former derives the latter, since the fork validates every
instance of the former and refutes one of the latter. -/
theorem demorgan₁₂OrLuk₁₂_nderiv_peirce₁₂OrImpOr₂₁ :
    ¬ DerivesFromSchema demorgan₁₂OrLuk₁₂Form peirce₁₂OrImpOr₂₁Form := fun h =>
  peirce₁₂OrImpOr₂₁Form_nvalid_fork (DerivesFromSchema.valid demorgan₁₂OrLuk₁₂Form_valid_fork h _)

/-- The bottom step is strict too: no instantiation of `Pierce₁₂OrPierce₂₁F`
derives `Pierce₁₂OrLukasiewicz₁₂F`, since the kite validates every instance of the
former and refutes one of the latter. -/
theorem pierce₁₂OrPierce₂₁_nderiv_pierce₁₂OrLuk₁₂ :
    ¬ DerivesFromSchema pierce₁₂OrPierce₂₁Form pierce₁₂OrLuk₁₂Form := fun h =>
  pierce₁₂OrLuk₁₂Form_nvalid_kite (DerivesFromSchema.valid pierce₁₂OrPierce₂₁Form_valid_kite h _)

/-! ## Both algebras are needed at the `Peirce₁₂OrImpOr₂₁F` step

`Fin 4` and `ForkUp 1 1` each refute `Peirce₁₂OrImpOr₂₁F`, and neither is a
subalgebra of a quotient of the other: quotients and subalgebras of a chain are
chains, so the fork cannot appear inside `Fin 4`, and the fork's only proper
generated subframe is an antichain, whose algebra is Boolean.

So a schema that derives `Peirce₁₂OrImpOr₂₁F` has to miss the top value in both
of them, which is what the two theorems below record.  Used in the other
direction, they are the test the separation proofs above perform: exhibiting a
schema valid throughout either algebra shows it derives nothing at this level. -/

theorem nvalid_four_of_derives_peirce₁₂OrImpOr₂₁ {X : Form}
    (h : DerivesFromSchema X peirce₁₂OrImpOr₂₁Form) :
    ¬ ∀ w : Nat → Fin 4, X.eval w = ⊤ := fun hv =>
  peirce₁₂OrImpOr₂₁Form_nvalid_four (DerivesFromSchema.valid hv h _)

theorem nvalid_fork_of_derives_peirce₁₂OrImpOr₂₁ {X : Form}
    (h : DerivesFromSchema X peirce₁₂OrImpOr₂₁Form) :
    ¬ ∀ w : Nat → ForkUp 1 1, X.eval w = ⊤ := fun hv =>
  peirce₁₂OrImpOr₂₁Form_nvalid_fork (DerivesFromSchema.valid hv h _)

/-! ## Two axioms beside the chain

Linearity and weak excluded middle are not disjunctions of two principles, so
neither is one of the levels; each hangs off the chain instead.

`LinearityF`, `(a → b) ∨ (b → a)`, lies strictly below Smetanich's axiom and
strictly above `NoDiamondF`, and is incomparable with `BD2F` sitting between
them: the four value chain is linear and of depth three, while the fork has
depth two and is not linear.  Smetanich's axiom is linearity together with
bounded depth two, which is why it lies above both while they lie beside each
other.

`WeakEmF`, `¬ a ∨ ¬ ¬ a`, lies strictly below linearity and is incomparable
with *every* level from `BD2F` down.  The diamond and the taller kites all
close their branches off with a tip, so all of them validate it, and between
them they refute every level below Smetanich's; the fork validates all of those
levels and refutes weak excluded middle.

The derivations in the other direction are not proved here but where each axiom
is settled on its own, since each of them reads off the list of that axiom's
minimal refuters rather than off a single separating algebra. -/

/-- Linearity does not reach Smetanich's axiom: every chain is linear, and the
four value chain refutes Smetanich's axiom. -/
theorem linearity_nderiv_smetanich :
    ¬ DerivesFromSchema linearityForm smetanichForm := fun h =>
  smetanichForm_nvalid_four
    (DerivesFromSchema.valid (linearityForm_valid_chain (n := 3)) h _)

/-- Nor does weak excluded middle, the diamond being directed but of depth
three. -/
theorem weakEm_nderiv_smetanich :
    ¬ DerivesFromSchema weakEmForm smetanichForm := fun h =>
  smetanichForm_nvalid_kite (DerivesFromSchema.valid weakEmForm_valid_kite h _)

/-- Nothing at the `NoDiamondF` level reaches linearity: the fork validates
`NoDiamondF` and refutes linearity. -/
theorem noDiamond_nderiv_linearity :
    ¬ DerivesFromSchema noDiamondForm linearityForm := fun h =>
  linearityForm_nvalid_fork (DerivesFromSchema.valid noDiamondForm_valid_fork h _)

/-! ### Linearity against bounded depth two -/

theorem linearity_nderiv_bd2 : ¬ DerivesFromSchema linearityForm bd2Form := fun h =>
  bd2Form_nvalid_four (DerivesFromSchema.valid (linearityForm_valid_chain (n := 3)) h _)

theorem bd2_nderiv_linearity : ¬ DerivesFromSchema bd2Form linearityForm := fun h =>
  linearityForm_nvalid_fork (DerivesFromSchema.valid bd2Form_valid_fork h _)

/-! ### Weak excluded middle against everything below Smetanich's axiom -/

theorem weakEm_nderiv_linearity :
    ¬ DerivesFromSchema weakEmForm linearityForm := fun h =>
  linearityForm_nvalid_kite (DerivesFromSchema.valid weakEmForm_valid_kite h _)

theorem weakEm_nderiv_bd2 : ¬ DerivesFromSchema weakEmForm bd2Form := fun h =>
  bd2Form_nvalid_kite (DerivesFromSchema.valid weakEmForm_valid_kite h _)

theorem bd2_nderiv_weakEm : ¬ DerivesFromSchema bd2Form weakEmForm := fun h =>
  weakEmForm_nvalid_fork (DerivesFromSchema.valid bd2Form_valid_fork h _)

theorem weakEm_nderiv_noDiamond :
    ¬ DerivesFromSchema weakEmForm noDiamondForm := fun h =>
  noDiamondForm_nvalid_diamond (DerivesFromSchema.valid weakEmForm_valid_kite h _)

theorem noDiamond_nderiv_weakEm :
    ¬ DerivesFromSchema noDiamondForm weakEmForm := fun h =>
  weakEmForm_nvalid_fork (DerivesFromSchema.valid noDiamondForm_valid_fork h _)

theorem weakEm_nderiv_pierce₁₂OrLuk₁₂ :
    ¬ DerivesFromSchema weakEmForm pierce₁₂OrLuk₁₂Form := fun h =>
  pierce₁₂OrLuk₁₂Form_nvalid_kite
    (DerivesFromSchema.valid weakEmForm_valid_kite12 h _)

theorem pierce₁₂OrLuk₁₂_nderiv_weakEm :
    ¬ DerivesFromSchema pierce₁₂OrLuk₁₂Form weakEmForm := fun h =>
  weakEmForm_nvalid_fork (DerivesFromSchema.valid pierce₁₂OrLuk₁₂Form_valid_fork h _)

theorem weakEm_nderiv_pierce₁₂OrPierce₂₁ :
    ¬ DerivesFromSchema weakEmForm pierce₁₂OrPierce₂₁Form := fun h =>
  pierce₁₂OrPierce₂₁Form_nvalid_kite22
    (DerivesFromSchema.valid weakEmForm_valid_kite22 h _)

theorem pierce₁₂OrPierce₂₁_nderiv_weakEm :
    ¬ DerivesFromSchema pierce₁₂OrPierce₂₁Form weakEmForm := fun h =>
  weakEmForm_nvalid_fork (DerivesFromSchema.valid pierce₁₂OrPierce₂₁Form_valid_fork h _)
