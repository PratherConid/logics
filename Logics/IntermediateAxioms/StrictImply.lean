import Logics.IntermediateAxioms.Model

/-!
# What the principles do not prove

Soundness, read backwards, turns the measurements of the previous file into
underivability: anything with a proof takes the top value under every
valuation, so a formula that misses the top value somewhere has no proof.

The first theorems apply this to bare intuitionistic logic.  Three of them
cover the whole development, one for each node at the bottom of the hierarchy
below, since every principle here derives one of those three: the tall fork
refutes `pierce₁₂OrPierce₂₁Form`, the uneven fork `scottForm`, and the three
branch fork `kreiselPutnamForm`.

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

The principles of this development fall into the poset below.  Each node is one
*representative*; an edge downwards means the upper derives the lower and the
lower does not derive the upper; and nodes joined by no downward path are
incomparable, neither deriving the other.

Only the covering relations are drawn, since `DerivesFromSchema.trans` supplies
the rest: a derivation along any downward path is the composite of its edges.
The separations come back the same way, read contrapositively -- a derivation
the diagram forbids would compose into one the file has already refuted -- which
is why so few of them need proving below.

```
                        excludedMiddleForm
                                |
                          smetanichForm
                         /             \
                  bd2Form               linearityForm
                 /       \             /             \
                /       noDiamondForm                weakEmForm
               /              |                     /          \
              |     pierce₁₂OrLuk₁₂Form            |   kreiselPutnamForm
              |               |                    |
              |     pierce₁₂OrPierce₂₁Form         |
              |                                    |
               \_____________ scottForm __________/
```

The spine, from `excludedMiddleForm` through `bd2Form` and `noDiamondForm` down
to `pierce₁₂OrPierce₂₁Form`, is the chain the combined principles fall into:
every disjunction of two basic principles studied here lands on one of its
nodes.  The other four nodes are axioms that are not such disjunctions, and none
of them lies on the spine.

* `linearityForm` lies below `smetanichForm` and above `noDiamondForm`, and is
  incomparable with `bd2Form` beside it.
* `weakEmForm` lies below linearity, and is incomparable with every node of the
  spine from `bd2Form` down.
* `scottForm` lies below both `bd2Form` and `weakEmForm`, and is incomparable
  with `noDiamondForm` and everything under it.
* `kreiselPutnamForm` lies below `weakEmForm`, and is incomparable with
  `bd2Form`, with everything under `noDiamondForm`, and with `scottForm`.

The last three sections of this file prove those separations.  The edges, and
the classes below, are derivations from a schema, each a natural deduction
derivation from substitution instances; where the hierarchy is assembled, edges
and separations together settle, for every pair of principles in the classes,
whether one derives the other.

Each node stands for a class of principles that derive one another:

```
excludedMiddleForm      ≡ emAOrNotBForm ≡ emAOrBForm ≡ pierce₁₂OrDeMorgan₁₂Form
                        ≡ demorgan₁₂OrImpOr₁₂Form ≡ impOr₁₂OrImpOr₂₁Form
smetanichForm           ≡ peirce₁₂OrImpOr₂₁Form ≡ em₁OrPeirce₂₁Form
                        ≡ emAOrNotB₁₂OrPeirce₁₂Form ≡ emAOrNotB₁₂OrPeirce₂₁Form
bd2Form                 ≡ demorgan₁₂OrLuk₁₂Form ≡ impOr₁₂OrLuk₁₂Form
                        ≡ pierce₁₂OrLuk₂₁Form ≡ em₁OrLuk₂₁Form
                        ≡ notNot₁OrLuk₂₁Form ≡ cm₁OrLuk₂₁Form
                        ≡ notNot₁OrPeirce₂₁Form ≡ cm₁OrPeirce₂₁Form
                        ≡ emAOrB₁₂OrLuk₁₂Form ≡ emAOrB₁₂OrLuk₂₁Form
                        ≡ emAOrNotB₁₂OrLuk₂₁Form
linearityForm           (alone)
noDiamondForm           ≡ notNotAndForm ≡ impOr₁₂OrLuk₂₁Form ≡ luk₁₂OrLuk₂₁Form
weakEmForm              (alone)
pierce₁₂OrLuk₁₂Form     ≡ peirce₁₂OrImpOr₁₂Form
pierce₁₂OrPierce₂₁Form  (alone)
scottForm               (alone)
kreiselPutnamForm       (alone)
```

Each `≡` is a pair of derivations at shifted instances, not an identity: the
principles so related are different formulas that prove each other.  One `≡` is
weaker than the rest: `smetanichForm` needs *two* instances of itself to recover
`peirce₁₂OrImpOr₂₁Form`, and no single instantiation suffices.  Swapping
Lukasiewicz's arguments in the Peirce principle lands inside a class; doing it
in the `impOrForm` principle drops a level; swapping `impOrForm`'s own
arguments in `peirce₁₂OrImpOr₁₂Form` climbs three.

Six of the nodes carry names from the literature, writing `a`, `b`, `c` for
the variables: `smetanichForm`, `(¬ b → a) → (((a → b) → a) → a)`, Smetanich's
axiom; `bd2Form`, `a ∨ (a → (b ∨ ¬ b))`, bounded depth two; `linearityForm`,
`(a → b) ∨ (b → a)`, the Godel--Dummett axiom; `weakEmForm`, `¬ a ∨ ¬ ¬ a`,
Jankov's; `scottForm`, `((¬ ¬ a → a) → (a ∨ ¬ a)) → (¬ a ∨ ¬ ¬ a)`, Scott's; and
`kreiselPutnamForm`, `(¬ a → b ∨ c) → ((¬ a → b) ∨ (¬ a → c))`, Kreisel and
Putnam's.  Smetanich's axiom is linearity together with bounded depth two,
which is what the branching under it records, and why it needs two separating
algebras where `bd2Form` needs one.

`noDiamondForm`, `(a → (b ∨ ¬ b)) ∨ (b → (a ∨ ¬ a))`, is shorter than either
combined principle at its node.  It is `bd2Form` with the bare disjunct `a`
replaced by the mirror image of the other disjunct, so the step down from
`bd2Form` is that one substitution, and bounded depth two derives it at the
plain arguments.  The name records what separates it from the node below: the
diamond refutes it, while every chain, of whatever length, validates it.
`notNotAndForm`, `¬ ¬ (a ∧ b) → ((a → b) ∨ (b → a))`, is the same level said
differently, that the two arguments are comparable as soon as they are jointly
consistent.

The algebras listed below separate the nodes of the spine, but separating is
not the same as exhausting.  Showing that one of them is also the *complete*
list of minimal refuters, so that a schema derives the level precisely when it
fails there, takes a further argument, made where a single axiom is studied on
its own rather than the whole chain at once.

Not every such disjunction is intermediate.  `pierce₁₂OrDeMorgan₁₂Form` and
`demorgan₁₂OrImpOr₁₂Form` avoid Lukasiewicz, and both land back on excluded
middle: at arguments built from `a ∨ ¬ a` each of their disjuncts collapses to
it on its own.  Every principle that stays below the top has `peirceForm` or
`lukForm` on at least one side, though that is not enough by itself, as
`pierce₁₂OrDeMorgan₁₂Form` shows: De Morgan is classical in any company but
Lukasiewicz's.

`emAOrNotBForm` and `emAOrBForm` reach the top by a different route.  Neither
of their disjuncts implies excluded middle; instead a substitution makes one of
the three *refutable*, and the remaining two are excluded middle exactly.
`emAOrNotBForm` needs its arguments aligned, at `b := a`, while `emAOrBForm`
gives way to the constant `b := fls`.

Paired with a two-argument axiom they need not stay at the top, since the
substitution that collapses them need not be available.  Of the seventy two
such pairings, twenty four are degenerate and thirty eight are classical; the
five listed above are the rest, and every one lands on a level the hierarchy
already had.  Pairing a split with Peirce reaches the `peirce₁₂OrImpOr₂₁Form`
level, and pairing either with Lukasiewicz reaches the De Morgan level.

Joining a one-argument axiom to a two-argument one adds nothing new, but it
does not always collapse.  At the *same* argument it does: excluded middle,
double negation and consequentia mirabilis at `a` each entail `peirceForm a b`,
`impOrForm a b` and `lukForm a b`, so the disjunction is the two-argument
principle again.  Crossed, at `(b, a)`, they do not, and the six `em₁`,
`notNot₁` and `cm₁` principles above are the result.

Two families never produce anything below the top.  A disjunction of two
one-argument axioms is classical, since taking both arguments to be the same
formula collapses it to a single one; and a *conjunction* of any of these
is classical too, being at least as strong as each conjunct, every one of which
is already excluded middle.  Only disjunction, and only with a two-argument
axiom on at least one side, leaves room below.

## The separating algebras

Each separation is witnessed by one algebra, which validates every instance of
the weaker principle and refutes one instance of the stronger.  All of them are
built in `Logics/Heyting.lean`.  Down the spine:

| step                                                | algebra      | theorem                                     |
| --------------------------------------------------- | ------------ | ------------------------------------------- |
| `excludedMiddleForm` over `smetanichForm`           | `Fin 3`      | `smetanich_nderiv_em`                       |
| `smetanichForm` over `bd2Form`                      | `ForkUp 1 1` | `bd2_nderiv_smetanich`                      |
| `bd2Form` over `noDiamondForm`                      | `Fin 4`      | `noDiamond_nderiv_bd2`                      |
| `noDiamondForm` over `pierce₁₂OrLuk₁₂Form`          | `KiteUp 1 1` | `pierce₁₂OrLuk₁₂_nderiv_noDiamond`          |
| `pierce₁₂OrLuk₁₂Form` over `pierce₁₂OrPierce₂₁Form` | `KiteUp 1 2` | `pierce₁₂OrPierce₂₁_nderiv_pierce₁₂OrLuk₁₂` |

Beside it, where the first principle does not derive the second:

| separation                                    | algebra         | theorem                                   |
| --------------------------------------------- | --------------- | ----------------------------------------- |
| `linearityForm`, `bd2Form`                    | `Fin 4`         | `linearity_nderiv_bd2`                    |
| `bd2Form`, `weakEmForm`                       | `ForkUp 1 1`    | `bd2_nderiv_weakEm`                       |
| `weakEmForm`, `pierce₁₂OrPierce₂₁Form`        | `KiteUp 2 2`    | `weakEm_nderiv_pierce₁₂OrPierce₂₁`        |
| `scottForm`, `bd2Form`                        | `Fin 4`         | `scott_nderiv_bd2`                        |
| `scottForm`, `weakEmForm`                     | `ForkUp 1 1`    | `scott_nderiv_weakEm`                     |
| `scottForm`, `pierce₁₂OrPierce₂₁Form`         | `KiteUp 2 2`    | `scott_nderiv_pierce₁₂OrPierce₂₁`         |
| `noDiamondForm`, `scottForm`                  | `ForkUp 1 2`    | `noDiamond_nderiv_scott`                  |
| `kreiselPutnamForm`, `bd2Form`                | `Fin 4`         | `kreiselPutnam_nderiv_bd2`                |
| `kreiselPutnamForm`, `weakEmForm`             | `ForkUp 1 1`    | `kreiselPutnam_nderiv_weakEm`             |
| `kreiselPutnamForm`, `pierce₁₂OrPierce₂₁Form` | `KiteUp 2 2`    | `kreiselPutnam_nderiv_pierce₁₂OrPierce₂₁` |
| `kreiselPutnamForm`, `scottForm`              | `ForkUp 1 2`    | `kreiselPutnam_nderiv_scott`              |
| `bd2Form`, `kreiselPutnamForm`                | `ForkUp3 1 1 1` | `bd2_nderiv_kreiselPutnam`                |

The shape of each algebra is what it contributes.  The chains `Fin 3` and
`Fin 4` are linear, and length is what tells the middle principles apart: the
lower classes survive every chain, while `bd2Form` dies once a chain has two
intermediate values.  The other three are not linear, and each differs
from the next in one parameter.  All three are `ForkUp m n` or `KiteUp m n`: a
root with two branches of the given lengths, the kite closing them off with a
tip.  `KiteUp 1 1` has that tip above its two incomparable middles, so the join
of those middles reaches the top; `ForkUp 1 1` has no tip, so it does not, and
that is why the fork separates the step the kite cannot.  `KiteUp 1 2` has a
tip again but reaches it by paths of different lengths, and that unevenness is
what the bottom step needs.

Beside the spine three more shapes enter.  `KiteUp 2 2` has a tip, so weak
excluded middle and everything under it hold there, while its longer branches
refute the bottom of the spine.  `ForkUp 1 2`, the uneven fork, has no tip and
a branch of depth two: Scott's axiom fails there, and bounded depth two with
it, while `noDiamondForm` and Kreisel and Putnam's axiom hold.  `ForkUp3 1 1 1`,
the fork with three branches, is the only algebra here refuting Kreisel and
Putnam's axiom, and has depth two, so bounded depth two holds there.
-/

/-- `pierce₁₂OrPierce₂₁Form` is not a theorem of bare intuitionistic logic: the
fork with two long branches refutes it, so no derivation from no hypotheses
exists.  Every node of the spine derives it, so none of them is one either. -/
theorem pierce₁₂OrPierce₂₁_nderiv : ¬ ([] ⊢ pierce₁₂OrPierce₂₁Form) := by
  intro d
  exact pierce₁₂OrPierce₂₁Form_nvalid_tallFork
    (Derives.valid_of_derives d (ForkUp 2 2)
      (fun n => if n = 0 then (ForkUp.tails 1 2 : ForkUp 2 2) else ForkUp.tails 2 1))

/-- Nor is `scottForm`, which the uneven fork refutes.  Bounded depth two and
weak excluded middle derive it, and so everything above either of them. -/
theorem scott_nderiv : ¬ ([] ⊢ scottForm) := fun d =>
  scottForm_nvalid_fork12 (Derives.valid_of_derives d (ForkUp 1 2) _)

/-- Nor is `kreiselPutnamForm`, which the three branch fork refutes.  With the
two above this covers every principle here, each deriving one of the three. -/
theorem kreiselPutnam_nderiv : ¬ ([] ⊢ kreiselPutnamForm) := fun d =>
  kreiselPutnamForm_nvalid_fork3 (Derives.valid_of_derives d (ForkUp3 1 1 1) _)

/-- Strictness below: no instantiation of `pierce₁₂OrLuk₁₂Form` derives
`noDiamondForm`.  The diamond validates every instance of the former and
refutes one of the latter. -/
theorem pierce₁₂OrLuk₁₂_nderiv_noDiamond :
    ¬ DerivesFromSchema pierce₁₂OrLuk₁₂Form noDiamondForm := fun h =>
  noDiamondForm_nvalid_diamond (DerivesFromSchema.valid pierce₁₂OrLuk₁₂Form_valid h _)

/-- Strictness above: no instantiation of `noDiamondForm` derives `bd2Form`.
Every chain validates the former, and the four value chain refutes the
latter. -/
theorem noDiamond_nderiv_bd2 : ¬ DerivesFromSchema noDiamondForm bd2Form := fun h =>
  bd2Form_nvalid_four (DerivesFromSchema.valid noDiamondForm_valid_chain h _)

/-- Strong as it is, Smetanich's axiom still does not reach excluded middle: it
holds throughout `Fin 3`, where excluded middle does not. -/
theorem smetanich_nderiv_em :
    ¬ DerivesFromSchema smetanichForm (excludedMiddleForm (.var 0)) := fun h =>
  excludedMiddleForm_nvalid_three (DerivesFromSchema.valid smetanichForm_valid_three h _)

/-- The step from `bd2Form` up to Smetanich's axiom is strict: no instantiation
of the former derives the latter, since the fork validates every instance of the
former and refutes one of the latter. -/
theorem bd2_nderiv_smetanich : ¬ DerivesFromSchema bd2Form smetanichForm := fun h =>
  smetanichForm_nvalid_fork (DerivesFromSchema.valid bd2Form_valid_fork h _)

/-- The bottom step is strict too: no instantiation of `pierce₁₂OrPierce₂₁Form`
derives `pierce₁₂OrLuk₁₂Form`, since the kite validates every instance of the
former and refutes one of the latter. -/
theorem pierce₁₂OrPierce₂₁_nderiv_pierce₁₂OrLuk₁₂ :
    ¬ DerivesFromSchema pierce₁₂OrPierce₂₁Form pierce₁₂OrLuk₁₂Form := fun h =>
  pierce₁₂OrLuk₁₂Form_nvalid_kite (DerivesFromSchema.valid pierce₁₂OrPierce₂₁Form_valid_kite h _)

/-! ## Both algebras are needed at the `peirce₁₂OrImpOr₂₁Form` step

`Fin 4` and `ForkUp 1 1` each refute `peirce₁₂OrImpOr₂₁Form`, and neither is a
subalgebra of a quotient of the other: quotients and subalgebras of a chain are
chains, so the fork cannot appear inside `Fin 4`, and the fork's only proper
generated subframe is an antichain, whose algebra is Boolean.

So a schema that derives `peirce₁₂OrImpOr₂₁Form` has to miss the top value in
both of them, which is what the two theorems below record.  Used in the other
direction, they are the test the separation proofs above perform: exhibiting a
schema valid throughout either algebra shows it derives nothing at this
level. -/

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
`linearityForm` lies strictly below Smetanich's axiom and strictly above
`noDiamondForm`, and is incomparable with `bd2Form` sitting between them;
`weakEmForm` lies strictly below linearity and is incomparable with every level
from `bd2Form` down.

Three separations settle all of that, every other one following from them by
`DerivesFromSchema.trans`.

* Linearity does not reach bounded depth two, so it reaches nothing above
  bounded depth two either.
* Bounded depth two does not reach weak excluded middle, so neither does
  anything bounded depth two derives; and since linearity derives weak excluded
  middle, none of those reach linearity either.
* Weak excluded middle does not reach the bottom level, so it reaches no level
  of the chain, and not linearity above them.

The derivations in the other direction are not proved here: each is a natural
deduction derivation from substitution instances. -/

/-- **Linearity does not reach bounded depth two**: every chain is linear,
while the four value chain has depth three.  Smetanich's axiom derives bounded
depth two, so linearity does not reach that either. -/
theorem linearity_nderiv_bd2 : ¬ DerivesFromSchema linearityForm bd2Form := fun h =>
  bd2Form_nvalid_four (DerivesFromSchema.valid (linearityForm_valid_chain (n := 3)) h _)

/-- **Bounded depth two does not reach weak excluded middle**: the fork has
depth two and is not directed.  Everything from `noDiamondForm` down is derived
by bounded depth two, so none of those reach it either; and linearity derives
it, so neither can anything that fails to reach linearity be reached from it. -/
theorem bd2_nderiv_weakEm : ¬ DerivesFromSchema bd2Form weakEmForm := fun h =>
  weakEmForm_nvalid_fork (DerivesFromSchema.valid bd2Form_valid_fork h _)

/-- **Weak excluded middle does not reach even the bottom level**: the even
kite is directed and refutes that level.  Every level of the chain derives the
bottom one, so weak excluded middle reaches none of them, nor linearity above
them. -/
theorem weakEm_nderiv_pierce₁₂OrPierce₂₁ :
    ¬ DerivesFromSchema weakEmForm pierce₁₂OrPierce₂₁Form := fun h =>
  pierce₁₂OrPierce₂₁Form_nvalid_kite22
    (DerivesFromSchema.valid weakEmForm_valid_kite22 h _)

/-! ## Scott's axiom

`scottForm` lies strictly below weak excluded middle and strictly below bounded
depth two, and is incomparable with `noDiamondForm` and everything under it.
Four separations settle that, the rest following by `DerivesFromSchema.trans`:
it does not reach bounded depth two, nor weak excluded middle, nor the bottom
level; and `noDiamondForm` does not reach it, so neither does anything
`noDiamondForm` derives. -/

theorem scott_nderiv_bd2 : ¬ DerivesFromSchema scottForm bd2Form := fun h =>
  bd2Form_nvalid_four (DerivesFromSchema.valid scottForm_valid_four h _)

theorem scott_nderiv_weakEm : ¬ DerivesFromSchema scottForm weakEmForm := fun h =>
  weakEmForm_nvalid_fork (DerivesFromSchema.valid scottForm_valid_fork h _)

theorem scott_nderiv_pierce₁₂OrPierce₂₁ :
    ¬ DerivesFromSchema scottForm pierce₁₂OrPierce₂₁Form := fun h =>
  pierce₁₂OrPierce₂₁Form_nvalid_kite22
    (DerivesFromSchema.valid scottForm_valid_kite22 h _)

theorem noDiamond_nderiv_scott :
    ¬ DerivesFromSchema noDiamondForm scottForm := fun h =>
  scottForm_nvalid_fork12 (DerivesFromSchema.valid noDiamondForm_valid_fork12 h _)

/-! ## Kreisel and Putnam's axiom

`kreiselPutnamForm` lies strictly below weak excluded middle and is incomparable
with bounded depth two, with everything under `noDiamondForm`, and with Scott's
axiom.  Five separations settle that, the rest following by
`DerivesFromSchema.trans`: it reaches neither bounded depth two, nor weak
excluded middle, nor the bottom level, nor Scott's axiom; and bounded depth two
does not reach it, so neither does anything bounded depth two derives, Scott's
axiom among them.

Its separating algebra is the one place in this development where two branches
are not enough.  Every algebra above validates it, the uneven fork that refutes
Scott's axiom included, and only the three branch fork refutes it. -/

theorem kreiselPutnam_nderiv_bd2 :
    ¬ DerivesFromSchema kreiselPutnamForm bd2Form := fun h =>
  bd2Form_nvalid_four (DerivesFromSchema.valid kreiselPutnamForm_valid_four h _)

theorem kreiselPutnam_nderiv_weakEm :
    ¬ DerivesFromSchema kreiselPutnamForm weakEmForm := fun h =>
  weakEmForm_nvalid_fork (DerivesFromSchema.valid kreiselPutnamForm_valid_fork h _)

theorem kreiselPutnam_nderiv_pierce₁₂OrPierce₂₁ :
    ¬ DerivesFromSchema kreiselPutnamForm pierce₁₂OrPierce₂₁Form := fun h =>
  pierce₁₂OrPierce₂₁Form_nvalid_kite22
    (DerivesFromSchema.valid kreiselPutnamForm_valid_kite22 h _)

theorem kreiselPutnam_nderiv_scott :
    ¬ DerivesFromSchema kreiselPutnamForm scottForm := fun h =>
  scottForm_nvalid_fork12 (DerivesFromSchema.valid kreiselPutnamForm_valid_fork12 h _)

theorem bd2_nderiv_kreiselPutnam :
    ¬ DerivesFromSchema bd2Form kreiselPutnamForm := fun h =>
  kreiselPutnamForm_nvalid_fork3 (DerivesFromSchema.valid bd2Form_valid_fork3 h _)
