import Logics.IntermediateAxioms.Derivation
import Logics.IntermediateAxioms.Refuter.SmetanichRefuter
import Logics.IntermediateAxioms.Refuter.BD2Refuter
import Logics.IntermediateAxioms.Refuter.LCRefuter
import Logics.IntermediateAxioms.Refuter.ScottRefuter

/-!
# The hierarchy

The principles of this development fall into the poset below.  Each node is one
*representative*; an edge downwards means the upper derives the lower and the
lower does not derive the upper; and nodes joined by no downward path are
incomparable, neither deriving the other.

Only the covering relations are drawn, since `DerivesFromSchema.trans` supplies
the rest: a derivation along any downward path is the composite of its edges.
The separations come back the same way, read contrapositively -- a derivation
the diagram forbids would compose into one already refuted -- which is why
seventeen separations (`Node.seps`) settle every pair (`Node.covered`).

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

## How it is proved

The edges, and the equivalences within each class, are derivations from a
schema, each a natural deduction derivation from substitution instances
(`Logics/IntermediateAxioms/Derivation.lean`).  The separations are
countermodels (`Logics/IntermediateAxioms/StrictImply.lean`), each an algebra
validating every instance of the weaker principle and refuting one instance of
the stronger.  This file puts the two halves together.  `hierarchy` says, for
every pair of the ten, that one derives the other exactly when the drawing puts
it at or above the other.

The drawing is recorded as data: the covering edges (`Node.edges`) and the
order they generate (`Node.below`, what lies at or under each node).

* **At or above means derivable.**  Every edge is a derivation
  (`derives_of_edge`), and what lies under a node is reached from it along
  edges (`Node.below_step`), so there is a derivation along the path
  (`derives_of_below`).
* **Apart means underivable.**  Every separation is a theorem
  (`nderiv_of_sep`).  A pair the drawing leaves apart has a separation above
  its first node and below its second (`Node.covered`); a derivation between
  them would compose with the paths into one across that separation.

The combinatorial facts about the drawing are checked by evaluation, over all
ten nodes at once.

The classes are recorded too (`Node.members`), and every member is equivalent
to the representative by derivations both ways (`members_equiv`), so
`hierarchy_members` extends the statement to all of them.
-/

/-- The ten representatives, one per node of the drawing. -/
inductive Node
  | em | smetanich | bd2 | linearity | noDiamond | weakEm | pierceLuk | piercePierce
  | scott | kreiselPutnam
  deriving DecidableEq

namespace Node

/-- The principle a node stands for. -/
def form : Node → Form
  | em => excludedMiddleForm (.var 0)
  | smetanich => (smetanichForm (.var 0) (.var 1))
  | bd2 => (bd2Form (.var 0) (.var 1))
  | linearity => (linearityForm (.var 0) (.var 1))
  | noDiamond => (noDiamondForm (.var 0) (.var 1))
  | weakEm => (weakEmForm (.var 0))
  | pierceLuk => (pierce₁₂OrLuk₁₂Form (.var 0) (.var 1))
  | piercePierce => (pierce₁₂OrPierce₂₁Form (.var 0) (.var 1))
  | scott => (scottForm (.var 0))
  | kreiselPutnam => (kreiselPutnamForm (.var 0) (.var 1) (.var 2))

def all : List Node :=
  [em, smetanich, bd2, linearity, noDiamond, weakEm, pierceLuk, piercePierce, scott,
    kreiselPutnam]

theorem mem_all (x : Node) : x ∈ all := by cases x <;> decide

instance (p : Node → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (∀ x ∈ all, p x) ⟨fun h x => h x (mem_all x), fun h x _ => h x⟩

/-- The covering edges, downwards from each node. -/
def edges : Node → List Node
  | em => [smetanich]
  | smetanich => [bd2, linearity]
  | bd2 => [noDiamond, scott]
  | linearity => [noDiamond, weakEm]
  | noDiamond => [pierceLuk]
  | weakEm => [scott, kreiselPutnam]
  | pierceLuk => [piercePierce]
  | piercePierce => []
  | scott => []
  | kreiselPutnam => []

/-- What lies at or under each node. -/
def below : Node → List Node
  | em => all
  | smetanich =>
    [smetanich, bd2, linearity, noDiamond, weakEm, pierceLuk, piercePierce, scott, kreiselPutnam]
  | bd2 => [bd2, noDiamond, pierceLuk, piercePierce, scott]
  | linearity => [linearity, noDiamond, weakEm, pierceLuk, piercePierce, scott, kreiselPutnam]
  | noDiamond => [noDiamond, pierceLuk, piercePierce]
  | weakEm => [weakEm, scott, kreiselPutnam]
  | pierceLuk => [pierceLuk, piercePierce]
  | piercePierce => [piercePierce]
  | scott => [scott]
  | kreiselPutnam => [kreiselPutnam]

/-- The separations proved: the first principle of each pair does not derive
the second. -/
def seps : List (Node × Node) :=
  [(smetanich, em), (bd2, smetanich), (noDiamond, bd2), (pierceLuk, noDiamond),
    (piercePierce, pierceLuk), (linearity, bd2), (bd2, weakEm), (weakEm, piercePierce),
    (scott, bd2), (scott, weakEm), (scott, piercePierce), (noDiamond, scott),
    (kreiselPutnam, bd2), (kreiselPutnam, weakEm), (kreiselPutnam, piercePierce),
    (kreiselPutnam, scott), (bd2, kreiselPutnam)]

/-- The class of each node: the principles that derive its representative and
are derived by it, the representative first. -/
def members : Node → List Form
  | em => [excludedMiddleForm (.var 0), emAOrNotBForm (.var 0) (.var 1),
      emAOrBForm (.var 0) (.var 1), pierce₁₂OrDeMorgan₁₂Form (.var 0) (.var 1),
      demorgan₁₂OrImpOr₁₂Form (.var 0) (.var 1), impOr₁₂OrImpOr₂₁Form (.var 0) (.var 1)]
  | smetanich => [smetanichForm (.var 0) (.var 1), peirce₁₂OrImpOr₂₁Form (.var 0) (.var 1),
      em₁OrPeirce₂₁Form (.var 0) (.var 1), emAOrNotB₁₂OrPeirce₁₂Form (.var 0) (.var 1),
      emAOrNotB₁₂OrPeirce₂₁Form (.var 0) (.var 1)]
  | bd2 => [bd2Form (.var 0) (.var 1), demorgan₁₂OrLuk₁₂Form (.var 0) (.var 1),
      impOr₁₂OrLuk₁₂Form (.var 0) (.var 1), pierce₁₂OrLuk₂₁Form (.var 0) (.var 1),
      em₁OrLuk₂₁Form (.var 0) (.var 1), notNot₁OrLuk₂₁Form (.var 0) (.var 1),
      cm₁OrLuk₂₁Form (.var 0) (.var 1), notNot₁OrPeirce₂₁Form (.var 0) (.var 1),
      cm₁OrPeirce₂₁Form (.var 0) (.var 1), emAOrB₁₂OrLuk₁₂Form (.var 0) (.var 1),
      emAOrB₁₂OrLuk₂₁Form (.var 0) (.var 1), emAOrNotB₁₂OrLuk₂₁Form (.var 0) (.var 1)]
  | linearity => [linearityForm (.var 0) (.var 1)]
  | noDiamond => [noDiamondForm (.var 0) (.var 1), notNotAndForm (.var 0) (.var 1),
      impOr₁₂OrLuk₂₁Form (.var 0) (.var 1), luk₁₂OrLuk₂₁Form (.var 0) (.var 1)]
  | weakEm => [weakEmForm (.var 0)]
  | pierceLuk => [pierce₁₂OrLuk₁₂Form (.var 0) (.var 1), peirce₁₂OrImpOr₁₂Form (.var 0) (.var 1)]
  | piercePierce => [pierce₁₂OrPierce₂₁Form (.var 0) (.var 1)]
  | scott => [scottForm (.var 0)]
  | kreiselPutnam => [kreiselPutnamForm (.var 0) (.var 1) (.var 2)]

/-- How far above the bottom a node sits; every edge goes down it. -/
def height : Node → Nat
  | em => 5
  | smetanich => 4
  | bd2 | linearity => 3
  | noDiamond | weakEm => 2
  | pierceLuk => 1
  | piercePierce | scott | kreiselPutnam => 0

theorem height_lt : ∀ x : Node, ∀ z ∈ x.edges, z.height < x.height := by decide

/-- What lies under a node is the node itself or lies under one of its edges. -/
theorem below_step : ∀ x y : Node, y ∈ x.below → y = x ∨ ∃ z ∈ x.edges, y ∈ z.below := by
  decide

/-- Every pair the drawing leaves apart is a separation moved up at its first
node and down at its second. -/
theorem covered : ∀ x y : Node, y ∉ x.below → ∃ p ∈ seps, x ∈ p.1.below ∧ p.2 ∈ y.below := by
  decide

end Node

open Node

/-- **Along an edge, a derivation.** -/
theorem derives_of_edge {x z : Node} (h : z ∈ x.edges) : DerivesFromSchema x.form z.form := by
  cases x <;> simp only [edges, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl <;>
    first
      | exact derives_smetanich_of_em
      | exact derives_bd2_of_smetanich
      | exact derives_linearity_of_smetanich
      | exact derives_noDiamond_of_bd2
      | exact derives_scott_of_bd2
      | exact derives_noDiamond_of_linearity
      | exact derives_weakEm_of_linearity
      | exact derives_pierce₁₂OrLuk₁₂_of_noDiamond
      | exact derives_scott_of_weakEm
      | exact derives_kreiselPutnam_of_weakEm
      | exact derives_pierce₁₂OrPierce₂₁_of_pierce₁₂OrLuk₁₂

/-- **Down the drawing, a derivation**: compose the edges along a path. -/
theorem derives_of_below {x y : Node} (h : y ∈ x.below) : DerivesFromSchema x.form y.form := by
  suffices H : ∀ n (x y : Node), x.height < n → y ∈ x.below →
      DerivesFromSchema x.form y.form from H _ x y (Nat.lt_succ_self _) h
  intro n
  induction n with
  | zero => intro x _ hx; exact absurd hx (Nat.not_lt_zero _)
  | succ n ih =>
    intro x y hx hy
    rcases below_step x y hy with rfl | ⟨z, hz, hyz⟩
    · exact DerivesFromSchema.refl _
    · exact (derives_of_edge hz).trans
        (ih z y (Nat.lt_of_lt_of_le (height_lt x z hz) (Nat.le_of_lt_succ hx)) hyz)

/-- **Each separation is a theorem.** -/
theorem nderiv_of_sep {p : Node × Node} (h : p ∈ seps) :
    ¬ DerivesFromSchema p.1.form p.2.form := by
  simp only [seps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
  first
    | exact smetanich_nderiv_em
    | exact bd2_nderiv_smetanich
    | exact noDiamond_nderiv_bd2
    | exact pierce₁₂OrLuk₁₂_nderiv_noDiamond
    | exact pierce₁₂OrPierce₂₁_nderiv_pierce₁₂OrLuk₁₂
    | exact linearity_nderiv_bd2
    | exact bd2_nderiv_weakEm
    | exact weakEm_nderiv_pierce₁₂OrPierce₂₁
    | exact scott_nderiv_bd2
    | exact scott_nderiv_weakEm
    | exact scott_nderiv_pierce₁₂OrPierce₂₁
    | exact noDiamond_nderiv_scott
    | exact kreiselPutnam_nderiv_bd2
    | exact kreiselPutnam_nderiv_weakEm
    | exact kreiselPutnam_nderiv_pierce₁₂OrPierce₂₁
    | exact kreiselPutnam_nderiv_scott
    | exact bd2_nderiv_kreiselPutnam

/-- **The hierarchy.**  Of any two of the ten principles, one derives the other
exactly when the drawing puts it at or above the other. -/
theorem hierarchy (x y : Node) : DerivesFromSchema x.form y.form ↔ y ∈ x.below := by
  refine ⟨fun h => Classical.byContradiction fun hy => ?_, derives_of_below⟩
  obtain ⟨p, hp, hpx, hyp⟩ := covered x y hy
  exact nderiv_of_sep hp ((derives_of_below hpx).trans (h.trans (derives_of_below hyp)))

/-- **Each member of a class axiomatises its node.**  Every equivalence is a
derivation both ways, from natural deduction derivations between substitution
instances. -/
theorem members_equiv {x : Node} {X : Form} (h : X ∈ x.members) : SchemaEquiv X x.form := by
  cases x <;> simp only [members, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact SchemaEquiv.refl _
      | exact emAOrNotB_equiv_em
      | exact emAOrB_equiv_em
      | exact pierce₁₂OrDeMorgan₁₂_equiv_em
      | exact demorgan₁₂OrImpOr₁₂_equiv_em
      | exact impOr₁₂OrImpOr₂₁_equiv_em
      | exact peirce₁₂OrImpOr₂₁_equiv_smetanich
      | exact em₁OrPeirce₂₁_equiv_smetanich
      | exact emAOrNotB₁₂OrPeirce₁₂_equiv_smetanich
      | exact emAOrNotB₁₂OrPeirce₂₁_equiv_smetanich
      | exact demorgan₁₂OrLuk₁₂_equiv_bd2
      | exact impOr₁₂OrLuk₁₂_equiv_bd2
      | exact pierce₁₂OrLuk₂₁_equiv_bd2
      | exact em₁OrLuk₂₁_equiv_bd2
      | exact notNot₁OrLuk₂₁_equiv_bd2
      | exact cm₁OrLuk₂₁_equiv_bd2
      | exact notNot₁OrPeirce₂₁_equiv_bd2
      | exact cm₁OrPeirce₂₁_equiv_bd2
      | exact emAOrB₁₂OrLuk₁₂_equiv_bd2
      | exact emAOrB₁₂OrLuk₂₁_equiv_bd2
      | exact emAOrNotB₁₂OrLuk₂₁_equiv_bd2
      | exact notNotAnd_equiv_noDiamond
      | exact impOr₁₂OrLuk₂₁_equiv_noDiamond
      | exact luk₁₂OrLuk₂₁_equiv_noDiamond
      | exact peirce₁₂OrImpOr₁₂_equiv_pierce₁₂OrLuk₁₂

/-- **The hierarchy, for every member of every class.**  Of any two principles
in the classes, one derives the other exactly when the drawing puts its node at
or above the other's. -/
theorem hierarchy_members {x y : Node} {X Y : Form} (hX : X ∈ x.members)
    (hY : Y ∈ y.members) : DerivesFromSchema X Y ↔ y ∈ x.below := by
  rw [← hierarchy x y]
  have ex := members_equiv hX
  have ey := members_equiv hY
  exact ⟨fun h => ex.2.trans (h.trans ey.1), fun h => ex.1.trans (h.trans ey.2)⟩
