import Logics.IntermediateAxioms.Derivation
import Logics.IntermediateAxioms.Refuter.SmetanichRefuter
import Logics.IntermediateAxioms.Refuter.BD2Refuter
import Logics.IntermediateAxioms.Refuter.LCRefuter
import Logics.IntermediateAxioms.Refuter.ScottRefuter

/-!
# The shape of the hierarchy

`Logics/IntermediateAxioms/StrictImply.lean` draws ten principles as a poset
and proves the separations the drawing needs.  The edges are derivations from
a schema, each a natural deduction derivation from substitution instances
(`Logics/IntermediateAxioms/Derivation.lean`).  This file puts the two halves
together.  `hierarchy` says, for every pair of the ten, that one derives the
other exactly when the drawing puts it at or above the other.

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

Each node also stands for a class (`Node.members`), and every member is
equivalent to the representative by derivations both ways (`members_equiv`),
so `hierarchy_members` extends the statement to all of them.
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
  | smetanich => smetanichForm
  | bd2 => bd2Form
  | linearity => linearityForm
  | noDiamond => noDiamondForm
  | weakEm => weakEmForm
  | pierceLuk => pierce₁₂OrLuk₁₂Form
  | piercePierce => pierce₁₂OrPierce₂₁Form
  | scott => scottForm
  | kreiselPutnam => kreiselPutnamForm

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
      emAOrBForm (.var 0) (.var 1), pierce₁₂OrDeMorgan₁₂Form, demorgan₁₂OrImpOr₁₂Form,
      impOr₁₂OrImpOr₂₁Form]
  | smetanich => [smetanichForm, peirce₁₂OrImpOr₂₁Form, em₁OrPeirce₂₁Form,
      emAOrNotB₁₂OrPeirce₁₂Form, emAOrNotB₁₂OrPeirce₂₁Form]
  | bd2 => [bd2Form, demorgan₁₂OrLuk₁₂Form, impOr₁₂OrLuk₁₂Form, pierce₁₂OrLuk₂₁Form,
      em₁OrLuk₂₁Form, notNot₁OrLuk₂₁Form, cm₁OrLuk₂₁Form, notNot₁OrPeirce₂₁Form,
      cm₁OrPeirce₂₁Form, emAOrB₁₂OrLuk₁₂Form, emAOrB₁₂OrLuk₂₁Form, emAOrNotB₁₂OrLuk₂₁Form]
  | linearity => [linearityForm]
  | noDiamond => [noDiamondForm, notNotAndForm, impOr₁₂OrLuk₂₁Form, luk₁₂OrLuk₂₁Form]
  | weakEm => [weakEmForm]
  | pierceLuk => [pierce₁₂OrLuk₁₂Form, peirce₁₂OrImpOr₁₂Form]
  | piercePierce => [pierce₁₂OrPierce₂₁Form]
  | scott => [scottForm]
  | kreiselPutnam => [kreiselPutnamForm]

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
