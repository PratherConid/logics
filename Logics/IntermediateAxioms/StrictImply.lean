import Logics.IntermediateAxioms.Model

/-!
# What the principles do not prove

Soundness, read backwards, turns the measurements of the previous file into
underivability: anything with a proof takes the top value under every
valuation, so a formula that misses the top value somewhere has no proof.

The first theorems apply this to bare intuitionistic logic.  Three of them
cover the whole development, since every principle here derives one of the
three: the tall fork refutes `pierce₁₂OrPierce₂₁Form`, the uneven fork
`scottForm`, and the three branch fork `kreiselPutnamForm`.

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

## The separating algebras

Most of the principles lie on one chain, the *spine*: from `excludedMiddleForm`
through `smetanichForm`, `bd2Form`, `noDiamondForm` and `pierce₁₂OrLuk₁₂Form`
down to `pierce₁₂OrPierce₂₁Form`.  Linearity, weak excluded middle, Scott's
axiom and Kreisel and Putnam's axiom lie beside it.  The separations below make
each step down the spine strict, and place the four beside it.

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

The algebras listed above separate the levels of the spine, but separating is
not the same as exhausting.  Showing that one of them is also the *complete*
list of minimal refuters, so that a schema derives the level precisely when it
fails there, takes a further argument, made where a single axiom is studied on
its own rather than the whole chain at once.

The shape of each algebra is what it contributes.  The chains `Fin 3` and
`Fin 4` are linear, and length is what tells the middle principles apart: the
lower levels survive every chain, while `bd2Form` dies once a chain has two
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
exists.  Every level of the spine derives it, so none of them is one
either. -/
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
