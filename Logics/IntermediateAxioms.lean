import Logics.IntermediateAxioms.AxiomDef
import Logics.IntermediateAxioms.Derivation
import Logics.IntermediateAxioms.Model
import Logics.IntermediateAxioms.StrictImply
import Logics.IntermediateAxioms.Refuter.ClassicalRefuter
import Logics.IntermediateAxioms.Refuter.SmetanichRefuter
import Logics.IntermediateAxioms.Refuter.BD2Refuter
import Logics.IntermediateAxioms.Refuter.NoDiamondRefuter
import Logics.IntermediateAxioms.Refuter.KCRefuter
import Logics.IntermediateAxioms.Refuter.LCRefuter
import Logics.IntermediateAxioms.Refuter.ScottRefuter
import Logics.IntermediateAxioms.Refuter.NoKiteUp1x2Refuter
import Logics.IntermediateAxioms.Refuter.NoDiamondHairRefuter
import Logics.IntermediateAxioms.Refuter.NoForkUp2x2Refuter
import Logics.IntermediateAxioms.Refuter.KPRefuter
import Logics.IntermediateAxioms.Refuter.KPMinimal
import Logics.IntermediateAxioms.Refuter.KPInfinite
import Logics.IntermediateAxioms.Hierarchy

/-!
# Axioms of the intermediate logics

The principles collected here are the classical ones and the weaker axioms
that combining or weakening them produces.  Only some are equivalent to
classical logic; the rest axiomatise logics strictly between it and the
intuitionistic calculus, which is what makes the hierarchy worth drawing.

* `AxiomDef`     -- the principles, as formulas
* `Derivation`   -- which principle derives which, and at which arguments, as
  natural deduction derivations from a schema
* `Model`        -- how each one fares in concrete Heyting algebras
* `StrictImply`  -- what none of their instances prove

Those four cover every principle at once.  The `Refuter` directory does the
opposite: each file takes a single axiom and settles it completely, naming the
algebras that refute it minimally and so exactly which schemas derive it.  All
but the last do this with a finite list; Kreisel and Putnam's axiom needs an
infinite one.

* `Refuter.ClassicalRefuter` -- excluded middle, refuted by `Fin 3` alone
* `Refuter.SmetanichRefuter` -- Smetanich's axiom, by `Fin 4` and `ForkUp 1 1`
* `Refuter.BD2Refuter`       -- bounded depth two, by `Fin 4` alone
* `Refuter.NoDiamondRefuter` -- `noDiamondForm`, by `KiteUp 1 1` alone
* `Refuter.KCRefuter`        -- weak excluded middle, by `ForkUp 1 1` alone
* `Refuter.LCRefuter`        -- linearity, by `ForkUp 1 1` and `KiteUp 1 1`
* `Refuter.ScottRefuter`     -- Scott's axiom, by `ForkUp 1 2` alone
* `Refuter.NoKiteUp1x2Refuter` -- `noKiteUp1x2Form`, by the uneven kite `KiteUp 1 2`
  alone
* `Refuter.NoDiamondHairRefuter` -- `noDiamondHairForm`, by `DiamondHair`, the
  diamond with a hair, alone
* `Refuter.NoForkUp2x2Refuter` -- `noForkUp2x2Form`, by the tall fork `ForkUp 2 2`
  alone
* `Refuter.KPRefuter`        -- Kreisel and Putnam's axiom, by the infinite list
  of finite rooted frames with a region entered at two points: sound, and
  complete for every schema with the finite model property
* `Refuter.KPMinimal`        -- the shape of that list's minimal members: two
  regimes, one with at most three frames and one with a fixed pure part
* `Refuter.KPInfinite`       -- those minimal members are infinitely many: a
  ladder of frames, one of each size from seven points up

`Hierarchy` draws the hierarchy and its classes, and puts the two halves
together: for every principle in the classes, it decides exactly which derives
which.
-/
