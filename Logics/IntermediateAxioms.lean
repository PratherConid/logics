import Logics.IntermediateAxioms.AxiomDef
import Logics.IntermediateAxioms.Implication
import Logics.IntermediateAxioms.Model
import Logics.IntermediateAxioms.StrictImply
import Logics.IntermediateAxioms.Refuter.ClassicalRefuter
import Logics.IntermediateAxioms.Refuter.SmetanichRefuter
import Logics.IntermediateAxioms.Refuter.BD2Refuter
import Logics.IntermediateAxioms.Refuter.NoDiamondRefuter
import Logics.IntermediateAxioms.Refuter.KCRefuter
import Logics.IntermediateAxioms.Refuter.LCRefuter

/-!
# Axioms of the intermediate logics

The principles collected here are the classical ones and the weaker axioms
that combining or weakening them produces.  Only some are equivalent to
classical logic; the rest axiomatise logics strictly between it and the
intuitionistic calculus, which is what makes the hierarchy worth drawing.

* `AxiomDef`     -- the principles, as predicates on propositions and as formulas
* `Implication`  -- which principle proves which, and at which arguments
* `Model`        -- how each one fares in concrete Heyting algebras
* `StrictImply`  -- what none of their instances prove

Those four cover every principle at once.  The `Refuter` directory does the
opposite: each file takes a single axiom and settles it completely, naming the
algebras that refute it minimally and so exactly which schemas derive it.

* `Refuter.ClassicalRefuter` -- excluded middle, refuted by `Fin 3` alone
* `Refuter.SmetanichRefuter` -- Smetanich's axiom, by `Fin 4` and `ForkUp 1 1`
* `Refuter.BD2Refuter`       -- bounded depth two, by `Fin 4` alone
* `Refuter.NoDiamondRefuter` -- `NoDiamondF`, by `KiteUp 1 1` alone
* `Refuter.KCRefuter`        -- weak excluded middle, by `ForkUp 1 1` alone
* `Refuter.LCRefuter`        -- linearity, by `ForkUp 1 1` and `KiteUp 1 1`
-/
