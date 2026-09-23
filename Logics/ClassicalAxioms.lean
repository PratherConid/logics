import Logics.ClassicalAxioms.AxiomDef
import Logics.ClassicalAxioms.Implication
import Logics.ClassicalAxioms.Model
import Logics.ClassicalAxioms.StrictImply
import Logics.ClassicalAxioms.Refuter.ClassicalRefuter
import Logics.ClassicalAxioms.Refuter.SmetanichRefuter
import Logics.ClassicalAxioms.Refuter.BD2Refuter

/-!
# Classical principles over intuitionistic logic

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
-/
