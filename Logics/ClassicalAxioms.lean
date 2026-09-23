import Logics.ClassicalAxioms.AxiomDef
import Logics.ClassicalAxioms.Implication
import Logics.ClassicalAxioms.Model
import Logics.ClassicalAxioms.Refuter.StrictImply
import Logics.ClassicalAxioms.ClassicalRefuter
import Logics.ClassicalAxioms.Refuter.SmetanichRefuter
import Logics.ClassicalAxioms.Refuter.BD2Refuter

/-!
# Classical principles over intuitionistic logic

* `AxiomDef`     -- the principles, as predicates on propositions and as formulas
* `Implication`  -- which principle proves which, and at which arguments
* `Model`        -- how each one fares in concrete Heyting algebras
* `Refuter.StrictImply` -- what none of their instances prove
* `ClassicalRefuter`    -- the one algebra that refutes excluded middle, and
  exactly which schemas derive it
* `Refuter.SmetanichRefuter` -- Smetanich's axiom in full: which algebras
  refute it minimally, and exactly which schemas derive it
* `Refuter.BD2Refuter` -- the same for bounded depth two, which has a single
  minimal refuter
-/
