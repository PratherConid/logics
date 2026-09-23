import Logics.ClassicalAxioms.AxiomDef
import Logics.ClassicalAxioms.Implication
import Logics.ClassicalAxioms.Model
import Logics.ClassicalAxioms.StrictImply
import Logics.ClassicalAxioms.ThreeChain
import Logics.ClassicalAxioms.Minimal
import Logics.ClassicalAxioms.ChainBranch

/-!
# Classical principles over intuitionistic logic

* `AxiomDef`     -- the principles, as predicates on propositions and as formulas
* `Implication`  -- which principle proves which, and at which arguments
* `Model`        -- how each one fares in concrete Heyting algebras
* `StrictImply`  -- what none of their instances prove
* `ThreeChain`   -- why the top of the hierarchy has exactly one witness
* `Minimal`      -- the separating algebras at the second level cannot be shrunk
-/
