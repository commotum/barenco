import Barenco.Basic
import Barenco.Semantics
import Barenco.Controlled
import Barenco.Circuit
import Barenco.Equivalence.Phase
import Barenco.Equivalence.Measurement
import Barenco.Equivalence.OperatorNorm
import Barenco.Cost

/-!
# Barenco

Reusable Lean formalization inspired by Barenco et al., “Elementary Gates for
Quantum Computation” (1995).

The root module exposes only stable, compiled public modules. Diagnostic examples
remain separate. See
`docs/conventions.md` and `docs/traceability.md` for the relationship between the
library and the paper.
-/
