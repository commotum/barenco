import Barenco.Basic
import Barenco.Semantics
import Barenco.Controlled
import Barenco.Circuit
import Barenco.Equivalence.Phase
import Barenco.Equivalence.Measurement
import Barenco.Equivalence.OperatorNorm
import Barenco.Cost
import Barenco.ControlledCircuit.Expansion
import Barenco.ControlledCircuit.ControlledZ
import Barenco.OneQubit.Lemma43
import Barenco.OneQubit.Pauli
import Barenco.OneQubit.U2Euler
import Barenco.OneQubit.Roots
import Barenco.OneQubit.CircuitBridge
import Barenco.ThreeQubit.Expansion
import Barenco.ThreeQubit.RelativePhase

/-!
# Barenco

Reusable Lean formalization inspired by Barenco et al., “Elementary Gates for
Quantum Computation” (1995).

The root module exposes only stable, compiled public modules. Diagnostic examples
remain separate. See
`docs/conventions.md` and `docs/traceability.md` for the relationship between the
library and the paper.
-/
