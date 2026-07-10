import Barenco.Basic
import Barenco.Semantics
import Barenco.Controlled
import Barenco.Circuit
import Barenco.Equivalence.Phase
import Barenco.Equivalence.Measurement
import Barenco.Equivalence.OperatorNorm
import Barenco.Equivalence.ControlledDistance
import Barenco.Equivalence.EventProbability
import Barenco.Cost
import Barenco.ControlledCircuit.Expansion
import Barenco.ControlledCircuit.ControlledZ
import Barenco.ControlledCircuit.Selected
import Barenco.ControlledCircuit.SelectedSpecial
import Barenco.OneQubit.Lemma43
import Barenco.OneQubit.Pauli
import Barenco.OneQubit.U2Euler
import Barenco.OneQubit.Roots
import Barenco.OneQubit.CoherentRoots
import Barenco.OneQubit.CircuitBridge
import Barenco.OneQubit.SelectedABC
import Barenco.State.CleanWire
import Barenco.ThreeQubit.Expansion
import Barenco.ThreeQubit.RelativePhase
import Barenco.MultiControl.Lemma71
import Barenco.MultiControl.BorrowedSemantics
import Barenco.MultiControl.BorrowedResources
import Barenco.MultiControl.FourBlock
import Barenco.MultiControl.Corollary74
import Barenco.MultiControl.RelativePhase
import Barenco.MultiControl.Corollary74Expansion
import Barenco.MultiControl.GrayExpansion
import Barenco.MultiControl.Recursive
import Barenco.MultiControl.RecursiveExpansion
import Barenco.MultiControl.Resources
import Barenco.MultiControl.Approximate
import Barenco.MultiControl.ApproximateExpansion
import Barenco.MultiControl.ApproximationResources
import Barenco.LowerBounds.BasicCircuit
import Barenco.LowerBounds.InteractionGraph
import Barenco.LowerBounds.PartitionFactorization
import Barenco.LowerBounds.ScalarObstruction
import Barenco.LowerBounds.Lemma77
import Barenco.MultiControl.LastTargetSwap
import Barenco.MultiControl.LinearSpecialUnitary
import Barenco.MultiControl.LinearSpecialUnitaryExpansion
import Barenco.MultiControl.LinearSpecialUnitaryPhase
import Barenco.MultiControl.CleanAncilla
import Barenco.MultiControl.CleanAncillaExpansion
import Barenco.MultiControl.LinearResources
import Barenco.Universality.ExactSynthesis
import Barenco.Universality.WidthOne
import Barenco.Universality.ZeroWidth

/-!
# Barenco

Reusable Lean formalization inspired by Barenco et al., “Elementary Gates for
Quantum Computation” (1995).

The root module exposes only stable, compiled public modules. Diagnostic examples
remain separate. See
`docs/conventions.md` and `docs/traceability.md` for the relationship between the
library and the paper.
-/
