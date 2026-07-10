import Barenco.ThreeQubit.RelativePhaseThreeGate

/-!
# Diagnostics for the three-gate relative-phase Toffoli construction

This root-excluded module checks the smallest canonical register and a padded
nonadjacent layout.  The checks expose literal ordered-pair chronology, exact
full-register semantics, the signed basis action, and both named cost models.
-/

namespace Barenco.ThreeQubit.RelativePhaseThreeGateExamples

open Barenco.Optimization
open scoped Matrix

noncomputable section

/-- Ordered-pair chronology of the generic two-wire nodes in a visible circuit. -/
private def twoQubitPairTrace {n : ℕ} : FusionCircuit n → List (OrderedWirePair n)
  | [] => []
  | FusionPrimitive.twoQubit pair _ :: circuit =>
      pair :: twoQubitPairTrace circuit
  | _ :: circuit => twoQubitPairTrace circuit

/-! ## Canonical width-three layout -/

private def first3 : Fin 3 := 0
private def second3 : Fin 3 := 1
private def target3 : Fin 3 := 2

private theorem first3_ne_second3 : first3 ≠ second3 := by decide
private theorem first3_ne_target3 : first3 ≠ target3 := by decide
private theorem second3_ne_target3 : second3 ≠ target3 := by decide

/-- The smallest layout retains the exact advertised ordered-pair chronology. -/
example :
    twoQubitPairTrace
        (relativePhaseToffoliThreeGateFusionCircuit first3 second3 target3
          first3_ne_target3 second3_ne_target3) =
      [⟨second3, target3, second3_ne_target3⟩,
        ⟨first3, target3, first3_ne_target3⟩,
        ⟨second3, target3, second3_ne_target3⟩] := rfl

/-- The width-three diagnostic uses the exact signed unitary, not a phase quotient. -/
example :
    Circuit.eval
        (relativePhaseToffoliThreeGateCircuit first3 second3 target3
          first3_ne_target3 second3_ne_target3) =
      relativeToffoliUnitary first3 second3 target3
        first3_ne_target3 second3_ne_target3 :=
  eval_relativePhaseToffoliThreeGateCircuit first3 second3 target3
    first3_ne_target3 second3_ne_target3

/-- The exact `101` input-column sign is visible at the smallest legal width. -/
example (input : Basis 3) :
    (Circuit.eval
        (relativePhaseToffoliThreeGateCircuit first3 second3 target3
          first3_ne_target3 second3_ne_target3) : Gate 3) *ᵥ basisKet input =
      (relativeToffoliPhase first3 second3 target3
        first3_ne_target3 second3_ne_target3
        (splitTarget target3 input).2 (input target3) : ℂ) •
        basisKet (toffoliOutput first3 second3 target3 input) :=
  relativePhaseToffoliThreeGateCircuit_mulVec_basisKet
    first3 second3 target3 first3_ne_second3 first3_ne_target3
      second3_ne_target3 input

/-- Section 8 charges three; the earlier one-qubit/CNOT model rejects the U(4)s. -/
example :
    Circuit.cost CostModel.arbitraryTwoQubit
        (relativePhaseToffoliThreeGateCircuit first3 second3 target3
          first3_ne_target3 second3_ne_target3) = some 3 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (relativePhaseToffoliThreeGateCircuit first3 second3 target3
          first3_ne_target3 second3_ne_target3) = none := by
  simp

/-! ## Padded nonadjacent width-five layout -/

private def first5 : Fin 5 := 4
private def second5 : Fin 5 := 0
private def target5 : Fin 5 := 2

private theorem first5_ne_second5 : first5 ≠ second5 := by decide
private theorem first5_ne_target5 : first5 ≠ target5 := by decide
private theorem second5_ne_target5 : second5 ≠ target5 := by decide

/-- Nonadjacent endpoints do not alter the literal ordered-pair schedule. -/
example :
    twoQubitPairTrace
        (relativePhaseToffoliThreeGateFusionCircuit first5 second5 target5
          first5_ne_target5 second5_ne_target5) =
      [⟨second5, target5, second5_ne_target5⟩,
        ⟨first5, target5, first5_ne_target5⟩,
        ⟨second5, target5, second5_ne_target5⟩] := rfl

/-- Exact equality is over the full padded register, including both spectators. -/
example :
    Circuit.eval
        (relativePhaseToffoliThreeGateCircuit first5 second5 target5
          first5_ne_target5 second5_ne_target5) =
      relativeToffoliUnitary first5 second5 target5
        first5_ne_target5 second5_ne_target5 :=
  eval_relativePhaseToffoliThreeGateCircuit first5 second5 target5
    first5_ne_target5 second5_ne_target5

/-- The padded circuit has the same exact signed basis action. -/
example (input : Basis 5) :
    (Circuit.eval
        (relativePhaseToffoliThreeGateCircuit first5 second5 target5
          first5_ne_target5 second5_ne_target5) : Gate 5) *ᵥ basisKet input =
      (relativeToffoliPhase first5 second5 target5
        first5_ne_target5 second5_ne_target5
        (splitTarget target5 input).2 (input target5) : ℂ) •
        basisKet (toffoliOutput first5 second5 target5 input) :=
  relativePhaseToffoliThreeGateCircuit_mulVec_basisKet
    first5 second5 target5 first5_ne_second5 first5_ne_target5
      second5_ne_target5 input

/-- Padding does not change either syntax-derived model result. -/
example :
    Circuit.cost CostModel.arbitraryTwoQubit
        (relativePhaseToffoliThreeGateCircuit first5 second5 target5
          first5_ne_target5 second5_ne_target5) = some 3 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (relativePhaseToffoliThreeGateCircuit first5 second5 target5
          first5_ne_target5 second5_ne_target5) = none := by
  simp

end

end Barenco.ThreeQubit.RelativePhaseThreeGateExamples
