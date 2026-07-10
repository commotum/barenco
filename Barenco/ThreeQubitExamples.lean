import Barenco.ThreeQubit.Expansion

/-!
# Diagnostic checks for Section 6 three-qubit constructions

This module instantiates the arbitrary-width public theorems at concrete wire
layouts. It is diagnostic and intentionally excluded from the public root.
-/

namespace Barenco.ThreeQubitExamples

open Barenco
open Barenco.OneQubit
open Barenco.ThreeQubit

noncomputable section

private theorem fin3_zero_ne_one : (0 : Fin 3) ≠ 1 := by decide
private theorem fin3_zero_ne_two : (0 : Fin 3) ≠ 2 := by decide
private theorem fin3_one_ne_two : (1 : Fin 3) ≠ 2 := by decide

/-- The selected-root Lemma 6.1 circuit specializes directly to three wires. -/
example (U : QubitUnitary) :
    Circuit.eval
        (doubleControlledRootCircuit (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_one fin3_zero_ne_two fin3_one_ne_two U) =
      positiveControlledUnitary (2 : Fin 3)
        (twoControlSet (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_two fin3_one_ne_two) U := by
  exact eval_doubleControlledRootCircuit (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
    fin3_zero_ne_one fin3_zero_ne_two fin3_one_ne_two U

/-- The unexpanded source diagram is five macros but is not early-basic syntax. -/
example (V : QubitUnitary) :
    Circuit.gateCount
        (doubleControlledViaSquareCircuit (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_one fin3_zero_ne_two fin3_one_ne_two V) = 5 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (doubleControlledViaSquareCircuit (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_one fin3_zero_ne_two fin3_one_ne_two V) = none := by
  simp

/-- Corollary 6.2 supplies an exact sixteen-basic-gate circuit for every target. -/
example (U : QubitUnitary) :
    ∃ circuit : Circuit 3,
      Circuit.eval circuit = positiveControlledUnitary (2 : Fin 3)
        (twoControlSet (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
          fin3_zero_ne_two fin3_one_ne_two) U ∧
      Circuit.gateCount circuit = 16 ∧
      Circuit.kindCount .oneQubit circuit = 8 ∧
      Circuit.kindCount .cnot circuit = 8 ∧
      Circuit.cost CostModel.oneQubitCNOT circuit = some 16 := by
  exact doubleControlledUnitary_has_sixteenPrimitiveCircuit
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
    fin3_zero_ne_one fin3_zero_ne_two fin3_one_ne_two U

private theorem fin5_four_ne_zero : (4 : Fin 5) ≠ 0 := by decide
private theorem fin5_four_ne_two : (4 : Fin 5) ≠ 2 := by decide
private theorem fin5_zero_ne_two : (0 : Fin 5) ≠ 2 := by decide

/--
The exact theorem is not tied to adjacent wires: controls `4` and `0` may target
wire `2`, with wires `1` and `3` included as untouched spectators.
-/
example (U : QubitUnitary) :
    Circuit.eval
        (doubleControlledRootCircuit (4 : Fin 5) (0 : Fin 5) (2 : Fin 5)
          fin5_four_ne_zero fin5_four_ne_two fin5_zero_ne_two U) =
      positiveControlledUnitary (2 : Fin 5)
        (twoControlSet (4 : Fin 5) (0 : Fin 5) (2 : Fin 5)
          fin5_four_ne_two fin5_zero_ne_two) U := by
  exact eval_doubleControlledRootCircuit (4 : Fin 5) (0 : Fin 5) (2 : Fin 5)
    fin5_four_ne_zero fin5_four_ne_two fin5_zero_ne_two U

end

end Barenco.ThreeQubitExamples
