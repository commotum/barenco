import Barenco.OneQubit.CircuitBridge
import Barenco.OneQubit.Lemma43
import Barenco.OneQubit.Roots
import Barenco.OneQubit.U2Euler

/-!
# Diagnostic one-qubit convention and boundary checks

This module is intentionally excluded from the public root.  Its examples pin the
row/column sign change, the independent Pauli-X constructions, and root boundary
cases without replacing any general proof by numerical testing. Every declaration
is diagnostic; none is public runtime or proof-side API.
-/

namespace Barenco.OneQubitExamples

open Barenco
open Barenco.OneQubit

/-- The paper-row Y rotation has a positive upper-right entry at angle `pi`. -/
example : paperRy Real.pi false true = 1 := by simp

/-- The standard-column transpose has the opposite upper-right sign. -/
example : ry Real.pi false true = -1 := by simp

/-- The standard-column lower-left entry has the corresponding positive sign. -/
example : ry Real.pi true false = 1 := by simp

/-- Explicit-matrix and permutation constructions of Pauli-X agree as certificates. -/
example : sigmaXUnitary = pauliX := sigmaXUnitary_eq_pauliX

/-- The selected exact square root works for Pauli-X. -/
example : unitarySquareRoot sigmaXUnitary ^ 2 = sigmaXUnitary := by simp

/-- The general root construction includes the identity on a zero-qubit register. -/
example : unitarySquareRoot (1 : UnitaryGate 0) ^ 2 = 1 := by simp

/-- The translated Euler expression exposes the reversal of its outer factors. -/
example (alpha theta beta : ℝ) :
    columnEuler alpha theta beta = rz beta * ry theta * rz alpha :=
  columnEuler_eq alpha theta beta

/-- The paper-facing existential theorem exposes its raw `A B C` product order. -/
example (W : QubitSpecialUnitary) :
    ∃ A B C : QubitSpecialUnitary,
      (A : QubitMatrix) * (B : QubitMatrix) * (C : QubitMatrix) = 1 ∧
        (A : QubitMatrix) * paperX * (B : QubitMatrix) * paperX *
          (C : QubitMatrix) = (W : QubitMatrix) :=
  specialUnitary_exists_paperABC W

/-- The standard-column existential theorem pins the reversed chronological order. -/
example (W : QubitSpecialUnitary) :
    ∃ A B C : QubitSpecialUnitary,
      (C : QubitMatrix) * (B : QubitMatrix) * (A : QubitMatrix) = 1 ∧
        (C : QubitMatrix) * sigmaX * (B : QubitMatrix) * sigmaX *
          (A : QubitMatrix) = (W : QubitMatrix) :=
  specialUnitary_exists_columnChronologicalABC W

/-- The A/B/C construction is a matrix theorem even at all-zero angles. -/
example :
    paperA 0 0 * paperX * paperB 0 0 0 * paperX * paperC 0 0 =
      (1 : QubitMatrix) := by
  rw [paperA_mul_X_mul_paperB_mul_X_mul_paperC]
  simp [paperEuler]

end Barenco.OneQubitExamples
