import Barenco.ControlledCircuit.Alternative
import Barenco.ControlledCircuit.ControlledZ

/-!
# Diagnostic checks for the Section 5 controlled-circuit library

This module is intentionally excluded from the public root. The low-dimensional
actions below are convention and boundary sanity checks only; all general claims
instantiate already-proved arbitrary-width theorems. No sampled calculation is
used as evidence for a circuit classification or resource bound.

Every computation is checked by the Lean kernel. This file uses neither native
evaluation nor bit-vector decision procedures.
-/

namespace Barenco.ControlledCircuitExamples

open Barenco
open Barenco.OneQubit
open Barenco.ControlledCircuit
open Matrix

noncomputable section

private theorem zero_ne_one_fin2 : (0 : Fin 2) ≠ 1 := by decide

/-! ## Lemma 5.2 and arbitrary-width applicability -/

/--
On two qubits, the controlled scalar phase multiplies both target states by the
same phase exactly when the control bit is true.
-/
theorem lemma52_twoQubit_action (delta : ℝ) (controlBit targetBit : Bool) :
    (Circuit.eval (controlledPhaseCircuit (0 : Fin 2) delta) : Gate 2) *ᵥ
        basisKet (twoBit controlBit targetBit) =
      if controlBit then
        (cis delta) • basisKet (twoBit controlBit targetBit)
      else basisKet (twoBit controlBit targetBit) := by
  rw [eval_controlledPhaseCircuit (0 : Fin 2) (1 : Fin 2) zero_ne_one_fin2 delta,
    coe_positiveControlledUnitary, coe_phaseShiftUnitary]
  funext row
  rw [mulVec_basisKet_apply, controlledScalarRaw_apply]
  by_cases hrow : row = twoBit controlBit targetBit
  · subst row
    cases controlBit <;> simp [twoBit, basisKet_apply]
  · cases controlBit <;> simp [hrow, basisKet_apply]

/-- Left endpoint of an arbitrarily padded, visibly non-adjacent register pair. -/
private def farControl (padding : ℕ) : Fin (padding + 3) :=
  ⟨0, by omega⟩

/-- Right endpoint of an arbitrarily padded, visibly non-adjacent register pair. -/
private def farTarget (padding : ℕ) : Fin (padding + 3) :=
  ⟨padding + 2, by omega⟩

private theorem farControl_ne_farTarget (padding : ℕ) :
    farControl padding ≠ farTarget padding := by
  intro h
  have hval := congrArg Fin.val h
  simp [farControl, farTarget] at hval

/-- Corollary 5.3 applies to the two endpoints of every padded register width. -/
theorem nonAdjacent_controlledU2_exists (padding : ℕ) (U : QubitUnitary) :
    ∃ A B C : QubitSpecialUnitary,
      Circuit.eval (controlledU2Circuit (farControl padding) (farTarget padding)
        (farControl_ne_farTarget padding)
        (determinantPhaseAngle U) (specialUnitaryAsUnitary A)
        (specialUnitaryAsUnitary B) (specialUnitaryAsUnitary C)) =
        positiveControlledUnitary (farTarget padding)
          ({⟨farControl padding, farControl_ne_farTarget padding⟩} :
            ControlSet (farTarget padding)) U := by
  exact controlledU2Circuit_exists (farControl padding) (farTarget padding)
    (farControl_ne_farTarget padding) U

/-! ## Lemma 5.1 converse and syntax-derived resources -/

/-- Pauli-X cannot occupy the determinant-one five-gate Lemma 5.1 topology. -/
theorem sigmaX_not_hasControlledSU2Circuit {n : ℕ}
    (control target : Fin n) (h : control ≠ target) :
    ¬ HasControlledSU2Circuit control target h sigmaXUnitary := by
  rw [controlledSU2Circuit_correct_iff]
  norm_num

/-- The Lemma 5.1 circuit contains exactly five priced primitives. -/
example {n : ℕ} (control target : Fin n) (h : control ≠ target)
    (A B C : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
      (controlledABCCircuit control target h A B C) = some 5 := by
  exact controlledABCCircuit_oneQubitCNOTCost control target h A B C

/-- The general controlled-unitary construction contains exactly six priced primitives. -/
example {n : ℕ} (control target : Fin n) (h : control ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
      (controlledU2Circuit control target h delta A B C) = some 6 := by
  exact controlledU2Circuit_oneQubitCNOTCost control target h delta A B C

/-- The Lemma 5.4 topology has exact one-qubit-plus-CNOT cost four. -/
example {n : ℕ} (control target : Fin n) (h : control ≠ target)
    (A B : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
      (twoCNOTCircuit control target h A B) = some 4 := by
  exact twoCNOTCircuit_oneQubitCNOTCost control target h A B

/-- The Lemma 5.5 topology has exact one-qubit-plus-CNOT cost three. -/
example {n : ℕ} (control target : Fin n) (h : control ≠ target)
    (A B : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
      (oneCNOTCircuit control target h A B) = some 3 := by
  exact oneCNOTCircuit_oneQubitCNOTCost control target h A B

/-! ## Symmetric-Euler and Pauli boundaries -/

/-- A zero middle angle collapses the symmetric family to one Z rotation. -/
theorem symmetricEuler_zero_angle (alpha : ℝ) :
    symmetricEuler alpha 0 = rz (2 * alpha) := by
  rw [symmetricEuler, ry_zero, Matrix.mul_one, rz_mul]
  congr 1
  ring

/-- The all-zero symmetric Euler parameters give the identity exactly. -/
example : symmetricEuler 0 0 = (1 : QubitMatrix) := by
  simp [symmetricEuler]

/-- At the zero-angle boundary, Pauli-X itself has a one-CNOT circuit. -/
theorem sigmaX_hasOneCNOTCircuit {n : ℕ}
    (control target : Fin n) (h : control ≠ target) :
    HasOneCNOTUnitaryCircuit control target h sigmaXUnitary := by
  apply (oneCNOTFamily_iff control target h sigmaXUnitary).mpr
  refine ⟨0, 0, ?_⟩
  simp [symmetricEuler]

/-- At the endpoint `theta = pi`, the one-CNOT family contains Pauli-Z. -/
theorem sigmaZ_oneCNOT_boundary :
    sigmaZ = sigmaX * symmetricEuler 0 Real.pi := by
  rw [sigmaX_mul_symmetricEuler_eq_matrix2, sigmaZ_eq_matrix2]
  simp

/-- The endpoint identity supplies an actual one-CNOT Pauli-Z circuit witness. -/
example : HasOneCNOTUnitaryCircuit (0 : Fin 2) (1 : Fin 2)
    zero_ne_one_fin2 sigmaZUnitary := by
  apply (oneCNOTFamily_iff (0 : Fin 2) (1 : Fin 2) zero_ne_one_fin2
    sigmaZUnitary).mpr
  exact ⟨0, Real.pi, by simpa using sigmaZ_oneCNOT_boundary⟩

/-! ## Controlled-Z symmetry and relative sign -/

private theorem zero_ne_two_fin3 : (0 : Fin 3) ≠ 2 := by decide

/-- Controlled-Z is unchanged when two non-adjacent wire labels are swapped. -/
example :
    controlledZUnitary (0 : Fin 3) (2 : Fin 3) zero_ne_two_fin3 =
      controlledZUnitary (2 : Fin 3) (0 : Fin 3) zero_ne_two_fin3.symm := by
  exact controlledZUnitary_swap (0 : Fin 3) (2 : Fin 3) zero_ne_two_fin3

/-- Every active computational-basis state acquires exactly a relative minus sign. -/
example {n : ℕ} (control target : Fin n) (h : control ≠ target)
    (x : Basis n) (hcontrol : x control = true) (htarget : x target = true) :
    controlledZRaw control target h *ᵥ basisKet x = -basisKet x := by
  rw [controlledZRaw_truthTable]
  simp [hcontrol, htarget]

end

end Barenco.ControlledCircuitExamples
