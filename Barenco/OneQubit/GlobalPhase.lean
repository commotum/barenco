import Barenco.OneQubit.Certified
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Splitting a one-qubit unitary into scalar phase and special-unitary part

This file supplies the determinant step that the proof of Lemma 4.1 sketches.
For a two-by-two unitary `U`, its determinant lies on the unit circle.  Dividing
the principal argument of that determinant by two chooses a scalar phase whose
two-by-two determinant is exactly `det U`; removing it leaves an element of
`SU(2)`.

The choice is noncanonical at the principal-argument branch cut, and no
continuity of the selected angle is claimed.  The reconstruction and determinant
equations are exact.
-/

namespace Barenco.OneQubit

noncomputable section

/-- Half the principal argument of a one-qubit unitary's determinant. -/
def determinantPhaseAngle (U : QubitUnitary) : ℝ :=
  Complex.arg (Matrix.det (U : QubitMatrix)) / 2

/-- The chosen scalar phase has exactly the determinant of `U`. -/
theorem cis_two_determinantPhaseAngle (U : QubitUnitary) :
    cis (2 * determinantPhaseAngle U) = Matrix.det (U : QubitMatrix) := by
  have hdetUnitary : Matrix.det (U : QubitMatrix) ∈ unitary ℂ :=
    Matrix.det_of_mem_unitary U.property
  have hnorm : ‖Matrix.det (U : QubitMatrix)‖ = 1 :=
    CStarRing.norm_of_mem_unitary hdetUnitary
  rw [determinantPhaseAngle]
  have hangle :
      2 * (Complex.arg (Matrix.det (U : QubitMatrix)) / 2) =
        Complex.arg (Matrix.det (U : QubitMatrix)) := by ring
  rw [hangle]
  simpa only [cis, hnorm, Complex.ofReal_one, one_mul] using
    Complex.norm_mul_exp_arg_mul_I (Matrix.det (U : QubitMatrix))

/-- Remove the selected scalar determinant phase while retaining unitarity. -/
def removeGlobalPhase (U : QubitUnitary) : QubitUnitary :=
  phaseShiftUnitary (-determinantPhaseAngle U) * U

@[simp]
theorem coe_removeGlobalPhase (U : QubitUnitary) :
    (removeGlobalPhase U : QubitMatrix) =
      phaseShift (-determinantPhaseAngle U) * (U : QubitMatrix) := rfl

/-- Removing the selected scalar phase leaves determinant one. -/
@[simp]
theorem removeGlobalPhase_det (U : QubitUnitary) :
    Matrix.det (removeGlobalPhase U : QubitMatrix) = 1 := by
  rw [coe_removeGlobalPhase, Matrix.det_mul, phaseShift_det,
    ← cis_two_determinantPhaseAngle U]
  calc
    cis (2 * -determinantPhaseAngle U) * cis (2 * determinantPhaseAngle U) =
        cis (2 * -determinantPhaseAngle U + 2 * determinantPhaseAngle U) :=
      (cis_add _ _).symm
    _ = cis 0 := by
      congr 1
      ring
    _ = 1 := cis_zero

/-- The determinant-one part of a one-qubit unitary, with its certificate. -/
def specialUnitaryPart (U : QubitUnitary) : QubitSpecialUnitary :=
  ⟨removeGlobalPhase U,
    Matrix.mem_specialUnitaryGroup_iff.mpr
      ⟨(removeGlobalPhase U).property, removeGlobalPhase_det U⟩⟩

@[simp]
theorem coe_specialUnitaryPart (U : QubitUnitary) :
    (specialUnitaryPart U : QubitMatrix) = (removeGlobalPhase U : QubitMatrix) := rfl

/-- Reattaching the selected scalar phase exactly reconstructs `U`. -/
theorem phaseShift_mul_removeGlobalPhase (U : QubitUnitary) :
    phaseShiftUnitary (determinantPhaseAngle U) * removeGlobalPhase U = U := by
  apply Subtype.ext
  change phaseShift (determinantPhaseAngle U) *
      (phaseShift (-determinantPhaseAngle U) * (U : QubitMatrix)) =
    (U : QubitMatrix)
  rw [← Matrix.mul_assoc, phaseShift_mul]
  simp

/-- Raw matrix form of exact phase reconstruction. -/
theorem phaseShift_mul_specialUnitaryPart (U : QubitUnitary) :
    phaseShift (determinantPhaseAngle U) *
        (specialUnitaryPart U : QubitMatrix) = (U : QubitMatrix) := by
  exact congrArg Subtype.val (phaseShift_mul_removeGlobalPhase U)

end

end Barenco.OneQubit
