import Barenco.ControlledCircuit.Phase
import Barenco.ControlledCircuit.SpecialTopology
import Barenco.ControlledCircuit.PauliConjugate

/-!
# Special controlled-one-qubit circuit classifications

This leaf combines the exact three- and four-gate topology semantics with the
Pauli-conjugate classification to prove both directions of Barenco et al.,
Lemmas 5.4 and 5.5.

Under standard-column semantics, the Lemma 5.4 target family is
`symmetricEuler alpha theta = Rz alpha * Ry theta * Rz alpha`. The Lemma 5.5
family is `X * symmetricEuler alpha theta`; this is the transpose of the paper's
display after harmless renaming of unrestricted parameters.

The paper gives only a one-sentence argument for Lemma 5.5's iff and changes
from special-unitary witnesses in Lemma 5.4 to arbitrary unitary witnesses. The
formal converse below derives `B = A†` from the inactive control branch and
removes the scalar phase of arbitrary `A` exactly before applying the proved
Pauli classification.
-/

namespace Barenco.ControlledCircuit

open Barenco.OneQubit

noncomputable section

/-! ## Lemma 5.4 -/

/-- Existence of special-unitary witnesses in the two-CNOT topology. -/
def HasTwoCNOTSpecialCircuit {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (W : QubitUnitary) : Prop :=
  ∃ A B : QubitSpecialUnitary,
    Circuit.eval (twoCNOTCircuit control target h
      (specialUnitaryAsUnitary A) (specialUnitaryAsUnitary B)) =
      positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) W

/--
Barenco et al., Lemma 5.4, both directions, in standard-column orientation.
-/
theorem twoCNOTFamily_iff {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (W : QubitUnitary) :
    HasTwoCNOTSpecialCircuit control target h W ↔
      ∃ alpha theta : ℝ, (W : QubitMatrix) = symmetricEuler alpha theta := by
  constructor
  · rintro ⟨A, B, heval⟩
    obtain ⟨hinactive, hactive⟩ :=
      (eval_twoCNOTCircuit_eq_iff control target h
        (specialUnitaryAsUnitary A) (specialUnitaryAsUnitary B) W).mp heval
    have hBA : specialUnitaryAsUnitary B * specialUnitaryAsUnitary A = 1 := by
      apply Subtype.ext
      simpa using hinactive
    have hB := eq_inv_of_mul_eq_one_left hBA
    have hBrawUnit : (specialUnitaryAsUnitary B : QubitMatrix) =
        star (specialUnitaryAsUnitary A : QubitMatrix) := by
      have hval := congrArg Subtype.val hB
      change (specialUnitaryAsUnitary B : QubitMatrix) =
        star (specialUnitaryAsUnitary A : QubitMatrix) at hval
      exact hval
    simp only [coe_specialUnitaryAsUnitary] at hBrawUnit hactive
    rw [hBrawUnit] at hactive
    obtain ⟨alpha, theta, hfamily⟩ :=
      exists_sigmaX_mul_star_mul_sigmaX_mul_eq_symmetricEuler A
    exact ⟨alpha, theta, hactive.symm.trans hfamily⟩
  · rintro ⟨alpha, theta, hW⟩
    let A := columnASpecialUnitary alpha theta
    let B := columnBSpecialUnitary alpha theta alpha
    have hBraw : (B : QubitMatrix) = star (A : QubitMatrix) := by
      simp only [A, B, coe_columnASpecialUnitary, coe_columnBSpecialUnitary]
      exact (star_columnA_eq_columnB alpha theta).symm
    have hinactive :
        (specialUnitaryAsUnitary B : QubitMatrix) *
          (specialUnitaryAsUnitary A : QubitMatrix) = 1 := by
      rw [coe_specialUnitaryAsUnitary, coe_specialUnitaryAsUnitary, hBraw]
      have hgroup : (specialUnitaryAsUnitary A)⁻¹ * specialUnitaryAsUnitary A = 1 :=
        inv_mul_cancel _
      exact congrArg Subtype.val hgroup
    have hactive :
        sigmaX * (specialUnitaryAsUnitary B : QubitMatrix) * sigmaX *
          (specialUnitaryAsUnitary A : QubitMatrix) = (W : QubitMatrix) := by
      rw [coe_specialUnitaryAsUnitary, coe_specialUnitaryAsUnitary, hBraw]
      exact (columnA_sigmaX_mul_star_mul_sigmaX_mul_eq_symmetricEuler alpha theta).trans
        hW.symm
    refine ⟨A, B, ?_⟩
    exact (eval_twoCNOTCircuit_eq_iff control target h
      (specialUnitaryAsUnitary A) (specialUnitaryAsUnitary B) W).mpr
      ⟨hinactive, hactive⟩

/-! ## Lemma 5.5 with special-unitary witnesses -/

/-- The stronger special-unitary-witness form of the one-CNOT topology. -/
def HasOneCNOTSpecialCircuit {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (V : QubitUnitary) : Prop :=
  ∃ A B : QubitSpecialUnitary,
    Circuit.eval (oneCNOTCircuit control target h
      (specialUnitaryAsUnitary A) (specialUnitaryAsUnitary B)) =
      positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) V

/-- Complete one-CNOT classification using special-unitary witnesses. -/
theorem oneCNOTSpecialFamily_iff {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (V : QubitUnitary) :
    HasOneCNOTSpecialCircuit control target h V ↔
      ∃ alpha theta : ℝ,
        (V : QubitMatrix) = sigmaX * symmetricEuler alpha theta := by
  constructor
  · rintro ⟨A, B, heval⟩
    obtain ⟨hinactive, hactive⟩ :=
      (eval_oneCNOTCircuit_eq_iff control target h
        (specialUnitaryAsUnitary A) (specialUnitaryAsUnitary B) V).mp heval
    have hBA : specialUnitaryAsUnitary B * specialUnitaryAsUnitary A = 1 := by
      apply Subtype.ext
      simpa using hinactive
    have hB := eq_inv_of_mul_eq_one_left hBA
    have hBrawUnit : (specialUnitaryAsUnitary B : QubitMatrix) =
        star (specialUnitaryAsUnitary A : QubitMatrix) := by
      have hval := congrArg Subtype.val hB
      change (specialUnitaryAsUnitary B : QubitMatrix) =
        star (specialUnitaryAsUnitary A : QubitMatrix) at hval
      exact hval
    simp only [coe_specialUnitaryAsUnitary] at hBrawUnit hactive
    rw [hBrawUnit] at hactive
    obtain ⟨alpha, theta, hfamily⟩ :=
      exists_pauliConjugate_eq_sigmaX_mul_symmetricEuler A
    exact ⟨alpha, theta, hactive.symm.trans hfamily⟩
  · rintro ⟨alpha, theta, hV⟩
    let A := columnASpecialUnitary alpha theta
    let B := columnBSpecialUnitary alpha theta alpha
    have hBraw : (B : QubitMatrix) = star (A : QubitMatrix) := by
      simp only [A, B, coe_columnASpecialUnitary, coe_columnBSpecialUnitary]
      exact (star_columnA_eq_columnB alpha theta).symm
    have hinactive :
        (specialUnitaryAsUnitary B : QubitMatrix) *
          (specialUnitaryAsUnitary A : QubitMatrix) = 1 := by
      rw [coe_specialUnitaryAsUnitary, coe_specialUnitaryAsUnitary, hBraw]
      have hgroup : (specialUnitaryAsUnitary A)⁻¹ * specialUnitaryAsUnitary A = 1 :=
        inv_mul_cancel _
      exact congrArg Subtype.val hgroup
    have hactive :
        (specialUnitaryAsUnitary B : QubitMatrix) * sigmaX *
          (specialUnitaryAsUnitary A : QubitMatrix) = (V : QubitMatrix) := by
      rw [coe_specialUnitaryAsUnitary, coe_specialUnitaryAsUnitary, hBraw]
      exact (columnA_pauliConjugate_eq_sigmaX_mul_symmetricEuler alpha theta).trans
        hV.symm
    refine ⟨A, B, ?_⟩
    exact (eval_oneCNOTCircuit_eq_iff control target h
      (specialUnitaryAsUnitary A) (specialUnitaryAsUnitary B) V).mpr
      ⟨hinactive, hactive⟩

/-! ## Lemma 5.5 exactly as quantified in the paper -/

/-- Opposite scalar phases cancel around Pauli-X. -/
theorem phaseShift_neg_mul_sigmaX_mul_phaseShift (delta : ℝ) :
    phaseShift (-delta) * (sigmaX * phaseShift delta) = sigmaX := by
  rw [← Matrix.mul_assoc, phaseShift_mul_comm, Matrix.mul_assoc, phaseShift_mul]
  simp

/-- Removing the global phase of `A` does not change `A† X A`. -/
theorem unitaryPauliConjugate_eq_specialUnitaryPart (A : QubitUnitary) :
    star (A : QubitMatrix) * sigmaX * (A : QubitMatrix) =
      star (specialUnitaryPart A : QubitMatrix) * sigmaX *
        (specialUnitaryPart A : QubitMatrix) := by
  conv_lhs =>
    enter [1, 1]
    rw [← phaseShift_mul_specialUnitaryPart A]
  conv_lhs =>
    enter [2]
    rw [← phaseShift_mul_specialUnitaryPart A]
  simp only [star_mul, star_phaseShift, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc sigmaX (phaseShift (determinantPhaseAngle A))
    (specialUnitaryPart A : QubitMatrix)]
  rw [← Matrix.mul_assoc (phaseShift (-determinantPhaseAngle A))
    (sigmaX * phaseShift (determinantPhaseAngle A))
    (specialUnitaryPart A : QubitMatrix)]
  rw [phaseShift_neg_mul_sigmaX_mul_phaseShift]

/-- Existence of arbitrary unitary witnesses, matching Lemma 5.5's wording. -/
def HasOneCNOTUnitaryCircuit {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (V : QubitUnitary) : Prop :=
  ∃ A B : QubitUnitary,
    Circuit.eval (oneCNOTCircuit control target h A B) =
      positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) V

/--
Barenco et al., Lemma 5.5, both directions, including phase normalization of its
arbitrary unitary witnesses.
-/
theorem oneCNOTFamily_iff {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (V : QubitUnitary) :
    HasOneCNOTUnitaryCircuit control target h V ↔
      ∃ alpha theta : ℝ,
        (V : QubitMatrix) = sigmaX * symmetricEuler alpha theta := by
  constructor
  · rintro ⟨A, B, heval⟩
    obtain ⟨hinactive, hactive⟩ :=
      (eval_oneCNOTCircuit_eq_iff control target h A B V).mp heval
    have hBA : B * A = 1 := by
      apply Subtype.ext
      simpa using hinactive
    have hB := eq_inv_of_mul_eq_one_left hBA
    have hBraw : (B : QubitMatrix) = star (A : QubitMatrix) := by
      have hval := congrArg Subtype.val hB
      change (B : QubitMatrix) = star (A : QubitMatrix) at hval
      exact hval
    rw [hBraw] at hactive
    rw [unitaryPauliConjugate_eq_specialUnitaryPart] at hactive
    obtain ⟨alpha, theta, hfamily⟩ :=
      exists_pauliConjugate_eq_sigmaX_mul_symmetricEuler (specialUnitaryPart A)
    exact ⟨alpha, theta, hactive.symm.trans hfamily⟩
  · intro hfamily
    obtain ⟨A, B, heval⟩ :=
      (oneCNOTSpecialFamily_iff control target h V).mpr hfamily
    exact ⟨specialUnitaryAsUnitary A, specialUnitaryAsUnitary B, heval⟩

end

end Barenco.ControlledCircuit
