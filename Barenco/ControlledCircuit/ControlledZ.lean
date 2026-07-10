import Barenco.ControlledCircuit.Phase

/-!
# Controlled-Z symmetry

The unnumbered diagram after Corollary 5.6 observes that controlled-Z is symmetric:
either wire may be designated as the control. This leaf proves that statement as
exact equality of full-register certified unitaries for arbitrary ambient width and
arbitrary distinct wire indices.

The definitions are public semantic runtime API, and the matrix, basis-action, and
symmetry theorems are public proof-side API. No circuit syntax or resource result is
claimed here.
-/

namespace Barenco.ControlledCircuit

open Barenco.OneQubit
open Matrix

noncomputable section

/-! ## Certified semantic Pauli-Z -/

/-- Standard-column Pauli-Z, obtained as the control phase at angle `pi`. -/
def sigmaZ : QubitMatrix := controlPhase Real.pi

/-- Pauli-Z with its inherited unitary certificate. -/
def sigmaZUnitary : QubitUnitary := controlPhaseUnitary Real.pi

@[simp]
theorem coe_sigmaZUnitary : (sigmaZUnitary : QubitMatrix) = sigmaZ := by
  rfl

/-- Pauli-Z is exactly the standard diagonal matrix `diag(1,-1)`. -/
theorem sigmaZ_eq_matrix2 : sigmaZ = matrix2 1 0 0 (-1) := by
  rw [sigmaZ, controlPhase_eq_matrix2]
  have hpi : cis Real.pi = -1 := by
    simpa only [cis] using Complex.exp_pi_mul_I
  rw [hpi]

/-! ## Singleton-controlled Pauli-Z -/

/-- Raw singleton-controlled Pauli-Z on two distinct named wires. -/
def controlledZRaw {n : ℕ} (control target : Fin n) (h : control ≠ target) : Gate n :=
  positiveControlledRaw target ({⟨control, h⟩} : ControlSet target) sigmaZ

/-- Certified singleton-controlled Pauli-Z on two distinct named wires. -/
def controlledZUnitary {n : ℕ} (control target : Fin n) (h : control ≠ target) :
    UnitaryGate n :=
  positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) sigmaZUnitary

@[simp]
theorem coe_controlledZUnitary {n : ℕ} (control target : Fin n)
    (h : control ≠ target) :
    (controlledZUnitary control target h : Gate n) = controlledZRaw control target h := by
  simp [controlledZUnitary, controlledZRaw]

/--
Exact full-register entry formula: controlled-Z is diagonal and contributes a
minus sign precisely when both named wires are true.
-/
theorem controlledZRaw_apply {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (row col : Basis n) :
    controlledZRaw control target h row col =
      if row = col then
        if row control = true ∧ row target = true then -1 else 1
      else 0 := by
  rw [controlledZRaw, positiveControlledRaw_singleton_eq_targetBlockRaw,
    targetBlockRaw_apply, sigmaZ_eq_matrix2]
  by_cases hrest : (splitTarget target row).2 = (splitTarget target col).2
  · rw [if_pos hrest]
    have hagree : AgreeOff target row col :=
      (splitTarget_snd_eq_iff target row col).mp hrest
    by_cases ht : row target = col target
    · have hrow : row = col :=
        (eq_iff_target_eq_of_agreeOff hagree).mpr ht
      subst col
      cases hc : row control <;> cases row target <;> simp [hc]
    · have hrow : row ≠ col := fun hrow => ht (congrFun hrow target)
      rw [if_neg hrow]
      cases hc : row control <;>
        cases hr : row target <;> cases hc' : col target <;>
          simp_all
  · rw [if_neg hrest]
    have hrow : row ≠ col := fun hrow =>
      hrest (congrArg (fun x => (splitTarget target x).2) hrow)
    rw [if_neg hrow]

/-- Computational-basis action of controlled-Z, including its relative sign. -/
theorem controlledZRaw_truthTable {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (x : Basis n) :
    controlledZRaw control target h *ᵥ basisKet x =
      if x control = true ∧ x target = true then - basisKet x else basisKet x := by
  funext row
  rw [mulVec_basisKet_apply, controlledZRaw_apply]
  by_cases hrow : row = x
  · subst row
    by_cases hactive : x control = true ∧ x target = true <;>
      simp [hactive, basisKet_apply]
  · by_cases hactive : x control = true ∧ x target = true <;>
      simp [hrow, hactive]

/-! ## Exact wire-swap symmetry -/

/-- Swapping the distinct control and target labels preserves the raw matrix exactly. -/
theorem controlledZRaw_swap {n : ℕ} (control target : Fin n)
    (h : control ≠ target) :
    controlledZRaw control target h = controlledZRaw target control h.symm := by
  ext row col
  rw [controlledZRaw_apply, controlledZRaw_apply]
  by_cases hrow : row = col
  · rw [if_pos hrow, if_pos hrow]
    simp only [and_comm]
  · rw [if_neg hrow, if_neg hrow]

/-- Swapping the distinct control and target labels preserves the certified gate exactly. -/
theorem controlledZUnitary_swap {n : ℕ} (control target : Fin n)
    (h : control ≠ target) :
    controlledZUnitary control target h = controlledZUnitary target control h.symm := by
  apply Subtype.ext
  simpa only [coe_controlledZUnitary] using controlledZRaw_swap control target h

end


end Barenco.ControlledCircuit
