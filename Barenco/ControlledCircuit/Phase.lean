import Barenco.ControlledCircuit.Decomposition
import Barenco.OneQubit.GlobalPhase

/-!
# Controlled scalar phases and arbitrary controlled one-qubit gates

Barenco et al., Lemma 5.2 observes that controlling the scalar target phase
`phaseShift delta = exp(i*delta) I` is exactly the local control-wire gate
`diag(1, exp(i*delta))`. This is exact full-register equality: the controlled
scalar is a relative phase between control branches, not an ignorable global
phase.

Combining that one-gate circuit with the five-gate special-unitary circuit gives
Corollary 5.3's exact six-primitive construction for every certified one-qubit
unitary. Its four one-qubit plus two CNOT cost is derived from circuit syntax.
-/

namespace Barenco.ControlledCircuit

open Barenco.OneQubit

noncomputable section

/-- The paper's control-wire gate `E = Rz(-delta) Ph(delta/2)`. -/
def controlPhase (delta : ℝ) : QubitMatrix :=
  rz (-delta) * phaseShift (delta / 2)

/-- Certified control-wire phase gate. -/
def controlPhaseUnitary (delta : ℝ) : QubitUnitary :=
  rzUnitary (-delta) * phaseShiftUnitary (delta / 2)

@[simp]
theorem coe_controlPhaseUnitary (delta : ℝ) :
    (controlPhaseUnitary delta : QubitMatrix) = controlPhase delta := rfl

/-- The paper's `E` is exactly `diag(1, exp(i*delta))`. -/
theorem controlPhase_eq_matrix2 (delta : ℝ) :
    controlPhase delta = matrix2 1 0 0 (cis delta) := by
  rw [controlPhase, rz_eq_paperRz, phaseShift_eq_paperPhase,
    paperRz, paperPhase, matrix2_mul]
  congr 1
  · simp only [mul_zero, add_zero]
    rw [← cis_add]
    rw [show -delta / 2 + delta / 2 = 0 by ring, cis_zero]
  · simp
  · simp
  · simp only [mul_zero, zero_add]
    rw [← cis_add]
    congr 1
    ring

/-- Entry formula for a scalar phase controlled onto a distinct target wire. -/
theorem controlledScalarRaw_apply (delta : ℝ) {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (row col : Basis n) :
    positiveControlledRaw target ({⟨control, h⟩} : ControlSet target)
        (phaseShift delta) row col =
      if row = col then (if row control then cis delta else 1) else 0 := by
  rw [positiveControlledRaw_singleton_eq_targetBlockRaw, targetBlockRaw_apply]
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

/-- Entry formula for the local diagonal gate on the control wire. -/
theorem localControlPhaseRaw_apply (delta : ℝ) {n : ℕ}
    (control : Fin n) (row col : Basis n) :
    localRaw control (controlPhase delta) row col =
      if row = col then (if row control then cis delta else 1) else 0 := by
  rw [localRaw_apply_eq_if_agreeOff, controlPhase_eq_matrix2]
  by_cases hagree : AgreeOff control row col
  · rw [if_pos hagree]
    by_cases hc : row control = col control
    · have hrow : row = col :=
        (eq_iff_target_eq_of_agreeOff hagree).mpr hc
      subst col
      cases row control <;> simp
    · have hrow : row ≠ col := fun hrow => hc (congrFun hrow control)
      rw [if_neg hrow]
      cases hr : row control <;> cases hc' : col control <;> simp_all
  · rw [if_neg hagree]
    have hrow : row ≠ col := by
      intro hrow
      apply hagree
      subst col
      intro i hi
      rfl
    rw [if_neg hrow]

/-- Raw full-register form of Lemma 5.2. -/
theorem controlledScalarRaw_eq_localControl (delta : ℝ) {n : ℕ}
    (control target : Fin n) (h : control ≠ target) :
    positiveControlledRaw target ({⟨control, h⟩} : ControlSet target)
        (phaseShift delta) =
      localRaw control (controlPhase delta) := by
  ext row col
  rw [controlledScalarRaw_apply, localControlPhaseRaw_apply]

/--
Barenco et al., Lemma 5.2 as exact certified full-register equality.
-/
theorem controlledScalarUnitary_eq_localControl (delta : ℝ) {n : ℕ}
    (control target : Fin n) (h : control ≠ target) :
    positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target)
        (phaseShiftUnitary delta) =
      localUnitary control (controlPhaseUnitary delta) := by
  apply Subtype.ext
  simpa using controlledScalarRaw_eq_localControl delta control target h

/-- The one-gate chronological circuit displayed in Lemma 5.2. -/
def controlledPhaseCircuit {n : ℕ} (control : Fin n) (delta : ℝ) : Circuit n :=
  [Primitive.oneQubit control (controlPhaseUnitary delta)]

@[simp]
theorem eval_controlledPhaseCircuit {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (delta : ℝ) :
    Circuit.eval (controlledPhaseCircuit control delta) =
      positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target)
        (phaseShiftUnitary delta) := by
  rw [controlledPhaseCircuit, Circuit.eval_singleton,
    Primitive.oneQubit_denotation, controlledScalarUnitary_eq_localControl]

@[simp]
theorem controlledPhaseCircuit_gateCount {n : ℕ} (control : Fin n) (delta : ℝ) :
    Circuit.gateCount (controlledPhaseCircuit control delta) = 1 := rfl

@[simp]
theorem controlledPhaseCircuit_oneQubitCNOTCost {n : ℕ}
    (control : Fin n) (delta : ℝ) :
    Circuit.cost CostModel.oneQubitCNOT (controlledPhaseCircuit control delta) = some 1 := rfl

/-! ## Composition of single positive controls -/

/-- Raw multiplication law for two gates with the same singleton control and target. -/
theorem singleControlledRaw_mul {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (U V : QubitMatrix) :
    positiveControlledRaw target ({⟨control, h⟩} : ControlSet target) U *
        positiveControlledRaw target ({⟨control, h⟩} : ControlSet target) V =
      positiveControlledRaw target ({⟨control, h⟩} : ControlSet target) (U * V) := by
  simp_rw [positiveControlledRaw_singleton_eq_targetBlockRaw]
  rw [targetBlockRaw_mul]
  congr 1
  funext rest
  cases hr : rest ⟨control, h⟩ <;> simp

/-- Certified multiplication law for the same singleton control and target. -/
theorem singleControlledUnitary_mul {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (U V : QubitUnitary) :
    positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) U *
        positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) V =
      positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) (U * V) := by
  apply Subtype.ext
  simpa only [Submonoid.coe_mul, coe_positiveControlledUnitary] using
    singleControlledRaw_mul control target h (U : QubitMatrix) (V : QubitMatrix)

/-- A scalar phase matrix commutes with every one-qubit matrix. -/
theorem phaseShift_mul_comm (delta : ℝ) (U : QubitMatrix) :
    phaseShift delta * U = U * phaseShift delta := by
  ext row col
  cases row <;> cases col <;>
    simp [Matrix.mul_apply, phaseShift_false_false, phaseShift_false_true,
      phaseShift_true_false, phaseShift_true_true] <;> ring

/-- Certified form of scalar-phase commutativity. -/
theorem phaseShiftUnitary_mul_comm (delta : ℝ) (U : QubitUnitary) :
    phaseShiftUnitary delta * U = U * phaseShiftUnitary delta := by
  apply Subtype.ext
  exact phaseShift_mul_comm delta U

/-! ## Corollary 5.3 -/

/--
Chronological arbitrary-U circuit: first the phase gate on the control, then the
five-gate A/B/C circuit on the target.
-/
def controlledU2Circuit {n : ℕ} (control target : Fin n) (h : control ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) : Circuit n :=
  Circuit.append (controlledPhaseCircuit control delta)
    (controlledABCCircuit control target h A B C)

/-- Parameterized exact correctness theorem for the six-gate circuit. -/
theorem eval_controlledU2Circuit_of_products {n : ℕ}
    (control target : Fin n) (h : control ≠ target) (delta : ℝ)
    (A B C W U : QubitUnitary)
    (hinactive : (C : QubitMatrix) * (B : QubitMatrix) * (A : QubitMatrix) = 1)
    (hactive : (C : QubitMatrix) * sigmaX * (B : QubitMatrix) * sigmaX *
      (A : QubitMatrix) = (W : QubitMatrix))
    (hU : (U : QubitMatrix) = phaseShift delta * (W : QubitMatrix)) :
    Circuit.eval (controlledU2Circuit control target h delta A B C) =
      positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) U := by
  have hABC : Circuit.eval (controlledABCCircuit control target h A B C) =
      positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) W :=
    (eval_controlledABCCircuit_eq_iff control target h A B C W).mpr
      ⟨hinactive, hactive⟩
  have hWU : W * phaseShiftUnitary delta = U := by
    apply Subtype.ext
    change (W : QubitMatrix) * phaseShift delta = (U : QubitMatrix)
    rw [← phaseShift_mul_comm]
    exact hU.symm
  rw [controlledU2Circuit, Circuit.eval_append, hABC,
    eval_controlledPhaseCircuit control target h delta,
    singleControlledUnitary_mul control target h W (phaseShiftUnitary delta), hWU]

/--
Barenco et al., Corollary 5.3: every certified one-qubit unitary has exact
six-gate controlled-U witnesses on any distinct pair of wires.
-/
theorem controlledU2Circuit_exists {n : ℕ} (control target : Fin n)
    (h : control ≠ target) (U : QubitUnitary) :
    ∃ A B C : QubitSpecialUnitary,
      Circuit.eval (controlledU2Circuit control target h
        (determinantPhaseAngle U) (specialUnitaryAsUnitary A)
        (specialUnitaryAsUnitary B) (specialUnitaryAsUnitary C)) =
        positiveControlledUnitary target ({⟨control, h⟩} : ControlSet target) U := by
  obtain ⟨A, B, C, hinactive, hactive⟩ :=
    specialUnitary_exists_columnChronologicalABC (specialUnitaryPart U)
  refine ⟨A, B, C, ?_⟩
  apply eval_controlledU2Circuit_of_products control target h
    (determinantPhaseAngle U) (specialUnitaryAsUnitary A)
      (specialUnitaryAsUnitary B) (specialUnitaryAsUnitary C)
      (specialUnitaryAsUnitary (specialUnitaryPart U)) U
  · exact hinactive
  · exact hactive
  · exact (phaseShift_mul_specialUnitaryPart U).symm

@[simp]
theorem controlledU2Circuit_gateCount {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) :
    Circuit.gateCount (controlledU2Circuit control target h delta A B C) = 6 := by
  rfl

@[simp]
theorem controlledU2Circuit_kindCounts {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (controlledU2Circuit control target h delta A B C) = 4 ∧
      Circuit.kindCount .cnot
        (controlledU2Circuit control target h delta A B C) = 2 := by
  simp [controlledU2Circuit, controlledPhaseCircuit, controlledABCCircuit,
    Circuit.append, Circuit.kindCount]

/-- Exact Sections 3–7 basic-operation cost of the six-gate construction. -/
@[simp]
theorem controlledU2Circuit_oneQubitCNOTCost {n : ℕ}
    (control target : Fin n) (h : control ≠ target)
    (delta : ℝ) (A B C : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
      (controlledU2Circuit control target h delta A B C) = some 6 := by
  rfl

end

end Barenco.ControlledCircuit
