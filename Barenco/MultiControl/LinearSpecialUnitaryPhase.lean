import Barenco.MultiControl.LinearSpecialUnitaryExpansion
import Barenco.ThreeQubit.RelativePhase

/-!
# The phase-relaxed n-bit Toffoli example after Lemma 7.9

The paper's special matrix `W` is in SU(2), so Lemma 7.9 gives an exact fully
controlled-`W` circuit.  It is not globally equal to fully controlled Pauli-X:
the input column with all controls and target equal to one acquires a minus sign.
This leaf records the exact arbitrary-control phase and derives only the valid
basis-behavior and computational-basis measurement consequences.
-/

namespace Barenco.MultiControl

open Barenco.OneQubit
open Barenco.ControlledCircuit

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The paper's `W`, packaged with its determinant-one certificate via `Ry(π)`. -/
def wSpecialUnitary : QubitSpecialUnitary :=
  rySpecialUnitary Real.pi

@[simp]
theorem coe_wSpecialUnitary :
    (wSpecialUnitary : QubitMatrix) = Barenco.ThreeQubit.wMatrix := by
  exact Barenco.ThreeQubit.wMatrix_eq_ry_pi.symm

namespace OrderedControlLayout

/-- Input-column sign of fully controlled paper `W`. -/
def fullyControlledWPhase {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (rest : ComplementBasis layout.targetWire) (input : Bool) : Circle :=
  if positiveControlsEnabled layout.controlSet rest = true ∧ input = true then
    (-1 : Circle)
  else 1

@[simp]
theorem fullyControlledWPhase_input {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (input : Basis ambientWidth) :
    layout.fullyControlledWPhase
        (splitTarget layout.targetWire input).2 (input layout.targetWire) =
      if (∀ wire ∈ layout.controlSet, input wire = true) ∧
          input layout.targetWire = true then
        (-1 : Circle)
      else 1 := by
  simp [fullyControlledWPhase]

private theorem fullyControlledWBlock_phase {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (rest : ComplementBasis layout.targetWire) (row input : Bool) :
    (if positiveControlsEnabled layout.controlSet rest then
        Barenco.ThreeQubit.wMatrix else 1) row input =
      (layout.fullyControlledWPhase rest input : ℂ) *
        (if positiveControlsEnabled layout.controlSet rest then sigmaX else 1)
          row input := by
  cases hcontrols : positiveControlsEnabled layout.controlSet rest <;>
    cases row <;> cases input <;>
      norm_num [fullyControlledWPhase, Barenco.ThreeQubit.wMatrix,
        Barenco.ThreeQubit.paperW, fromPaper, sigmaX_eq_paperX, paperX,
        hcontrols]

/-- Fully controlled paper `W` differs from fully controlled X by input phases. -/
theorem fullyControlledW_basisPhaseEq_pauliX
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) :
    BasisPhaseEq
      (positiveControlledUnitary layout.targetWire layout.controlSet pauliX :
        Gate ambientWidth)
  (positiveControlledUnitary layout.targetWire layout.controlSet
        (specialUnitaryAsUnitary wSpecialUnitary) : Gate ambientWidth) := by
  simp only [coe_positiveControlledUnitary, coe_specialUnitaryAsUnitary,
    coe_wSpecialUnitary]
  rw [← sigmaX_eq_coe_pauliX]
  rw [positiveControlledRaw, positiveControlledRaw,
    controlledRaw_eq_targetBlockRaw, controlledRaw_eq_targetBlockRaw]
  exact Barenco.ThreeQubit.targetBlockRaw_basisPhaseEq layout.targetWire
    (fun rest => if positiveControlsEnabled layout.controlSet rest then sigmaX else 1)
    (fun rest => if positiveControlsEnabled layout.controlSet rest then
      Barenco.ThreeQubit.wMatrix else 1)
    layout.fullyControlledWPhase
    (layout.fullyControlledWBlock_phase)

/-- The exact selected Lemma 7.9 circuit has the same phase-relaxed X behavior. -/
theorem linearWSU2Circuit_basisPhaseEq_pauliX {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    BasisPhaseEq
      (positiveControlledUnitary layout.targetWire layout.controlSet pauliX :
        Gate ambientWidth)
      (Circuit.eval (layout.linearSU2Circuit wSpecialUnitary) : Gate ambientWidth) := by
  rw [eval_linearSU2Circuit]
  exact layout.fullyControlledW_basisPhaseEq_pauliX

theorem linearWSU2Circuit_sameBasisBehavior {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    SameBasisBehavior
      (positiveControlledUnitary layout.targetWire layout.controlSet pauliX :
        Gate ambientWidth)
      (Circuit.eval (layout.linearSU2Circuit wSpecialUnitary) : Gate ambientWidth) :=
  BasisPhaseEq.toSameBasisBehavior layout.linearWSU2Circuit_basisPhaseEq_pauliX

theorem linearWSU2Circuit_basisMeasurementEq {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    BasisMeasurementEq
      (positiveControlledUnitary layout.targetWire layout.controlSet pauliX :
        Gate ambientWidth)
      (Circuit.eval (layout.linearSU2Circuit wSpecialUnitary) : Gate ambientWidth) :=
  BasisPhaseEq.toBasisMeasurementEq layout.linearWSU2Circuit_basisPhaseEq_pauliX

/-- The fully expanded linear circuit retains the exact input-column phase. -/
theorem expandedLinearWSU2Circuit_basisPhaseEq_pauliX {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    BasisPhaseEq
      (positiveControlledUnitary layout.targetWire layout.controlSet pauliX :
        Gate ambientWidth)
      (Circuit.eval (layout.expandedLinearSU2Circuit hwidth wSpecialUnitary) :
        Gate ambientWidth) := by
  rw [eval_expandedLinearSU2Circuit_eq_linear]
  exact layout.linearWSU2Circuit_basisPhaseEq_pauliX

theorem expandedLinearWSU2Circuit_sameBasisBehavior {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    SameBasisBehavior
      (positiveControlledUnitary layout.targetWire layout.controlSet pauliX :
        Gate ambientWidth)
      (Circuit.eval (layout.expandedLinearSU2Circuit hwidth wSpecialUnitary) :
        Gate ambientWidth) :=
  BasisPhaseEq.toSameBasisBehavior
    (layout.expandedLinearWSU2Circuit_basisPhaseEq_pauliX hwidth)

theorem expandedLinearWSU2Circuit_basisMeasurementEq {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    BasisMeasurementEq
      (positiveControlledUnitary layout.targetWire layout.controlSet pauliX :
        Gate ambientWidth)
      (Circuit.eval (layout.expandedLinearSU2Circuit hwidth wSpecialUnitary) :
        Gate ambientWidth) :=
  BasisPhaseEq.toBasisMeasurementEq
    (layout.expandedLinearWSU2Circuit_basisPhaseEq_pauliX hwidth)

end OrderedControlLayout

end

end Barenco.MultiControl
