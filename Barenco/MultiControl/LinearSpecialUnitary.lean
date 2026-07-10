import Barenco.MultiControl.Recursive
import Barenco.OneQubit.SelectedABC
import Barenco.OneQubit.CircuitBridge
import Barenco.ControlledCircuit.Decomposition
import Barenco.Cost

/-!
# Barenco Lemma 7.9: linear macro circuit for fully controlled SU(2)

For `p + 1` controls, split off the final ordered control `c`.  The exact
chronology reconstructed from the diagram is

`C(c,A,target); MCX(prefix,target); C(c,B,target);`
`MCX(prefix,target); C(c,C,target)`.

The semantic theorem is valid for every `p`, including an empty prefix.  This
module retains the two MCX nodes and three controlled target nodes as macros;
their one-qubit/CNOT expansion and linear cost live in a separate leaf.
-/

namespace Barenco.MultiControl

open Barenco.OneQubit
open Barenco.ControlledCircuit
open scoped Matrix

noncomputable section

attribute [local instance] Classical.propDecidable

namespace OrderedControlLayout

/-- The exact five-macro chronology displayed in Lemma 7.9. -/
def linearABCCircuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (A B C : QubitUnitary) : Circuit ambientWidth :=
  [layout.lastControlledTarget A,
    layout.prefixControlledTarget pauliX,
    layout.lastControlledTarget B,
    layout.prefixControlledTarget pauliX,
    layout.lastControlledTarget C]

/-- Target-qubit product selected by the prefix and final-control bits. -/
def linearABCTargetProduct {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (A B C : QubitUnitary) (input : Basis ambientWidth) : QubitMatrix :=
  (if input layout.lastControlWire then (C : QubitMatrix) else 1) *
    ((if layout.prefixEnabled input then sigmaX else 1) *
      ((if input layout.lastControlWire then (B : QubitMatrix) else 1) *
        ((if layout.prefixEnabled input then sigmaX else 1) *
          (if input layout.lastControlWire then (A : QubitMatrix) else 1))))

/-- Direct full-register product of the five chronological macro nodes. -/
theorem eval_linearABCCircuit_raw {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (A B C : QubitUnitary) :
    (Circuit.eval (layout.linearABCCircuit A B C) : Gate ambientWidth) =
      (layout.lastControlledTarget C).denotation *
        (layout.prefixControlledTarget pauliX).denotation *
        (layout.lastControlledTarget B).denotation *
        (layout.prefixControlledTarget pauliX).denotation *
        (layout.lastControlledTarget A).denotation := by
  simp [linearABCCircuit, Circuit.eval]

private theorem localRaw_one {ambientWidth : ℕ} (target : Fin ambientWidth) :
    localRaw target (1 : QubitMatrix) = 1 := by
  rw [localRaw_eq_targetBlockRaw, targetBlockRaw_one]

private theorem lastControlledTarget_denotation_mulVec_basisKet
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (U : QubitUnitary) (input : Basis ambientWidth) :
    (layout.lastControlledTarget U).denotation *ᵥ basisKet input =
      localRaw layout.targetWire
          (if input layout.lastControlWire then (U : QubitMatrix) else 1) *ᵥ
        basisKet input := by
  simpa [localRaw_one] using
    layout.lastControlledTarget_denotation_mulVec_localRaw_basisKet
      U (1 : QubitMatrix) input

/-- Exact target-local basis-column action of the five macro nodes. -/
theorem eval_linearABCCircuit_mulVec_basisKet {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (A B C : QubitUnitary) (input : Basis ambientWidth) :
    (Circuit.eval (layout.linearABCCircuit A B C) : Gate ambientWidth) *ᵥ
        basisKet input =
      localRaw layout.targetWire (layout.linearABCTargetProduct A B C input) *ᵥ
        basisKet input := by
  rw [eval_linearABCCircuit_raw]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [layout.lastControlledTarget_denotation_mulVec_basisKet]
  rw [layout.prefixControlledTarget_denotation_mulVec_localRaw_basisKet]
  rw [layout.lastControlledTarget_denotation_mulVec_localRaw_basisKet]
  rw [layout.prefixControlledTarget_denotation_mulVec_localRaw_basisKet]
  rw [layout.lastControlledTarget_denotation_mulVec_localRaw_basisKet]
  simp only [linearABCTargetProduct, sigmaX_eq_coe_pauliX]

/-- The four control branches collapse to identity except on the fully active branch. -/
theorem linearABCTargetProduct_eq {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (A B C W : QubitUnitary)
    (hinactive : (C : QubitMatrix) * (B : QubitMatrix) * (A : QubitMatrix) = 1)
    (hactive : (C : QubitMatrix) * sigmaX * (B : QubitMatrix) * sigmaX *
      (A : QubitMatrix) = (W : QubitMatrix))
    (input : Basis ambientWidth) :
    layout.linearABCTargetProduct A B C input =
      if layout.prefixEnabled input ∧ input layout.lastControlWire = true then
        (W : QubitMatrix)
      else 1 := by
  by_cases hprefix : layout.prefixEnabled input
  · cases hlast : input layout.lastControlWire
    · simp [linearABCTargetProduct, hprefix, hlast, sigmaX_sq]
    · simp [linearABCTargetProduct, hprefix, hlast]
      simpa only [Matrix.mul_assoc] using hactive
  · cases hlast : input layout.lastControlWire
    · simp [linearABCTargetProduct, hprefix, hlast]
    · simp [linearABCTargetProduct, hprefix, hlast]
      simpa only [Matrix.mul_assoc] using hinactive

/--
Parameterized Lemma 7.9: the displayed macro circuit exactly implements full
positive control whenever its inactive and active target products are `I` and
`W`.
-/
theorem eval_linearABCCircuit_of_products {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (A B C W : QubitUnitary)
    (hinactive : (C : QubitMatrix) * (B : QubitMatrix) * (A : QubitMatrix) = 1)
    (hactive : (C : QubitMatrix) * sigmaX * (B : QubitMatrix) * sigmaX *
      (A : QubitMatrix) = (W : QubitMatrix)) :
    Circuit.eval (layout.linearABCCircuit A B C) =
      positiveControlledUnitary layout.targetWire layout.controlSet W := by
  apply Subtype.ext
  rw [matrix_eq_iff_mulVec_basisKet_eq]
  intro input
  rw [eval_linearABCCircuit_mulVec_basisKet,
    linearABCTargetProduct_eq layout A B C W hinactive hactive,
    coe_positiveControlledUnitary, positiveControlledRaw_truthTable]
  by_cases hall : ∀ wire ∈ layout.controlSet, input wire = true
  · have hsplit :
        layout.prefixEnabled input ∧ input layout.lastControlWire = true :=
      (layout.all_controls_iff_prefixEnabled_and_last input).1 hall
    rw [if_pos hall, if_pos hsplit]
  · have hnot :
        ¬(layout.prefixEnabled input ∧ input layout.lastControlWire = true) :=
      fun h => hall ((layout.all_controls_iff_prefixEnabled_and_last input).2 h)
    rw [if_neg hall, if_neg hnot]
    change localRaw layout.targetWire (1 : QubitMatrix) *ᵥ basisKet input = _
    rw [localRaw_one, Matrix.one_mulVec]

/-! ## Selected exact SU(2) wrapper -/

/-- Lemma 7.9 using one selected checked ABC factorization of `W`. -/
def linearSU2Circuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (W : QubitSpecialUnitary) : Circuit ambientWidth :=
  let factors := selectedColumnABCFactors W
  layout.linearABCCircuit
    (specialUnitaryAsUnitary factors.A)
    (specialUnitaryAsUnitary factors.B)
    (specialUnitaryAsUnitary factors.C)

/-- Exact arbitrary-register fully controlled SU(2) semantics. -/
@[simp]
theorem eval_linearSU2Circuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (W : QubitSpecialUnitary) :
    Circuit.eval (layout.linearSU2Circuit W) =
      positiveControlledUnitary layout.targetWire layout.controlSet
        (specialUnitaryAsUnitary W) := by
  let factors := selectedColumnABCFactors W
  apply eval_linearABCCircuit_of_products layout
    (specialUnitaryAsUnitary factors.A)
    (specialUnitaryAsUnitary factors.B)
    (specialUnitaryAsUnitary factors.C)
    (specialUnitaryAsUnitary W)
  · exact factors.inactive
  · simpa only [coe_specialUnitaryAsUnitary] using factors.active

/-! ## Macro resources -/

@[simp]
theorem linearABCCircuit_gateCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (A B C : QubitUnitary) :
    Circuit.gateCount (layout.linearABCCircuit A B C) = 5 := by
  rfl

/-- Collision-safe macro-kind accounting, including `p=1`. -/
theorem linearABCCircuit_kindCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (A B C : QubitUnitary) (kind : PrimitiveKind) :
    Circuit.kindCount kind (layout.linearABCCircuit A B C) =
      (if .controlledOneQubit 1 = kind then 3 else 0) +
        (if .controlledOneQubit p = kind then 2 else 0) := by
  by_cases hone : .controlledOneQubit 1 = kind <;>
    by_cases hp : .controlledOneQubit p = kind <;>
      simp [linearABCCircuit, Circuit.kindCount, hone, hp]

@[simp]
theorem linearABCCircuit_oneQubitCNOTCost {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (A B C : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (layout.linearABCCircuit A B C) = none := by
  simp [linearABCCircuit, lastControlledTarget, prefixControlledTarget,
    Circuit.cost, Circuit.addCost]

end OrderedControlLayout

end

end Barenco.MultiControl
