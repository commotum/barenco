import Barenco.OneQubit.CoherentRoots
import Barenco.MultiControl.Recursive
import Barenco.Equivalence.ControlledDistance

/-!
# Truncated recursive multi-control synthesis

This module gives the semantic, macro-level core of Barenco Lemma 7.8.  At each
retained recursion level it keeps the first four chronological macros from
Lemma 7.5 and recursively replaces that lemma's final prefix-controlled target
gate.  At depth zero the remaining controlled root is omitted, so the literal
truncated circuit is empty at that point.

For `residualDepth + 6 + depth` controls, `residualDepth + 6` controls remain
after `depth` retained shells.  The offset six records the smallest residual
layout accepted by the established exact primitive expansion; it is not needed
for the macro semantics themselves.  This file deliberately makes no primitive
expansion or resource claim.
-/

namespace Barenco.MultiControl

open Barenco.OneQubit
open Barenco.ControlledCircuit

noncomputable section

namespace OrderedControlLayout

/-! ## Residual layouts and literal truncated syntax -/

/-- Remove the final ordered control `depth` times. -/
def recursiveResidualLayout {ambientWidth residualDepth : ℕ} :
    (depth : ℕ) →
      OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth →
        OrderedControlLayout (residualDepth + 6) ambientWidth
  | 0, layout => layout
  | depth + 1, layout =>
      recursiveResidualLayout depth layout.prefixTargetLayout

/--
The four retained outer macros of one Lemma 7.5 step.  The omitted fifth macro
is the prefix-controlled target gate recursively handled by the next shell.
-/
def recursiveRetainedShell {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) : Circuit ambientWidth :=
  [layout.lastControlledTarget V,
    layout.prefixControlledX,
    layout.lastControlledTarget V⁻¹,
    layout.prefixControlledX]

/-- The five-macro circuit is one retained shell followed by its residual gate. -/
theorem recursiveViaSquareCircuit_eq_retainedShell_append {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) :
    layout.recursiveViaSquareCircuit V =
      Circuit.append (layout.recursiveRetainedShell V)
        [layout.prefixControlledTarget V] := by
  rfl

/--
Retain `depth` recursive shells, starting with the `rootIndex` member of the
coherent power-of-two root sequence, and omit the final residual controlled
root.  This is literal circuit syntax, not a semantic placeholder.
-/
def truncatedRecursiveCircuitFrom {ambientWidth : ℕ} :
    (rootIndex residualDepth depth : ℕ) →
      OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth →
        QubitUnitary → Circuit ambientWidth
  | _rootIndex, _residualDepth, 0, _layout, _U => []
  | rootIndex, residualDepth, depth + 1, layout, U =>
      Circuit.append
        (layout.recursiveRetainedShell (powerTwoRoot (rootIndex + 1) U))
        (truncatedRecursiveCircuitFrom (rootIndex + 1) residualDepth depth
          layout.prefixTargetLayout U)
termination_by _rootIndex _residualDepth depth _layout _U => depth

/-- Root-index-zero wrapper used to approximate full control of `U`. -/
def truncatedRecursiveCircuit {ambientWidth : ℕ} (residualDepth depth : ℕ)
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) : Circuit ambientWidth :=
  truncatedRecursiveCircuitFrom 0 residualDepth depth layout U

/-! ## Exact factorization of the omitted residual gate -/

/--
The exact full controlled root factors into the omitted residual controlled
root followed algebraically by the evaluator of the literal truncated circuit.
-/
theorem positiveControlledUnitary_eq_residual_mul_eval_truncatedFrom
    {ambientWidth : ℕ} (rootIndex residualDepth depth : ℕ)
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    positiveControlledUnitary layout.targetWire layout.controlSet
        (powerTwoRoot rootIndex U) =
      positiveControlledUnitary
          (layout.recursiveResidualLayout depth).targetWire
          (layout.recursiveResidualLayout depth).controlSet
          (powerTwoRoot (rootIndex + depth) U) *
        Circuit.eval
          (truncatedRecursiveCircuitFrom rootIndex residualDepth depth layout U) := by
  induction depth generalizing rootIndex with
  | zero =>
      simp [recursiveResidualLayout, truncatedRecursiveCircuitFrom]
  | succ depth ih =>
      let V : QubitUnitary := powerTwoRoot (rootIndex + 1) U
      have hsq : V ^ 2 = powerTwoRoot rootIndex U := by
        simp [V]
      have hstep :
          positiveControlledUnitary layout.targetWire layout.controlSet
              (powerTwoRoot rootIndex U) =
            (layout.prefixControlledTarget V).denotation *
              Circuit.eval (layout.recursiveRetainedShell V) := by
        calc
          positiveControlledUnitary layout.targetWire layout.controlSet
                (powerTwoRoot rootIndex U) =
              Circuit.eval (layout.recursiveViaSquareCircuit V) :=
            (layout.eval_recursiveViaSquareCircuit_of_sq_eq
              (powerTwoRoot rootIndex U) V hsq).symm
          _ = Circuit.eval
              (Circuit.append (layout.recursiveRetainedShell V)
                [layout.prefixControlledTarget V]) := by
            rw [layout.recursiveViaSquareCircuit_eq_retainedShell_append V]
          _ = (layout.prefixControlledTarget V).denotation *
              Circuit.eval (layout.recursiveRetainedShell V) := by
            rw [Circuit.eval_append, Circuit.eval_singleton]
      have htail := ih (rootIndex := rootIndex + 1)
        (layout := layout.prefixTargetLayout)
      have hindex : (rootIndex + 1) + depth = rootIndex + (depth + 1) := by
        omega
      rw [hindex] at htail
      have htail' :
          (layout.prefixControlledTarget V).denotation =
            positiveControlledUnitary
                (layout.recursiveResidualLayout (depth + 1)).targetWire
                (layout.recursiveResidualLayout (depth + 1)).controlSet
                (powerTwoRoot (rootIndex + (depth + 1)) U) *
              Circuit.eval
                (truncatedRecursiveCircuitFrom (rootIndex + 1) residualDepth depth
                  layout.prefixTargetLayout U) := by
        simpa [V, prefixControlledTarget, recursiveResidualLayout] using htail
      rw [hstep, htail']
      rw [mul_assoc, ← Circuit.eval_append]
      rw [truncatedRecursiveCircuitFrom]

/-- Root-index-zero factorization for the original unitary `U`. -/
theorem positiveControlledUnitary_eq_residual_mul_eval_truncated
    {ambientWidth residualDepth depth : ℕ}
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    positiveControlledUnitary layout.targetWire layout.controlSet U =
      positiveControlledUnitary
          (layout.recursiveResidualLayout depth).targetWire
          (layout.recursiveResidualLayout depth).controlSet
          (powerTwoRoot depth U) *
        Circuit.eval (truncatedRecursiveCircuit residualDepth depth layout U) := by
  simpa [truncatedRecursiveCircuit] using
    layout.positiveControlledUnitary_eq_residual_mul_eval_truncatedFrom
      0 residualDepth depth U

/-! ## Exact truncation error and analytic bound -/

/--
Exact operator-distance identity: truncation error is precisely the distance
from the omitted residual root to the one-qubit identity.
-/
theorem operatorDistance_truncatedRecursiveCircuitFrom_eq_residual
    {ambientWidth : ℕ} (rootIndex residualDepth depth : ℕ)
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    operatorDistance
        (positiveControlledUnitary layout.targetWire layout.controlSet
          (powerTwoRoot rootIndex U) : Gate ambientWidth)
        (Circuit.eval
          (truncatedRecursiveCircuitFrom rootIndex residualDepth depth layout U) :
            Gate ambientWidth) =
      operatorDistance
        (powerTwoRoot (rootIndex + depth) U : QubitMatrix)
        (1 : QubitMatrix) := by
  let residual : UnitaryGate ambientWidth :=
    positiveControlledUnitary
      (layout.recursiveResidualLayout depth).targetWire
      (layout.recursiveResidualLayout depth).controlSet
      (powerTwoRoot (rootIndex + depth) U)
  let truncated : UnitaryGate ambientWidth :=
    Circuit.eval
      (truncatedRecursiveCircuitFrom rootIndex residualDepth depth layout U)
  have hfactor :=
    layout.positiveControlledUnitary_eq_residual_mul_eval_truncatedFrom
      rootIndex residualDepth depth U
  change operatorDistance
      (positiveControlledUnitary layout.targetWire layout.controlSet
        (powerTwoRoot rootIndex U) : Gate ambientWidth)
      (truncated : Gate ambientWidth) = _
  rw [hfactor]
  calc
    operatorDistance (residual * truncated : Gate ambientWidth)
          (truncated : Gate ambientWidth) =
        operatorDistance (residual : Gate ambientWidth) (1 : Gate ambientWidth) := by
      simpa only [Submonoid.coe_mul, Submonoid.coe_one, Matrix.one_mul] using
        (operatorDistance_unitary_mul_right
          (residual : Gate ambientWidth) (1 : Gate ambientWidth) truncated)
    _ = operatorDistance
        (powerTwoRoot (rootIndex + depth) U : QubitMatrix)
        (1 : QubitMatrix) := by
      exact operatorDistance_positiveControlledUnitary_one_eq
        (layout.recursiveResidualLayout depth).targetWire
        (layout.recursiveResidualLayout depth).controlSet
        (powerTwoRoot (rootIndex + depth) U)

/-- General root-indexed truncation bound. -/
theorem operatorDistance_truncatedRecursiveCircuitFrom_le
    {ambientWidth : ℕ} (rootIndex residualDepth depth : ℕ)
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    operatorDistance
        (positiveControlledUnitary layout.targetWire layout.controlSet
          (powerTwoRoot rootIndex U) : Gate ambientWidth)
        (Circuit.eval
          (truncatedRecursiveCircuitFrom rootIndex residualDepth depth layout U) :
            Gate ambientWidth) ≤
      Real.pi / (2 ^ (rootIndex + depth) : ℝ) := by
  rw [layout.operatorDistance_truncatedRecursiveCircuitFrom_eq_residual]
  exact powerTwoRoot_operatorDistance_one_le (rootIndex + depth) U

/-- Root-index-zero exact truncation-error identity. -/
theorem operatorDistance_truncatedRecursiveCircuit_eq_residual
    {ambientWidth residualDepth depth : ℕ}
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    operatorDistance
        (positiveControlledUnitary layout.targetWire layout.controlSet U :
          Gate ambientWidth)
        (Circuit.eval (truncatedRecursiveCircuit residualDepth depth layout U) :
          Gate ambientWidth) =
      operatorDistance (powerTwoRoot depth U : QubitMatrix) (1 : QubitMatrix) := by
  simpa [truncatedRecursiveCircuit] using
    layout.operatorDistance_truncatedRecursiveCircuitFrom_eq_residual
      0 residualDepth depth U

/-- The depth-`depth` truncated circuit has operator error at most `pi / 2^depth`. -/
theorem operatorDistance_truncatedRecursiveCircuit_le
    {ambientWidth residualDepth depth : ℕ}
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    operatorDistance
        (positiveControlledUnitary layout.targetWire layout.controlSet U :
          Gate ambientWidth)
        (Circuit.eval (truncatedRecursiveCircuit residualDepth depth layout U) :
          Gate ambientWidth) ≤
      Real.pi / (2 ^ depth : ℝ) := by
  simpa [truncatedRecursiveCircuit] using
    layout.operatorDistance_truncatedRecursiveCircuitFrom_le
      0 residualDepth depth U

/-! ## Optional exact macro completion -/

/--
Append the omitted residual controlled primitive.  This remains macro syntax and
does not assert that the primitive has been expanded into the accepted basis.
-/
def completedTruncatedRecursiveCircuitFrom {ambientWidth : ℕ}
    (rootIndex residualDepth depth : ℕ)
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) : Circuit ambientWidth :=
  Circuit.append
    (truncatedRecursiveCircuitFrom rootIndex residualDepth depth layout U)
    [Primitive.positiveControlled
      (layout.recursiveResidualLayout depth).targetWire
      (layout.recursiveResidualLayout depth).controlSet
      (powerTwoRoot (rootIndex + depth) U)]

/-- Appending the residual macro exactly completes the selected controlled root. -/
@[simp]
theorem eval_completedTruncatedRecursiveCircuitFrom
    {ambientWidth : ℕ} (rootIndex residualDepth depth : ℕ)
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    Circuit.eval
        (completedTruncatedRecursiveCircuitFrom rootIndex residualDepth depth
          layout U) =
      positiveControlledUnitary layout.targetWire layout.controlSet
        (powerTwoRoot rootIndex U) := by
  rw [completedTruncatedRecursiveCircuitFrom, Circuit.eval_append,
    Circuit.eval_singleton, Primitive.positiveControlled_denotation]
  exact (layout.positiveControlledUnitary_eq_residual_mul_eval_truncatedFrom
    rootIndex residualDepth depth U).symm

/-- Root-index-zero exact macro completion for `U`. -/
def completedTruncatedRecursiveCircuit {ambientWidth : ℕ}
    (residualDepth depth : ℕ)
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) : Circuit ambientWidth :=
  completedTruncatedRecursiveCircuitFrom 0 residualDepth depth layout U

@[simp]
theorem eval_completedTruncatedRecursiveCircuit
    {ambientWidth residualDepth depth : ℕ}
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    Circuit.eval
        (completedTruncatedRecursiveCircuit residualDepth depth layout U) =
      positiveControlledUnitary layout.targetWire layout.controlSet U := by
  simp [completedTruncatedRecursiveCircuit]

end OrderedControlLayout

end

end Barenco.MultiControl
