import Barenco.MultiControl.Approximate
import Barenco.MultiControl.RecursiveExpansion

/-!
# Primitive expansion of truncated recursive synthesis

This leaf expands every retained shell of the truncated Lemma 7.5 recursion
into the library's literal one-qubit/CNOT syntax.  Depth zero is the empty
circuit: the omitted residual controlled root is not smuggled into the
approximation syntax.

The semantic theorem compares this literal expansion with the macro circuit in
`Barenco.MultiControl.Approximate` on the full ambient register.  Resource
theorems below are derived from the primitive lists themselves.  No count is
inferred from a matrix equality.

An optional exact completion appends the already verified primitive recursive
implementation of the omitted residual controlled root.  It is semantically
exact and its counts agree algebraically with the established full recursive
construction at the combined depth.
-/

namespace Barenco.MultiControl

open Barenco.OneQubit
open Barenco.ControlledCircuit

noncomputable section

namespace OrderedControlLayout

/-! ## One expanded retained shell -/

/--
Literal one-qubit/CNOT expansion of the four retained macros in one truncated
recursion shell.  The fifth substitution component is empty because the
residual target operation is supplied by the recursive tail.
-/
def expandedRecursiveRetainedShell {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (V : QubitUnitary) : Circuit ambientWidth :=
  recursiveSubstitutionCircuit
    (layout.expandedLastControlledTargetCircuit V)
    (layout.expandedRecursivePrefixXCircuit hwidth)
    (layout.expandedLastControlledTargetCircuit V⁻¹)
    (layout.expandedRecursivePrefixXCircuit hwidth)
    []

/-- Expanding a retained shell preserves its arbitrary-register evaluator. -/
@[simp]
theorem eval_expandedRecursiveRetainedShell {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (V : QubitUnitary) :
    Circuit.eval (layout.expandedRecursiveRetainedShell hwidth V) =
      Circuit.eval (layout.recursiveRetainedShell V) := by
  rw [expandedRecursiveRetainedShell, eval_recursiveSubstitutionCircuit]
  simp only [Circuit.eval_nil,
    eval_expandedLastControlledTargetCircuit,
    eval_expandedRecursivePrefixXCircuit]
  simp [recursiveRetainedShell, Circuit.eval]

/-- Exact one-qubit count of one retained primitive shell. -/
@[simp]
theorem expandedRecursiveRetainedShell_oneQubitCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (V : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (layout.expandedRecursiveRetainedShell hwidth V) = 64 * p - 152 := by
  rw [expandedRecursiveRetainedShell, recursiveSubstitutionCircuit_kindCount]
  simp only [expandedLastControlledTargetCircuit_oneQubitCount,
    expandedRecursivePrefixXCircuit_oneQubitCount]
  simp only [Circuit.kindCount, List.countP_nil, Nat.add_zero]
  omega

/-- Exact CNOT count of one retained primitive shell. -/
@[simp]
theorem expandedRecursiveRetainedShell_cnotCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (V : QubitUnitary) :
    Circuit.kindCount .cnot
        (layout.expandedRecursiveRetainedShell hwidth V) = 48 * p - 100 := by
  rw [expandedRecursiveRetainedShell, recursiveSubstitutionCircuit_kindCount]
  simp only [expandedLastControlledTargetCircuit_cnotCount,
    expandedRecursivePrefixXCircuit_cnotCount]
  simp only [Circuit.kindCount, List.countP_nil, Nat.add_zero]
  omega

/-- Exact primitive count of one retained primitive shell. -/
@[simp]
theorem expandedRecursiveRetainedShell_gateCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (V : QubitUnitary) :
    Circuit.gateCount (layout.expandedRecursiveRetainedShell hwidth V) =
      112 * p - 252 := by
  rw [expandedRecursiveRetainedShell, recursiveSubstitutionCircuit_gateCount]
  simp only [expandedLastControlledTargetCircuit_gateCount,
    expandedRecursivePrefixXCircuit_gateCount]
  simp only [Circuit.gateCount, List.length_nil, Nat.add_zero]
  omega

/-- Exact accepted one-qubit/CNOT cost of one retained primitive shell. -/
@[simp]
theorem expandedRecursiveRetainedShell_oneQubitCNOTCost {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) (V : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (layout.expandedRecursiveRetainedShell hwidth V) =
      some (112 * p - 252) := by
  rw [expandedRecursiveRetainedShell, recursiveSubstitutionCircuit_cost]
  simp only [expandedLastControlledTargetCircuit_oneQubitCNOTCost,
    expandedRecursivePrefixXCircuit_oneQubitCNOTCost]
  simp only [Circuit.cost, Circuit.addCost]
  exact congrArg some (by omega)

/-! ## Literal truncated expansion -/

/--
Expand `depth` retained shells, starting at an arbitrary coherent-root index.
The literal circuit is empty at depth zero.
-/
def expandedTruncatedRecursiveCircuitFrom {ambientWidth : ℕ} :
    (rootIndex residualDepth depth : ℕ) →
      OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth →
        QubitUnitary → Circuit ambientWidth
  | _rootIndex, _residualDepth, 0, _layout, _U => []
  | rootIndex, residualDepth, depth + 1, layout, U =>
      let V := powerTwoRoot (rootIndex + 1) U
      Circuit.append
        (expandedRecursiveRetainedShell
          (p := (residualDepth + 6) + depth) layout (by omega) V)
        (expandedTruncatedRecursiveCircuitFrom (rootIndex + 1) residualDepth
          depth layout.prefixTargetLayout U)
termination_by _rootIndex _residualDepth depth _layout _U => depth

@[simp]
theorem expandedTruncatedRecursiveCircuitFrom_zero {ambientWidth : ℕ}
    (rootIndex residualDepth : ℕ)
    (layout : OrderedControlLayout (residualDepth + 6) ambientWidth)
    (U : QubitUnitary) :
    expandedTruncatedRecursiveCircuitFrom rootIndex residualDepth 0 layout U = [] :=
  by simp [expandedTruncatedRecursiveCircuitFrom]

@[simp]
theorem expandedTruncatedRecursiveCircuitFrom_succ
    {ambientWidth : ℕ} (rootIndex residualDepth depth : ℕ)
    (layout : OrderedControlLayout ((residualDepth + 6) + (depth + 1)) ambientWidth)
    (U : QubitUnitary) :
    expandedTruncatedRecursiveCircuitFrom rootIndex residualDepth (depth + 1)
        layout U =
      let V := powerTwoRoot (rootIndex + 1) U
      Circuit.append
        (expandedRecursiveRetainedShell
          (p := (residualDepth + 6) + depth) layout (by omega) V)
        (expandedTruncatedRecursiveCircuitFrom (rootIndex + 1) residualDepth
          depth layout.prefixTargetLayout U) :=
  by simp only [expandedTruncatedRecursiveCircuitFrom]

/-- Root-index-zero wrapper for the truncated primitive expansion. -/
def expandedTruncatedRecursiveCircuit {ambientWidth : ℕ}
    (residualDepth depth : ℕ)
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) : Circuit ambientWidth :=
  expandedTruncatedRecursiveCircuitFrom 0 residualDepth depth layout U

/-- The literal primitive expansion has exactly the macro truncation evaluator. -/
@[simp]
theorem eval_expandedTruncatedRecursiveCircuitFrom {ambientWidth : ℕ} :
    ∀ (rootIndex residualDepth depth : ℕ)
      (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
      (U : QubitUnitary),
      Circuit.eval
          (expandedTruncatedRecursiveCircuitFrom rootIndex residualDepth depth
            layout U) =
        Circuit.eval
          (truncatedRecursiveCircuitFrom rootIndex residualDepth depth layout U)
  | _rootIndex, _residualDepth, 0, _layout, _U => by
      simp [truncatedRecursiveCircuitFrom]
  | rootIndex, residualDepth, depth + 1, layout, U => by
      rw [expandedTruncatedRecursiveCircuitFrom_succ,
        truncatedRecursiveCircuitFrom, Circuit.eval_append, Circuit.eval_append,
        eval_expandedRecursiveRetainedShell,
        eval_expandedTruncatedRecursiveCircuitFrom]

/-- Root-index-zero evaluator preservation. -/
@[simp]
theorem eval_expandedTruncatedRecursiveCircuit
    {ambientWidth residualDepth depth : ℕ}
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    Circuit.eval
        (expandedTruncatedRecursiveCircuit residualDepth depth layout U) =
      Circuit.eval (truncatedRecursiveCircuit residualDepth depth layout U) := by
  simp [expandedTruncatedRecursiveCircuit, truncatedRecursiveCircuit]

/-! ## Exact syntax recurrences and closed counts -/

/-- One-qubit count added by the outer retained shell. -/
theorem expandedTruncatedRecursiveCircuitFrom_oneQubitCount_succ
    {ambientWidth : ℕ} (rootIndex residualDepth depth : ℕ)
    (layout : OrderedControlLayout ((residualDepth + 6) + (depth + 1)) ambientWidth)
    (U : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (expandedTruncatedRecursiveCircuitFrom rootIndex residualDepth (depth + 1)
          layout U) =
      Circuit.kindCount .oneQubit
          (expandedTruncatedRecursiveCircuitFrom (rootIndex + 1) residualDepth
            depth layout.prefixTargetLayout U) +
        (64 * residualDepth + 64 * depth + 232) := by
  rw [expandedTruncatedRecursiveCircuitFrom_succ, Circuit.kindCount_append,
    expandedRecursiveRetainedShell_oneQubitCount]
  omega

/-- CNOT count added by the outer retained shell. -/
theorem expandedTruncatedRecursiveCircuitFrom_cnotCount_succ
    {ambientWidth : ℕ} (rootIndex residualDepth depth : ℕ)
    (layout : OrderedControlLayout ((residualDepth + 6) + (depth + 1)) ambientWidth)
    (U : QubitUnitary) :
    Circuit.kindCount .cnot
        (expandedTruncatedRecursiveCircuitFrom rootIndex residualDepth (depth + 1)
          layout U) =
      Circuit.kindCount .cnot
          (expandedTruncatedRecursiveCircuitFrom (rootIndex + 1) residualDepth
            depth layout.prefixTargetLayout U) +
        (48 * residualDepth + 48 * depth + 188) := by
  rw [expandedTruncatedRecursiveCircuitFrom_succ, Circuit.kindCount_append,
    expandedRecursiveRetainedShell_cnotCount]
  omega

/-- Primitive count added by the outer retained shell. -/
theorem expandedTruncatedRecursiveCircuitFrom_gateCount_succ
    {ambientWidth : ℕ} (rootIndex residualDepth depth : ℕ)
    (layout : OrderedControlLayout ((residualDepth + 6) + (depth + 1)) ambientWidth)
    (U : QubitUnitary) :
    Circuit.gateCount
        (expandedTruncatedRecursiveCircuitFrom rootIndex residualDepth (depth + 1)
          layout U) =
      Circuit.gateCount
          (expandedTruncatedRecursiveCircuitFrom (rootIndex + 1) residualDepth
            depth layout.prefixTargetLayout U) +
        (112 * residualDepth + 112 * depth + 420) := by
  rw [expandedTruncatedRecursiveCircuitFrom_succ, Circuit.gateCount_append,
    expandedRecursiveRetainedShell_gateCount]
  omega

/-- Exact one-qubit count of the retained-shell syntax. -/
@[simp]
theorem expandedTruncatedRecursiveCircuitFrom_oneQubitCount
    {ambientWidth : ℕ} :
    ∀ (rootIndex residualDepth depth : ℕ)
      (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
      (U : QubitUnitary),
      Circuit.kindCount .oneQubit
          (expandedTruncatedRecursiveCircuitFrom rootIndex residualDepth depth
            layout U) =
        32 * depth ^ 2 + (64 * residualDepth + 200) * depth
  | _rootIndex, _residualDepth, 0, _layout, _U => by
      rw [expandedTruncatedRecursiveCircuitFrom_zero]
      rfl
  | rootIndex, residualDepth, depth + 1, layout, U => by
      rw [expandedTruncatedRecursiveCircuitFrom_oneQubitCount_succ,
        expandedTruncatedRecursiveCircuitFrom_oneQubitCount]
      ring

/-- Exact CNOT count of the retained-shell syntax. -/
@[simp]
theorem expandedTruncatedRecursiveCircuitFrom_cnotCount
    {ambientWidth : ℕ} :
    ∀ (rootIndex residualDepth depth : ℕ)
      (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
      (U : QubitUnitary),
      Circuit.kindCount .cnot
          (expandedTruncatedRecursiveCircuitFrom rootIndex residualDepth depth
            layout U) =
        24 * depth ^ 2 + (48 * residualDepth + 164) * depth
  | _rootIndex, _residualDepth, 0, _layout, _U => by
      rw [expandedTruncatedRecursiveCircuitFrom_zero]
      rfl
  | rootIndex, residualDepth, depth + 1, layout, U => by
      rw [expandedTruncatedRecursiveCircuitFrom_cnotCount_succ,
        expandedTruncatedRecursiveCircuitFrom_cnotCount]
      ring

/-- Exact primitive count of the retained-shell syntax. -/
@[simp]
theorem expandedTruncatedRecursiveCircuitFrom_gateCount
    {ambientWidth : ℕ} :
    ∀ (rootIndex residualDepth depth : ℕ)
      (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
      (U : QubitUnitary),
      Circuit.gateCount
          (expandedTruncatedRecursiveCircuitFrom rootIndex residualDepth depth
            layout U) =
        56 * depth ^ 2 + (112 * residualDepth + 364) * depth
  | _rootIndex, _residualDepth, 0, _layout, _U => by
      rw [expandedTruncatedRecursiveCircuitFrom_zero]
      rfl
  | rootIndex, residualDepth, depth + 1, layout, U => by
      rw [expandedTruncatedRecursiveCircuitFrom_gateCount_succ,
        expandedTruncatedRecursiveCircuitFrom_gateCount]
      ring

/-- Exact accepted one-qubit/CNOT cost of the retained-shell syntax. -/
@[simp]
theorem expandedTruncatedRecursiveCircuitFrom_oneQubitCNOTCost
    {ambientWidth : ℕ} :
    ∀ (rootIndex residualDepth depth : ℕ)
      (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
      (U : QubitUnitary),
      Circuit.cost CostModel.oneQubitCNOT
          (expandedTruncatedRecursiveCircuitFrom rootIndex residualDepth depth
            layout U) =
        some (56 * depth ^ 2 + (112 * residualDepth + 364) * depth)
  | _rootIndex, _residualDepth, 0, _layout, _U => by
      rw [expandedTruncatedRecursiveCircuitFrom_zero]
      rfl
  | rootIndex, residualDepth, depth + 1, layout, U => by
      rw [expandedTruncatedRecursiveCircuitFrom_succ, Circuit.cost_append,
        expandedRecursiveRetainedShell_oneQubitCNOTCost,
        expandedTruncatedRecursiveCircuitFrom_oneQubitCNOTCost,
        Circuit.addCost_some]
      rw [show 112 * (residualDepth + 6 + depth) - 252 =
        112 * residualDepth + 112 * depth + 420 by omega]
      exact congrArg some (by ring)

/-- Root-index-zero exact one-qubit count. -/
@[simp]
theorem expandedTruncatedRecursiveCircuit_oneQubitCount
    {ambientWidth residualDepth depth : ℕ}
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (expandedTruncatedRecursiveCircuit residualDepth depth layout U) =
      32 * depth ^ 2 + (64 * residualDepth + 200) * depth := by
  simp [expandedTruncatedRecursiveCircuit]

/-- Root-index-zero exact CNOT count. -/
@[simp]
theorem expandedTruncatedRecursiveCircuit_cnotCount
    {ambientWidth residualDepth depth : ℕ}
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    Circuit.kindCount .cnot
        (expandedTruncatedRecursiveCircuit residualDepth depth layout U) =
      24 * depth ^ 2 + (48 * residualDepth + 164) * depth := by
  simp [expandedTruncatedRecursiveCircuit]

/-- Root-index-zero exact primitive count. -/
@[simp]
theorem expandedTruncatedRecursiveCircuit_gateCount
    {ambientWidth residualDepth depth : ℕ}
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    Circuit.gateCount
        (expandedTruncatedRecursiveCircuit residualDepth depth layout U) =
      56 * depth ^ 2 + (112 * residualDepth + 364) * depth := by
  simp [expandedTruncatedRecursiveCircuit]

/-- Root-index-zero exact accepted one-qubit/CNOT cost. -/
@[simp]
theorem expandedTruncatedRecursiveCircuit_oneQubitCNOTCost
    {ambientWidth residualDepth depth : ℕ}
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (expandedTruncatedRecursiveCircuit residualDepth depth layout U) =
      some (56 * depth ^ 2 + (112 * residualDepth + 364) * depth) := by
  simp [expandedTruncatedRecursiveCircuit]

/-! ## Operator-distance preservation -/

/--
The primitive expansion has the same exact residual-root error as the macro
truncation, at an arbitrary coherent-root index.
-/
theorem operatorDistance_expandedTruncatedRecursiveCircuitFrom_eq_residual
    {ambientWidth : ℕ} (rootIndex residualDepth depth : ℕ)
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    operatorDistance
        (positiveControlledUnitary layout.targetWire layout.controlSet
          (powerTwoRoot rootIndex U) : Gate ambientWidth)
        (Circuit.eval
          (expandedTruncatedRecursiveCircuitFrom rootIndex residualDepth depth
            layout U) : Gate ambientWidth) =
      operatorDistance (powerTwoRoot (rootIndex + depth) U : QubitMatrix)
        (1 : QubitMatrix) := by
  rw [eval_expandedTruncatedRecursiveCircuitFrom]
  exact layout.operatorDistance_truncatedRecursiveCircuitFrom_eq_residual
    rootIndex residualDepth depth U

/-- Root-index-zero exact residual-root error identity. -/
theorem operatorDistance_expandedTruncatedRecursiveCircuit_eq_residual
    {ambientWidth residualDepth depth : ℕ}
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    operatorDistance
        (positiveControlledUnitary layout.targetWire layout.controlSet U :
          Gate ambientWidth)
        (Circuit.eval
          (expandedTruncatedRecursiveCircuit residualDepth depth layout U) :
            Gate ambientWidth) =
      operatorDistance (powerTwoRoot depth U : QubitMatrix)
        (1 : QubitMatrix) := by
  rw [eval_expandedTruncatedRecursiveCircuit]
  exact layout.operatorDistance_truncatedRecursiveCircuit_eq_residual
    U

/-- General-root primitive truncation error is at most `pi / 2^(rootIndex+depth)`. -/
theorem operatorDistance_expandedTruncatedRecursiveCircuitFrom_le
    {ambientWidth : ℕ} (rootIndex residualDepth depth : ℕ)
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    operatorDistance
        (positiveControlledUnitary layout.targetWire layout.controlSet
          (powerTwoRoot rootIndex U) : Gate ambientWidth)
        (Circuit.eval
          (expandedTruncatedRecursiveCircuitFrom rootIndex residualDepth depth
            layout U) : Gate ambientWidth) ≤
      Real.pi / (2 ^ (rootIndex + depth) : ℝ) := by
  rw [layout.operatorDistance_expandedTruncatedRecursiveCircuitFrom_eq_residual]
  exact powerTwoRoot_operatorDistance_one_le (rootIndex + depth) U

/-- Root-index-zero primitive truncation error is at most `pi / 2^depth`. -/
theorem operatorDistance_expandedTruncatedRecursiveCircuit_le
    {ambientWidth residualDepth depth : ℕ}
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    operatorDistance
        (positiveControlledUnitary layout.targetWire layout.controlSet U :
          Gate ambientWidth)
        (Circuit.eval
          (expandedTruncatedRecursiveCircuit residualDepth depth layout U) :
            Gate ambientWidth) ≤
      Real.pi / (2 ^ depth : ℝ) := by
  rw [layout.operatorDistance_expandedTruncatedRecursiveCircuit_eq_residual]
  exact powerTwoRoot_operatorDistance_one_le depth U

/-! ## Optional exact primitive completion -/

/--
Append the exact primitive implementation of the omitted residual controlled
root.  The residual has `residualDepth + 6` controls, so its established
recursive expansion has depth `residualDepth`.
-/
def completedExpandedTruncatedRecursiveCircuitFrom {ambientWidth : ℕ}
    (rootIndex residualDepth depth : ℕ)
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) : Circuit ambientWidth :=
  Circuit.append
    (expandedTruncatedRecursiveCircuitFrom rootIndex residualDepth depth layout U)
    (recursivePrimitiveCircuit residualDepth
      (layout.recursiveResidualLayout depth)
      (powerTwoRoot (rootIndex + depth) U))

/-- Exact full controlled semantics of the primitive completion. -/
@[simp]
theorem eval_completedExpandedTruncatedRecursiveCircuitFrom
    {ambientWidth : ℕ} (rootIndex residualDepth depth : ℕ)
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    Circuit.eval
        (completedExpandedTruncatedRecursiveCircuitFrom rootIndex residualDepth
          depth layout U) =
      positiveControlledUnitary layout.targetWire layout.controlSet
        (powerTwoRoot rootIndex U) := by
  rw [completedExpandedTruncatedRecursiveCircuitFrom, Circuit.eval_append,
    eval_recursivePrimitiveCircuit, eval_expandedTruncatedRecursiveCircuitFrom]
  exact (layout.positiveControlledUnitary_eq_residual_mul_eval_truncatedFrom
    rootIndex residualDepth depth U).symm

/-- Root-index-zero exact primitive completion. -/
def completedExpandedTruncatedRecursiveCircuit {ambientWidth : ℕ}
    (residualDepth depth : ℕ)
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) : Circuit ambientWidth :=
  completedExpandedTruncatedRecursiveCircuitFrom 0 residualDepth depth layout U

/-- Root-index-zero exact full controlled semantics. -/
@[simp]
theorem eval_completedExpandedTruncatedRecursiveCircuit
    {ambientWidth residualDepth depth : ℕ}
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    Circuit.eval
        (completedExpandedTruncatedRecursiveCircuit residualDepth depth layout U) =
      positiveControlledUnitary layout.targetWire layout.controlSet U := by
  simp [completedExpandedTruncatedRecursiveCircuit]

end OrderedControlLayout

end

end Barenco.MultiControl
