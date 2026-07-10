import Barenco.MultiControl.ApproximationResources

/-!
# Boundary diagnostics for approximate multi-control synthesis

This root-excluded leaf checks the depth selector and the first two legal
logical widths of the corrected Lemma 7.8 construction.  Every resource claim
is obtained from the selected circuit syntax or from the exact-completion
syntax; none is inferred from semantic equality.
-/

namespace Barenco.MultiControl.ApproximationExamples

open Barenco
open Barenco.OneQubit
open Barenco.ControlledCircuit
open OrderedControlLayout
open scoped Matrix

noncomputable section

/-! ## Canonical consecutive layouts -/

/-- Consecutive controls `0,…,k-1` followed by target wire `k`. -/
def consecutiveLayout (controlCount : ℕ) :
    OrderedControlLayout controlCount (controlCount + 1) where
  controlWire := Fin.castSuccEmb
  targetWire := Fin.last controlCount
  control_ne_target := Fin.castSucc_ne_last

/-- Six controls followed by the target on logical width seven. -/
def widthSevenLayout : OrderedControlLayout 6 7 := consecutiveLayout 6

/-- Seven controls followed by the target on logical width eight. -/
def widthEightLayout : OrderedControlLayout 7 8 := consecutiveLayout 7

/-! ## Exact selector boundaries -/

/-- Tolerance `pi` requests no retained recursion shells. -/
theorem principalRootBoundDepth_pi :
    principalRootBoundDepth Real.pi = 0 := by
  exact (principalRootBoundDepth_eq_zero_iff Real.pi Real.pi_pos).2 le_rfl

/-- Tolerance `pi/2` requests exactly one retained recursion shell. -/
theorem principalRootBoundDepth_pi_div_two :
    principalRootBoundDepth (Real.pi / 2) = 1 := by
  have hepsilon : 0 < Real.pi / 2 := by positivity
  have hle : principalRootBoundDepth (Real.pi / 2) ≤ 1 :=
    (principalRootBoundDepth_le_iff (Real.pi / 2) hepsilon 1).2 (by
      simp [principalRootErrorBound])
  have hne : principalRootBoundDepth (Real.pi / 2) ≠ 0 := by
    intro hzero
    have hpi : Real.pi ≤ Real.pi / 2 :=
      (principalRootBoundDepth_eq_zero_iff (Real.pi / 2) hepsilon).1 hzero
    linarith [Real.pi_pos]
  omega

/-! ## Width seven: empty truncation and exact fallback -/

/-- At tolerance `pi`, width seven selects the literal empty truncation. -/
@[simp]
theorem widthSeven_pi_circuit (U : QubitUnitary) :
    epsilonSynthesisPrimitiveCircuit 0 widthSevenLayout U Real.pi = [] := by
  apply List.eq_nil_of_length_eq_zero
  change Circuit.gateCount
    (epsilonSynthesisPrimitiveCircuit 0 widthSevenLayout U Real.pi) = 0
  rw [epsilonSynthesisPrimitiveCircuit_gateCount]
  norm_num [epsilonSynthesisTotalCount, principalRootBoundDepth_pi,
    truncatedRecursiveTotalCount]

/-- The selected empty width-seven truncation has zero syntax resources. -/
theorem widthSeven_pi_resources (U : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (epsilonSynthesisPrimitiveCircuit 0 widthSevenLayout U Real.pi) = 0 ∧
      Circuit.kindCount .cnot
        (epsilonSynthesisPrimitiveCircuit 0 widthSevenLayout U Real.pi) = 0 ∧
      Circuit.gateCount
        (epsilonSynthesisPrimitiveCircuit 0 widthSevenLayout U Real.pi) = 0 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (epsilonSynthesisPrimitiveCircuit 0 widthSevenLayout U Real.pi) = some 0 := by
  rw [widthSeven_pi_circuit]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- At tolerance `pi/2`, width seven cannot retain one shell and selects exact fallback. -/
theorem widthSeven_pi_div_two_circuit (U : QubitUnitary) :
    epsilonSynthesisPrimitiveCircuit 0 widthSevenLayout U (Real.pi / 2) =
      recursivePrimitiveCircuit 0 widthSevenLayout U := by
  apply epsilonSynthesisPrimitiveCircuit_eq_exact
  rw [principalRootBoundDepth_pi_div_two]
  omega

/-- The exact width-seven fallback has profile `(252,188,440)`. -/
theorem widthSeven_pi_div_two_resources (U : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (epsilonSynthesisPrimitiveCircuit 0 widthSevenLayout U (Real.pi / 2)) =
        252 ∧
      Circuit.kindCount .cnot
        (epsilonSynthesisPrimitiveCircuit 0 widthSevenLayout U (Real.pi / 2)) =
        188 ∧
      Circuit.gateCount
        (epsilonSynthesisPrimitiveCircuit 0 widthSevenLayout U (Real.pi / 2)) =
        440 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (epsilonSynthesisPrimitiveCircuit 0 widthSevenLayout U (Real.pi / 2)) =
        some 440 := by
  rw [widthSeven_pi_div_two_circuit]
  exact recursivePrimitiveCircuit_depth_zero_resources widthSevenLayout U

/-- Exact semantics of the width-seven fallback. -/
theorem widthSeven_pi_div_two_eval (U : QubitUnitary) :
    Circuit.eval
        (epsilonSynthesisPrimitiveCircuit 0 widthSevenLayout U (Real.pi / 2)) =
      positiveControlledUnitary widthSevenLayout.targetWire
        widthSevenLayout.controlSet U := by
  rw [widthSeven_pi_div_two_circuit]
  exact eval_recursivePrimitiveCircuit 0 widthSevenLayout U

/-- The selected width-seven fallback meets the requested error certificate. -/
theorem widthSeven_pi_div_two_error_le (U : QubitUnitary) :
    operatorDistance
        (positiveControlledUnitary widthSevenLayout.targetWire
          widthSevenLayout.controlSet U : Gate 7)
        (Circuit.eval
          (epsilonSynthesisPrimitiveCircuit 0 widthSevenLayout U
            (Real.pi / 2)) : Gate 7) ≤
      Real.pi / 2 := by
  exact widthSevenLayout.operatorDistance_epsilonSynthesisPrimitiveCircuit_le
    U (Real.pi / 2) (by positivity)

/-! ## Width eight: maximum one-shell truncation -/

/-- Width eight has exactly enough capacity for the requested one-shell truncation. -/
theorem widthEight_pi_div_two_depth_fits :
    principalRootBoundDepth (Real.pi / 2) ≤ 1 := by
  rw [principalRootBoundDepth_pi_div_two]

/-- The selected width-eight circuit is a residual-depth-zero, one-shell truncation. -/
theorem widthEight_pi_div_two_is_oneShellTruncation (U : QubitUnitary) :
    ∃ (residualDepth depth : ℕ)
      (truncatedLayout : OrderedControlLayout ((residualDepth + 6) + depth) 8),
      residualDepth = 0 ∧ depth = 1 ∧
        epsilonSynthesisPrimitiveCircuit 1 widthEightLayout U (Real.pi / 2) =
          expandedTruncatedRecursiveCircuit residualDepth depth
            truncatedLayout U := by
  have h := epsilonSynthesisPrimitiveCircuit_eq_truncated widthEightLayout U
    (Real.pi / 2) widthEight_pi_div_two_depth_fits
  refine ⟨1 - principalRootBoundDepth (Real.pi / 2),
    principalRootBoundDepth (Real.pi / 2), _, ?_, ?_, h⟩
  · rw [principalRootBoundDepth_pi_div_two]
  · exact principalRootBoundDepth_pi_div_two

/-- The selected one-shell truncation has profile `(232,188,420)`. -/
theorem widthEight_pi_div_two_resources (U : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (epsilonSynthesisPrimitiveCircuit 1 widthEightLayout U (Real.pi / 2)) =
        232 ∧
      Circuit.kindCount .cnot
        (epsilonSynthesisPrimitiveCircuit 1 widthEightLayout U (Real.pi / 2)) =
        188 ∧
      Circuit.gateCount
        (epsilonSynthesisPrimitiveCircuit 1 widthEightLayout U (Real.pi / 2)) =
        420 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (epsilonSynthesisPrimitiveCircuit 1 widthEightLayout U (Real.pi / 2)) =
        some 420 := by
  norm_num [epsilonSynthesisOneQubitCount, epsilonSynthesisCNOTCount,
    epsilonSynthesisTotalCount, principalRootBoundDepth_pi_div_two,
    truncatedRecursiveOneQubitCount, truncatedRecursiveCNOTCount,
    truncatedRecursiveTotalCount]

/-- The selected one-shell truncation meets error `pi/2`. -/
theorem widthEight_pi_div_two_error_le (U : QubitUnitary) :
    operatorDistance
        (positiveControlledUnitary widthEightLayout.targetWire
          widthEightLayout.controlSet U : Gate 8)
        (Circuit.eval
          (epsilonSynthesisPrimitiveCircuit 1 widthEightLayout U
            (Real.pi / 2)) : Gate 8) ≤
      Real.pi / 2 := by
  exact widthEightLayout.operatorDistance_epsilonSynthesisPrimitiveCircuit_le
    U (Real.pi / 2) (by positivity)

/-! ## Exact completion of the one-shell truncation -/

/-- The canonical one-shell exact completion has profile `(484,376,860)`. -/
theorem widthEight_oneShell_completion_resources (U : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (completedExpandedTruncatedRecursiveCircuit 0 1 widthEightLayout U) = 484 ∧
      Circuit.kindCount .cnot
        (completedExpandedTruncatedRecursiveCircuit 0 1 widthEightLayout U) = 376 ∧
      Circuit.gateCount
        (completedExpandedTruncatedRecursiveCircuit 0 1 widthEightLayout U) = 860 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (completedExpandedTruncatedRecursiveCircuit 0 1 widthEightLayout U) =
        some 860 := by
  norm_num

/-- The same canonical completion is exactly the seven-control target unitary. -/
theorem widthEight_oneShell_completion_eval (U : QubitUnitary) :
    Circuit.eval
        (completedExpandedTruncatedRecursiveCircuit 0 1 widthEightLayout U) =
      positiveControlledUnitary widthEightLayout.targetWire
        widthEightLayout.controlSet U := by
  exact eval_completedExpandedTruncatedRecursiveCircuit
    (residualDepth := 0) (depth := 1) widthEightLayout U

/-! ## Representative finite-event consequence -/

/--
Every finite computational-basis event changes by at most `pi/2` for the
selected width-eight circuit and a pure input of norm at most one.
-/
theorem widthEight_pi_div_two_eventProbability_le
    (U : QubitUnitary) (psi : EuclideanSpace ℂ (Basis 8)) (hpsi : ‖psi‖ ≤ 1)
    (event : Finset (Basis 8)) :
    abs
        (eventProbability event
            ((positiveControlledUnitary widthEightLayout.targetWire
              widthEightLayout.controlSet U : Gate 8) *ᵥ psi) -
          eventProbability event
            ((Circuit.eval
              (epsilonSynthesisPrimitiveCircuit 1 widthEightLayout U
                (Real.pi / 2)) : Gate 8) *ᵥ psi)) ≤
      Real.pi / 2 := by
  exact widthEightLayout.epsilonSynthesisPrimitiveCircuit_eventProbability_le
    U (Real.pi / 2) (by positivity) psi hpsi event

end

end Barenco.MultiControl.ApproximationExamples
