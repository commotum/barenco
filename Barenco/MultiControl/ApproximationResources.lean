import Barenco.MultiControl.ApproximateExpansion
import Barenco.MultiControl.Resources
import Barenco.Equivalence.EventProbability
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Epsilon selection and resources for truncated recursive synthesis

This leaf packages the corrected, source-aligned form of Barenco Lemma 7.8.
The requested principal-root depth is the natural ceiling of
`logb 2 (pi / epsilon)`.  If that many retained recursion shells fit in the
available exact depth, the literal primitive truncation is used.  Otherwise the
already verified exact recursive circuit is selected; a capped truncation is
never presented as meeting an error it cannot certify.

All count equalities below are tied to the selected circuit syntax.  The
asymptotic results are upper bounds for this named construction, not lower
bounds for synthesis and not `Theta` claims.  Event-probability corollaries are
only for finite computational-basis events on pure inputs of norm at most one.
-/

namespace Barenco.MultiControl

open Barenco.OneQubit
open Barenco.ControlledCircuit
open Filter Asymptotics
open scoped Matrix

noncomputable section

/-! ## Source-aligned principal-root depth -/

/-- The residual-root error bound after retaining `depth` recursive shells. -/
def principalRootErrorBound (depth : ℕ) : ℝ :=
  Real.pi / (2 ^ depth : ℝ)

/--
The least natural depth certified by the paper's principal-root estimate.

This definition is total, but every approximation theorem explicitly assumes
`0 < epsilon`.  In particular, mathlib's total logarithm assigns zero at a zero
argument, which is not an approximation certificate for zero tolerance.
-/
noncomputable def principalRootBoundDepth (epsilon : ℝ) : ℕ :=
  ⌈Real.logb 2 (Real.pi / epsilon)⌉₊

/-- Exact characterization of the least depth certified by the root bound. -/
theorem principalRootBoundDepth_le_iff (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (depth : ℕ) :
    principalRootBoundDepth epsilon ≤ depth ↔
      principalRootErrorBound depth ≤ epsilon := by
  have hx : 0 < Real.pi / epsilon := div_pos Real.pi_pos hepsilon
  rw [principalRootBoundDepth, Nat.ceil_le,
    Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hx,
    Real.rpow_natCast]
  have hpow : 0 < (2 : ℝ) ^ depth := by positivity
  constructor
  · intro h
    rw [principalRootErrorBound, div_le_iff₀ hpow]
    calc
      Real.pi = (Real.pi / epsilon) * epsilon := by
        simp [hepsilon.ne']
      _ ≤ (2 : ℝ) ^ depth * epsilon :=
        mul_le_mul_of_nonneg_right h hepsilon.le
      _ = epsilon * (2 : ℝ) ^ depth := mul_comm _ _
  · intro h
    rw [principalRootErrorBound, div_le_iff₀ hpow] at h
    rw [div_le_iff₀ hepsilon]
    simpa [mul_comm] using h

/-- The selected depth itself certifies the requested positive tolerance. -/
theorem principalRootBoundDepth_spec (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    principalRootErrorBound (principalRootBoundDepth epsilon) ≤ epsilon :=
  (principalRootBoundDepth_le_iff epsilon hepsilon _).1 le_rfl

/-- The source-aligned selector uses zero retained shells exactly at `pi ≤ epsilon`. -/
theorem principalRootBoundDepth_eq_zero_iff (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    principalRootBoundDepth epsilon = 0 ↔ Real.pi ≤ epsilon := by
  simpa [principalRootErrorBound] using
    principalRootBoundDepth_le_iff epsilon hepsilon 0

/-- Failure of a finite depth cap is exactly failure of its residual-root bound. -/
theorem capacity_lt_principalRootBoundDepth_iff (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (capacity : ℕ) :
    capacity < principalRootBoundDepth epsilon ↔
      epsilon < principalRootErrorBound capacity := by
  simpa only [not_le] using
    not_congr (principalRootBoundDepth_le_iff epsilon hepsilon capacity)

/-- Natural ceiling is strictly below the source logarithm plus one in its nonnegative regime. -/
theorem principalRootBoundDepth_lt_log_add_one (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ Real.pi) :
    (principalRootBoundDepth epsilon : ℝ) <
      Real.logb 2 (Real.pi / epsilon) + 1 := by
  have hratio : 1 ≤ Real.pi / epsilon := (one_le_div hepsilon).2 hsmall
  exact Nat.ceil_lt_add_one
    (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hratio)

/-- Separate the fixed `pi` factor from the conventional `logb 2 (1/epsilon)`. -/
theorem logb_pi_div_epsilon (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Real.logb 2 (Real.pi / epsilon) =
      Real.logb 2 Real.pi + Real.logb 2 (1 / epsilon) := by
  rw [show Real.pi / epsilon = Real.pi * (1 / epsilon) by ring,
    Real.logb_mul Real.pi_ne_zero (one_div_ne_zero hepsilon.ne')]

/-! ## Exact numerical counts of retained primitive shells -/

/-- Exact one-qubit count for residual exact depth `r` and retained depth `k`. -/
def truncatedRecursiveOneQubitCount (residualDepth depth : ℕ) : ℕ :=
  32 * depth ^ 2 + (64 * residualDepth + 200) * depth

/-- Exact CNOT count for residual exact depth `r` and retained depth `k`. -/
def truncatedRecursiveCNOTCount (residualDepth depth : ℕ) : ℕ :=
  24 * depth ^ 2 + (48 * residualDepth + 164) * depth

/-- Exact total primitive count for residual exact depth `r` and retained depth `k`. -/
def truncatedRecursiveTotalCount (residualDepth depth : ℕ) : ℕ :=
  56 * depth ^ 2 + (112 * residualDepth + 364) * depth

@[simp]
theorem truncatedRecursiveTotalCount_eq_add (residualDepth depth : ℕ) :
    truncatedRecursiveTotalCount residualDepth depth =
      truncatedRecursiveOneQubitCount residualDepth depth +
        truncatedRecursiveCNOTCount residualDepth depth := by
  simp [truncatedRecursiveTotalCount, truncatedRecursiveOneQubitCount,
    truncatedRecursiveCNOTCount]
  ring

namespace OrderedControlLayout

/-- The numerical one-qubit count is exactly the literal expanded circuit count. -/
@[simp]
theorem expandedTruncatedRecursiveCircuit_oneQubitCount_eq_resource
    {ambientWidth residualDepth depth : ℕ}
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (expandedTruncatedRecursiveCircuit residualDepth depth layout U) =
      truncatedRecursiveOneQubitCount residualDepth depth := by
  exact expandedTruncatedRecursiveCircuit_oneQubitCount layout U

/-- The numerical CNOT count is exactly the literal expanded circuit count. -/
@[simp]
theorem expandedTruncatedRecursiveCircuit_cnotCount_eq_resource
    {ambientWidth residualDepth depth : ℕ}
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    Circuit.kindCount .cnot
        (expandedTruncatedRecursiveCircuit residualDepth depth layout U) =
      truncatedRecursiveCNOTCount residualDepth depth := by
  exact expandedTruncatedRecursiveCircuit_cnotCount layout U

/-- The numerical total is exactly the literal expanded circuit length. -/
@[simp]
theorem expandedTruncatedRecursiveCircuit_gateCount_eq_resource
    {ambientWidth residualDepth depth : ℕ}
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    Circuit.gateCount
        (expandedTruncatedRecursiveCircuit residualDepth depth layout U) =
      truncatedRecursiveTotalCount residualDepth depth := by
  exact expandedTruncatedRecursiveCircuit_gateCount layout U

/-- The same total is accepted exactly by the one-qubit/CNOT cost model. -/
@[simp]
theorem expandedTruncatedRecursiveCircuit_oneQubitCNOTCost_eq_resource
    {ambientWidth residualDepth depth : ℕ}
    (layout : OrderedControlLayout ((residualDepth + 6) + depth) ambientWidth)
    (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (expandedTruncatedRecursiveCircuit residualDepth depth layout U) =
      some (truncatedRecursiveTotalCount residualDepth depth) := by
  exact expandedTruncatedRecursiveCircuit_oneQubitCNOTCost layout U

end OrderedControlLayout

/-! ## Pointwise and source-width upper bounds -/

theorem truncatedRecursiveOneQubitCount_le (residualDepth depth : ℕ) :
    truncatedRecursiveOneQubitCount residualDepth depth ≤
      64 * (residualDepth + depth + 7) * depth := by
  simp [truncatedRecursiveOneQubitCount]
  nlinarith

theorem truncatedRecursiveCNOTCount_le (residualDepth depth : ℕ) :
    truncatedRecursiveCNOTCount residualDepth depth ≤
      48 * (residualDepth + depth + 7) * depth := by
  simp [truncatedRecursiveCNOTCount]
  nlinarith

theorem truncatedRecursiveTotalCount_le (residualDepth depth : ℕ) :
    truncatedRecursiveTotalCount residualDepth depth ≤
      112 * (residualDepth + depth + 7) * depth := by
  simp [truncatedRecursiveTotalCount]
  nlinarith

/-- Source-width view of the exact retained one-qubit count. -/
def truncatedRecursiveOneQubitCountAtWidth (sourceWidth depth : ℕ) : ℕ :=
  truncatedRecursiveOneQubitCount (sourceWidth - 7 - depth) depth

/-- Source-width view of the exact retained CNOT count. -/
def truncatedRecursiveCNOTCountAtWidth (sourceWidth depth : ℕ) : ℕ :=
  truncatedRecursiveCNOTCount (sourceWidth - 7 - depth) depth

/-- Source-width view of the exact retained total count. -/
def truncatedRecursiveTotalCountAtWidth (sourceWidth depth : ℕ) : ℕ :=
  truncatedRecursiveTotalCount (sourceWidth - 7 - depth) depth

private theorem sourceWidth_decomposition (sourceWidth depth : ℕ)
    (hwidth : 7 ≤ sourceWidth) (hdepth : depth ≤ sourceWidth - 7) :
    sourceWidth - 7 - depth + depth + 7 = sourceWidth := by
  omega

theorem truncatedRecursiveOneQubitCountAtWidth_le (sourceWidth depth : ℕ)
    (hwidth : 7 ≤ sourceWidth) (hdepth : depth ≤ sourceWidth - 7) :
    truncatedRecursiveOneQubitCountAtWidth sourceWidth depth ≤
      64 * sourceWidth * depth := by
  calc
    truncatedRecursiveOneQubitCountAtWidth sourceWidth depth ≤
        64 * (sourceWidth - 7 - depth + depth + 7) * depth :=
      truncatedRecursiveOneQubitCount_le _ _
    _ = 64 * sourceWidth * depth := by
      rw [sourceWidth_decomposition sourceWidth depth hwidth hdepth]

theorem truncatedRecursiveCNOTCountAtWidth_le (sourceWidth depth : ℕ)
    (hwidth : 7 ≤ sourceWidth) (hdepth : depth ≤ sourceWidth - 7) :
    truncatedRecursiveCNOTCountAtWidth sourceWidth depth ≤
      48 * sourceWidth * depth := by
  calc
    truncatedRecursiveCNOTCountAtWidth sourceWidth depth ≤
        48 * (sourceWidth - 7 - depth + depth + 7) * depth :=
      truncatedRecursiveCNOTCount_le _ _
    _ = 48 * sourceWidth * depth := by
      rw [sourceWidth_decomposition sourceWidth depth hwidth hdepth]

theorem truncatedRecursiveTotalCountAtWidth_le (sourceWidth depth : ℕ)
    (hwidth : 7 ≤ sourceWidth) (hdepth : depth ≤ sourceWidth - 7) :
    truncatedRecursiveTotalCountAtWidth sourceWidth depth ≤
      112 * sourceWidth * depth := by
  calc
    truncatedRecursiveTotalCountAtWidth sourceWidth depth ≤
        112 * (sourceWidth - 7 - depth + depth + 7) * depth :=
      truncatedRecursiveTotalCount_le _ _
    _ = 112 * sourceWidth * depth := by
      rw [sourceWidth_decomposition sourceWidth depth hwidth hdepth]

/-- The named retained-shell construction is `O(width * retainedDepth)`. -/
theorem truncatedRecursiveTotalCount_isBigOWith_width_mul_depth :
    IsBigOWith 112 atTop
      (fun rk : ℕ × ℕ =>
        (truncatedRecursiveTotalCount rk.1 rk.2 : ℝ))
      (fun rk : ℕ × ℕ =>
        (((rk.1 + rk.2 + 7) * rk.2 : ℕ) : ℝ)) := by
  rw [isBigOWith_iff]
  exact Filter.Eventually.of_forall fun rk => by
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ (truncatedRecursiveTotalCount rk.1 rk.2 : ℝ)),
      abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ (((rk.1 + rk.2 + 7) * rk.2 : ℕ) : ℝ))]
    exact_mod_cast (show truncatedRecursiveTotalCount rk.1 rk.2 ≤
      112 * ((rk.1 + rk.2 + 7) * rk.2) by
        simpa [mul_assoc] using truncatedRecursiveTotalCount_le rk.1 rk.2)

/-- Unparameterized Big-O form of the named construction bound. -/
theorem truncatedRecursiveTotalCount_isBigO_width_mul_depth :
    (fun rk : ℕ × ℕ =>
      (truncatedRecursiveTotalCount rk.1 rk.2 : ℝ)) =O[atTop]
      (fun rk : ℕ × ℕ =>
        (((rk.1 + rk.2 + 7) * rk.2 : ℕ) : ℝ)) :=
  truncatedRecursiveTotalCount_isBigOWith_width_mul_depth.isBigO

/-! ## Source-aligned primitive circuit selector -/

namespace OrderedControlLayout

/-- Reindex only the logical control positions along an equality of their counts. -/
private def reindexControlCount {first second ambientWidth : ℕ}
    (hcount : first = second)
    (layout : OrderedControlLayout second ambientWidth) :
    OrderedControlLayout first ambientWidth where
  controlWire :=
    { toFun := fun control => layout.controlWire (Fin.cast hcount control)
      inj' := fun {_ _} h =>
        Fin.cast_injective _ (layout.controlWire.injective h) }
  targetWire := layout.targetWire
  control_ne_target := fun control =>
    layout.control_ne_target (Fin.cast hcount control)

@[simp]
private theorem reindexControlCount_targetWire
    {first second ambientWidth : ℕ} (hcount : first = second)
    (layout : OrderedControlLayout second ambientWidth) :
    (reindexControlCount hcount layout).targetWire = layout.targetWire := rfl

@[simp]
private theorem reindexControlCount_controlSet
    {first second ambientWidth : ℕ} (hcount : first = second)
    (layout : OrderedControlLayout second ambientWidth) :
    (reindexControlCount hcount layout).controlSet = layout.controlSet := by
  subst second
  rfl

/-- Checked layout cast used only when the requested truncation depth fits. -/
private def truncationLayout {availableDepth depth ambientWidth : ℕ}
    (hdepth : depth ≤ availableDepth)
    (layout : OrderedControlLayout (availableDepth + 6) ambientWidth) :
    OrderedControlLayout (((availableDepth - depth) + 6) + depth) ambientWidth :=
  reindexControlCount (by omega) layout

@[simp]
private theorem truncationLayout_targetWire
    {availableDepth depth ambientWidth : ℕ}
    (hdepth : depth ≤ availableDepth)
    (layout : OrderedControlLayout (availableDepth + 6) ambientWidth) :
    (truncationLayout hdepth layout).targetWire = layout.targetWire := by
  simp [truncationLayout]

@[simp]
private theorem truncationLayout_controlSet
    {availableDepth depth ambientWidth : ℕ}
    (hdepth : depth ≤ availableDepth)
    (layout : OrderedControlLayout (availableDepth + 6) ambientWidth) :
    (truncationLayout hdepth layout).controlSet = layout.controlSet := by
  simp [truncationLayout]

/--
Primitive Lemma 7.8 circuit at available exact depth `availableDepth`.

The truncated branch is selected only when its source-aligned required depth
fits.  Otherwise this definition uses the exact recursive circuit.
-/
def epsilonSynthesisPrimitiveCircuit {ambientWidth : ℕ}
    (availableDepth : ℕ)
    (layout : OrderedControlLayout (availableDepth + 6) ambientWidth)
    (U : QubitUnitary) (epsilon : ℝ) : Circuit ambientWidth :=
  let depth := principalRootBoundDepth epsilon
  if hdepth : depth ≤ availableDepth then
    expandedTruncatedRecursiveCircuit (availableDepth - depth) depth
      (truncationLayout hdepth layout) U
  else
    recursivePrimitiveCircuit availableDepth layout U

theorem epsilonSynthesisPrimitiveCircuit_eq_truncated
    {ambientWidth availableDepth : ℕ}
    (layout : OrderedControlLayout (availableDepth + 6) ambientWidth)
    (U : QubitUnitary) (epsilon : ℝ)
    (hdepth : principalRootBoundDepth epsilon ≤ availableDepth) :
    epsilonSynthesisPrimitiveCircuit availableDepth layout U epsilon =
      expandedTruncatedRecursiveCircuit
        (availableDepth - principalRootBoundDepth epsilon)
        (principalRootBoundDepth epsilon)
        (truncationLayout hdepth layout) U := by
  simp [epsilonSynthesisPrimitiveCircuit, hdepth]

theorem epsilonSynthesisPrimitiveCircuit_eq_exact
    {ambientWidth availableDepth : ℕ}
    (layout : OrderedControlLayout (availableDepth + 6) ambientWidth)
    (U : QubitUnitary) (epsilon : ℝ)
    (hdepth : availableDepth < principalRootBoundDepth epsilon) :
    epsilonSynthesisPrimitiveCircuit availableDepth layout U epsilon =
      recursivePrimitiveCircuit availableDepth layout U := by
  simp [epsilonSynthesisPrimitiveCircuit, Nat.not_le_of_lt hdepth]

/-- The source-aligned selector meets every positive tolerance on an arbitrary register. -/
theorem operatorDistance_epsilonSynthesisPrimitiveCircuit_le
    {ambientWidth availableDepth : ℕ}
    (layout : OrderedControlLayout (availableDepth + 6) ambientWidth)
    (U : QubitUnitary) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    operatorDistance
        (positiveControlledUnitary layout.targetWire layout.controlSet U :
          Gate ambientWidth)
        (Circuit.eval
          (epsilonSynthesisPrimitiveCircuit availableDepth layout U epsilon) :
            Gate ambientWidth) ≤ epsilon := by
  by_cases hdepth : principalRootBoundDepth epsilon ≤ availableDepth
  · rw [epsilonSynthesisPrimitiveCircuit_eq_truncated layout U epsilon hdepth]
    have herror :=
      operatorDistance_expandedTruncatedRecursiveCircuit_le
        (truncationLayout hdepth layout) U
    rw [truncationLayout_controlSet hdepth layout,
      truncationLayout_targetWire hdepth layout] at herror
    exact herror.trans (principalRootBoundDepth_spec epsilon hepsilon)
  · rw [epsilonSynthesisPrimitiveCircuit, dif_neg hdepth,
      eval_recursivePrimitiveCircuit]
    simpa using hepsilon.le

/-! ### Selected-circuit event probabilities -/

/-- Strong constant-one bound for a finite computational-basis event. -/
theorem epsilonSynthesisPrimitiveCircuit_eventProbability_le
    {ambientWidth availableDepth : ℕ}
    (layout : OrderedControlLayout (availableDepth + 6) ambientWidth)
    (U : QubitUnitary) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (psi : EuclideanSpace ℂ (Basis ambientWidth)) (hpsi : ‖psi‖ ≤ 1)
    (event : Finset (Basis ambientWidth)) :
    abs
        (eventProbability event
            ((positiveControlledUnitary layout.targetWire layout.controlSet U :
              Gate ambientWidth) *ᵥ psi) -
          eventProbability event
            ((Circuit.eval
              (epsilonSynthesisPrimitiveCircuit availableDepth layout U epsilon) :
                Gate ambientWidth) *ᵥ psi)) ≤ epsilon := by
  exact (operatorDistance_eventProbability_le
    (positiveControlledUnitary layout.targetWire layout.controlSet U)
    (Circuit.eval
      (epsilonSynthesisPrimitiveCircuit availableDepth layout U epsilon))
    psi hpsi event).trans
      (layout.operatorDistance_epsilonSynthesisPrimitiveCircuit_le
        U epsilon hepsilon)

/-- Paper-facing constant-two bound for the same finite computational-basis event. -/
theorem epsilonSynthesisPrimitiveCircuit_eventProbability_le_two_mul
    {ambientWidth availableDepth : ℕ}
    (layout : OrderedControlLayout (availableDepth + 6) ambientWidth)
    (U : QubitUnitary) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (psi : EuclideanSpace ℂ (Basis ambientWidth)) (hpsi : ‖psi‖ ≤ 1)
    (event : Finset (Basis ambientWidth)) :
    abs
        (eventProbability event
            ((positiveControlledUnitary layout.targetWire layout.controlSet U :
              Gate ambientWidth) *ᵥ psi) -
          eventProbability event
            ((Circuit.eval
              (epsilonSynthesisPrimitiveCircuit availableDepth layout U epsilon) :
                Gate ambientWidth) *ᵥ psi)) ≤ 2 * epsilon := by
  calc
    abs
          (eventProbability event
              ((positiveControlledUnitary layout.targetWire layout.controlSet U :
                Gate ambientWidth) *ᵥ psi) -
            eventProbability event
              ((Circuit.eval
                (epsilonSynthesisPrimitiveCircuit availableDepth layout U epsilon) :
                  Gate ambientWidth) *ᵥ psi)) ≤
        2 * operatorDistance
          (positiveControlledUnitary layout.targetWire layout.controlSet U :
            Gate ambientWidth)
          (Circuit.eval
            (epsilonSynthesisPrimitiveCircuit availableDepth layout U epsilon) :
              Gate ambientWidth) :=
      operatorDistance_eventProbability_le_two_mul
        (positiveControlledUnitary layout.targetWire layout.controlSet U)
        (Circuit.eval
          (epsilonSynthesisPrimitiveCircuit availableDepth layout U epsilon))
        psi hpsi event
    _ ≤ 2 * epsilon := by
      gcongr
      exact layout.operatorDistance_epsilonSynthesisPrimitiveCircuit_le
        U epsilon hepsilon

end OrderedControlLayout

/-! ## Selected numerical resources -/

/-- Selected one-qubit count indexed by available exact recursion depth. -/
def epsilonSynthesisOneQubitCount (availableDepth : ℕ) (epsilon : ℝ) : ℕ :=
  let depth := principalRootBoundDepth epsilon
  if depth ≤ availableDepth then
    truncatedRecursiveOneQubitCount (availableDepth - depth) depth
  else
    recursivePrimitiveOneQubitCount availableDepth

/-- Selected CNOT count indexed by available exact recursion depth. -/
def epsilonSynthesisCNOTCount (availableDepth : ℕ) (epsilon : ℝ) : ℕ :=
  let depth := principalRootBoundDepth epsilon
  if depth ≤ availableDepth then
    truncatedRecursiveCNOTCount (availableDepth - depth) depth
  else
    recursivePrimitiveCNOTCount availableDepth

/-- Selected total count indexed by available exact recursion depth. -/
def epsilonSynthesisTotalCount (availableDepth : ℕ) (epsilon : ℝ) : ℕ :=
  let depth := principalRootBoundDepth epsilon
  if depth ≤ availableDepth then
    truncatedRecursiveTotalCount (availableDepth - depth) depth
  else
    recursivePrimitiveTotalCount availableDepth

@[simp]
theorem epsilonSynthesisTotalCount_eq_add (availableDepth : ℕ)
    (epsilon : ℝ) :
    epsilonSynthesisTotalCount availableDepth epsilon =
      epsilonSynthesisOneQubitCount availableDepth epsilon +
        epsilonSynthesisCNOTCount availableDepth epsilon := by
  by_cases hdepth : principalRootBoundDepth epsilon ≤ availableDepth <;>
    simp [epsilonSynthesisTotalCount, epsilonSynthesisOneQubitCount,
      epsilonSynthesisCNOTCount, hdepth]

namespace OrderedControlLayout

@[simp]
theorem epsilonSynthesisPrimitiveCircuit_oneQubitCount
    {ambientWidth availableDepth : ℕ}
    (layout : OrderedControlLayout (availableDepth + 6) ambientWidth)
    (U : QubitUnitary) (epsilon : ℝ) :
    Circuit.kindCount .oneQubit
        (epsilonSynthesisPrimitiveCircuit availableDepth layout U epsilon) =
      epsilonSynthesisOneQubitCount availableDepth epsilon := by
  by_cases hdepth : principalRootBoundDepth epsilon ≤ availableDepth
  · rw [epsilonSynthesisPrimitiveCircuit_eq_truncated layout U epsilon hdepth]
    rw [epsilonSynthesisOneQubitCount, if_pos hdepth]
    simpa only [truncatedRecursiveOneQubitCount] using
      expandedTruncatedRecursiveCircuit_oneQubitCount
        (truncationLayout hdepth layout) U
  · rw [epsilonSynthesisPrimitiveCircuit, dif_neg hdepth]
    rw [epsilonSynthesisOneQubitCount, if_neg hdepth]
    simpa only [recursivePrimitiveOneQubitCount] using
      recursivePrimitiveCircuit_oneQubitCount availableDepth layout U

@[simp]
theorem epsilonSynthesisPrimitiveCircuit_cnotCount
    {ambientWidth availableDepth : ℕ}
    (layout : OrderedControlLayout (availableDepth + 6) ambientWidth)
    (U : QubitUnitary) (epsilon : ℝ) :
    Circuit.kindCount .cnot
        (epsilonSynthesisPrimitiveCircuit availableDepth layout U epsilon) =
      epsilonSynthesisCNOTCount availableDepth epsilon := by
  by_cases hdepth : principalRootBoundDepth epsilon ≤ availableDepth
  · rw [epsilonSynthesisPrimitiveCircuit_eq_truncated layout U epsilon hdepth]
    rw [epsilonSynthesisCNOTCount, if_pos hdepth]
    simpa only [truncatedRecursiveCNOTCount] using
      expandedTruncatedRecursiveCircuit_cnotCount
        (truncationLayout hdepth layout) U
  · rw [epsilonSynthesisPrimitiveCircuit, dif_neg hdepth]
    rw [epsilonSynthesisCNOTCount, if_neg hdepth]
    simpa only [recursivePrimitiveCNOTCount] using
      recursivePrimitiveCircuit_cnotCount availableDepth layout U

@[simp]
theorem epsilonSynthesisPrimitiveCircuit_gateCount
    {ambientWidth availableDepth : ℕ}
    (layout : OrderedControlLayout (availableDepth + 6) ambientWidth)
    (U : QubitUnitary) (epsilon : ℝ) :
    Circuit.gateCount
        (epsilonSynthesisPrimitiveCircuit availableDepth layout U epsilon) =
      epsilonSynthesisTotalCount availableDepth epsilon := by
  by_cases hdepth : principalRootBoundDepth epsilon ≤ availableDepth
  · rw [epsilonSynthesisPrimitiveCircuit_eq_truncated layout U epsilon hdepth]
    rw [epsilonSynthesisTotalCount, if_pos hdepth]
    simpa only [truncatedRecursiveTotalCount] using
      expandedTruncatedRecursiveCircuit_gateCount
        (truncationLayout hdepth layout) U
  · rw [epsilonSynthesisPrimitiveCircuit, dif_neg hdepth]
    rw [epsilonSynthesisTotalCount, if_neg hdepth]
    simpa only [recursivePrimitiveTotalCount] using
      recursivePrimitiveCircuit_gateCount availableDepth layout U

@[simp]
theorem epsilonSynthesisPrimitiveCircuit_oneQubitCNOTCost
    {ambientWidth availableDepth : ℕ}
    (layout : OrderedControlLayout (availableDepth + 6) ambientWidth)
    (U : QubitUnitary) (epsilon : ℝ) :
    Circuit.cost CostModel.oneQubitCNOT
        (epsilonSynthesisPrimitiveCircuit availableDepth layout U epsilon) =
      some (epsilonSynthesisTotalCount availableDepth epsilon) := by
  by_cases hdepth : principalRootBoundDepth epsilon ≤ availableDepth
  · rw [epsilonSynthesisPrimitiveCircuit_eq_truncated layout U epsilon hdepth]
    rw [epsilonSynthesisTotalCount, if_pos hdepth]
    simpa only [truncatedRecursiveTotalCount] using
      expandedTruncatedRecursiveCircuit_oneQubitCNOTCost
        (truncationLayout hdepth layout) U
  · rw [epsilonSynthesisPrimitiveCircuit, dif_neg hdepth]
    rw [epsilonSynthesisTotalCount, if_neg hdepth]
    simpa only [recursivePrimitiveTotalCount] using
      recursivePrimitiveCircuit_oneQubitCNOTCost availableDepth layout U

end OrderedControlLayout

/-! ### Logical source-width views and uniform bounds -/

def epsilonSynthesisOneQubitCountAtWidth (sourceWidth : ℕ)
    (epsilon : ℝ) : ℕ :=
  epsilonSynthesisOneQubitCount (sourceWidth - 7) epsilon

def epsilonSynthesisCNOTCountAtWidth (sourceWidth : ℕ)
    (epsilon : ℝ) : ℕ :=
  epsilonSynthesisCNOTCount (sourceWidth - 7) epsilon

def epsilonSynthesisTotalCountAtWidth (sourceWidth : ℕ)
    (epsilon : ℝ) : ℕ :=
  epsilonSynthesisTotalCount (sourceWidth - 7) epsilon

private theorem recursivePrimitiveOneQubitCount_eq_base_add
    (depth : ℕ) :
    recursivePrimitiveOneQubitCount depth =
      252 + truncatedRecursiveOneQubitCount 0 depth := by
  simp [recursivePrimitiveOneQubitCount, truncatedRecursiveOneQubitCount]
  ring

private theorem recursivePrimitiveCNOTCount_eq_base_add (depth : ℕ) :
    recursivePrimitiveCNOTCount depth =
      188 + truncatedRecursiveCNOTCount 0 depth := by
  simp [recursivePrimitiveCNOTCount, truncatedRecursiveCNOTCount]
  ring

private theorem recursivePrimitiveTotalCount_eq_base_add (depth : ℕ) :
    recursivePrimitiveTotalCount depth =
      440 + truncatedRecursiveTotalCount 0 depth := by
  simp [recursivePrimitiveTotalCount, truncatedRecursiveTotalCount]
  ring

theorem epsilonSynthesisOneQubitCountAtWidth_le (sourceWidth : ℕ)
    (epsilon : ℝ) (hwidth : 7 ≤ sourceWidth) :
    epsilonSynthesisOneQubitCountAtWidth sourceWidth epsilon ≤
      252 + 64 * sourceWidth *
        min (principalRootBoundDepth epsilon) (sourceWidth - 7) := by
  by_cases hdepth : principalRootBoundDepth epsilon ≤ sourceWidth - 7
  · rw [epsilonSynthesisOneQubitCountAtWidth,
      epsilonSynthesisOneQubitCount, if_pos hdepth,
      Nat.min_eq_left hdepth]
    exact (truncatedRecursiveOneQubitCountAtWidth_le sourceWidth
      (principalRootBoundDepth epsilon) hwidth hdepth).trans
        (Nat.le_add_left _ _)
  · have hcapacity : sourceWidth - 7 ≤ principalRootBoundDepth epsilon :=
      Nat.le_of_lt (Nat.lt_of_not_ge hdepth)
    rw [epsilonSynthesisOneQubitCountAtWidth,
      epsilonSynthesisOneQubitCount, if_neg hdepth,
      Nat.min_eq_right hcapacity,
      recursivePrimitiveOneQubitCount_eq_base_add]
    have hbase := truncatedRecursiveOneQubitCount_le 0 (sourceWidth - 7)
    have hdecomp : 0 + (sourceWidth - 7) + 7 = sourceWidth := by omega
    rw [hdecomp] at hbase
    exact Nat.add_le_add_left hbase 252

theorem epsilonSynthesisCNOTCountAtWidth_le (sourceWidth : ℕ)
    (epsilon : ℝ) (hwidth : 7 ≤ sourceWidth) :
    epsilonSynthesisCNOTCountAtWidth sourceWidth epsilon ≤
      188 + 48 * sourceWidth *
        min (principalRootBoundDepth epsilon) (sourceWidth - 7) := by
  by_cases hdepth : principalRootBoundDepth epsilon ≤ sourceWidth - 7
  · rw [epsilonSynthesisCNOTCountAtWidth,
      epsilonSynthesisCNOTCount, if_pos hdepth,
      Nat.min_eq_left hdepth]
    exact (truncatedRecursiveCNOTCountAtWidth_le sourceWidth
      (principalRootBoundDepth epsilon) hwidth hdepth).trans
        (Nat.le_add_left _ _)
  · have hcapacity : sourceWidth - 7 ≤ principalRootBoundDepth epsilon :=
      Nat.le_of_lt (Nat.lt_of_not_ge hdepth)
    rw [epsilonSynthesisCNOTCountAtWidth,
      epsilonSynthesisCNOTCount, if_neg hdepth,
      Nat.min_eq_right hcapacity,
      recursivePrimitiveCNOTCount_eq_base_add]
    have hbase := truncatedRecursiveCNOTCount_le 0 (sourceWidth - 7)
    have hdecomp : 0 + (sourceWidth - 7) + 7 = sourceWidth := by omega
    rw [hdecomp] at hbase
    exact Nat.add_le_add_left hbase 188

/-- Uniform selected-construction count, including the exact fallback base. -/
theorem epsilonSynthesisTotalCountAtWidth_le (sourceWidth : ℕ)
    (epsilon : ℝ) (hwidth : 7 ≤ sourceWidth) :
    epsilonSynthesisTotalCountAtWidth sourceWidth epsilon ≤
      440 + 112 * sourceWidth *
        min (principalRootBoundDepth epsilon) (sourceWidth - 7) := by
  by_cases hdepth : principalRootBoundDepth epsilon ≤ sourceWidth - 7
  · rw [epsilonSynthesisTotalCountAtWidth,
      epsilonSynthesisTotalCount, if_pos hdepth,
      Nat.min_eq_left hdepth]
    exact (truncatedRecursiveTotalCountAtWidth_le sourceWidth
      (principalRootBoundDepth epsilon) hwidth hdepth).trans
        (Nat.le_add_left _ _)
  · have hcapacity : sourceWidth - 7 ≤ principalRootBoundDepth epsilon :=
      Nat.le_of_lt (Nat.lt_of_not_ge hdepth)
    rw [epsilonSynthesisTotalCountAtWidth,
      epsilonSynthesisTotalCount, if_neg hdepth,
      Nat.min_eq_right hcapacity,
      recursivePrimitiveTotalCount_eq_base_add]
    have hbase := truncatedRecursiveTotalCount_le 0 (sourceWidth - 7)
    have hdecomp : 0 + (sourceWidth - 7) + 7 = sourceWidth := by omega
    rw [hdecomp] at hbase
    exact Nat.add_le_add_left hbase 440

/--
Explicit logarithmic-regime upper bound for the selected construction.

The exact fallback is included.  The domain `0 < epsilon ≤ 1` makes
`logb 2 (1 / epsilon)` the conventional nonnegative accuracy parameter.
-/
theorem epsilonSynthesisTotalCountAtWidth_lt_logarithmic
    (sourceWidth : ℕ) (epsilon : ℝ) (hwidth : 7 ≤ sourceWidth)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1) :
    (epsilonSynthesisTotalCountAtWidth sourceWidth epsilon : ℝ) <
      440 + 112 * (sourceWidth : ℝ) *
        (Real.logb 2 (1 / epsilon) + (Real.logb 2 Real.pi + 1)) := by
  have hsmall : epsilon ≤ Real.pi :=
    hepsilonOne.trans (one_le_two.trans Real.two_le_pi)
  have hcount := epsilonSynthesisTotalCountAtWidth_le
    sourceWidth epsilon hwidth
  have hmin :
      min (principalRootBoundDepth epsilon) (sourceWidth - 7) ≤
        principalRootBoundDepth epsilon := min_le_left _ _
  have hcountNat :
      epsilonSynthesisTotalCountAtWidth sourceWidth epsilon ≤
        440 + 112 * sourceWidth * principalRootBoundDepth epsilon :=
    hcount.trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left (112 * sourceWidth) hmin) 440)
  have hcountReal :
      (epsilonSynthesisTotalCountAtWidth sourceWidth epsilon : ℝ) ≤
        440 + 112 * (sourceWidth : ℝ) *
          (principalRootBoundDepth epsilon : ℝ) := by
    exact_mod_cast hcountNat
  have hdepth := principalRootBoundDepth_lt_log_add_one
    epsilon hepsilon hsmall
  rw [logb_pi_div_epsilon epsilon hepsilon] at hdepth
  have hdepth' :
      (principalRootBoundDepth epsilon : ℝ) <
        Real.logb 2 (1 / epsilon) + (Real.logb 2 Real.pi + 1) := by
    linarith
  calc
    (epsilonSynthesisTotalCountAtWidth sourceWidth epsilon : ℝ) ≤
        440 + 112 * (sourceWidth : ℝ) *
          (principalRootBoundDepth epsilon : ℝ) := hcountReal
    _ < 440 + 112 * (sourceWidth : ℝ) *
        (Real.logb 2 (1 / epsilon) +
          (Real.logb 2 Real.pi + 1)) := by
      gcongr

end

end Barenco.MultiControl
