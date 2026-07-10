import Barenco.MultiControl.Lemma71
import Barenco.ControlledCircuit.CanonicalSelected

/-!
# Transparent fusion syntax for the Gray-code construction

This module reconstructs the complete Lemma 7.1 Gray schedule in
payload-preserving `FusionCircuit` syntax.  Each signed controlled root uses the
same transparent canonical six-node controlled-unitary circuit, and each Gray
edge remains a literal CNOT.  No opaque selected circuit is inspected or used as
optimizer input.

The construction is chronological and valid in every ambient register carrying
the supplied ordered controls and distinct target.  Its evaluator is proved
exactly equal to the checked macro circuit from `Lemma71`; resource formulas are
then derived from the literal fusion syntax itself.
-/

namespace Barenco.MultiControl

open Barenco.ControlledCircuit
open Barenco.Optimization

noncomputable section

namespace OrderedControlLayout

private theorem grayFusionPivot_index_lt_of_mask {controlCount index : ℕ}
    (hindex : index < (grayCode controlCount).length) :
    index < (grayPivots controlCount).length := by
  rw [length_grayPivots_eq_grayCode]
  exact hindex

private theorem grayFusionMask_index_lt_of_edge {controlCount index : ℕ}
    (hindex : index < (grayCNOTEdges controlCount).length) :
    index < (grayCode controlCount).length := by
  rw [length_grayCNOTEdges] at hindex
  rw [length_grayCode]
  omega

private theorem grayFusionFinalMask_index_lt (tail : ℕ) :
    (grayCNOTEdges (tail + 1)).length <
      (grayCode (tail + 1)).length := by
  rw [length_grayCNOTEdges, length_grayCode]
  have hpow : 0 < 2 ^ (tail + 1) := pow_pos (by omega) _
  omega

/-! ## Schedule-aware payload syntax -/

/--
The transparent six-node implementation of one indexed controlled signed root.
The pivot and signed payload are read directly from the public Gray schedule.
-/
def grayFusionRootCircuitAt {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCode controlCount).length) :
    FusionCircuit ambientWidth :=
  let pivot :=
    (grayPivots controlCount)[index]'
      (grayFusionPivot_index_lt_of_mask hindex)
  canonicalSelectedControlledU2FusionCircuit
    (layout.controlWire pivot) layout.targetWire
    (layout.control_ne_target pivot)
    (signedGrayRoot ((grayCode controlCount)[index]'hindex) V)

/-- One transparent controlled root followed by its generated Gray CNOT. -/
def grayFusionTransitionPair {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCNOTEdges controlCount).length) :
    FusionCircuit ambientWidth :=
  let edge := (grayCNOTEdges controlCount)[index]'hindex
  FusionCircuit.append
    (grayFusionRootCircuitAt layout V index
      (grayFusionMask_index_lt_of_edge hindex))
    [.cnot (layout.controlWire edge.1) (layout.controlWire edge.2)
      (layout.controlWire_ne (grayCNOTEdges_getElem_ne hindex))]

/-- The first `count` transparent controlled-root/CNOT transition pairs. -/
def grayFusionTransitionPrefixCircuit {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) :
    (count : ℕ) → count ≤ (grayCNOTEdges controlCount).length →
      FusionCircuit ambientWidth
  | 0, _ => []
  | count + 1, hcount =>
      FusionCircuit.append
        (grayFusionTransitionPrefixCircuit layout V count (by omega))
        (grayFusionTransitionPair layout V count (by omega))

/--
The complete transparent Gray circuit for `tail + 1` positive controls: every
nonfinal controlled root is followed by its Gray CNOT and the final root stands
alone.
-/
def grayFusionControlledViaRootCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) : FusionCircuit ambientWidth :=
  FusionCircuit.append
    (grayFusionTransitionPrefixCircuit layout V
      (grayCNOTEdges (tail + 1)).length le_rfl)
    (grayFusionRootCircuitAt layout V
      (grayCNOTEdges (tail + 1)).length
      (grayFusionFinalMask_index_lt tail))

/-- Selected-root wrapper implementing an arbitrary controlled `U` exactly. -/
def grayFusionControlledCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (U : QubitUnitary) : FusionCircuit ambientWidth :=
  grayFusionControlledViaRootCircuit layout (graySelectedRoot tail U)

/-! ## Exact evaluator preservation -/

/-- One transparent root expansion has exactly its checked macro denotation. -/
@[simp]
theorem eval_grayFusionRootCircuitAt {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCode controlCount).length) :
    FusionCircuit.eval (grayFusionRootCircuitAt layout V index hindex) =
      (grayRootPrimitiveAt layout V index hindex).denotation := by
  simp [grayFusionRootCircuitAt, grayRootPrimitiveAt,
    controlledTargetPrimitive, controlComplement]

/-- Every transparent root/CNOT pair preserves its checked macro evaluator. -/
@[simp]
theorem eval_grayFusionTransitionPair {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCNOTEdges controlCount).length) :
    FusionCircuit.eval (grayFusionTransitionPair layout V index hindex) =
      Circuit.eval (grayTransitionPair layout V index hindex) := by
  simp [grayFusionTransitionPair, grayTransitionPair,
    FusionCircuit.eval_append, FusionPrimitive.denotation, cnotPrimitive]

/-- Exact evaluator preservation for every generated prefix. -/
theorem eval_grayFusionTransitionPrefixCircuit
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) :
    ∀ count (hcount : count ≤ (grayCNOTEdges controlCount).length),
      FusionCircuit.eval
          (grayFusionTransitionPrefixCircuit layout V count hcount) =
        Circuit.eval (grayTransitionPrefixCircuit layout V count hcount) := by
  intro count hcount
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [grayFusionTransitionPrefixCircuit, grayTransitionPrefixCircuit,
        FusionCircuit.eval_append, Circuit.eval_append,
        eval_grayFusionTransitionPair, ih]

/--
The complete transparent syntax has exactly the evaluator of the checked
Lemma 7.1 macro schedule, on the full ambient register.
-/
theorem eval_grayFusionControlledViaRootCircuit_eq_macro
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    FusionCircuit.eval (grayFusionControlledViaRootCircuit layout V) =
      Circuit.eval (grayControlledViaRootCircuit layout V) := by
  rw [grayFusionControlledViaRootCircuit, grayControlledViaRootCircuit,
    FusionCircuit.eval_append, Circuit.eval_append,
    eval_grayFusionTransitionPrefixCircuit,
    eval_grayFusionRootCircuitAt]
  simp

/-- The lowered trusted circuit retains the same exact macro evaluator. -/
theorem eval_lower_grayFusionControlledViaRootCircuit_eq_macro
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    Circuit.eval (grayFusionControlledViaRootCircuit layout V).lower =
      Circuit.eval (grayControlledViaRootCircuit layout V) := by
  rw [FusionCircuit.eval_lower]
  exact eval_grayFusionControlledViaRootCircuit_eq_macro layout V

/-- Exact arbitrary-register semantics of the selected-root transparent circuit. -/
@[simp]
theorem eval_grayFusionControlledCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (U : QubitUnitary) :
    FusionCircuit.eval (grayFusionControlledCircuit layout U) =
      positiveControlledUnitary layout.targetWire layout.controlSet U := by
  rw [grayFusionControlledCircuit,
    eval_grayFusionControlledViaRootCircuit_eq_macro]
  simpa [grayControlledCircuit] using eval_grayControlledCircuit layout U

/-! ## Local and prefix resources -/

@[simp]
theorem grayFusionRootCircuitAt_gateCount {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCode controlCount).length) :
    FusionCircuit.gateCount (grayFusionRootCircuitAt layout V index hindex) = 6 := by
  simp [grayFusionRootCircuitAt]

@[simp]
theorem grayFusionRootCircuitAt_oneQubitCount
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCode controlCount).length) :
    FusionCircuit.oneQubitCount
        (grayFusionRootCircuitAt layout V index hindex) = 4 := by
  simp [grayFusionRootCircuitAt]

@[simp]
theorem grayFusionRootCircuitAt_cnotCount {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCode controlCount).length) :
    FusionCircuit.cnotCount
        (grayFusionRootCircuitAt layout V index hindex) = 2 := by
  simp [grayFusionRootCircuitAt]

@[simp]
theorem grayFusionRootCircuitAt_twoQubitCount
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCode controlCount).length) :
    FusionCircuit.twoQubitCount
        (grayFusionRootCircuitAt layout V index hindex) = 0 := by
  simp [grayFusionRootCircuitAt]

@[simp]
theorem grayFusionRootCircuitAt_oneQubitCNOTCost
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCode controlCount).length) :
    FusionCircuit.cost CostModel.oneQubitCNOT
        (grayFusionRootCircuitAt layout V index hindex) = some 6 := by
  simp [grayFusionRootCircuitAt]

@[simp]
theorem grayFusionTransitionPair_gateCount {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCNOTEdges controlCount).length) :
    FusionCircuit.gateCount
        (grayFusionTransitionPair layout V index hindex) = 7 := by
  rw [grayFusionTransitionPair, FusionCircuit.gateCount_append,
    grayFusionRootCircuitAt_gateCount]
  rfl

@[simp]
theorem grayFusionTransitionPair_oneQubitCount
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCNOTEdges controlCount).length) :
    FusionCircuit.oneQubitCount
        (grayFusionTransitionPair layout V index hindex) = 4 := by
  rw [grayFusionTransitionPair, FusionCircuit.oneQubitCount_append,
    grayFusionRootCircuitAt_oneQubitCount]
  rfl

@[simp]
theorem grayFusionTransitionPair_cnotCount {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCNOTEdges controlCount).length) :
    FusionCircuit.cnotCount
        (grayFusionTransitionPair layout V index hindex) = 3 := by
  rw [grayFusionTransitionPair, FusionCircuit.cnotCount_append,
    grayFusionRootCircuitAt_cnotCount]
  rfl

@[simp]
theorem grayFusionTransitionPair_twoQubitCount
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCNOTEdges controlCount).length) :
    FusionCircuit.twoQubitCount
        (grayFusionTransitionPair layout V index hindex) = 0 := by
  rw [grayFusionTransitionPair, FusionCircuit.twoQubitCount_append,
    grayFusionRootCircuitAt_twoQubitCount]
  rfl

@[simp]
theorem grayFusionTransitionPair_oneQubitCNOTCost
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) (index : ℕ)
    (hindex : index < (grayCNOTEdges controlCount).length) :
    FusionCircuit.cost CostModel.oneQubitCNOT
        (grayFusionTransitionPair layout V index hindex) = some 7 := by
  rw [grayFusionTransitionPair, FusionCircuit.cost_append,
    grayFusionRootCircuitAt_oneQubitCNOTCost]
  rfl

@[simp]
theorem grayFusionTransitionPrefixCircuit_gateCount
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) :
    ∀ count (hcount : count ≤ (grayCNOTEdges controlCount).length),
      FusionCircuit.gateCount
          (grayFusionTransitionPrefixCircuit layout V count hcount) =
        7 * count := by
  intro count hcount
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [grayFusionTransitionPrefixCircuit, FusionCircuit.gateCount_append,
        grayFusionTransitionPair_gateCount, ih]
      omega

theorem grayFusionTransitionPrefixCircuit_kindCounts
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) :
    ∀ count (hcount : count ≤ (grayCNOTEdges controlCount).length),
      FusionCircuit.oneQubitCount
          (grayFusionTransitionPrefixCircuit layout V count hcount) =
            4 * count ∧
        FusionCircuit.cnotCount
          (grayFusionTransitionPrefixCircuit layout V count hcount) =
            3 * count := by
  intro count hcount
  induction count with
  | zero => exact ⟨rfl, rfl⟩
  | succ count ih =>
      rw [grayFusionTransitionPrefixCircuit,
        FusionCircuit.oneQubitCount_append,
        FusionCircuit.cnotCount_append]
      rcases ih (by omega) with ⟨hone, hcnot⟩
      rw [hone, hcnot, grayFusionTransitionPair_oneQubitCount,
        grayFusionTransitionPair_cnotCount]
      omega

@[simp]
theorem grayFusionTransitionPrefixCircuit_twoQubitCount
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth)
    (V : QubitUnitary) :
    ∀ count (hcount : count ≤ (grayCNOTEdges controlCount).length),
      FusionCircuit.twoQubitCount
          (grayFusionTransitionPrefixCircuit layout V count hcount) = 0 := by
  intro count hcount
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [grayFusionTransitionPrefixCircuit,
        FusionCircuit.twoQubitCount_append,
        grayFusionTransitionPair_twoQubitCount, ih]

/-! ## Complete-circuit resources -/

@[simp]
theorem grayFusionControlledViaRootCircuit_oneQubitCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    FusionCircuit.oneQubitCount
        (grayFusionControlledViaRootCircuit layout V) =
      4 * (2 ^ (tail + 1) - 1) := by
  rw [grayFusionControlledViaRootCircuit,
    FusionCircuit.oneQubitCount_append]
  rcases grayFusionTransitionPrefixCircuit_kindCounts layout V
      (grayCNOTEdges (tail + 1)).length le_rfl with ⟨hone, _⟩
  rw [hone, grayFusionRootCircuitAt_oneQubitCount, length_grayCNOTEdges]
  have hpow : 0 < 2 ^ tail := pow_pos (by omega) tail
  simp only [pow_succ]
  omega

@[simp]
theorem grayFusionControlledViaRootCircuit_cnotCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    FusionCircuit.cnotCount
        (grayFusionControlledViaRootCircuit layout V) =
      3 * 2 ^ (tail + 1) - 4 := by
  rw [grayFusionControlledViaRootCircuit,
    FusionCircuit.cnotCount_append]
  rcases grayFusionTransitionPrefixCircuit_kindCounts layout V
      (grayCNOTEdges (tail + 1)).length le_rfl with ⟨_, hcnot⟩
  rw [hcnot, grayFusionRootCircuitAt_cnotCount, length_grayCNOTEdges]
  have hpow : 0 < 2 ^ tail := pow_pos (by omega) tail
  simp only [pow_succ]
  omega

@[simp]
theorem grayFusionControlledViaRootCircuit_twoQubitCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    FusionCircuit.twoQubitCount
        (grayFusionControlledViaRootCircuit layout V) = 0 := by
  rw [grayFusionControlledViaRootCircuit,
    FusionCircuit.twoQubitCount_append,
    grayFusionTransitionPrefixCircuit_twoQubitCount,
    grayFusionRootCircuitAt_twoQubitCount]

@[simp]
theorem grayFusionControlledViaRootCircuit_gateCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    FusionCircuit.gateCount
        (grayFusionControlledViaRootCircuit layout V) =
      7 * 2 ^ (tail + 1) - 8 := by
  rw [grayFusionControlledViaRootCircuit, FusionCircuit.gateCount_append,
    grayFusionTransitionPrefixCircuit_gateCount,
    grayFusionRootCircuitAt_gateCount, length_grayCNOTEdges]
  have hpow : 0 < 2 ^ tail := pow_pos (by omega) tail
  simp only [pow_succ]
  omega

@[simp]
theorem grayFusionControlledViaRootCircuit_oneQubitCNOTCost
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (V : QubitUnitary) :
    FusionCircuit.cost CostModel.oneQubitCNOT
        (grayFusionControlledViaRootCircuit layout V) =
      some (7 * 2 ^ (tail + 1) - 8) := by
  rw [FusionCircuit.oneQubitCNOT_cost_eq,
    grayFusionControlledViaRootCircuit_twoQubitCount,
    if_pos rfl, grayFusionControlledViaRootCircuit_gateCount]

@[simp]
theorem grayFusionControlledCircuit_oneQubitCount {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (U : QubitUnitary) :
    FusionCircuit.oneQubitCount (grayFusionControlledCircuit layout U) =
      4 * (2 ^ (tail + 1) - 1) := by
  simp [grayFusionControlledCircuit]

@[simp]
theorem grayFusionControlledCircuit_cnotCount {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (U : QubitUnitary) :
    FusionCircuit.cnotCount (grayFusionControlledCircuit layout U) =
      3 * 2 ^ (tail + 1) - 4 := by
  simp [grayFusionControlledCircuit]

@[simp]
theorem grayFusionControlledCircuit_twoQubitCount {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (U : QubitUnitary) :
    FusionCircuit.twoQubitCount (grayFusionControlledCircuit layout U) = 0 := by
  simp [grayFusionControlledCircuit]

@[simp]
theorem grayFusionControlledCircuit_gateCount {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (U : QubitUnitary) :
    FusionCircuit.gateCount (grayFusionControlledCircuit layout U) =
      7 * 2 ^ (tail + 1) - 8 := by
  simp [grayFusionControlledCircuit]

@[simp]
theorem grayFusionControlledCircuit_oneQubitCNOTCost
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth)
    (U : QubitUnitary) :
    FusionCircuit.cost CostModel.oneQubitCNOT
        (grayFusionControlledCircuit layout U) =
      some (7 * 2 ^ (tail + 1) - 8) := by
  simp [grayFusionControlledCircuit]

/-! ## Low-control raw-profile sanity checks -/

/-- One control expands to one transparent six-node controlled-unitary block. -/
theorem grayFusionControlledCircuit_oneControl_profile {ambientWidth : ℕ}
    (layout : OrderedControlLayout 1 ambientWidth) (U : QubitUnitary) :
    FusionCircuit.oneQubitCount
          (grayFusionControlledCircuit (tail := 0) layout U) = 4 ∧
      FusionCircuit.cnotCount
          (grayFusionControlledCircuit (tail := 0) layout U) = 2 ∧
      FusionCircuit.gateCount
          (grayFusionControlledCircuit (tail := 0) layout U) = 6 := by
  norm_num

/-- Two controls have the literal unmerged raw profile `(12, 8, 20)`. -/
theorem grayFusionControlledCircuit_twoControl_profile {ambientWidth : ℕ}
    (layout : OrderedControlLayout 2 ambientWidth) (U : QubitUnitary) :
    FusionCircuit.oneQubitCount
          (grayFusionControlledCircuit (tail := 1) layout U) = 12 ∧
      FusionCircuit.cnotCount
          (grayFusionControlledCircuit (tail := 1) layout U) = 8 ∧
      FusionCircuit.gateCount
          (grayFusionControlledCircuit (tail := 1) layout U) = 20 := by
  norm_num

/-- Three controls have the literal unmerged raw profile `(28, 20, 48)`. -/
theorem grayFusionControlledCircuit_threeControl_profile {ambientWidth : ℕ}
    (layout : OrderedControlLayout 3 ambientWidth) (U : QubitUnitary) :
    FusionCircuit.oneQubitCount
          (grayFusionControlledCircuit (tail := 2) layout U) = 28 ∧
      FusionCircuit.cnotCount
          (grayFusionControlledCircuit (tail := 2) layout U) = 20 ∧
      FusionCircuit.gateCount
          (grayFusionControlledCircuit (tail := 2) layout U) = 48 := by
  norm_num

end OrderedControlLayout

end

end Barenco.MultiControl
