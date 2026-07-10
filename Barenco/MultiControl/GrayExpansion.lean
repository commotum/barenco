import Barenco.MultiControl.Lemma71
import Barenco.ControlledCircuit.Selected

/-!
# Primitive expansion of the Gray-code controlled-unitary construction

This leaf replaces each singly controlled signed-root macro in Lemma 7.1 by the
selected six-node Corollary 5.3 circuit.  The replacement is reconstructed from
the Gray schedule itself: opaque primitive metadata is never inspected or
rewritten.

The circuit remains chronological.  Every nonfinal selected root expansion is
followed by the same generated Gray CNOT as in `grayControlledViaRootCircuit`,
and the final selected root expansion stands alone.  Evaluator preservation and
all resource counts are proved from this named syntax.
-/

namespace Barenco.MultiControl

open Barenco.ControlledCircuit

noncomputable section

namespace OrderedControlLayout

private theorem expandedGrayPivot_index_lt_of_mask {controlCount index : ℕ}
    (hindex : index < (grayCode controlCount).length) :
    index < (grayPivots controlCount).length := by
  rw [length_grayPivots_eq_grayCode]
  exact hindex

private theorem expandedGrayMask_index_lt_of_edge {controlCount index : ℕ}
    (hindex : index < (grayCNOTEdges controlCount).length) :
    index < (grayCode controlCount).length := by
  rw [length_grayCNOTEdges] at hindex
  rw [length_grayCode]
  omega

private theorem expandedGrayFinalMask_index_lt (tail : ℕ) :
    (grayCNOTEdges (tail + 1)).length < (grayCode (tail + 1)).length := by
  rw [length_grayCNOTEdges, length_grayCode]
  have hpow : 0 < 2 ^ (tail + 1) := pow_pos (by omega) _
  omega

/-! ## Schedule-aware primitive syntax -/

/--
The selected six-node implementation of one indexed controlled signed root.

The logical pivot and signed root are recovered from the certified Gray lists,
not from the opaque `Primitive` stored in the macro circuit.
-/
def expandedGrayRootCircuitAt {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary)
    (index : ℕ) (hindex : index < (grayCode controlCount).length) :
    Circuit ambientWidth :=
  let pivot :=
    (grayPivots controlCount)[index]'(expandedGrayPivot_index_lt_of_mask hindex)
  selectedControlledU2Circuit
    (layout.controlWire pivot) layout.targetWire
    (layout.control_ne_target pivot)
    (signedGrayRoot ((grayCode controlCount)[index]'hindex) V)

/-- One expanded root followed chronologically by its generated Gray CNOT. -/
def expandedGrayTransitionPair {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    Circuit ambientWidth :=
  let edge := (grayCNOTEdges controlCount)[index]'hindex
  Circuit.append
    (expandedGrayRootCircuitAt layout V index
      (expandedGrayMask_index_lt_of_edge hindex))
    [layout.cnotPrimitive edge.1 edge.2 (grayCNOTEdges_getElem_ne hindex)]

/-- The first `count` expanded root/CNOT transition pairs. -/
def expandedGrayTransitionPrefixCircuit {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary) :
    (count : ℕ) → count ≤ (grayCNOTEdges controlCount).length → Circuit ambientWidth
  | 0, _ => []
  | count + 1, hcount =>
      Circuit.append
        (expandedGrayTransitionPrefixCircuit layout V count (by omega))
        (expandedGrayTransitionPair layout V count (by omega))

/--
The complete primitive Gray circuit for `tail + 1` positive controls.

All controlled-root macros are expanded, while the already primitive Gray CNOTs
are retained verbatim.
-/
def expandedGrayControlledViaRootCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) (V : QubitUnitary) :
    Circuit ambientWidth :=
  Circuit.append
    (expandedGrayTransitionPrefixCircuit layout V
      (grayCNOTEdges (tail + 1)).length le_rfl)
    (expandedGrayRootCircuitAt layout V (grayCNOTEdges (tail + 1)).length
      (expandedGrayFinalMask_index_lt tail))

/-- Selected-root wrapper for the fully primitive exact controlled-`U` circuit. -/
def expandedGrayControlledCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) (U : QubitUnitary) :
    Circuit ambientWidth :=
  expandedGrayControlledViaRootCircuit layout (graySelectedRoot tail U)

/-! ## Evaluator preservation -/

/-- Each selected six-node root expansion has exactly the macro evaluator. -/
@[simp]
theorem eval_expandedGrayRootCircuitAt {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary)
    (index : ℕ) (hindex : index < (grayCode controlCount).length) :
    Circuit.eval (expandedGrayRootCircuitAt layout V index hindex) =
      (grayRootPrimitiveAt layout V index hindex).denotation := by
  simp [expandedGrayRootCircuitAt, grayRootPrimitiveAt,
    controlledTargetPrimitive, controlComplement]

/-- Every expanded root/CNOT pair preserves the corresponding macro pair. -/
@[simp]
theorem eval_expandedGrayTransitionPair {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    Circuit.eval (expandedGrayTransitionPair layout V index hindex) =
      Circuit.eval (grayTransitionPair layout V index hindex) := by
  simp [expandedGrayTransitionPair, grayTransitionPair, Circuit.eval_append]

/-- Evaluator preservation for every generated prefix of the Gray schedule. -/
theorem eval_expandedGrayTransitionPrefixCircuit
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary) :
    ∀ count (hcount : count ≤ (grayCNOTEdges controlCount).length),
      Circuit.eval (expandedGrayTransitionPrefixCircuit layout V count hcount) =
        Circuit.eval (grayTransitionPrefixCircuit layout V count hcount) := by
  intro count hcount
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [expandedGrayTransitionPrefixCircuit, grayTransitionPrefixCircuit,
        Circuit.eval_append, Circuit.eval_append,
        eval_expandedGrayTransitionPair, ih]

/-- The fully expanded circuit has exactly the evaluator of Lemma 7.1's macro syntax. -/
theorem eval_expandedGrayControlledViaRootCircuit
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) (V : QubitUnitary) :
    Circuit.eval (expandedGrayControlledViaRootCircuit layout V) =
      Circuit.eval (grayControlledViaRootCircuit layout V) := by
  rw [expandedGrayControlledViaRootCircuit, grayControlledViaRootCircuit,
    Circuit.eval_append, Circuit.eval_append,
    eval_expandedGrayTransitionPrefixCircuit,
    eval_expandedGrayRootCircuitAt]
  simp

/-- Exact full-register semantics of the fully primitive selected-root circuit. -/
@[simp]
theorem eval_expandedGrayControlledCircuit {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) (U : QubitUnitary) :
    Circuit.eval (expandedGrayControlledCircuit layout U) =
      positiveControlledUnitary layout.targetWire layout.controlSet U := by
  rw [expandedGrayControlledCircuit,
    eval_expandedGrayControlledViaRootCircuit]
  exact eval_grayControlledCircuit layout U

/-! ## Local and prefix resources -/

@[simp]
theorem expandedGrayRootCircuitAt_gateCount {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary)
    (index : ℕ) (hindex : index < (grayCode controlCount).length) :
    Circuit.gateCount (expandedGrayRootCircuitAt layout V index hindex) = 6 := by
  simp [expandedGrayRootCircuitAt]

@[simp]
theorem expandedGrayRootCircuitAt_oneQubitCount
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary)
    (index : ℕ) (hindex : index < (grayCode controlCount).length) :
    Circuit.kindCount .oneQubit
        (expandedGrayRootCircuitAt layout V index hindex) = 4 := by
  simp [expandedGrayRootCircuitAt]

@[simp]
theorem expandedGrayRootCircuitAt_cnotCount {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary)
    (index : ℕ) (hindex : index < (grayCode controlCount).length) :
    Circuit.kindCount .cnot
        (expandedGrayRootCircuitAt layout V index hindex) = 2 := by
  simp [expandedGrayRootCircuitAt]

@[simp]
theorem expandedGrayRootCircuitAt_oneQubitCNOTCost
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary)
    (index : ℕ) (hindex : index < (grayCode controlCount).length) :
    Circuit.cost CostModel.oneQubitCNOT
        (expandedGrayRootCircuitAt layout V index hindex) = some 6 := by
  simp [expandedGrayRootCircuitAt]

@[simp]
theorem expandedGrayTransitionPair_gateCount {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    Circuit.gateCount (expandedGrayTransitionPair layout V index hindex) = 7 := by
  simp [expandedGrayTransitionPair, Circuit.gateCount, Circuit.append]

@[simp]
theorem expandedGrayTransitionPair_oneQubitCount
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    Circuit.kindCount .oneQubit
        (expandedGrayTransitionPair layout V index hindex) = 4 := by
  simp [expandedGrayTransitionPair, Circuit.kindCount, Circuit.append]

@[simp]
theorem expandedGrayTransitionPair_cnotCount {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    Circuit.kindCount .cnot
        (expandedGrayTransitionPair layout V index hindex) = 3 := by
  simp [expandedGrayTransitionPair, Circuit.kindCount, Circuit.append]

@[simp]
theorem expandedGrayTransitionPair_oneQubitCNOTCost
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary)
    (index : ℕ) (hindex : index < (grayCNOTEdges controlCount).length) :
    Circuit.cost CostModel.oneQubitCNOT
        (expandedGrayTransitionPair layout V index hindex) = some 7 := by
  simp [expandedGrayTransitionPair, Circuit.cost_append, Circuit.cost,
    Circuit.addCost]

@[simp]
theorem expandedGrayTransitionPrefixCircuit_gateCount
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary) :
    ∀ count (hcount : count ≤ (grayCNOTEdges controlCount).length),
      Circuit.gateCount
          (expandedGrayTransitionPrefixCircuit layout V count hcount) = 7 * count := by
  intro count hcount
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [expandedGrayTransitionPrefixCircuit, Circuit.gateCount_append,
        expandedGrayTransitionPair_gateCount, ih]
      omega

theorem expandedGrayTransitionPrefixCircuit_kindCounts
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary) :
    ∀ count (hcount : count ≤ (grayCNOTEdges controlCount).length),
      Circuit.kindCount .oneQubit
          (expandedGrayTransitionPrefixCircuit layout V count hcount) = 4 * count ∧
        Circuit.kindCount .cnot
          (expandedGrayTransitionPrefixCircuit layout V count hcount) = 3 * count := by
  intro count hcount
  induction count with
  | zero => simp [expandedGrayTransitionPrefixCircuit, Circuit.kindCount]
  | succ count ih =>
      rw [expandedGrayTransitionPrefixCircuit, Circuit.kindCount_append,
        Circuit.kindCount_append]
      rcases ih (by omega) with ⟨hone, hcnot⟩
      rw [hone, hcnot, expandedGrayTransitionPair_oneQubitCount,
        expandedGrayTransitionPair_cnotCount]
      omega

@[simp]
theorem expandedGrayTransitionPrefixCircuit_oneQubitCNOTCost
    {controlCount ambientWidth : ℕ}
    (layout : OrderedControlLayout controlCount ambientWidth) (V : QubitUnitary) :
    ∀ count (hcount : count ≤ (grayCNOTEdges controlCount).length),
      Circuit.cost CostModel.oneQubitCNOT
          (expandedGrayTransitionPrefixCircuit layout V count hcount) =
        some (7 * count) := by
  intro count hcount
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [expandedGrayTransitionPrefixCircuit, Circuit.cost_append, ih,
        expandedGrayTransitionPair_oneQubitCNOTCost]
      simp [Circuit.addCost]
      omega

/-! ## Complete-circuit resources -/

@[simp]
theorem expandedGrayControlledViaRootCircuit_oneQubitCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) (V : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (expandedGrayControlledViaRootCircuit layout V) =
      4 * (2 ^ (tail + 1) - 1) := by
  rw [expandedGrayControlledViaRootCircuit, Circuit.kindCount_append]
  rcases expandedGrayTransitionPrefixCircuit_kindCounts layout V
      (grayCNOTEdges (tail + 1)).length le_rfl with ⟨hone, _⟩
  rw [hone, expandedGrayRootCircuitAt_oneQubitCount, length_grayCNOTEdges]
  have hpow : 0 < 2 ^ tail := pow_pos (by omega) tail
  simp only [pow_succ]
  omega

@[simp]
theorem expandedGrayControlledViaRootCircuit_cnotCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) (V : QubitUnitary) :
    Circuit.kindCount .cnot
        (expandedGrayControlledViaRootCircuit layout V) =
      3 * 2 ^ (tail + 1) - 4 := by
  rw [expandedGrayControlledViaRootCircuit, Circuit.kindCount_append]
  rcases expandedGrayTransitionPrefixCircuit_kindCounts layout V
      (grayCNOTEdges (tail + 1)).length le_rfl with ⟨_, hcnot⟩
  rw [hcnot, expandedGrayRootCircuitAt_cnotCount, length_grayCNOTEdges]
  have hpow : 0 < 2 ^ tail := pow_pos (by omega) tail
  simp only [pow_succ]
  omega

@[simp]
theorem expandedGrayControlledViaRootCircuit_gateCount
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) (V : QubitUnitary) :
    Circuit.gateCount (expandedGrayControlledViaRootCircuit layout V) =
      7 * 2 ^ (tail + 1) - 8 := by
  rw [expandedGrayControlledViaRootCircuit, Circuit.gateCount_append,
    expandedGrayTransitionPrefixCircuit_gateCount,
    expandedGrayRootCircuitAt_gateCount, length_grayCNOTEdges]
  have hpow : 0 < 2 ^ tail := pow_pos (by omega) tail
  simp only [pow_succ]
  omega

@[simp]
theorem expandedGrayControlledViaRootCircuit_oneQubitCNOTCost
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) (V : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (expandedGrayControlledViaRootCircuit layout V) =
      some (7 * 2 ^ (tail + 1) - 8) := by
  rw [expandedGrayControlledViaRootCircuit, Circuit.cost_append,
    expandedGrayTransitionPrefixCircuit_oneQubitCNOTCost,
    expandedGrayRootCircuitAt_oneQubitCNOTCost]
  simp only [Circuit.addCost_some]
  have hpow : 0 < 2 ^ tail := pow_pos (by omega) tail
  rw [length_grayCNOTEdges]
  simp only [pow_succ]
  congr 1
  omega

@[simp]
theorem expandedGrayControlledCircuit_oneQubitCount {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) (U : QubitUnitary) :
    Circuit.kindCount .oneQubit (expandedGrayControlledCircuit layout U) =
      4 * (2 ^ (tail + 1) - 1) := by
  simp [expandedGrayControlledCircuit]

@[simp]
theorem expandedGrayControlledCircuit_cnotCount {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) (U : QubitUnitary) :
    Circuit.kindCount .cnot (expandedGrayControlledCircuit layout U) =
      3 * 2 ^ (tail + 1) - 4 := by
  simp [expandedGrayControlledCircuit]

@[simp]
theorem expandedGrayControlledCircuit_gateCount {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) (U : QubitUnitary) :
    Circuit.gateCount (expandedGrayControlledCircuit layout U) =
      7 * 2 ^ (tail + 1) - 8 := by
  simp [expandedGrayControlledCircuit]

@[simp]
theorem expandedGrayControlledCircuit_oneQubitCNOTCost
    {tail ambientWidth : ℕ}
    (layout : OrderedControlLayout (tail + 1) ambientWidth) (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT (expandedGrayControlledCircuit layout U) =
      some (7 * 2 ^ (tail + 1) - 8) := by
  simp [expandedGrayControlledCircuit]

/-! ## Six-control base for the quadratic recursion -/

/-- The directly expanded Gray base on six controls (logical width seven). -/
def sixControlExpandedGrayCircuit {ambientWidth : ℕ}
    (layout : OrderedControlLayout 6 ambientWidth) (U : QubitUnitary) :
    Circuit ambientWidth :=
  expandedGrayControlledCircuit (tail := 5) layout U

@[simp]
theorem eval_sixControlExpandedGrayCircuit {ambientWidth : ℕ}
    (layout : OrderedControlLayout 6 ambientWidth) (U : QubitUnitary) :
    Circuit.eval (sixControlExpandedGrayCircuit layout U) =
      positiveControlledUnitary layout.targetWire layout.controlSet U := by
  simp [sixControlExpandedGrayCircuit]

@[simp]
theorem sixControlExpandedGrayCircuit_oneQubitCount {ambientWidth : ℕ}
    (layout : OrderedControlLayout 6 ambientWidth) (U : QubitUnitary) :
    Circuit.kindCount .oneQubit (sixControlExpandedGrayCircuit layout U) = 252 := by
  norm_num [sixControlExpandedGrayCircuit]

@[simp]
theorem sixControlExpandedGrayCircuit_cnotCount {ambientWidth : ℕ}
    (layout : OrderedControlLayout 6 ambientWidth) (U : QubitUnitary) :
    Circuit.kindCount .cnot (sixControlExpandedGrayCircuit layout U) = 188 := by
  norm_num [sixControlExpandedGrayCircuit]

@[simp]
theorem sixControlExpandedGrayCircuit_gateCount {ambientWidth : ℕ}
    (layout : OrderedControlLayout 6 ambientWidth) (U : QubitUnitary) :
    Circuit.gateCount (sixControlExpandedGrayCircuit layout U) = 440 := by
  norm_num [sixControlExpandedGrayCircuit]

@[simp]
theorem sixControlExpandedGrayCircuit_oneQubitCNOTCost {ambientWidth : ℕ}
    (layout : OrderedControlLayout 6 ambientWidth) (U : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT (sixControlExpandedGrayCircuit layout U) =
      some 440 := by
  norm_num [sixControlExpandedGrayCircuit]

end OrderedControlLayout

end

end Barenco.MultiControl
