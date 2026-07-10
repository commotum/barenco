import Barenco.MultiControl.RecursiveExpansion

/-!
# Swapping the final control with the target

Lemma 7.9 needs a prefix-controlled X on the original unitary target while the
final logical control is available as dirty workspace.  Stage 7 already provides
the opposite-looking interface: `expandedRecursivePrefixXCircuit` targets the
last ordered control and uses the layout target as dirty workspace.

This leaf swaps those two roles, proves the exact layout projections, and exposes
the resulting primitive one-qubit/CNOT circuit with inherited evaluator and
resource theorems.  All prefix controls and arbitrary ambient spectators retain
their original positions.
-/

namespace Barenco.MultiControl

noncomputable section

namespace OrderedControlLayout

/-- The wire embedding obtained by replacing the final control with the old target. -/
def swapLastControlTargetEmbedding {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    Fin (p + 1) ↪ Fin ambientWidth where
  toFun := fun control =>
    Fin.lastCases layout.targetWire
      (fun prefixIndex => layout.controlWire prefixIndex.castSucc) control
  inj' := by
    intro first second
    refine Fin.lastCases ?_ (fun firstPrefix => ?_) first <;>
      refine Fin.lastCases ?_ (fun secondPrefix => ?_) second
    · intro
      rfl
    · intro heq
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at heq
      exact False.elim (layout.control_ne_target secondPrefix.castSucc heq.symm)
    · intro heq
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at heq
      exact False.elim (layout.control_ne_target firstPrefix.castSucc heq)
    · intro heq
      simp only [Fin.lastCases_castSucc] at heq
      exact layout.controlWire.injective heq

@[simp]
theorem swapLastControlTargetEmbedding_castSucc {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) (control : Fin p) :
    layout.swapLastControlTargetEmbedding control.castSucc =
      layout.controlWire control.castSucc := by
  simp [swapLastControlTargetEmbedding]

@[simp]
theorem swapLastControlTargetEmbedding_last {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    layout.swapLastControlTargetEmbedding (Fin.last p) = layout.targetWire := by
  simp [swapLastControlTargetEmbedding]

/--
Exchange the last ordered control with the target while preserving the prefix
control order.
-/
def swapLastControlTarget {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    OrderedControlLayout (p + 1) ambientWidth where
  controlWire := layout.swapLastControlTargetEmbedding
  targetWire := layout.lastControlWire
  control_ne_target := by
    intro control
    refine Fin.lastCases ?_ (fun prefixIndex => ?_) control
    · rw [swapLastControlTargetEmbedding_last]
      exact layout.lastControlWire_ne_targetWire.symm
    · rw [swapLastControlTargetEmbedding_castSucc]
      change layout.controlWire prefixIndex.castSucc ≠
        layout.controlWire (Fin.last p)
      exact layout.controlWire_ne (Fin.castSucc_ne_last prefixIndex)

@[simp]
theorem swapLastControlTarget_controlWire_castSucc {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) (control : Fin p) :
    layout.swapLastControlTarget.controlWire control.castSucc =
      layout.controlWire control.castSucc := by
  simp [swapLastControlTarget]

@[simp]
theorem swapLastControlTarget_lastControlWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    layout.swapLastControlTarget.lastControlWire = layout.targetWire := by
  simp [lastControlWire, swapLastControlTarget]

@[simp]
theorem swapLastControlTarget_targetWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    layout.swapLastControlTarget.targetWire = layout.lastControlWire := rfl

/-- The swapped prefix-to-last layout is the original prefix-to-target layout. -/
@[simp]
theorem swapLastControlTarget_prefixToLastLayout {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    layout.swapLastControlTarget.prefixToLastLayout =
      layout.prefixTargetLayout := by
  rw [OrderedControlLayout.mk.injEq]
  constructor
  · apply Function.Embedding.ext
    intro control
    simp
  · simp

/-- Swapping converts the Stage 7 prefix-X macro into the desired target-X macro. -/
@[simp]
theorem swapLastControlTarget_prefixControlledX {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    layout.swapLastControlTarget.prefixControlledX =
      layout.prefixControlledTarget pauliX := by
  rw [prefixControlledX, prefixControlledTarget,
    swapLastControlTarget_prefixToLastLayout]
  rfl

/-! ## Exact primitive prefix-to-target X expansion -/

/--
Literal corrected Corollary 7.4 expansion of an X on the original target,
controlled by the first `p` controls and borrowing the last control.
-/
def expandedPrefixTargetXCircuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) : Circuit ambientWidth :=
  layout.swapLastControlTarget.expandedRecursivePrefixXCircuit hwidth

/-- Exact full-register semantics, including restoration of the dirty final control. -/
@[simp]
theorem eval_expandedPrefixTargetXCircuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    Circuit.eval (layout.expandedPrefixTargetXCircuit hwidth) =
      (layout.prefixControlledTarget pauliX).denotation := by
  rw [expandedPrefixTargetXCircuit,
    eval_expandedRecursivePrefixXCircuit,
    swapLastControlTarget_prefixControlledX]

/-- The transported Corollary 7.4 dirty wire is exactly the final logical control. -/
@[simp]
theorem expandedPrefixTargetXCircuit_dirtyWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    (layout.swapLastControlTarget.recursivePrefixFourBlockLayout hwidth).dirtyWire =
      layout.lastControlWire := by
  simp

/-- The transported Corollary 7.4 target is exactly the original target. -/
@[simp]
theorem expandedPrefixTargetXCircuit_targetWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    (layout.swapLastControlTarget.recursivePrefixFourBlockLayout hwidth).targetWire =
      layout.targetWire := by
  simp

@[simp]
theorem expandedPrefixTargetXCircuit_oneQubitCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    Circuit.kindCount .oneQubit (layout.expandedPrefixTargetXCircuit hwidth) =
      32 * p - 80 := by
  simp [expandedPrefixTargetXCircuit]

@[simp]
theorem expandedPrefixTargetXCircuit_cnotCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    Circuit.kindCount .cnot (layout.expandedPrefixTargetXCircuit hwidth) =
      24 * p - 52 := by
  simp [expandedPrefixTargetXCircuit]

@[simp]
theorem expandedPrefixTargetXCircuit_gateCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    Circuit.gateCount (layout.expandedPrefixTargetXCircuit hwidth) =
      56 * p - 132 := by
  simp [expandedPrefixTargetXCircuit]

@[simp]
theorem expandedPrefixTargetXCircuit_oneQubitCNOTCost {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    Circuit.cost CostModel.oneQubitCNOT
        (layout.expandedPrefixTargetXCircuit hwidth) =
      some (56 * p - 132) := by
  simp [expandedPrefixTargetXCircuit]

end OrderedControlLayout

end

end Barenco.MultiControl
