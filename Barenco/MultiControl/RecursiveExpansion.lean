import Barenco.MultiControl.Recursive
import Barenco.MultiControl.GrayExpansion
import Barenco.MultiControl.Corollary74Expansion

/-!
# Primitive expansion of the recursive multi-control construction

This leaf gives the syntax-level expansion promised by Barenco Lemma 7.5 and
the construction-specific part of Corollary 7.6.  A recursive step uses two
selected six-node singly controlled circuits, two literal corrected
Corollary 7.4 multi-controlled-X circuits, and the smaller recursive circuit.

The recursion stops at six controls, where `sixControlExpandedGrayCircuit`
provides a directly expanded exact base.  All circuits act on the original
ambient register: the Corollary 7.4 workspace embeds the prefix controls, uses
the final unitary target as a dirty wire, and temporarily targets the last
control.  Thus evaluator preservation includes arbitrary spectator wires and
restoration of the dirty target wire.
-/

namespace Barenco.MultiControl

open Barenco.OneQubit
open Barenco.ControlledCircuit

noncomputable section

namespace OrderedControlLayout

/-! ## Ambient workspace for an expanded prefix-controlled X -/

/--
Inject the `p + 2` logical Corollary 7.4 wires into a recursive layout.

The first `p` positions are the prefix controls, position `p` is the original
unitary target (used as dirty workspace), and the final position is the last
control (used as the multi-controlled-X target).
-/
def recursivePrefixWorkspaceEmbedding {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    Fin (p + 2) ↪ Fin ambientWidth where
  toFun index :=
    Fin.lastCases layout.lastControlWire
      (fun prior =>
        Fin.lastCases layout.targetWire
          (fun control => layout.controlWire control.castSucc) prior)
      index
  inj' := by
    intro first second
    refine Fin.lastCases ?_ (fun firstPrior => ?_) first <;>
      refine Fin.lastCases ?_ (fun secondPrior => ?_) second
    · intro
      rfl
    · refine Fin.lastCases ?_ (fun secondControl => ?_) secondPrior
      · intro heq
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at heq
        exact False.elim (layout.lastControlWire_ne_targetWire heq)
      · intro heq
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at heq
        exact False.elim
          (layout.controlWire_ne (Fin.castSucc_ne_last secondControl) heq.symm)
    · refine Fin.lastCases ?_ (fun firstControl => ?_) firstPrior
      · intro heq
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at heq
        exact False.elim (layout.lastControlWire_ne_targetWire heq.symm)
      · intro heq
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at heq
        exact False.elim
          (layout.controlWire_ne (Fin.castSucc_ne_last firstControl) heq)
    · refine Fin.lastCases ?_ (fun firstControl => ?_) firstPrior
      · refine Fin.lastCases ?_ (fun secondControl => ?_) secondPrior
        · intro
          rfl
        · intro heq
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at heq
          exact False.elim (layout.control_ne_target secondControl.castSucc heq.symm)
      · refine Fin.lastCases ?_ (fun secondControl => ?_) secondPrior
        · intro heq
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at heq
          exact False.elim (layout.control_ne_target firstControl.castSucc heq)
        · intro heq
          simp only [Fin.lastCases_castSucc] at heq
          have hcast : firstControl.castSucc = secondControl.castSucc :=
            layout.controlWire.injective heq
          have hcontrol : firstControl = secondControl :=
            Fin.castSucc_injective _ hcast
          subst secondControl
          rfl

@[simp]
theorem recursivePrefixWorkspaceEmbedding_control {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) (control : Fin p) :
    layout.recursivePrefixWorkspaceEmbedding control.castSucc.castSucc =
      layout.controlWire control.castSucc := by
  simp [recursivePrefixWorkspaceEmbedding]

@[simp]
theorem recursivePrefixWorkspaceEmbedding_dirty {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    layout.recursivePrefixWorkspaceEmbedding (Fin.last p).castSucc =
      layout.targetWire := by
  simp [recursivePrefixWorkspaceEmbedding]

@[simp]
theorem recursivePrefixWorkspaceEmbedding_target {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth) :
    layout.recursivePrefixWorkspaceEmbedding (Fin.last (p + 1)) =
      layout.lastControlWire := by
  simp [recursivePrefixWorkspaceEmbedding]

/-- The canonical balanced four-block layout transported into the ambient recursion. -/
def recursivePrefixFourBlockLayout {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    FourBlockLayout (FourBlockLayout.balancedLeftTail (p + 2) + 1)
      (FourBlockLayout.balancedRightTail (p + 2) + 1) ambientWidth where
  wire :=
    ((FourBlockLayout.balancedLayout (p + 2) hwidth).wire).trans
      layout.recursivePrefixWorkspaceEmbedding

private theorem balancedLayout_targetWire_eq_last (p : ℕ) (hwidth : 7 ≤ p + 2) :
    (FourBlockLayout.balancedLayout (p + 2) hwidth).targetWire =
      Fin.last (p + 1) := by
  apply Fin.ext
  simp [FourBlockLayout.targetWire, FourBlockLayout.balancedLayout,
    FourBlockLayout.consecutiveSlotEmbedding, FourBlockLayout.logicalWidth]
  have hsum := FourBlockLayout.balancedTails_add_seven hwidth
  omega

private theorem balancedLayout_dirtyWire_eq_penultimate
    (p : ℕ) (hwidth : 7 ≤ p + 2) :
    (FourBlockLayout.balancedLayout (p + 2) hwidth).dirtyWire =
      (Fin.last p).castSucc := by
  apply Fin.ext
  simp [FourBlockLayout.dirtyWire, FourBlockLayout.balancedLayout,
    FourBlockLayout.consecutiveSlotEmbedding, FourBlockLayout.logicalWidth]
  have hsum := FourBlockLayout.balancedTails_add_seven hwidth
  omega

private theorem balancedLayout_dataCount_eq (p : ℕ) (hwidth : 7 ≤ p + 2) :
    ((FourBlockLayout.balancedLeftTail (p + 2) + 1 + 2) +
      (FourBlockLayout.balancedRightTail (p + 2) + 1 + 1)) = p := by
  have hsum := FourBlockLayout.balancedTails_add_seven hwidth
  omega

private theorem balancedLayout_dataControlWire_eq_cast
    (p : ℕ) (hwidth : 7 ≤ p + 2)
    (control : Fin
      ((FourBlockLayout.balancedLeftTail (p + 2) + 1 + 2) +
        (FourBlockLayout.balancedRightTail (p + 2) + 1 + 1))) :
    (FourBlockLayout.balancedLayout (p + 2) hwidth).dataLayout.controlWire control =
      (Fin.cast (balancedLayout_dataCount_eq p hwidth) control).castSucc.castSucc := by
  apply Fin.ext
  cases hcontrol : (@finSumFinEquiv
      (FourBlockLayout.balancedLeftTail (p + 2) + 1 + 2)
      (FourBlockLayout.balancedRightTail (p + 2) + 1 + 1)).symm control with
  | inl left =>
      simp [FourBlockLayout.dataLayout, FourBlockLayout.dataControlEmbedding,
        FourBlockLayout.dataControlSlotEmbedding,
        FourBlockLayout.dataControlSumEmbedding, FourBlockLayout.balancedLayout,
        FourBlockLayout.consecutiveSlotEmbedding, FourBlockLayout.logicalWidth,
        hcontrol]
      have hforward := congrArg
        (@finSumFinEquiv
          (FourBlockLayout.balancedLeftTail (p + 2) + 1 + 2)
          (FourBlockLayout.balancedRightTail (p + 2) + 1 + 1)) hcontrol
      simpa using congrArg Fin.val hforward.symm
  | inr right =>
      simp [FourBlockLayout.dataLayout, FourBlockLayout.dataControlEmbedding,
        FourBlockLayout.dataControlSlotEmbedding,
        FourBlockLayout.dataControlSumEmbedding, FourBlockLayout.balancedLayout,
        FourBlockLayout.consecutiveSlotEmbedding, FourBlockLayout.logicalWidth,
        hcontrol]
      have hforward := congrArg
        (@finSumFinEquiv
          (FourBlockLayout.balancedLeftTail (p + 2) + 1 + 2)
          (FourBlockLayout.balancedRightTail (p + 2) + 1 + 1)) hcontrol
      simpa using congrArg Fin.val hforward.symm

theorem recursivePrefixFourBlockLayout_dataControlWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2)
    (control : Fin
      ((FourBlockLayout.balancedLeftTail (p + 2) + 1 + 2) +
        (FourBlockLayout.balancedRightTail (p + 2) + 1 + 1))) :
    (layout.recursivePrefixFourBlockLayout hwidth).dataLayout.controlWire control =
      layout.controlWire
        (Fin.cast (balancedLayout_dataCount_eq p hwidth) control).castSucc := by
  change layout.recursivePrefixWorkspaceEmbedding
      ((FourBlockLayout.balancedLayout (p + 2) hwidth).dataLayout.controlWire
        control) = _
  rw [balancedLayout_dataControlWire_eq_cast]
  exact layout.recursivePrefixWorkspaceEmbedding_control _

@[simp]
theorem recursivePrefixFourBlockLayout_targetWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    (layout.recursivePrefixFourBlockLayout hwidth).targetWire =
      layout.lastControlWire := by
  change layout.recursivePrefixWorkspaceEmbedding
      (FourBlockLayout.balancedLayout (p + 2) hwidth).targetWire = _
  rw [balancedLayout_targetWire_eq_last]
  exact layout.recursivePrefixWorkspaceEmbedding_target

@[simp]
theorem recursivePrefixFourBlockLayout_dirtyWire {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    (layout.recursivePrefixFourBlockLayout hwidth).dirtyWire =
      layout.targetWire := by
  change layout.recursivePrefixWorkspaceEmbedding
      (FourBlockLayout.balancedLayout (p + 2) hwidth).dirtyWire = _
  rw [balancedLayout_dirtyWire_eq_penultimate]
  exact layout.recursivePrefixWorkspaceEmbedding_dirty

private theorem positiveControlledUnitary_eq_of_layout_reindex
    {firstCount secondCount ambientWidth : ℕ}
    (first : OrderedControlLayout firstCount ambientWidth)
    (second : OrderedControlLayout secondCount ambientWidth)
    (hcount : firstCount = secondCount)
    (htarget : first.targetWire = second.targetWire)
    (hwire : ∀ control,
      first.controlWire control = second.controlWire (Fin.cast hcount control))
    (U : QubitUnitary) :
    positiveControlledUnitary first.targetWire first.controlSet U =
      positiveControlledUnitary second.targetWire second.controlSet U := by
  subst firstCount
  have hlayout : first = second := by
    cases first with
    | mk firstWire firstTarget firstNe =>
        cases second with
        | mk secondWire secondTarget secondNe =>
            simp only at htarget hwire ⊢
            subst secondTarget
            congr
            ext control
            exact congrArg Fin.val (by simpa using hwire control)
  subst second
  rfl

/-! ## Fully primitive expansion of the recursive prefix-controlled X -/

/--
Literal corrected Corollary 7.4 expansion of the prefix-controlled X macro.
The ambient unitary target is the construction's dirty wire and is restored.
-/
def expandedRecursivePrefixXCircuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) : Circuit ambientWidth :=
  let fourBlock := layout.recursivePrefixFourBlockLayout hwidth
  fourBlock.expandedRelativeCorollary74Circuit
    (FourBlockLayout.balancedLeftCapacity hwidth)
    (FourBlockLayout.balancedRightCapacity hwidth)

@[simp]
theorem eval_expandedRecursivePrefixXCircuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    Circuit.eval (layout.expandedRecursivePrefixXCircuit hwidth) =
      layout.prefixControlledX.denotation := by
  rw [expandedRecursivePrefixXCircuit,
    FourBlockLayout.eval_expandedRelativeCorollary74Circuit]
  · change positiveControlledUnitary
        (layout.recursivePrefixFourBlockLayout hwidth).dataLayout.targetWire
          (layout.recursivePrefixFourBlockLayout hwidth).dataLayout.controlSet pauliX =
        positiveControlledUnitary layout.prefixToLastLayout.targetWire
          layout.prefixToLastLayout.controlSet pauliX
    apply positiveControlledUnitary_eq_of_layout_reindex
      ((layout.recursivePrefixFourBlockLayout hwidth).dataLayout)
      layout.prefixToLastLayout (balancedLayout_dataCount_eq p hwidth)
    · exact layout.recursivePrefixFourBlockLayout_targetWire hwidth
    · intro control
      exact layout.recursivePrefixFourBlockLayout_dataControlWire hwidth control
  · exact FourBlockLayout.balancedLeftTail_le_right_add_one hwidth

/-- Exact one-qubit count for an ambient expanded prefix-controlled X. -/
@[simp]
theorem expandedRecursivePrefixXCircuit_oneQubitCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    Circuit.kindCount .oneQubit
        (layout.expandedRecursivePrefixXCircuit hwidth) = 32 * p - 80 := by
  rw [expandedRecursivePrefixXCircuit,
    FourBlockLayout.expandedRelativeCorollary74Circuit_oneQubitCount]
  have hsum := FourBlockLayout.balancedTails_add_seven hwidth
  omega

/-- Exact CNOT count for an ambient expanded prefix-controlled X. -/
@[simp]
theorem expandedRecursivePrefixXCircuit_cnotCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    Circuit.kindCount .cnot
        (layout.expandedRecursivePrefixXCircuit hwidth) = 24 * p - 52 := by
  rw [expandedRecursivePrefixXCircuit,
    FourBlockLayout.expandedRelativeCorollary74Circuit_cnotCount]
  have hsum := FourBlockLayout.balancedTails_add_seven hwidth
  omega

/-- Exact literal one-qubit-plus-CNOT node count for the ambient expansion. -/
@[simp]
theorem expandedRecursivePrefixXCircuit_gateCount {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    Circuit.gateCount (layout.expandedRecursivePrefixXCircuit hwidth) =
      56 * p - 132 := by
  rw [expandedRecursivePrefixXCircuit,
    FourBlockLayout.expandedRelativeCorollary74Circuit_gateCount]
  have hsum := FourBlockLayout.balancedTails_add_seven hwidth
  omega

/-- The ambient expanded prefix-controlled X is accepted by the early cost model. -/
@[simp]
theorem expandedRecursivePrefixXCircuit_oneQubitCNOTCost
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (hwidth : 7 ≤ p + 2) :
    Circuit.cost CostModel.oneQubitCNOT
        (layout.expandedRecursivePrefixXCircuit hwidth) =
      some (56 * p - 132) := by
  rw [expandedRecursivePrefixXCircuit,
    FourBlockLayout.expandedRelativeCorollary74Circuit_oneQubitCNOTCost]
  have hsum := FourBlockLayout.balancedTails_add_seven hwidth
  exact congrArg some (by omega)

/-! ## Selected singly controlled components -/

/-- Selected six-node expansion of the final-control target macro. -/
def expandedLastControlledTargetCircuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) : Circuit ambientWidth :=
  selectedControlledU2Circuit layout.lastControlWire layout.targetWire
    layout.lastControlWire_ne_targetWire V

@[simp]
theorem eval_expandedLastControlledTargetCircuit {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) :
    Circuit.eval (layout.expandedLastControlledTargetCircuit V) =
      (layout.lastControlledTarget V).denotation := by
  simp [expandedLastControlledTargetCircuit, lastControlledTarget]

@[simp]
theorem expandedLastControlledTargetCircuit_oneQubitCount
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (layout.expandedLastControlledTargetCircuit V) = 4 := by
  simp [expandedLastControlledTargetCircuit]

@[simp]
theorem expandedLastControlledTargetCircuit_cnotCount
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) :
    Circuit.kindCount .cnot
        (layout.expandedLastControlledTargetCircuit V) = 2 := by
  simp [expandedLastControlledTargetCircuit]

@[simp]
theorem expandedLastControlledTargetCircuit_gateCount
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) :
    Circuit.gateCount (layout.expandedLastControlledTargetCircuit V) = 6 := by
  simp [expandedLastControlledTargetCircuit]

@[simp]
theorem expandedLastControlledTargetCircuit_oneQubitCNOTCost
    {p ambientWidth : ℕ}
    (layout : OrderedControlLayout (p + 1) ambientWidth)
    (V : QubitUnitary) :
    Circuit.cost CostModel.oneQubitCNOT
        (layout.expandedLastControlledTargetCircuit V) = some 6 := by
  simp [expandedLastControlledTargetCircuit]

/-! ## Fully primitive recursive construction -/

/--
The fully primitive depth-`depth` Lemma 7.5 construction.

Depth zero has six controls.  A successor uses the exact square root `V` of
`U`, two selected controlled-`V` circuits, two expanded prefix-controlled X
circuits, and the recursively expanded residual prefix-controlled `V`.
-/
def recursivePrimitiveCircuit {ambientWidth : ℕ} :
    (depth : ℕ) → OrderedControlLayout (depth + 6) ambientWidth →
      QubitUnitary → Circuit ambientWidth
  | 0, layout, U => layout.sixControlExpandedGrayCircuit U
  | depth + 1, layout, U =>
      let V := unitarySquareRoot U
      recursiveSubstitutionCircuit
        (layout.expandedLastControlledTargetCircuit V)
        (layout.expandedRecursivePrefixXCircuit (by omega))
        (layout.expandedLastControlledTargetCircuit V⁻¹)
        (layout.expandedRecursivePrefixXCircuit (by omega))
        (recursivePrimitiveCircuit depth layout.prefixTargetLayout V)

@[simp]
theorem recursivePrimitiveCircuit_zero {ambientWidth : ℕ}
    (layout : OrderedControlLayout 6 ambientWidth) (U : QubitUnitary) :
    recursivePrimitiveCircuit 0 layout U =
      layout.sixControlExpandedGrayCircuit U := rfl

@[simp]
theorem recursivePrimitiveCircuit_succ {depth ambientWidth : ℕ}
    (layout : OrderedControlLayout (depth + 1 + 6) ambientWidth)
    (U : QubitUnitary) :
    recursivePrimitiveCircuit (depth + 1) layout U =
      let V := unitarySquareRoot U
      recursiveSubstitutionCircuit
        (layout.expandedLastControlledTargetCircuit V)
        (layout.expandedRecursivePrefixXCircuit (by omega))
        (layout.expandedLastControlledTargetCircuit V⁻¹)
        (layout.expandedRecursivePrefixXCircuit (by omega))
        (recursivePrimitiveCircuit depth layout.prefixTargetLayout V) := rfl

/-- Exact full-register semantics of the fully primitive recursive construction. -/
@[simp]
theorem eval_recursivePrimitiveCircuit {ambientWidth : ℕ} :
    ∀ (depth : ℕ) (layout : OrderedControlLayout (depth + 6) ambientWidth)
      (U : QubitUnitary),
      Circuit.eval (recursivePrimitiveCircuit depth layout U) =
        positiveControlledUnitary layout.targetWire layout.controlSet U
  | 0, layout, U => by
      exact eval_sixControlExpandedGrayCircuit layout U
  | depth + 1, layout, U => by
      let V := unitarySquareRoot U
      rw [recursivePrimitiveCircuit_succ]
      apply eval_recursiveSubstitutionCircuit_of_sq_eq layout U V
        (unitarySquareRoot_pow_two U)
      · exact eval_expandedLastControlledTargetCircuit layout V
      · exact eval_expandedRecursivePrefixXCircuit layout (by omega)
      · exact eval_expandedLastControlledTargetCircuit layout V⁻¹
      · exact eval_expandedRecursivePrefixXCircuit layout (by omega)
      · change Circuit.eval
          (recursivePrimitiveCircuit depth layout.prefixTargetLayout V) =
          positiveControlledUnitary layout.prefixTargetLayout.targetWire
            layout.prefixTargetLayout.controlSet V
        exact eval_recursivePrimitiveCircuit depth layout.prefixTargetLayout V

/-! ## Exact syntax recurrences -/

theorem recursivePrimitiveCircuit_oneQubitCount_succ
    {depth ambientWidth : ℕ}
    (layout : OrderedControlLayout (depth + 1 + 6) ambientWidth)
    (U : QubitUnitary) :
    Circuit.kindCount .oneQubit
        (recursivePrimitiveCircuit (depth + 1) layout U) =
      Circuit.kindCount .oneQubit
          (recursivePrimitiveCircuit depth layout.prefixTargetLayout
            (unitarySquareRoot U)) +
        (64 * depth + 232) := by
  rw [recursivePrimitiveCircuit_succ,
    recursiveSubstitutionCircuit_kindCount]
  simp only [expandedLastControlledTargetCircuit_oneQubitCount,
    expandedRecursivePrefixXCircuit_oneQubitCount]
  omega

theorem recursivePrimitiveCircuit_cnotCount_succ
    {depth ambientWidth : ℕ}
    (layout : OrderedControlLayout (depth + 1 + 6) ambientWidth)
    (U : QubitUnitary) :
    Circuit.kindCount .cnot
        (recursivePrimitiveCircuit (depth + 1) layout U) =
      Circuit.kindCount .cnot
          (recursivePrimitiveCircuit depth layout.prefixTargetLayout
            (unitarySquareRoot U)) +
        (48 * depth + 188) := by
  rw [recursivePrimitiveCircuit_succ,
    recursiveSubstitutionCircuit_kindCount]
  simp only [expandedLastControlledTargetCircuit_cnotCount,
    expandedRecursivePrefixXCircuit_cnotCount]
  omega

theorem recursivePrimitiveCircuit_gateCount_succ
    {depth ambientWidth : ℕ}
    (layout : OrderedControlLayout (depth + 1 + 6) ambientWidth)
    (U : QubitUnitary) :
    Circuit.gateCount (recursivePrimitiveCircuit (depth + 1) layout U) =
      Circuit.gateCount
          (recursivePrimitiveCircuit depth layout.prefixTargetLayout
            (unitarySquareRoot U)) +
        (112 * depth + 420) := by
  rw [recursivePrimitiveCircuit_succ,
    recursiveSubstitutionCircuit_gateCount]
  simp only [expandedLastControlledTargetCircuit_gateCount,
    expandedRecursivePrefixXCircuit_gateCount]
  omega

/-! ## Closed construction counts -/

/-- Exact one-qubit count of the named depth-indexed construction. -/
@[simp]
theorem recursivePrimitiveCircuit_oneQubitCount {ambientWidth : ℕ} :
    ∀ (depth : ℕ) (layout : OrderedControlLayout (depth + 6) ambientWidth)
      (U : QubitUnitary),
      Circuit.kindCount .oneQubit
          (recursivePrimitiveCircuit depth layout U) =
        32 * depth ^ 2 + 200 * depth + 252
  | 0, layout, U => by
      exact sixControlExpandedGrayCircuit_oneQubitCount layout U
  | depth + 1, layout, U => by
      rw [recursivePrimitiveCircuit_oneQubitCount_succ,
        recursivePrimitiveCircuit_oneQubitCount]
      ring

/-- Exact CNOT count of the named depth-indexed construction. -/
@[simp]
theorem recursivePrimitiveCircuit_cnotCount {ambientWidth : ℕ} :
    ∀ (depth : ℕ) (layout : OrderedControlLayout (depth + 6) ambientWidth)
      (U : QubitUnitary),
      Circuit.kindCount .cnot (recursivePrimitiveCircuit depth layout U) =
        24 * depth ^ 2 + 164 * depth + 188
  | 0, layout, U => by
      exact sixControlExpandedGrayCircuit_cnotCount layout U
  | depth + 1, layout, U => by
      rw [recursivePrimitiveCircuit_cnotCount_succ,
        recursivePrimitiveCircuit_cnotCount]
      ring

/-- Exact primitive node count of the named depth-indexed construction. -/
@[simp]
theorem recursivePrimitiveCircuit_gateCount {ambientWidth : ℕ} :
    ∀ (depth : ℕ) (layout : OrderedControlLayout (depth + 6) ambientWidth)
      (U : QubitUnitary),
      Circuit.gateCount (recursivePrimitiveCircuit depth layout U) =
        56 * depth ^ 2 + 364 * depth + 440
  | 0, layout, U => by
      exact sixControlExpandedGrayCircuit_gateCount layout U
  | depth + 1, layout, U => by
      rw [recursivePrimitiveCircuit_gateCount_succ,
        recursivePrimitiveCircuit_gateCount]
      ring

/-- Exact accepted one-qubit-plus-CNOT cost of the recursive primitive syntax. -/
@[simp]
theorem recursivePrimitiveCircuit_oneQubitCNOTCost {ambientWidth : ℕ} :
    ∀ (depth : ℕ) (layout : OrderedControlLayout (depth + 6) ambientWidth)
      (U : QubitUnitary),
      Circuit.cost CostModel.oneQubitCNOT
          (recursivePrimitiveCircuit depth layout U) =
        some (56 * depth ^ 2 + 364 * depth + 440)
  | 0, layout, U => by
      exact sixControlExpandedGrayCircuit_oneQubitCNOTCost layout U
  | depth + 1, layout, U => by
      rw [recursivePrimitiveCircuit_succ,
        recursiveSubstitutionCircuit_cost]
      simp only [expandedLastControlledTargetCircuit_oneQubitCNOTCost,
        expandedRecursivePrefixXCircuit_oneQubitCNOTCost,
        recursivePrimitiveCircuit_oneQubitCNOTCost,
        Circuit.addCost_some]
      rw [show 56 * (depth + 6) - 132 = 56 * depth + 204 by omega]
      exact congrArg some (by ring)

/-! ## Boundary sanity checks -/

/-- The recursive syntax agrees with the directly expanded six-control base. -/
theorem recursivePrimitiveCircuit_depth_zero_resources {ambientWidth : ℕ}
    (layout : OrderedControlLayout 6 ambientWidth) (U : QubitUnitary) :
    Circuit.kindCount .oneQubit (recursivePrimitiveCircuit 0 layout U) = 252 ∧
      Circuit.kindCount .cnot (recursivePrimitiveCircuit 0 layout U) = 188 ∧
      Circuit.gateCount (recursivePrimitiveCircuit 0 layout U) = 440 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (recursivePrimitiveCircuit 0 layout U) = some 440 := by
  norm_num

/-- The first recursive step has the exact profile `(484, 376, 860)`. -/
theorem recursivePrimitiveCircuit_depth_one_resources {ambientWidth : ℕ}
    (layout : OrderedControlLayout 7 ambientWidth) (U : QubitUnitary) :
    Circuit.kindCount .oneQubit (recursivePrimitiveCircuit 1 layout U) = 484 ∧
      Circuit.kindCount .cnot (recursivePrimitiveCircuit 1 layout U) = 376 ∧
      Circuit.gateCount (recursivePrimitiveCircuit 1 layout U) = 860 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (recursivePrimitiveCircuit 1 layout U) = some 860 := by
  constructor
  · simpa using recursivePrimitiveCircuit_oneQubitCount 1 layout U
  constructor
  · simpa using recursivePrimitiveCircuit_cnotCount 1 layout U
  constructor
  · simpa using recursivePrimitiveCircuit_gateCount 1 layout U
  · simpa using recursivePrimitiveCircuit_oneQubitCNOTCost 1 layout U

end OrderedControlLayout

end

end Barenco.MultiControl
