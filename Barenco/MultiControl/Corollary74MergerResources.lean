import Barenco.MultiControl.Corollary74CompleteMergers

/-!
# Resources for the complete Corollary 7.4 merger

The counts in this leaf are folds of the named emitted symbolic, visible, and
lowered circuit lists. Both named cost models accept the output because it
contains only one-qubit and CNOT nodes.
-/

namespace Barenco.MultiControl

open Barenco.Optimization
open scoped Matrix

noncomputable section

namespace FourBlockLayout

/-- Visible fusion syntax emitted by the complete certified Corollary 7.4 merger. -/
def completeMergedRelativeCorollary74FusionCircuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) : FusionCircuit n :=
  SymbolicCircuit.erase corollary74FactorValuation
    (layout.completeMergedRelativeCorollary74SymbolicCircuit hleft hright)

/-- Public primitive circuit obtained by lowering the complete fusion syntax. -/
def completeMergedRelativeCorollary74Circuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) : Circuit n :=
  (layout.completeMergedRelativeCorollary74FusionCircuit hleft hright).lower

/-- Exact arbitrary-register semantics of the visible post-merger syntax. -/
@[simp]
theorem eval_completeMergedRelativeCorollary74FusionCircuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2)
    (htargetFree : leftTail ≤ rightTail + 1) :
    (layout.completeMergedRelativeCorollary74FusionCircuit
      hleft hright).eval =
      positiveControlledUnitary layout.targetWire
        layout.dataLayout.controlSet pauliX := by
  exact layout.eval_completeMergedRelativeCorollary74SymbolicCircuit
    hleft hright htargetFree

/-- Exact arbitrary-register semantics after lowering to trusted circuit syntax. -/
@[simp]
theorem eval_completeMergedRelativeCorollary74Circuit
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2)
    (htargetFree : leftTail ≤ rightTail + 1) :
    Circuit.eval
        (layout.completeMergedRelativeCorollary74Circuit hleft hright) =
      positiveControlledUnitary layout.targetWire
        layout.dataLayout.controlSet pauliX := by
  rw [completeMergedRelativeCorollary74Circuit,
    FusionCircuit.eval_lower,
    eval_completeMergedRelativeCorollary74FusionCircuit
      layout hleft hright htargetFree]

/-- The emitted circuit has the corrected four-block basis action exactly. -/
theorem eval_completeMergedRelativeCorollary74Circuit_mulVec_basisKet
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2)
    (htargetFree : leftTail ≤ rightTail + 1) (input : Basis n) :
    (Circuit.eval
      (layout.completeMergedRelativeCorollary74Circuit hleft hright) : Gate n) *ᵥ
        basisKet input = basisKet (layout.fourBlockUpdate input) := by
  rw [eval_completeMergedRelativeCorollary74Circuit
    layout hleft hright htargetFree,
    ← eval_relativeCorollary74Circuit
      layout hleft hright htargetFree]
  exact eval_relativeCorollary74Circuit_mulVec_basisKet
    layout hleft hright htargetFree input

/-- Every non-target wire, including the arbitrary dirty wire, is restored. -/
theorem completeMergedRelativeCorollary74Circuit_basisAction_and_restoration
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2)
    (htargetFree : leftTail ≤ rightTail + 1) (input : Basis n) :
    (Circuit.eval
      (layout.completeMergedRelativeCorollary74Circuit hleft hright) : Gate n) *ᵥ
        basisKet input = basisKet (layout.fourBlockUpdate input) ∧
      (∀ wire, wire ≠ layout.targetWire →
        layout.fourBlockUpdate input wire = input wire) := by
  exact ⟨eval_completeMergedRelativeCorollary74Circuit_mulVec_basisKet
      layout hleft hright htargetFree input,
    fun wire hwire ↦ layout.fourBlockUpdate_apply_of_ne input wire hwire⟩

@[simp]
theorem completeMergedRelativeCorollary74FusionCircuit_oneQubitCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    FusionCircuit.oneQubitCount
        (layout.completeMergedRelativeCorollary74FusionCircuit hleft hright) =
      24 * (leftTail + rightTail) + 66 := by
  rw [completeMergedRelativeCorollary74FusionCircuit,
    SymbolicCircuit.erase_oneQubitCount,
    completeMergedRelativeCorollary74SymbolicCircuit_oneQubitCount]

@[simp]
theorem completeMergedRelativeCorollary74FusionCircuit_cnotCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    FusionCircuit.cnotCount
        (layout.completeMergedRelativeCorollary74FusionCircuit hleft hright) =
      24 * (leftTail + rightTail) + 68 := by
  rw [completeMergedRelativeCorollary74FusionCircuit,
    SymbolicCircuit.erase_cnotCount,
    completeMergedRelativeCorollary74SymbolicCircuit_cnotCount]

@[simp]
theorem completeMergedRelativeCorollary74FusionCircuit_twoQubitCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    FusionCircuit.twoQubitCount
        (layout.completeMergedRelativeCorollary74FusionCircuit hleft hright) = 0 := by
  simp [completeMergedRelativeCorollary74FusionCircuit]

@[simp]
theorem completeMergedRelativeCorollary74FusionCircuit_gateCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    FusionCircuit.gateCount
        (layout.completeMergedRelativeCorollary74FusionCircuit hleft hright) =
      48 * (leftTail + rightTail) + 134 := by
  rw [completeMergedRelativeCorollary74FusionCircuit,
    SymbolicCircuit.erase_gateCount,
    completeMergedRelativeCorollary74SymbolicCircuit_gateCount]

@[simp]
theorem completeMergedRelativeCorollary74FusionCircuit_oneQubitCNOTCost
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    FusionCircuit.cost CostModel.oneQubitCNOT
        (layout.completeMergedRelativeCorollary74FusionCircuit hleft hright) =
      some (48 * (leftTail + rightTail) + 134) := by
  rw [completeMergedRelativeCorollary74FusionCircuit,
    SymbolicCircuit.erase_oneQubitCNOTCost,
    completeMergedRelativeCorollary74SymbolicCircuit_gateCount]

@[simp]
theorem completeMergedRelativeCorollary74FusionCircuit_arbitraryTwoQubitCost
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    FusionCircuit.cost CostModel.arbitraryTwoQubit
        (layout.completeMergedRelativeCorollary74FusionCircuit hleft hright) =
      some (48 * (leftTail + rightTail) + 134) := by
  rw [FusionCircuit.arbitraryTwoQubit_cost_eq_gateCount,
    completeMergedRelativeCorollary74FusionCircuit_gateCount]

@[simp]
theorem completeMergedRelativeCorollary74Circuit_oneQubitCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    Circuit.kindCount .oneQubit
        (layout.completeMergedRelativeCorollary74Circuit hleft hright) =
      24 * (leftTail + rightTail) + 66 := by
  rw [completeMergedRelativeCorollary74Circuit,
    FusionCircuit.oneQubitCount_lower,
    completeMergedRelativeCorollary74FusionCircuit_oneQubitCount]

@[simp]
theorem completeMergedRelativeCorollary74Circuit_cnotCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    Circuit.kindCount .cnot
        (layout.completeMergedRelativeCorollary74Circuit hleft hright) =
      24 * (leftTail + rightTail) + 68 := by
  rw [completeMergedRelativeCorollary74Circuit,
    FusionCircuit.cnotCount_lower,
    completeMergedRelativeCorollary74FusionCircuit_cnotCount]

@[simp]
theorem completeMergedRelativeCorollary74Circuit_twoQubitCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    Circuit.kindCount .arbitraryTwoQubit
        (layout.completeMergedRelativeCorollary74Circuit hleft hright) = 0 := by
  rw [completeMergedRelativeCorollary74Circuit,
    FusionCircuit.twoQubitCount_lower,
    completeMergedRelativeCorollary74FusionCircuit_twoQubitCount]

@[simp]
theorem completeMergedRelativeCorollary74Circuit_gateCount
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    Circuit.gateCount
        (layout.completeMergedRelativeCorollary74Circuit hleft hright) =
      48 * (leftTail + rightTail) + 134 := by
  rw [completeMergedRelativeCorollary74Circuit,
    FusionCircuit.gateCount_lower,
    completeMergedRelativeCorollary74FusionCircuit_gateCount]

@[simp]
theorem completeMergedRelativeCorollary74Circuit_oneQubitCNOTCost
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    Circuit.cost CostModel.oneQubitCNOT
        (layout.completeMergedRelativeCorollary74Circuit hleft hright) =
      some (48 * (leftTail + rightTail) + 134) := by
  rw [completeMergedRelativeCorollary74Circuit,
    FusionCircuit.cost_lower,
    completeMergedRelativeCorollary74FusionCircuit_oneQubitCNOTCost]

@[simp]
theorem completeMergedRelativeCorollary74Circuit_arbitraryTwoQubitCost
    {leftTail rightTail n : ℕ}
    (layout : FourBlockLayout (leftTail + 1) (rightTail + 1) n)
    (hleft : leftTail ≤ rightTail + 2)
    (hright : rightTail ≤ leftTail + 2) :
    Circuit.cost CostModel.arbitraryTwoQubit
        (layout.completeMergedRelativeCorollary74Circuit hleft hright) =
      some (48 * (leftTail + rightTail) + 134) := by
  rw [completeMergedRelativeCorollary74Circuit,
    FusionCircuit.cost_lower,
    completeMergedRelativeCorollary74FusionCircuit_arbitraryTwoQubitCost]

/-! ## Balanced exact-width wrappers -/

def balancedCompleteMergedRelativeCorollary74FusionCircuit
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) : FusionCircuit sourceWidth :=
  (balancedLayout sourceWidth hwidth).completeMergedRelativeCorollary74FusionCircuit
    (balancedLeftCapacity hwidth) (balancedRightCapacity hwidth)

def balancedCompleteMergedRelativeCorollary74Circuit
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) : Circuit sourceWidth :=
  (balancedCompleteMergedRelativeCorollary74FusionCircuit sourceWidth hwidth).lower

@[simp]
theorem eval_balancedCompleteMergedRelativeCorollary74FusionCircuit
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    (balancedCompleteMergedRelativeCorollary74FusionCircuit
      sourceWidth hwidth).eval =
      positiveControlledUnitary
        (balancedLayout sourceWidth hwidth).targetWire
        (balancedLayout sourceWidth hwidth).dataLayout.controlSet pauliX := by
  apply eval_completeMergedRelativeCorollary74FusionCircuit
  exact balancedLeftTail_le_right_add_one hwidth

@[simp]
theorem eval_balancedCompleteMergedRelativeCorollary74Circuit
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.eval
        (balancedCompleteMergedRelativeCorollary74Circuit sourceWidth hwidth) =
      positiveControlledUnitary
        (balancedLayout sourceWidth hwidth).targetWire
        (balancedLayout sourceWidth hwidth).dataLayout.controlSet pauliX := by
  rw [balancedCompleteMergedRelativeCorollary74Circuit,
    FusionCircuit.eval_lower,
    eval_balancedCompleteMergedRelativeCorollary74FusionCircuit]

@[simp]
theorem balancedCompleteMergedRelativeCorollary74FusionCircuit_oneQubitCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    FusionCircuit.oneQubitCount
        (balancedCompleteMergedRelativeCorollary74FusionCircuit
          sourceWidth hwidth) =
      24 * sourceWidth - 102 := by
  rw [balancedCompleteMergedRelativeCorollary74FusionCircuit,
    completeMergedRelativeCorollary74FusionCircuit_oneQubitCount]
  have hsum := balancedTails_add_seven hwidth
  omega

@[simp]
theorem balancedCompleteMergedRelativeCorollary74FusionCircuit_cnotCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    FusionCircuit.cnotCount
        (balancedCompleteMergedRelativeCorollary74FusionCircuit
          sourceWidth hwidth) =
      24 * sourceWidth - 100 := by
  rw [balancedCompleteMergedRelativeCorollary74FusionCircuit,
    completeMergedRelativeCorollary74FusionCircuit_cnotCount]
  have hsum := balancedTails_add_seven hwidth
  omega

@[simp]
theorem balancedCompleteMergedRelativeCorollary74FusionCircuit_twoQubitCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    FusionCircuit.twoQubitCount
        (balancedCompleteMergedRelativeCorollary74FusionCircuit
          sourceWidth hwidth) = 0 := by
  rw [balancedCompleteMergedRelativeCorollary74FusionCircuit,
    completeMergedRelativeCorollary74FusionCircuit_twoQubitCount]

@[simp]
theorem balancedCompleteMergedRelativeCorollary74FusionCircuit_gateCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    FusionCircuit.gateCount
        (balancedCompleteMergedRelativeCorollary74FusionCircuit
          sourceWidth hwidth) =
      48 * sourceWidth - 202 := by
  rw [balancedCompleteMergedRelativeCorollary74FusionCircuit,
    completeMergedRelativeCorollary74FusionCircuit_gateCount]
  have hsum := balancedTails_add_seven hwidth
  omega

@[simp]
theorem balancedCompleteMergedRelativeCorollary74FusionCircuit_oneQubitCNOTCost
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    FusionCircuit.cost CostModel.oneQubitCNOT
        (balancedCompleteMergedRelativeCorollary74FusionCircuit
          sourceWidth hwidth) =
      some (48 * sourceWidth - 202) := by
  rw [balancedCompleteMergedRelativeCorollary74FusionCircuit,
    completeMergedRelativeCorollary74FusionCircuit_oneQubitCNOTCost]
  have hsum := balancedTails_add_seven hwidth
  simp only [Option.some.injEq]
  omega

@[simp]
theorem balancedCompleteMergedRelativeCorollary74FusionCircuit_arbitraryTwoQubitCost
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    FusionCircuit.cost CostModel.arbitraryTwoQubit
        (balancedCompleteMergedRelativeCorollary74FusionCircuit
          sourceWidth hwidth) =
      some (48 * sourceWidth - 202) := by
  rw [FusionCircuit.arbitraryTwoQubit_cost_eq_gateCount,
    balancedCompleteMergedRelativeCorollary74FusionCircuit_gateCount]

@[simp]
theorem balancedCompleteMergedRelativeCorollary74Circuit_oneQubitCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.kindCount .oneQubit
        (balancedCompleteMergedRelativeCorollary74Circuit sourceWidth hwidth) =
      24 * sourceWidth - 102 := by
  rw [balancedCompleteMergedRelativeCorollary74Circuit,
    FusionCircuit.oneQubitCount_lower,
    balancedCompleteMergedRelativeCorollary74FusionCircuit_oneQubitCount]

@[simp]
theorem balancedCompleteMergedRelativeCorollary74Circuit_cnotCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.kindCount .cnot
        (balancedCompleteMergedRelativeCorollary74Circuit sourceWidth hwidth) =
      24 * sourceWidth - 100 := by
  rw [balancedCompleteMergedRelativeCorollary74Circuit,
    FusionCircuit.cnotCount_lower,
    balancedCompleteMergedRelativeCorollary74FusionCircuit_cnotCount]

@[simp]
theorem balancedCompleteMergedRelativeCorollary74Circuit_twoQubitCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.kindCount .arbitraryTwoQubit
        (balancedCompleteMergedRelativeCorollary74Circuit sourceWidth hwidth) = 0 := by
  rw [balancedCompleteMergedRelativeCorollary74Circuit,
    FusionCircuit.twoQubitCount_lower,
    balancedCompleteMergedRelativeCorollary74FusionCircuit_twoQubitCount]

@[simp]
theorem balancedCompleteMergedRelativeCorollary74Circuit_gateCount
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.gateCount
        (balancedCompleteMergedRelativeCorollary74Circuit sourceWidth hwidth) =
      48 * sourceWidth - 202 := by
  rw [balancedCompleteMergedRelativeCorollary74Circuit,
    FusionCircuit.gateCount_lower,
    balancedCompleteMergedRelativeCorollary74FusionCircuit_gateCount]

/--
The checked emitted circuit remains exactly two gates above the paper's printed
`48n-204`; this compares one named construction and is not a lower bound.
-/
theorem balancedCompleteMergedRelativeCorollary74Circuit_gateCount_eq_paper_add_two
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.gateCount
        (balancedCompleteMergedRelativeCorollary74Circuit sourceWidth hwidth) =
      (48 * sourceWidth - 204) + 2 := by
  rw [balancedCompleteMergedRelativeCorollary74Circuit_gateCount]
  omega

/-- The named certified output does not realize the printed constant. -/
theorem balancedCompleteMergedRelativeCorollary74Circuit_gateCount_ne_paper
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.gateCount
        (balancedCompleteMergedRelativeCorollary74Circuit sourceWidth hwidth) ≠
      48 * sourceWidth - 204 := by
  rw [balancedCompleteMergedRelativeCorollary74Circuit_gateCount]
  omega

@[simp]
theorem balancedCompleteMergedRelativeCorollary74Circuit_oneQubitCNOTCost
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.cost CostModel.oneQubitCNOT
        (balancedCompleteMergedRelativeCorollary74Circuit sourceWidth hwidth) =
      some (48 * sourceWidth - 202) := by
  rw [balancedCompleteMergedRelativeCorollary74Circuit,
    FusionCircuit.cost_lower,
    balancedCompleteMergedRelativeCorollary74FusionCircuit_oneQubitCNOTCost]

@[simp]
theorem balancedCompleteMergedRelativeCorollary74Circuit_arbitraryTwoQubitCost
    (sourceWidth : ℕ) (hwidth : 7 ≤ sourceWidth) :
    Circuit.cost CostModel.arbitraryTwoQubit
        (balancedCompleteMergedRelativeCorollary74Circuit sourceWidth hwidth) =
      some (48 * sourceWidth - 202) := by
  rw [balancedCompleteMergedRelativeCorollary74Circuit,
    FusionCircuit.cost_lower,
    balancedCompleteMergedRelativeCorollary74FusionCircuit_arbitraryTwoQubitCost]

end FourBlockLayout

end

end Barenco.MultiControl
