import Barenco.MultiControl.Corollary74MergerResources

/-!
# Low-width Corollary 7.4 merger diagnostics

These regressions stay outside `Barenco.lean`. They check the smallest legal
width and the next two balanced partitions against the general literal-resource
theorems; they are not runtime branches in the construction.
-/

namespace Barenco.MultiControl

open Barenco.Optimization

noncomputable section

namespace FourBlockLayout

theorem balancedCompleteMergedRelativeCorollary74Circuit_width7_profile :
    Circuit.kindCount .oneQubit
        (balancedCompleteMergedRelativeCorollary74Circuit 7 (by omega)) = 66 ∧
      Circuit.kindCount .cnot
        (balancedCompleteMergedRelativeCorollary74Circuit 7 (by omega)) = 68 ∧
      Circuit.gateCount
        (balancedCompleteMergedRelativeCorollary74Circuit 7 (by omega)) = 134 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (balancedCompleteMergedRelativeCorollary74Circuit 7 (by omega)) = some 134 ∧
      Circuit.cost CostModel.arbitraryTwoQubit
        (balancedCompleteMergedRelativeCorollary74Circuit 7 (by omega)) = some 134 := by
  norm_num

theorem balancedCompleteMergedRelativeCorollary74Circuit_width8_profile :
    Circuit.kindCount .oneQubit
        (balancedCompleteMergedRelativeCorollary74Circuit 8 (by omega)) = 90 ∧
      Circuit.kindCount .cnot
        (balancedCompleteMergedRelativeCorollary74Circuit 8 (by omega)) = 92 ∧
      Circuit.gateCount
        (balancedCompleteMergedRelativeCorollary74Circuit 8 (by omega)) = 182 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (balancedCompleteMergedRelativeCorollary74Circuit 8 (by omega)) = some 182 ∧
      Circuit.cost CostModel.arbitraryTwoQubit
        (balancedCompleteMergedRelativeCorollary74Circuit 8 (by omega)) = some 182 := by
  norm_num

theorem balancedCompleteMergedRelativeCorollary74Circuit_width9_profile :
    Circuit.kindCount .oneQubit
        (balancedCompleteMergedRelativeCorollary74Circuit 9 (by omega)) = 114 ∧
      Circuit.kindCount .cnot
        (balancedCompleteMergedRelativeCorollary74Circuit 9 (by omega)) = 116 ∧
      Circuit.gateCount
        (balancedCompleteMergedRelativeCorollary74Circuit 9 (by omega)) = 230 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (balancedCompleteMergedRelativeCorollary74Circuit 9 (by omega)) = some 230 ∧
      Circuit.cost CostModel.arbitraryTwoQubit
        (balancedCompleteMergedRelativeCorollary74Circuit 9 (by omega)) = some 230 := by
  norm_num

theorem balancedCompleteMergedRelativeCorollary74Circuit_width7_exact :
    Circuit.eval
        (balancedCompleteMergedRelativeCorollary74Circuit 7 (by omega)) =
      positiveControlledUnitary
        (balancedLayout 7 (by omega)).targetWire
        (balancedLayout 7 (by omega)).dataLayout.controlSet pauliX := by
  exact eval_balancedCompleteMergedRelativeCorollary74Circuit 7 (by omega)

theorem balancedCompleteMergedRelativeCorollary74Circuit_width7_not_paper_count :
    Circuit.gateCount
        (balancedCompleteMergedRelativeCorollary74Circuit 7 (by omega)) ≠ 132 := by
  norm_num

end FourBlockLayout

end


end Barenco.MultiControl
