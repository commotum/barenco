import Barenco.MultiControl.Corollary74

/-!
# Diagnostic checks for corrected Corollary 7.4

This root-excluded leaf pins the three smallest balanced source widths, including
the repaired width-seven boundary.  It also contrasts the paper's original
`n = 9, m = 5` partition with the balanced partition used by the public
construction.  All checks are kernel proofs; the general semantic and resource
theorems remain in `Barenco.MultiControl.Corollary74`.
-/

namespace Barenco.MultiControl.Corollary74Examples

open Barenco
open FourBlockLayout

private theorem widthSeven : 7 ≤ 7 := by decide
private theorem widthEight : 7 ≤ 8 := by decide
private theorem widthNine : 7 ≤ 9 := by decide

/-! ## Balanced partition values -/

/-- Width seven is the smallest case, with one borrowed wire in each block. -/
theorem seven_tails :
    balancedLeftTail 7 = 0 ∧ balancedRightTail 7 = 0 := by
  decide

/-- Width eight assigns two borrowed wires to A and one to B. -/
theorem eight_tails :
    balancedLeftTail 8 = 1 ∧ balancedRightTail 8 = 0 := by
  decide

/-- Width nine uses the symmetric repaired partition. -/
theorem nine_tails :
    balancedLeftTail 9 = 1 ∧ balancedRightTail 9 = 1 := by
  decide

/-! ## Source-facing control cardinalities -/

theorem seven_controlCount :
    (balancedLayout 7 widthSeven).dataLayout.controlSet.card = 5 := by
  simpa using balancedLayout_dataControlCount 7 widthSeven

theorem eight_controlCount :
    (balancedLayout 8 widthEight).dataLayout.controlSet.card = 6 := by
  simpa using balancedLayout_dataControlCount 8 widthEight

theorem nine_controlCount :
    (balancedLayout 9 widthNine).dataLayout.controlSet.card = 7 := by
  simpa using balancedLayout_dataControlCount 9 widthNine

/-! ## Exact macro counts -/

theorem seven_counts :
    Circuit.gateCount (balancedCorollary74Circuit 7 widthSeven) = 16 ∧
      Circuit.kindCount .toffoli
        (balancedCorollary74Circuit 7 widthSeven) = 16 := by
  simp

theorem eight_counts :
    Circuit.gateCount (balancedCorollary74Circuit 8 widthEight) = 24 ∧
      Circuit.kindCount .toffoli
        (balancedCorollary74Circuit 8 widthEight) = 24 := by
  simp

theorem nine_counts :
    Circuit.gateCount (balancedCorollary74Circuit 9 widthNine) = 32 ∧
      Circuit.kindCount .toffoli
        (balancedCorollary74Circuit 9 widthNine) = 32 := by
  simp

/-! ## Balanced A never touches the final target -/

theorem seven_a_targetFree :
    (balancedLayout 7 widthSeven).targetWire ∉
      Circuit.touchedSupport
        ((balancedLayout 7 widthSeven).corollary74AImplementation
          (balancedLeftCapacity widthSeven)) :=
  balancedLayout_targetWire_not_mem_aImplementation_touchedSupport 7 widthSeven

theorem eight_a_targetFree :
    (balancedLayout 8 widthEight).targetWire ∉
      Circuit.touchedSupport
        ((balancedLayout 8 widthEight).corollary74AImplementation
          (balancedLeftCapacity widthEight)) :=
  balancedLayout_targetWire_not_mem_aImplementation_touchedSupport 8 widthEight

theorem nine_a_targetFree :
    (balancedLayout 9 widthNine).targetWire ∉
      Circuit.touchedSupport
        ((balancedLayout 9 widthNine).corollary74AImplementation
          (balancedLeftCapacity widthNine)) :=
  balancedLayout_targetWire_not_mem_aImplementation_touchedSupport 9 widthNine

/-! ## Original versus repaired nine-wire split -/

/--
For the paper's original `n = 9, m = 5` choice, the borrowed tails are `(2,0)`.
The third A borrow exhausts the two right controls and reaches the final target.
-/
theorem originalNineWire_aWorkspace_reaches_target :
    aBorrowSlotEmbedding (l := 3) (r := 1) (by decide) (2 : Fin 3) =
      (Sum.inr (Sum.inr 1) : FourBlockSlot 3 1) := by
  decide

/--
The repaired balanced tails are `(1,1)`.  Both A borrows remain in the enlarged
right-control group, so no borrowed A slot is the final target.
-/
theorem repairedNineWire_aWorkspace_avoids_target (borrowed : Fin 2) :
    aBorrowSlotEmbedding (l := 2) (r := 2) (by decide) borrowed ≠
      (Sum.inr (Sum.inr 1) : FourBlockSlot 2 2) := by
  exact aBorrowSlotEmbedding_ne_target (by decide) (by decide) borrowed

end Barenco.MultiControl.Corollary74Examples
