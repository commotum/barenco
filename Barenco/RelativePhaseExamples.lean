import Barenco.MultiControl.RelativePhase

/-!
# Diagnostic checks for contextual relative-phase Corollary 7.4

This root-excluded leaf specializes the exact contextual semantics and the
mixed-syntax accounting to the three smallest balanced widths.  The retained
`.toffoli` nodes are the four exact final-target occurrences; the other
occurrences are the seven-node relative-phase implementation.

All statements are kernel-checked consequences of the general arbitrary-width
theorems in `Barenco.MultiControl.RelativePhase`.
-/

namespace Barenco.MultiControl.RelativePhaseExamples

open Barenco
open FourBlockLayout

private theorem widthSeven : 7 ≤ 7 := by decide
private theorem widthEight : 7 ≤ 8 := by decide
private theorem widthNine : 7 ≤ 9 := by decide

/-! ## Exact evaluator specializations -/

theorem seven_eval :
    Circuit.eval (balancedRelativeCorollary74Circuit 7 widthSeven) =
      positiveControlledUnitary
        (balancedLayout 7 widthSeven).targetWire
        (balancedLayout 7 widthSeven).dataLayout.controlSet pauliX := by
  exact eval_balancedRelativeCorollary74Circuit 7 widthSeven

theorem eight_eval :
    Circuit.eval (balancedRelativeCorollary74Circuit 8 widthEight) =
      positiveControlledUnitary
        (balancedLayout 8 widthEight).targetWire
        (balancedLayout 8 widthEight).dataLayout.controlSet pauliX := by
  exact eval_balancedRelativeCorollary74Circuit 8 widthEight

theorem nine_eval :
    Circuit.eval (balancedRelativeCorollary74Circuit 9 widthNine) =
      positiveControlledUnitary
        (balancedLayout 9 widthNine).targetWire
        (balancedLayout 9 widthNine).dataLayout.controlSet pauliX := by
  exact eval_balancedRelativeCorollary74Circuit 9 widthNine

/-! ## Relative and exact occurrence profiles -/

/-- Width seven retains four exact Toffolis and expands twelve relative ones. -/
theorem seven_occurrenceProfile :
    Circuit.kindCount .toffoli
        (balancedRelativeCorollary74Circuit 7 widthSeven) = 4 ∧
      relativeCorollary74RelativeOccurrenceCount
        (balancedLeftTail 7) (balancedRightTail 7) = 12 := by
  constructor
  · exact balancedRelativeCorollary74Circuit_toffoliCount 7 widthSeven
  · simpa using
      balancedRelativeCorollary74RelativeOccurrenceCount 7 widthSeven

/-- Width eight retains four exact Toffolis and expands twenty relative ones. -/
theorem eight_occurrenceProfile :
    Circuit.kindCount .toffoli
        (balancedRelativeCorollary74Circuit 8 widthEight) = 4 ∧
      relativeCorollary74RelativeOccurrenceCount
        (balancedLeftTail 8) (balancedRightTail 8) = 20 := by
  constructor
  · exact balancedRelativeCorollary74Circuit_toffoliCount 8 widthEight
  · simpa using
      balancedRelativeCorollary74RelativeOccurrenceCount 8 widthEight

/-- Width nine retains four exact Toffolis and expands twenty-eight relative ones. -/
theorem nine_occurrenceProfile :
    Circuit.kindCount .toffoli
        (balancedRelativeCorollary74Circuit 9 widthNine) = 4 ∧
      relativeCorollary74RelativeOccurrenceCount
        (balancedLeftTail 9) (balancedRightTail 9) = 28 := by
  constructor
  · exact balancedRelativeCorollary74Circuit_toffoliCount 9 widthNine
  · simpa using
      balancedRelativeCorollary74RelativeOccurrenceCount 9 widthNine

/-! ## Mixed one-qubit/CNOT syntax profiles -/

theorem seven_mixedProfile :
    Circuit.kindCount .oneQubit
        (balancedRelativeCorollary74Circuit 7 widthSeven) = 48 ∧
      Circuit.kindCount .cnot
        (balancedRelativeCorollary74Circuit 7 widthSeven) = 36 ∧
      Circuit.gateCount
        (balancedRelativeCorollary74Circuit 7 widthSeven) = 88 := by
  constructor
  · simp
  · constructor <;> simp

theorem eight_mixedProfile :
    Circuit.kindCount .oneQubit
        (balancedRelativeCorollary74Circuit 8 widthEight) = 80 ∧
      Circuit.kindCount .cnot
        (balancedRelativeCorollary74Circuit 8 widthEight) = 60 ∧
      Circuit.gateCount
        (balancedRelativeCorollary74Circuit 8 widthEight) = 144 := by
  constructor
  · simp
  · constructor <;> simp

theorem nine_mixedProfile :
    Circuit.kindCount .oneQubit
        (balancedRelativeCorollary74Circuit 9 widthNine) = 112 ∧
      Circuit.kindCount .cnot
        (balancedRelativeCorollary74Circuit 9 widthNine) = 84 ∧
      Circuit.gateCount
        (balancedRelativeCorollary74Circuit 9 widthNine) = 200 := by
  constructor
  · simp
  · constructor <;> simp

/-! ## Smallest supported boundary -/

/--
At the `sourceWidth = 7` boundary both balanced tails are zero, the five data
controls are present, and the mixed syntax still has the four exact macros that
make its one-qubit+CNOT cost intentionally undefined before exact expansion.
-/
theorem seven_boundary :
    balancedLeftTail 7 = 0 ∧
      balancedRightTail 7 = 0 ∧
      (balancedLayout 7 widthSeven).dataLayout.controlSet.card = 5 ∧
      Circuit.registerWidth
        (balancedRelativeCorollary74Circuit 7 widthSeven) = 7 ∧
      Circuit.cost CostModel.oneQubitCNOT
        (balancedRelativeCorollary74Circuit 7 widthSeven) = none := by
  constructor
  · decide
  · constructor
    · decide
    · constructor
      · simpa using balancedLayout_dataControlCount 7 widthSeven
      · constructor
        · rfl
        · exact balancedRelativeCorollary74Circuit_oneQubitCNOTCost 7 widthSeven

end Barenco.MultiControl.RelativePhaseExamples
