import Barenco.MultiControl.GrayAccumulator

/-!
# Diagnostic checks for the Section 7 Gray-code foundation

This module is intentionally excluded from the public root.  Its finite checks
pin the paper's width-three masks, toggles, pivots, CNOT chronology, signed parity
identity, and final restoration without replacing any general public proof.
-/

namespace Barenco.MultiControlExamples

open Barenco.MultiControl

/-- The displayed inclusion-exclusion identity, with all eight inputs checked. -/
theorem threeControl_signedParity_identity (x₁ x₂ x₃ : Bool) :
    boolInt x₁ + boolInt x₂ + boolInt x₃ -
          boolInt (x₁ + x₂) - boolInt (x₁ + x₃) - boolInt (x₂ + x₃) +
        boolInt (x₁ + x₂ + x₃) =
      if x₁ && x₂ && x₃ then (4 : ℤ) else 0 := by
  cases x₁ <;> cases x₂ <;> cases x₃ <;> decide

/-- Generic inclusion-exclusion specializes to exponent four on three controls. -/
example (bits : Fin 3 → Bool) :
    parityInclusionExclusionSum (Finset.univ : Finset (Fin 3)) bits =
      if (∀ control, bits control = true) then 4 else 0 := by
  simpa using parityInclusionExclusionSum_univ bits

/-- Exact nonempty bit-reversed Gray masks used in the four-bit diagram. -/
example :
    grayCode 3 = [{0}, {0, 1}, {1}, {1, 2}, {0, 1, 2}, {0, 2}, {2}] :=
  grayCode_three

/-- Exact changed positions between the seven parity masks. -/
example : grayToggles 3 = [1, 0, 2, 0, 1, 0] :=
  grayToggles_three

/-- Exact maximum-mask accumulator pivot at each controlled-root gate. -/
example : grayPivots 3 = [0, 1, 1, 2, 2, 2, 2] :=
  grayPivots_three

/-- Exact CNOT chronology reconstructed from the paper diagram. -/
example :
    grayCNOTEdges 3 = [(0, 1), (0, 1), (1, 2), (0, 2), (1, 2), (0, 2)] :=
  grayCNOTEdges_three

/-- The six displayed CNOTs restore all three controls for every basis input. -/
theorem threeControl_grayCNOTs_restore (input : Fin 3 → Bool) :
    runXorEdges (grayCNOTEdges 3) input = input := by
  rw [grayCNOTEdges_three]
  funext wire
  fin_cases wire <;>
    cases h₀ : input 0 <;>
    cases h₁ : input 1 <;>
    cases h₂ : input 2 <;>
    simp [runXorEdges, xorWireUpdate, h₀, h₁, h₂] <;>
    decide

end Barenco.MultiControlExamples
