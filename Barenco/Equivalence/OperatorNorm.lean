import Barenco.Semantics
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# L² operator distance for finite gate matrices

The norm instance in this file is deliberately scoped. Algebraic gate and circuit
modules do not import it, so an unqualified matrix norm elsewhere cannot silently
change meaning.
-/

namespace Barenco

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Distance induced by the Euclidean/L² operator norm. -/
noncomputable def operatorDistance (A B : Matrix ι ι ℂ) : ℝ := ‖A - B‖

@[simp]
theorem operatorDistance_self (A : Matrix ι ι ℂ) : operatorDistance A A = 0 := by
  simp [operatorDistance]

theorem operatorDistance_nonneg (A B : Matrix ι ι ℂ) : 0 ≤ operatorDistance A B :=
  norm_nonneg _

@[simp]
theorem operatorDistance_eq_zero_iff (A B : Matrix ι ι ℂ) :
    operatorDistance A B = 0 ↔ A = B := by
  simp only [operatorDistance, norm_eq_zero, sub_eq_zero]

theorem operatorDistance_comm (A B : Matrix ι ι ℂ) :
    operatorDistance A B = operatorDistance B A := by
  simpa [operatorDistance] using norm_sub_rev A B

theorem operatorDistance_triangle (A B C : Matrix ι ι ℂ) :
    operatorDistance A C ≤ operatorDistance A B + operatorDistance B C := by
  simpa [operatorDistance, dist_eq_norm] using dist_triangle A B C

/-- Left multiplication is Lipschitz in the L² operator norm. -/
theorem operatorDistance_mul_left_le (A B L : Matrix ι ι ℂ) :
    operatorDistance (L * A) (L * B) ≤ ‖L‖ * operatorDistance A B := by
  rw [operatorDistance, operatorDistance, ← mul_sub]
  exact Matrix.l2_opNorm_mul L (A - B)

/-- Right multiplication is Lipschitz in the L² operator norm. -/
theorem operatorDistance_mul_right_le (A B R : Matrix ι ι ℂ) :
    operatorDistance (A * R) (B * R) ≤ operatorDistance A B * ‖R‖ := by
  rw [operatorDistance, operatorDistance, ← sub_mul]
  exact Matrix.l2_opNorm_mul (A - B) R

/-- Left multiplication by a certified unitary preserves operator distance. -/
@[simp]
theorem operatorDistance_unitary_mul_left (U : Matrix.unitaryGroup ι ℂ)
    (A B : Matrix ι ι ℂ) :
    operatorDistance ((U : Matrix ι ι ℂ) * A) ((U : Matrix ι ι ℂ) * B) =
      operatorDistance A B := by
  rw [operatorDistance, operatorDistance, ← mul_sub]
  exact CStarRing.norm_coe_unitary_mul U (A - B)

/-- Right multiplication by a certified unitary preserves operator distance. -/
@[simp]
theorem operatorDistance_unitary_mul_right (A B : Matrix ι ι ℂ)
    (U : Matrix.unitaryGroup ι ℂ) :
    operatorDistance (A * (U : Matrix ι ι ℂ)) (B * (U : Matrix ι ι ℂ)) =
      operatorDistance A B := by
  rw [operatorDistance, operatorDistance, ← sub_mul]
  exact CStarRing.norm_mul_coe_unitary (A - B) U

/-- Errors of two sequential unitary factors add in operator distance. -/
theorem operatorDistance_mul_unitary_le
    (A A' B B' : Matrix.unitaryGroup ι ℂ) :
    operatorDistance
        ((A : Matrix ι ι ℂ) * (B : Matrix ι ι ℂ))
        ((A' : Matrix ι ι ℂ) * (B' : Matrix ι ι ℂ)) ≤
      operatorDistance (A : Matrix ι ι ℂ) (A' : Matrix ι ι ℂ) +
        operatorDistance (B : Matrix ι ι ℂ) (B' : Matrix ι ι ℂ) := by
  calc
    operatorDistance
          ((A : Matrix ι ι ℂ) * (B : Matrix ι ι ℂ))
          ((A' : Matrix ι ι ℂ) * (B' : Matrix ι ι ℂ)) ≤
        operatorDistance
            ((A : Matrix ι ι ℂ) * (B : Matrix ι ι ℂ))
            ((A : Matrix ι ι ℂ) * (B' : Matrix ι ι ℂ)) +
          operatorDistance
            ((A : Matrix ι ι ℂ) * (B' : Matrix ι ι ℂ))
            ((A' : Matrix ι ι ℂ) * (B' : Matrix ι ι ℂ)) :=
      operatorDistance_triangle _ _ _
    _ = operatorDistance (B : Matrix ι ι ℂ) (B' : Matrix ι ι ℂ) +
        operatorDistance (A : Matrix ι ι ℂ) (A' : Matrix ι ι ℂ) := by
      rw [operatorDistance_unitary_mul_left,
        operatorDistance_unitary_mul_right]
    _ = operatorDistance (A : Matrix ι ι ℂ) (A' : Matrix ι ι ℂ) +
        operatorDistance (B : Matrix ι ι ℂ) (B' : Matrix ι ι ℂ) := add_comm _ _

/--
Operator distance controls the Euclidean norm of the output-state difference.
The explicit `EuclideanSpace.equiv` wrapper is mathlib's bridge from raw amplitude
functions to the L² normed space.
-/
theorem operatorDistance_action_le (A B : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) :
    ‖(EuclideanSpace.equiv ι ℂ).symm ((A - B) *ᵥ ψ)‖ ≤
      operatorDistance A B * ‖ψ‖ := by
  simpa [operatorDistance] using Matrix.l2_opNorm_mulVec (A - B) ψ

/-- Any two certified unitaries are at operator distance at most two. -/
theorem operatorDistance_unitary_le_two [Nonempty ι]
    (U V : Matrix.unitaryGroup ι ℂ) :
    operatorDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) ≤ 2 := by
  calc
    operatorDistance (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) ≤
        ‖(U : Matrix ι ι ℂ)‖ + ‖(V : Matrix ι ι ℂ)‖ := by
      simpa [operatorDistance] using norm_sub_le (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ)
    _ = 2 := by
      rw [CStarRing.norm_coe_unitary, CStarRing.norm_coe_unitary]
      norm_num

end Barenco
