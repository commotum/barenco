import Barenco.OneQubit.Certified

/-!
# Exact complex Givens blocks

This module defines the two-dimensional unitary used by the finite-unitary
elimination in Stage 11. Given complex amplitudes `a` and `b`,
`givensUnitary a b` sends the column `(a,b)` to
`(0, sqrt (normSq a + normSq b))`. The zero pair is handled by the identity, so
the definition is total and later elimination code needs no pivoting side
condition.

The matrix uses the library's standard column-vector convention and Bool order
`false,true`. Thus the `false` coordinate is eliminated and the `true` coordinate
is the accumulator.
-/

namespace Barenco.Universality

open Matrix
open Barenco.OneQubit

noncomputable section

/-- Euclidean radius of a pair of complex amplitudes. -/
def givensRadius (a b : ℂ) : ℝ :=
  Real.sqrt (Complex.normSq a + Complex.normSq b)

theorem givensRadius_nonneg (a b : ℂ) : 0 ≤ givensRadius a b :=
  Real.sqrt_nonneg _

theorem givensRadius_sq (a b : ℂ) :
    givensRadius a b ^ 2 = Complex.normSq a + Complex.normSq b := by
  rw [givensRadius, Real.sq_sqrt]
  exact add_nonneg (Complex.normSq_nonneg a) (Complex.normSq_nonneg b)

theorem givensRadius_eq_zero_iff (a b : ℂ) :
    givensRadius a b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [givensRadius, Real.sqrt_eq_zero]
  · constructor
    · intro h
      have hab := (add_eq_zero_iff_of_nonneg
        (Complex.normSq_nonneg a) (Complex.normSq_nonneg b)).mp h
      exact ⟨Complex.normSq_eq_zero.mp hab.1, Complex.normSq_eq_zero.mp hab.2⟩
    · rintro ⟨rfl, rfl⟩
      simp
  · exact add_nonneg (Complex.normSq_nonneg a) (Complex.normSq_nonneg b)

/--
A convenient certified `SU(2)` block. The displayed norm equation is exactly the
unitarity obligation for `[[c,d],[-conj d,conj c]]`.
-/
def su2Block (c d : ℂ) (h : Complex.normSq c + Complex.normSq d = 1) :
    QubitUnitary := by
  refine ⟨matrix2 c d (-star d) (star c), ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, star_matrix2, matrix2_mul]
  apply Matrix.ext
  intro i j
  cases i <;> cases j
  · simp only [matrix2_false_false, Matrix.one_apply_eq]
    change c * (starRingEnd ℂ) c + d * (starRingEnd ℂ) d = 1
    rw [Complex.mul_conj, Complex.mul_conj]
    simpa using congrArg ((↑) : ℝ → ℂ) h
  · simp only [matrix2_false_true, Matrix.one_apply_ne (by decide : false ≠ true)]
    simp
    ring
  · simp only [matrix2_true_false, Matrix.one_apply_ne (by decide : true ≠ false)]
    simp
    ring
  · simp only [matrix2_true_true, Matrix.one_apply_eq]
    simp only [star_neg, star_star, neg_mul_neg]
    change (starRingEnd ℂ) d * d + (starRingEnd ℂ) c * c = 1
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
    simpa [add_comm] using congrArg ((↑) : ℝ → ℂ) h

theorem givensNormalized (a b : ℂ)
    (h : Complex.normSq a + Complex.normSq b ≠ 0) :
    Complex.normSq (b / (givensRadius a b : ℂ)) +
      Complex.normSq (-a / (givensRadius a b : ℂ)) = 1 := by
  let s := Complex.normSq a + Complex.normSq b
  have hs0 : 0 ≤ s := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h)
  have hr2 : givensRadius a b * givensRadius a b = s := by
    simpa [givensRadius, pow_two] using Real.sq_sqrt hs0
  rw [Complex.normSq_div, Complex.normSq_div, Complex.normSq_neg,
    Complex.normSq_ofReal, hr2]
  dsimp [s] at hr2 hspos ⊢
  field_simp
  ring

/--
The total certified Givens block. The first Bool coordinate is eliminated and the
second receives the nonnegative pair radius.
-/
def givensUnitary (a b : ℂ) : QubitUnitary :=
  if h : Complex.normSq a + Complex.normSq b = 0 then 1
  else su2Block (b / (givensRadius a b : ℂ))
    (-a / (givensRadius a b : ℂ)) (givensNormalized a b h)

/-- Raw matrix underlying `givensUnitary`. -/
def givensMatrix (a b : ℂ) : QubitMatrix :=
  givensUnitary a b

@[simp]
theorem coe_givensUnitary (a b : ℂ) :
    (givensUnitary a b : QubitMatrix) = givensMatrix a b := rfl

@[simp]
theorem givensUnitary_zero_zero : givensUnitary 0 0 = 1 := by
  simp [givensUnitary]

@[simp]
theorem givensMatrix_zero_zero : givensMatrix 0 0 = 1 := by
  simp [givensMatrix]

/-- The first output coordinate is exactly zero. -/
theorem givensUnitary_eliminates (a b : ℂ) :
    givensUnitary a b false false * a +
      givensUnitary a b false true * b = 0 := by
  rw [givensUnitary]
  split_ifs with h
  · have hab := (add_eq_zero_iff_of_nonneg
      (Complex.normSq_nonneg a) (Complex.normSq_nonneg b)).mp h
    have ha : a = 0 := Complex.normSq_eq_zero.mp hab.1
    have hb : b = 0 := Complex.normSq_eq_zero.mp hab.2
    simp [ha, hb]
  · simp only [su2Block, matrix2_false_false, matrix2_false_true]
    ring

/-- The second output coordinate is exactly the nonnegative pair radius. -/
theorem givensUnitary_accumulates (a b : ℂ) :
    givensUnitary a b true false * a +
      givensUnitary a b true true * b = (givensRadius a b : ℂ) := by
  rw [givensUnitary]
  split_ifs with h
  · have hab := (add_eq_zero_iff_of_nonneg
      (Complex.normSq_nonneg a) (Complex.normSq_nonneg b)).mp h
    have ha : a = 0 := Complex.normSq_eq_zero.mp hab.1
    have hb : b = 0 := Complex.normSq_eq_zero.mp hab.2
    simp [ha, hb, givensRadius]
  · simp only [su2Block, matrix2_true_false, matrix2_true_true]
    simp only [star_neg, star_div₀, Complex.star_def,
      Complex.conj_ofReal, neg_div, neg_neg]
    have hs0 : 0 ≤ Complex.normSq a + Complex.normSq b :=
      add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    have hr2 : givensRadius a b * givensRadius a b =
        Complex.normSq a + Complex.normSq b := by
      simpa [givensRadius, pow_two] using Real.sq_sqrt hs0
    have hr0 : givensRadius a b ≠ 0 := by
      rw [givensRadius, Real.sqrt_ne_zero']
      exact lt_of_le_of_ne hs0 (Ne.symm h)
    change ((starRingEnd ℂ) a / (givensRadius a b : ℂ)) * a +
      ((starRingEnd ℂ) b / (givensRadius a b : ℂ)) * b =
        (givensRadius a b : ℂ)
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
    rw [← Complex.ofReal_add, ← hr2, Complex.ofReal_mul]
    field_simp

end

end Barenco.Universality
