import Barenco.OneQubit.Matrix

/-!
# The parameterized A/B/C decomposition from Barenco et al., Lemma 4.3

This leaf proves the algebraic part of Lemma 4.3 for arbitrary real Euler
parameters.  It does not assume the existential Euler theorem: that implication
belongs in the later Euler leaf.

Names beginning with `paper` use the manuscript's row-action matrices and product
order.  Names beginning with `column` are their `fromPaper` transposes.  The
column-action theorems reverse products explicitly, so they are ready to feed into
the library's chronological evaluator without treating a paper diagram as a proof.
-/

namespace Barenco.OneQubit

open Matrix

noncomputable section

/-- The paper's three-factor special-unitary Euler expression. -/
def paperEuler (alpha theta beta : ℝ) : QubitMatrix :=
  paperRz alpha * paperRy theta * paperRz beta

/-- The first one-qubit factor in Lemma 4.3. -/
def paperA (alpha theta : ℝ) : QubitMatrix :=
  paperRz alpha * paperRy (theta / 2)

/-- The middle one-qubit factor in Lemma 4.3. -/
def paperB (alpha theta beta : ℝ) : QubitMatrix :=
  paperRy (-theta / 2) * paperRz (-(alpha + beta) / 2)

/-- The final one-qubit factor in Lemma 4.3. -/
def paperC (alpha beta : ℝ) : QubitMatrix :=
  paperRz ((beta - alpha) / 2)

/-- Conjugation by an involution distributes over a product. -/
theorem paperX_mul_product_mul_paperX (U V : QubitMatrix) :
    paperX * (U * V) * paperX =
      (paperX * U * paperX) * (paperX * V * paperX) := by
  calc
    paperX * (U * V) * paperX = paperX * U * V * paperX := by
      simp only [Matrix.mul_assoc]
    _ = paperX * U * 1 * V * paperX := by simp
    _ = paperX * U * (paperX * paperX) * V * paperX := by rw [paperX_sq]
    _ = (paperX * U * paperX) * (paperX * V * paperX) := by
      simp only [Matrix.mul_assoc]

/-- The parameterized factors cancel when the control is zero: `A B C = I`. -/
theorem paperA_mul_paperB_mul_paperC (alpha theta beta : ℝ) :
    paperA alpha theta * paperB alpha theta beta * paperC alpha beta =
      (1 : QubitMatrix) := by
  calc
    paperA alpha theta * paperB alpha theta beta * paperC alpha beta =
        paperRz alpha *
          ((paperRy (theta / 2) * paperRy (-theta / 2)) *
            (paperRz (-(alpha + beta) / 2) * paperRz ((beta - alpha) / 2))) := by
      simp only [paperA, paperB, paperC, Matrix.mul_assoc]
    _ = paperRz alpha *
          (paperRy (theta / 2 + -theta / 2) *
            paperRz (-(alpha + beta) / 2 + (beta - alpha) / 2)) := by
      rw [paperRy_mul, paperRz_mul]
    _ = paperRz alpha * (paperRy 0 * paperRz (-alpha)) := by
      congr 3 <;> ring
    _ = paperRz alpha * paperRz (-alpha) := by simp
    _ = paperRz (alpha + -alpha) := paperRz_mul _ _
    _ = 1 := by simp

/--
The parameterized active-control product is the Euler matrix:
`A X B X C = Rz(alpha) Ry(theta) Rz(beta)`.
-/
theorem paperA_mul_X_mul_paperB_mul_X_mul_paperC (alpha theta beta : ℝ) :
    paperA alpha theta * paperX * paperB alpha theta beta * paperX *
        paperC alpha beta = paperEuler alpha theta beta := by
  have hconj :
      paperX * paperB alpha theta beta * paperX =
        paperRy (theta / 2) * paperRz ((alpha + beta) / 2) := by
    calc
      paperX * paperB alpha theta beta * paperX =
          paperX *
              (paperRy (-theta / 2) * paperRz (-(alpha + beta) / 2)) *
            paperX := by rfl
      _ = (paperX * paperRy (-theta / 2) * paperX) *
            (paperX * paperRz (-(alpha + beta) / 2) * paperX) :=
        paperX_mul_product_mul_paperX _ _
      _ = paperRy (-(-theta / 2)) * paperRz (-(-(alpha + beta) / 2)) := by
        rw [paperX_mul_paperRy_mul_paperX, paperX_mul_paperRz_mul_paperX]
      _ = paperRy (theta / 2) * paperRz ((alpha + beta) / 2) := by
        congr 2 <;> ring
  calc
    paperA alpha theta * paperX * paperB alpha theta beta * paperX *
          paperC alpha beta =
        paperA alpha theta *
          (paperX * paperB alpha theta beta * paperX) * paperC alpha beta := by
      simp only [Matrix.mul_assoc]
    _ = (paperRz alpha * paperRy (theta / 2)) *
          (paperRy (theta / 2) * paperRz ((alpha + beta) / 2)) *
            paperRz ((beta - alpha) / 2) := by
      rw [hconj]
      rfl
    _ = paperRz alpha *
          (paperRy (theta / 2) * paperRy (theta / 2)) *
            (paperRz ((alpha + beta) / 2) * paperRz ((beta - alpha) / 2)) := by
      simp only [Matrix.mul_assoc]
    _ = paperRz alpha * paperRy theta * paperRz beta := by
      rw [paperRy_mul, paperRz_mul]
      congr 2 <;> ring
    _ = paperEuler alpha theta beta := rfl

/-! ## Standard-column translations -/

/-- Standard-column semantic transpose of the paper's `A`. -/
def columnA (alpha theta : ℝ) : QubitMatrix := fromPaper (paperA alpha theta)

/-- Standard-column semantic transpose of the paper's `B`. -/
def columnB (alpha theta beta : ℝ) : QubitMatrix := fromPaper (paperB alpha theta beta)

/-- Standard-column semantic transpose of the paper's `C`. -/
def columnC (alpha beta : ℝ) : QubitMatrix := fromPaper (paperC alpha beta)

/-- Standard-column transpose of the paper's Euler expression. -/
def columnEuler (alpha theta beta : ℝ) : QubitMatrix :=
  fromPaper (paperEuler alpha theta beta)

/-- Reversed standard-column product for the chronological sequence `A,B,C`. -/
theorem columnC_mul_columnB_mul_columnA (alpha theta beta : ℝ) :
    columnC alpha beta * columnB alpha theta beta * columnA alpha theta =
      (1 : QubitMatrix) := by
  calc
    columnC alpha beta * columnB alpha theta beta * columnA alpha theta =
        fromPaper
          (paperA alpha theta * paperB alpha theta beta * paperC alpha beta) := by
      simp [columnA, columnB, columnC, fromPaper_mul, Matrix.mul_assoc]
    _ = fromPaper (1 : QubitMatrix) := by
      rw [paperA_mul_paperB_mul_paperC]
    _ = 1 := fromPaper_one

/-- Reversed standard-column product for the chronological sequence `A,X,B,X,C`. -/
theorem columnC_mul_X_mul_columnB_mul_X_mul_columnA (alpha theta beta : ℝ) :
    columnC alpha beta * fromPaper paperX * columnB alpha theta beta *
        fromPaper paperX * columnA alpha theta = columnEuler alpha theta beta := by
  calc
    columnC alpha beta * fromPaper paperX * columnB alpha theta beta *
          fromPaper paperX * columnA alpha theta =
        fromPaper
          (paperA alpha theta * paperX * paperB alpha theta beta * paperX *
            paperC alpha beta) := by
      simp [columnA, columnB, columnC, fromPaper_mul, Matrix.mul_assoc]
    _ = fromPaper (paperEuler alpha theta beta) := by
      rw [paperA_mul_X_mul_paperB_mul_X_mul_paperC]
    _ = columnEuler alpha theta beta := rfl

end

end Barenco.OneQubit
