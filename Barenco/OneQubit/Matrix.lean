import Barenco.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Explicit one-qubit matrices from Barenco et al., Section 4

This file defines the four matrices displayed in Section 4 of *Elementary Gates
for Quantum Computation* and proves the six identities in Lemma 4.2.

The definitions named `paper...` are deliberately the paper's raw displays. The
paper acts on row vectors from the right, whereas the semantic library acts on
column vectors from the left. Consequently these matrices are not yet semantic
gates: downstream code must translate them with `Barenco.fromPaper`. In particular,
that translation transposes `paperRy` and reverses products.

The public runtime declarations in this leaf are `matrix2`, `cis`, `paperRy`,
`paperRz`, `paperPhase`, and `paperX`. All other declarations are public proof-side
facts. There are no certified gates or circuit declarations here.
-/

namespace Barenco.OneQubit

open Matrix

noncomputable section

/-! ## Explicit two-by-two matrices -/

/--
The Bool-indexed matrix `[[a,b],[c,d]]`, with rows and columns ordered
`false,true`.
-/
def matrix2 (a b c d : ℂ) : QubitMatrix :=
  Matrix.reindex finTwoEquiv finTwoEquiv !![a, b; c, d]

@[simp]
theorem matrix2_false_false (a b c d : ℂ) : matrix2 a b c d false false = a := by
  rfl

@[simp]
theorem matrix2_false_true (a b c d : ℂ) : matrix2 a b c d false true = b := by
  rfl

@[simp]
theorem matrix2_true_false (a b c d : ℂ) : matrix2 a b c d true false = c := by
  rfl

@[simp]
theorem matrix2_true_true (a b c d : ℂ) : matrix2 a b c d true true = d := by
  rfl

/-- Multiplication of explicit Bool-indexed two-by-two matrices. -/
theorem matrix2_mul (a b c d e f g h : ℂ) :
    matrix2 a b c d * matrix2 e f g h =
      matrix2 (a * e + b * g) (a * f + b * h)
        (c * e + d * g) (c * f + d * h) := by
  change Matrix.reindexAlgEquiv ℂ ℂ finTwoEquiv !![a, b; c, d] *
      Matrix.reindexAlgEquiv ℂ ℂ finTwoEquiv !![e, f; g, h] =
    Matrix.reindexAlgEquiv ℂ ℂ finTwoEquiv
      !![a * e + b * g, a * f + b * h; c * e + d * g, c * f + d * h]
  rw [← map_mul]
  exact congrArg (Matrix.reindexAlgEquiv ℂ ℂ finTwoEquiv) (Matrix.mulᵣ_eq _ _).symm

/-- Determinant of an explicit Bool-indexed two-by-two matrix. -/
theorem matrix2_det (a b c d : ℂ) :
    Matrix.det (matrix2 a b c d) = a * d - b * c := by
  rw [matrix2, Matrix.det_reindex_self, Matrix.det_fin_two_of]

@[simp]
theorem matrix2_one : matrix2 1 0 0 1 = (1 : QubitMatrix) := by
  ext i j
  cases i <;> cases j <;> rfl

/-- Transpose of an explicit two-by-two matrix. -/
theorem matrix2_transpose (a b c d : ℂ) :
    (matrix2 a b c d).transpose = matrix2 a c b d := by
  ext i j
  cases i <;> cases j <;> rfl

/-- Conjugate transpose (matrix `star`) of an explicit two-by-two matrix. -/
theorem star_matrix2 (a b c d : ℂ) :
    star (matrix2 a b c d) = matrix2 (star a) (star c) (star b) (star d) := by
  ext i j
  cases i <;> cases j <;> rfl

/-! ## Scalar phases -/

/-- The unit complex scalar `exp(x i)` for a real angle `x`. -/
def cis (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

/-- Addition of real angles becomes multiplication of their phases. -/
theorem cis_add (x y : ℝ) : cis (x + y) = cis x * cis y := by
  simp only [cis, Complex.ofReal_add, add_mul, Complex.exp_add]

/-- Negating an angle inverts its phase. -/
theorem cis_neg (x : ℝ) : cis (-x) = (cis x)⁻¹ := by
  simp [cis, Complex.exp_neg]

@[simp]
theorem cis_zero : cis 0 = 1 := by
  simp [cis]

/-- Complex conjugation negates the real phase angle. -/
theorem star_cis (x : ℝ) : star (cis x) = cis (-x) := by
  rw [cis, cis, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

/-! ## The paper's raw row-action displays -/

/--
The displayed `R_y(theta)` from Section 4:
`[[cos(theta/2), sin(theta/2)],[-sin(theta/2), cos(theta/2)]]`.
-/
def paperRy (theta : ℝ) : QubitMatrix :=
  matrix2 (Real.cos (theta / 2)) (Real.sin (theta / 2))
    (-Real.sin (theta / 2)) (Real.cos (theta / 2))

/--
The displayed `R_z(alpha)` from Section 4:
`diag(exp(i alpha/2), exp(-i alpha/2))`.
-/
def paperRz (alpha : ℝ) : QubitMatrix :=
  matrix2 (cis (alpha / 2)) 0 0 (cis (-alpha / 2))

/-- The displayed scalar phase `Ph(delta) = exp(i delta) I` from Section 4. -/
def paperPhase (delta : ℝ) : QubitMatrix :=
  matrix2 (cis delta) 0 0 (cis delta)

/-- The displayed Pauli-X matrix `[[0,1],[1,0]]` from Section 4. -/
def paperX : QubitMatrix := matrix2 0 1 1 0

/-! ### Entry formulas -/

@[simp]
theorem paperRy_false_false (theta : ℝ) :
    paperRy theta false false = Real.cos (theta / 2) := by
  rfl

@[simp]
theorem paperRy_false_true (theta : ℝ) :
    paperRy theta false true = Real.sin (theta / 2) := by
  rfl

@[simp]
theorem paperRy_true_false (theta : ℝ) :
    paperRy theta true false = -Real.sin (theta / 2) := by
  rfl

@[simp]
theorem paperRy_true_true (theta : ℝ) :
    paperRy theta true true = Real.cos (theta / 2) := by
  rfl

@[simp]
theorem paperRz_false_false (alpha : ℝ) : paperRz alpha false false = cis (alpha / 2) := by
  rfl

@[simp]
theorem paperRz_false_true (alpha : ℝ) : paperRz alpha false true = 0 := by
  rfl

@[simp]
theorem paperRz_true_false (alpha : ℝ) : paperRz alpha true false = 0 := by
  rfl

@[simp]
theorem paperRz_true_true (alpha : ℝ) : paperRz alpha true true = cis (-alpha / 2) := by
  rfl

@[simp]
theorem paperPhase_false_false (delta : ℝ) : paperPhase delta false false = cis delta := by
  rfl

@[simp]
theorem paperPhase_false_true (delta : ℝ) : paperPhase delta false true = 0 := by
  rfl

@[simp]
theorem paperPhase_true_false (delta : ℝ) : paperPhase delta true false = 0 := by
  rfl

@[simp]
theorem paperPhase_true_true (delta : ℝ) : paperPhase delta true true = cis delta := by
  rfl

@[simp]
theorem paperX_false_false : paperX false false = 0 := by
  rfl

@[simp]
theorem paperX_false_true : paperX false true = 1 := by
  rfl

@[simp]
theorem paperX_true_false : paperX true false = 1 := by
  rfl

@[simp]
theorem paperX_true_true : paperX true true = 0 := by
  rfl

/-! ### Zero angles, adjoints, and determinants -/

@[simp]
theorem paperRy_zero : paperRy 0 = (1 : QubitMatrix) := by
  simp [paperRy, matrix2_one]

@[simp]
theorem paperRz_zero : paperRz 0 = (1 : QubitMatrix) := by
  simp [paperRz, matrix2_one]

@[simp]
theorem paperPhase_zero : paperPhase 0 = (1 : QubitMatrix) := by
  simp [paperPhase, matrix2_one]

/-- The adjoint of the paper's Y rotation negates its angle. -/
theorem star_paperRy (theta : ℝ) : star (paperRy theta) = paperRy (-theta) := by
  rw [paperRy, star_matrix2, paperRy]
  simp only [Complex.star_def, Complex.conj_ofReal, map_neg]
  congr 1
  · norm_cast
    rw [show (-theta) / 2 = -(theta / 2) by ring, Real.cos_neg]
  · norm_cast
    rw [show (-theta) / 2 = -(theta / 2) by ring, Real.sin_neg]
  · norm_cast
    rw [show (-theta) / 2 = -(theta / 2) by ring, Real.sin_neg]
    ring
  · norm_cast
    rw [show (-theta) / 2 = -(theta / 2) by ring, Real.cos_neg]

/-- The adjoint of the paper's Z rotation negates its angle. -/
theorem star_paperRz (alpha : ℝ) : star (paperRz alpha) = paperRz (-alpha) := by
  rw [paperRz, star_matrix2, paperRz]
  simp only [star_cis, star_zero]
  have h₁ : -(alpha / 2) = -alpha / 2 := by ring
  have h₂ : -(-alpha / 2) = - -alpha / 2 := by ring
  rw [h₁, h₂]

/-- The adjoint of the paper's scalar phase negates its angle. -/
theorem star_paperPhase (delta : ℝ) : star (paperPhase delta) = paperPhase (-delta) := by
  rw [paperPhase, star_matrix2, paperPhase]
  simp only [star_cis, star_zero]

/-- Pauli-X is self-adjoint. -/
@[simp]
theorem star_paperX : star paperX = paperX := by
  rw [paperX, star_matrix2]
  norm_num

/-- The scalar phase has determinant `exp(2 i delta)`, not `exp(i delta)`. -/
theorem paperPhase_det (delta : ℝ) : Matrix.det (paperPhase delta) = cis (2 * delta) := by
  rw [paperPhase, matrix2_det]
  simp only [mul_zero, sub_zero]
  rw [← cis_add]
  congr 1
  ring

/-- Every displayed Z rotation has determinant one. -/
@[simp]
theorem paperRz_det (alpha : ℝ) : Matrix.det (paperRz alpha) = 1 := by
  rw [paperRz, matrix2_det]
  simp only [mul_zero, sub_zero]
  calc
    cis (alpha / 2) * cis (-alpha / 2) = cis (alpha / 2 + -alpha / 2) :=
      (cis_add _ _).symm
    _ = cis 0 := by
      congr 1
      ring
    _ = 1 := cis_zero

/-- Every displayed Y rotation has determinant one. -/
@[simp]
theorem paperRy_det (theta : ℝ) : Matrix.det (paperRy theta) = 1 := by
  rw [paperRy, matrix2_det]
  norm_cast
  nlinarith [Real.sin_sq_add_cos_sq (theta / 2)]

/-- Pauli-X has determinant minus one. -/
@[simp]
theorem paperX_det : Matrix.det paperX = -1 := by
  rw [paperX, matrix2_det]
  norm_num

/-! ## Barenco et al., Lemma 4.2 -/

/-- Lemma 4.2(i): Y rotations add their angles under multiplication. -/
theorem paperRy_mul (theta₁ theta₂ : ℝ) :
    paperRy theta₁ * paperRy theta₂ = paperRy (theta₁ + theta₂) := by
  rw [paperRy, paperRy, paperRy, matrix2_mul]
  congr 1
  · norm_cast
    rw [show (theta₁ + theta₂) / 2 = theta₁ / 2 + theta₂ / 2 by ring, Real.cos_add]
    ring
  · norm_cast
    rw [show (theta₁ + theta₂) / 2 = theta₁ / 2 + theta₂ / 2 by ring, Real.sin_add]
    ring
  · norm_cast
    rw [show (theta₁ + theta₂) / 2 = theta₁ / 2 + theta₂ / 2 by ring, Real.sin_add]
    ring
  · norm_cast
    rw [show (theta₁ + theta₂) / 2 = theta₁ / 2 + theta₂ / 2 by ring, Real.cos_add]
    ring

/-- Lemma 4.2(ii): Z rotations add their angles under multiplication. -/
theorem paperRz_mul (alpha₁ alpha₂ : ℝ) :
    paperRz alpha₁ * paperRz alpha₂ = paperRz (alpha₁ + alpha₂) := by
  rw [paperRz, paperRz, paperRz, matrix2_mul]
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [← cis_add, ← cis_add]
  congr 2 <;> ring

/-- Lemma 4.2(iii): scalar phases add their angles under multiplication. -/
theorem paperPhase_mul (delta₁ delta₂ : ℝ) :
    paperPhase delta₁ * paperPhase delta₂ = paperPhase (delta₁ + delta₂) := by
  rw [paperPhase, paperPhase, paperPhase, matrix2_mul]
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [← cis_add]

/-- Lemma 4.2(iv): Pauli-X is an involution. -/
theorem paperX_sq : paperX * paperX = (1 : QubitMatrix) := by
  rw [paperX, matrix2_mul]
  norm_num

/-- Lemma 4.2(v): conjugation by Pauli-X negates a Y-rotation angle. -/
theorem paperX_mul_paperRy_mul_paperX (theta : ℝ) :
    paperX * paperRy theta * paperX = paperRy (-theta) := by
  rw [paperX, paperRy, matrix2_mul, matrix2_mul, paperRy]
  simp only [zero_mul, one_mul, add_zero, mul_zero, mul_one, zero_add]
  congr 1
  · norm_cast
    rw [show (-theta) / 2 = -(theta / 2) by ring, Real.cos_neg]
  · norm_cast
    rw [show (-theta) / 2 = -(theta / 2) by ring, Real.sin_neg]
  · norm_cast
    rw [show (-theta) / 2 = -(theta / 2) by ring, Real.sin_neg]
    ring
  · norm_cast
    rw [show (-theta) / 2 = -(theta / 2) by ring, Real.cos_neg]

/-- Lemma 4.2(vi): conjugation by Pauli-X negates a Z-rotation angle. -/
theorem paperX_mul_paperRz_mul_paperX (alpha : ℝ) :
    paperX * paperRz alpha * paperX = paperRz (-alpha) := by
  rw [paperX, paperRz, matrix2_mul, matrix2_mul, paperRz]
  simp only [zero_mul, one_mul, add_zero, mul_zero, mul_one, zero_add]
  have h : alpha / 2 = - -alpha / 2 := by ring
  rw [h]

end


end Barenco.OneQubit
