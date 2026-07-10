import Barenco.OneQubit.Certified

/-!
# Pauli-Y in the paper and semantic conventions

Barenco et al. display the usual Pauli-Y matrix while using row vectors acted on
from the right.  The library therefore keeps the displayed matrix as `paperY`
and defines its standard-column semantic translation `sigmaY` with
`Barenco.fromPaper`.  Unlike Pauli-X, Pauli-Y is antisymmetric, so this transpose
changes its sign: `sigmaY = -paperY`.

The raw matrices and certified gates are public runtime API.  Entry, orientation,
adjoint, determinant, involution, and certification declarations are public
proof-side API.  This leaf intentionally imports no circuit or resource layer.
-/

namespace Barenco.OneQubit

open Matrix

noncomputable section

/-! ## The paper's row-action display -/

/-- The paper's displayed Pauli-Y matrix `[[0,-i],[i,0]]`. -/
def paperY : QubitMatrix := matrix2 0 (-Complex.I) Complex.I 0

@[simp]
theorem paperY_false_false : paperY false false = 0 := by
  rfl

@[simp]
theorem paperY_false_true : paperY false true = -Complex.I := by
  rfl

@[simp]
theorem paperY_true_false : paperY true false = Complex.I := by
  rfl

@[simp]
theorem paperY_true_true : paperY true true = 0 := by
  rfl

/-- The displayed Pauli-Y matrix is self-adjoint. -/
@[simp]
theorem star_paperY : star paperY = paperY := by
  rw [paperY, star_matrix2]
  simp

/-- The displayed Pauli-Y matrix is an involution. -/
@[simp]
theorem paperY_sq : paperY * paperY = (1 : QubitMatrix) := by
  rw [paperY, matrix2_mul]
  norm_num

/-- The displayed Pauli-Y matrix has determinant minus one. -/
@[simp]
theorem paperY_det : Matrix.det paperY = -1 := by
  rw [paperY, matrix2_det]
  norm_num

/-- The paper's displayed Pauli-Y matrix is unitary. -/
theorem paperY_mem_unitaryGroup : paperY ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_paperY, paperY_sq]

/-- The paper's displayed Pauli-Y matrix with its unitary certificate. -/
def paperYUnitary : QubitUnitary := ⟨paperY, paperY_mem_unitaryGroup⟩

@[simp]
theorem coe_paperYUnitary : (paperYUnitary : QubitMatrix) = paperY := by
  rfl

@[simp]
theorem paperYUnitary_det : Matrix.det (paperYUnitary : QubitMatrix) = -1 := by
  exact paperY_det

/-! ## Standard-column semantic translation -/

/-- Standard-column Pauli-Y obtained by transposing the paper's row-action display. -/
def sigmaY : QubitMatrix := fromPaper paperY

/-- The semantic Pauli-Y is exactly the transpose of the paper display. -/
theorem sigmaY_eq_paperY_transpose : sigmaY = paperY.transpose := by
  rfl

/-- Explicit standard-column matrix `[[0,i],[-i,0]]`. -/
theorem sigmaY_eq_matrix2 : sigmaY = matrix2 0 Complex.I (-Complex.I) 0 := by
  rw [sigmaY, fromPaper, paperY, matrix2_transpose]

/-- Transposing the antisymmetric paper display changes its sign. -/
theorem sigmaY_eq_neg_paperY : sigmaY = -paperY := by
  rw [sigmaY_eq_matrix2, paperY]
  ext row col
  cases row <;> cases col <;> simp

@[simp]
theorem sigmaY_false_false : sigmaY false false = 0 := by
  rfl

@[simp]
theorem sigmaY_false_true : sigmaY false true = Complex.I := by
  rfl

@[simp]
theorem sigmaY_true_false : sigmaY true false = -Complex.I := by
  rfl

@[simp]
theorem sigmaY_true_true : sigmaY true true = 0 := by
  rfl

/-- The semantic Pauli-Y is self-adjoint. -/
@[simp]
theorem star_sigmaY : star sigmaY = sigmaY := by
  rw [sigmaY_eq_matrix2, star_matrix2]
  simp

/-- The semantic Pauli-Y is an involution. -/
@[simp]
theorem sigmaY_sq : sigmaY * sigmaY = (1 : QubitMatrix) := by
  rw [sigmaY_eq_matrix2, matrix2_mul]
  norm_num

/-- The semantic Pauli-Y has determinant minus one. -/
@[simp]
theorem sigmaY_det : Matrix.det sigmaY = -1 := by
  rw [sigmaY_eq_matrix2, matrix2_det]
  norm_num

/-- The standard-column Pauli-Y is unitary. -/
theorem sigmaY_mem_unitaryGroup : sigmaY ∈ Matrix.unitaryGroup Bool ℂ := by
  change fromPaper paperY ∈ Matrix.unitaryGroup Bool ℂ
  exact (fromPaper_mem_unitaryGroup_iff paperY).mpr paperY_mem_unitaryGroup

/-- Standard-column Pauli-Y with its unitary certificate. -/
def sigmaYUnitary : QubitUnitary := ⟨sigmaY, sigmaY_mem_unitaryGroup⟩

@[simp]
theorem coe_sigmaYUnitary : (sigmaYUnitary : QubitMatrix) = sigmaY := by
  rfl

@[simp]
theorem sigmaYUnitary_det : Matrix.det (sigmaYUnitary : QubitMatrix) = -1 := by
  exact sigmaY_det

end

end Barenco.OneQubit
