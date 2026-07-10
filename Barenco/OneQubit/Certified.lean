import Barenco.OneQubit.Matrix

/-!
# Certified and semantic one-qubit gates

This leaf certifies the raw Section 4 displays from `Barenco.OneQubit.Matrix` and
then translates them to the library's standard column-vector convention. The
semantic matrices `ry`, `rz`, `phaseShift`, and `sigmaX` are explicitly defined as
`Barenco.fromPaper` of the corresponding row-action display. Thus `ry theta` is
the transpose of the paper's displayed `R_y(theta)`; the other three displays are
symmetric.

The matrix and certified-gate definitions are public runtime API. Membership,
entry, bridge, determinant, adjoint, and Lemma 4.2 declarations are public
proof-side API. This file intentionally imports no circuit, cost, approximation,
or controlled-gate layer.
-/

namespace Barenco

/-- Certified determinant-one one-qubit unitaries. -/
abbrev QubitSpecialUnitary := Matrix.specialUnitaryGroup Bool ℂ

namespace OneQubit

noncomputable section

/-! ## Certification of the paper's row-action displays -/

/-- The paper's displayed Y rotation is unitary for every real angle. -/
theorem paperRy_mem_unitaryGroup (theta : ℝ) :
    paperRy theta ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_paperRy, paperRy_mul]
  simp

/-- The paper's displayed Z rotation is unitary for every real angle. -/
theorem paperRz_mem_unitaryGroup (alpha : ℝ) :
    paperRz alpha ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_paperRz, paperRz_mul]
  simp

/-- The paper's displayed scalar phase is unitary for every real angle. -/
theorem paperPhase_mem_unitaryGroup (delta : ℝ) :
    paperPhase delta ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_paperPhase, paperPhase_mul]
  simp

/-- The paper's displayed Pauli-X matrix is unitary. -/
theorem paperX_mem_unitaryGroup : paperX ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_paperX, paperX_sq]

/-- The displayed Y rotation is special unitary. -/
theorem paperRy_mem_specialUnitaryGroup (theta : ℝ) :
    paperRy theta ∈ Matrix.specialUnitaryGroup Bool ℂ := by
  exact Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨paperRy_mem_unitaryGroup theta, paperRy_det theta⟩

/-- The displayed Z rotation is special unitary. -/
theorem paperRz_mem_specialUnitaryGroup (alpha : ℝ) :
    paperRz alpha ∈ Matrix.specialUnitaryGroup Bool ℂ := by
  exact Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨paperRz_mem_unitaryGroup alpha, paperRz_det alpha⟩

/-- The paper's displayed Y rotation with its special-unitary certificate. -/
def paperRySpecialUnitary (theta : ℝ) : QubitSpecialUnitary :=
  ⟨paperRy theta, paperRy_mem_specialUnitaryGroup theta⟩

/-- The paper's displayed Z rotation with its special-unitary certificate. -/
def paperRzSpecialUnitary (alpha : ℝ) : QubitSpecialUnitary :=
  ⟨paperRz alpha, paperRz_mem_specialUnitaryGroup alpha⟩

/-- The paper's displayed scalar phase with its unitary certificate. -/
def paperPhaseUnitary (delta : ℝ) : QubitUnitary :=
  ⟨paperPhase delta, paperPhase_mem_unitaryGroup delta⟩

/-- The paper's displayed Pauli-X matrix with its unitary certificate. -/
def paperXUnitary : QubitUnitary := ⟨paperX, paperX_mem_unitaryGroup⟩

@[simp]
theorem coe_paperRySpecialUnitary (theta : ℝ) :
    (paperRySpecialUnitary theta : QubitMatrix) = paperRy theta := by
  rfl

@[simp]
theorem coe_paperRzSpecialUnitary (alpha : ℝ) :
    (paperRzSpecialUnitary alpha : QubitMatrix) = paperRz alpha := by
  rfl

@[simp]
theorem coe_paperPhaseUnitary (delta : ℝ) :
    (paperPhaseUnitary delta : QubitMatrix) = paperPhase delta := by
  rfl

@[simp]
theorem coe_paperXUnitary : (paperXUnitary : QubitMatrix) = paperX := by
  rfl

/-- The certified paper Pauli-X still has determinant minus one. -/
@[simp]
theorem paperXUnitary_det : Matrix.det (paperXUnitary : QubitMatrix) = -1 := by
  exact paperX_det

/-! ## Standard-column semantic matrices and orientation bridges -/

/-- Standard-column Y rotation obtained from the paper's row-action display. -/
def ry (theta : ℝ) : QubitMatrix := fromPaper (paperRy theta)

/-- Standard-column Z rotation obtained from the paper's row-action display. -/
def rz (alpha : ℝ) : QubitMatrix := fromPaper (paperRz alpha)

/-- Standard-column scalar phase obtained from the paper's row-action display. -/
def phaseShift (delta : ℝ) : QubitMatrix := fromPaper (paperPhase delta)

/-- Standard-column Pauli-X obtained from the paper's row-action display. -/
def sigmaX : QubitMatrix := fromPaper paperX

/-- The semantic Y rotation is exactly the transpose of the paper display. -/
theorem ry_eq_paperRy_transpose (theta : ℝ) :
    ry theta = (paperRy theta).transpose := by
  rfl

/-- The semantic Z rotation is exactly the transpose of the paper display. -/
theorem rz_eq_paperRz_transpose (alpha : ℝ) :
    rz alpha = (paperRz alpha).transpose := by
  rfl

/-- The semantic scalar phase is exactly the transpose of the paper display. -/
theorem phaseShift_eq_paperPhase_transpose (delta : ℝ) :
    phaseShift delta = (paperPhase delta).transpose := by
  rfl

/-- The semantic Pauli-X is exactly the transpose of the paper display. -/
theorem sigmaX_eq_paperX_transpose : sigmaX = paperX.transpose := by
  rfl

/-- Transposition changes the sign convention of the paper's displayed Y rotation. -/
theorem ry_eq_paperRy_neg (theta : ℝ) : ry theta = paperRy (-theta) := by
  rw [ry, fromPaper, paperRy, matrix2_transpose, paperRy]
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

/-- The paper's displayed Z rotation is symmetric. -/
theorem rz_eq_paperRz (alpha : ℝ) : rz alpha = paperRz alpha := by
  rw [rz, fromPaper, paperRz, matrix2_transpose]

/-- The paper's displayed scalar phase is symmetric. -/
theorem phaseShift_eq_paperPhase (delta : ℝ) : phaseShift delta = paperPhase delta := by
  rw [phaseShift, fromPaper, paperPhase, matrix2_transpose]

/-- The paper's displayed Pauli-X matrix is symmetric. -/
theorem sigmaX_eq_paperX : sigmaX = paperX := by
  rw [sigmaX, fromPaper, paperX, matrix2_transpose]

/-! ### Semantic entry formulas -/

@[simp]
theorem ry_false_false (theta : ℝ) : ry theta false false = Real.cos (theta / 2) := by
  rfl

@[simp]
theorem ry_false_true (theta : ℝ) : ry theta false true = -Real.sin (theta / 2) := by
  rfl

@[simp]
theorem ry_true_false (theta : ℝ) : ry theta true false = Real.sin (theta / 2) := by
  rfl

@[simp]
theorem ry_true_true (theta : ℝ) : ry theta true true = Real.cos (theta / 2) := by
  rfl

@[simp]
theorem rz_false_false (alpha : ℝ) : rz alpha false false = cis (alpha / 2) := by
  rfl

@[simp]
theorem rz_false_true (alpha : ℝ) : rz alpha false true = 0 := by
  rfl

@[simp]
theorem rz_true_false (alpha : ℝ) : rz alpha true false = 0 := by
  rfl

@[simp]
theorem rz_true_true (alpha : ℝ) : rz alpha true true = cis (-alpha / 2) := by
  rfl

@[simp]
theorem phaseShift_false_false (delta : ℝ) : phaseShift delta false false = cis delta := by
  rfl

@[simp]
theorem phaseShift_false_true (delta : ℝ) : phaseShift delta false true = 0 := by
  rfl

@[simp]
theorem phaseShift_true_false (delta : ℝ) : phaseShift delta true false = 0 := by
  rfl

@[simp]
theorem phaseShift_true_true (delta : ℝ) : phaseShift delta true true = cis delta := by
  rfl

@[simp]
theorem sigmaX_false_false : sigmaX false false = 0 := by
  rfl

@[simp]
theorem sigmaX_false_true : sigmaX false true = 1 := by
  rfl

@[simp]
theorem sigmaX_true_false : sigmaX true false = 1 := by
  rfl

@[simp]
theorem sigmaX_true_true : sigmaX true true = 0 := by
  rfl

/-! ## Semantic adjoints, determinants, and Lemma 4.2 -/

@[simp]
theorem ry_zero : ry 0 = (1 : QubitMatrix) := by
  rw [ry_eq_paperRy_neg]
  simp

@[simp]
theorem rz_zero : rz 0 = (1 : QubitMatrix) := by
  rw [rz_eq_paperRz]
  simp

@[simp]
theorem phaseShift_zero : phaseShift 0 = (1 : QubitMatrix) := by
  rw [phaseShift_eq_paperPhase]
  simp

/-- The semantic Y rotation's adjoint negates its angle. -/
theorem star_ry (theta : ℝ) : star (ry theta) = ry (-theta) := by
  rw [ry_eq_paperRy_neg, star_paperRy, ry_eq_paperRy_neg]

/-- The semantic Z rotation's adjoint negates its angle. -/
theorem star_rz (alpha : ℝ) : star (rz alpha) = rz (-alpha) := by
  rw [rz_eq_paperRz, star_paperRz, rz_eq_paperRz]

/-- The semantic scalar phase's adjoint negates its angle. -/
theorem star_phaseShift (delta : ℝ) : star (phaseShift delta) = phaseShift (-delta) := by
  rw [phaseShift_eq_paperPhase, star_paperPhase, phaseShift_eq_paperPhase]

/-- The semantic Pauli-X is self-adjoint. -/
@[simp]
theorem star_sigmaX : star sigmaX = sigmaX := by
  rw [sigmaX_eq_paperX, star_paperX]

/-- The semantic Y rotation has determinant one. -/
@[simp]
theorem ry_det (theta : ℝ) : Matrix.det (ry theta) = 1 := by
  rw [ry_eq_paperRy_neg, paperRy_det]

/-- The semantic Z rotation has determinant one. -/
@[simp]
theorem rz_det (alpha : ℝ) : Matrix.det (rz alpha) = 1 := by
  rw [rz_eq_paperRz, paperRz_det]

/-- The semantic scalar phase has determinant `exp(2 i delta)`. -/
theorem phaseShift_det (delta : ℝ) : Matrix.det (phaseShift delta) = cis (2 * delta) := by
  rw [phaseShift_eq_paperPhase, paperPhase_det]

/-- The semantic Pauli-X has determinant minus one. -/
@[simp]
theorem sigmaX_det : Matrix.det sigmaX = -1 := by
  rw [sigmaX_eq_paperX, paperX_det]

/-- Semantic Lemma 4.2(i): Y rotations add their angles. -/
theorem ry_mul (theta₁ theta₂ : ℝ) : ry theta₁ * ry theta₂ = ry (theta₁ + theta₂) := by
  rw [ry_eq_paperRy_neg, ry_eq_paperRy_neg, ry_eq_paperRy_neg, paperRy_mul]
  congr 1
  ring

/-- Semantic Lemma 4.2(ii): Z rotations add their angles. -/
theorem rz_mul (alpha₁ alpha₂ : ℝ) : rz alpha₁ * rz alpha₂ = rz (alpha₁ + alpha₂) := by
  rw [rz_eq_paperRz, rz_eq_paperRz, rz_eq_paperRz, paperRz_mul]

/-- Semantic Lemma 4.2(iii): scalar phases add their angles. -/
theorem phaseShift_mul (delta₁ delta₂ : ℝ) :
    phaseShift delta₁ * phaseShift delta₂ = phaseShift (delta₁ + delta₂) := by
  rw [phaseShift_eq_paperPhase, phaseShift_eq_paperPhase,
    phaseShift_eq_paperPhase, paperPhase_mul]

/-- Semantic Lemma 4.2(iv): Pauli-X is an involution. -/
theorem sigmaX_sq : sigmaX * sigmaX = (1 : QubitMatrix) := by
  rw [sigmaX_eq_paperX, paperX_sq]

/-- Semantic Lemma 4.2(v): Pauli-X conjugation negates a Y-rotation angle. -/
theorem sigmaX_mul_ry_mul_sigmaX (theta : ℝ) :
    sigmaX * ry theta * sigmaX = ry (-theta) := by
  rw [sigmaX_eq_paperX, ry_eq_paperRy_neg,
    paperX_mul_paperRy_mul_paperX, ry_eq_paperRy_neg]

/-- Semantic Lemma 4.2(vi): Pauli-X conjugation negates a Z-rotation angle. -/
theorem sigmaX_mul_rz_mul_sigmaX (alpha : ℝ) :
    sigmaX * rz alpha * sigmaX = rz (-alpha) := by
  rw [sigmaX_eq_paperX, rz_eq_paperRz,
    paperX_mul_paperRz_mul_paperX, rz_eq_paperRz]

/-! ## Certification of the standard-column matrices -/

/-- The standard-column Y rotation is unitary. -/
theorem ry_mem_unitaryGroup (theta : ℝ) : ry theta ∈ Matrix.unitaryGroup Bool ℂ := by
  change fromPaper (paperRy theta) ∈ Matrix.unitaryGroup Bool ℂ
  exact (fromPaper_mem_unitaryGroup_iff (paperRy theta)).mpr
    (paperRy_mem_unitaryGroup theta)

/-- The standard-column Z rotation is unitary. -/
theorem rz_mem_unitaryGroup (alpha : ℝ) : rz alpha ∈ Matrix.unitaryGroup Bool ℂ := by
  change fromPaper (paperRz alpha) ∈ Matrix.unitaryGroup Bool ℂ
  exact (fromPaper_mem_unitaryGroup_iff (paperRz alpha)).mpr
    (paperRz_mem_unitaryGroup alpha)

/-- The standard-column scalar phase is unitary. -/
theorem phaseShift_mem_unitaryGroup (delta : ℝ) :
    phaseShift delta ∈ Matrix.unitaryGroup Bool ℂ := by
  change fromPaper (paperPhase delta) ∈ Matrix.unitaryGroup Bool ℂ
  exact (fromPaper_mem_unitaryGroup_iff (paperPhase delta)).mpr
    (paperPhase_mem_unitaryGroup delta)

/-- The standard-column Pauli-X is unitary. -/
theorem sigmaX_mem_unitaryGroup : sigmaX ∈ Matrix.unitaryGroup Bool ℂ := by
  change fromPaper paperX ∈ Matrix.unitaryGroup Bool ℂ
  exact (fromPaper_mem_unitaryGroup_iff paperX).mpr paperX_mem_unitaryGroup

/-- The standard-column Y rotation is special unitary. -/
theorem ry_mem_specialUnitaryGroup (theta : ℝ) :
    ry theta ∈ Matrix.specialUnitaryGroup Bool ℂ := by
  exact Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨ry_mem_unitaryGroup theta, ry_det theta⟩

/-- The standard-column Z rotation is special unitary. -/
theorem rz_mem_specialUnitaryGroup (alpha : ℝ) :
    rz alpha ∈ Matrix.specialUnitaryGroup Bool ℂ := by
  exact Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨rz_mem_unitaryGroup alpha, rz_det alpha⟩

/-- Standard-column Y rotation with an ordinary unitary certificate. -/
def ryUnitary (theta : ℝ) : QubitUnitary := ⟨ry theta, ry_mem_unitaryGroup theta⟩

/-- Standard-column Z rotation with an ordinary unitary certificate. -/
def rzUnitary (alpha : ℝ) : QubitUnitary := ⟨rz alpha, rz_mem_unitaryGroup alpha⟩

/-- Standard-column Y rotation with its special-unitary certificate. -/
def rySpecialUnitary (theta : ℝ) : QubitSpecialUnitary :=
  ⟨ry theta, ry_mem_specialUnitaryGroup theta⟩

/-- Standard-column Z rotation with its special-unitary certificate. -/
def rzSpecialUnitary (alpha : ℝ) : QubitSpecialUnitary :=
  ⟨rz alpha, rz_mem_specialUnitaryGroup alpha⟩

/-- Standard-column scalar phase with its unitary certificate. -/
def phaseShiftUnitary (delta : ℝ) : QubitUnitary :=
  ⟨phaseShift delta, phaseShift_mem_unitaryGroup delta⟩

/-- Standard-column Pauli-X with its unitary certificate. -/
def sigmaXUnitary : QubitUnitary := ⟨sigmaX, sigmaX_mem_unitaryGroup⟩

@[simp]
theorem coe_ryUnitary (theta : ℝ) : (ryUnitary theta : QubitMatrix) = ry theta := by
  rfl

@[simp]
theorem coe_rzUnitary (alpha : ℝ) : (rzUnitary alpha : QubitMatrix) = rz alpha := by
  rfl

@[simp]
theorem coe_rySpecialUnitary (theta : ℝ) :
    (rySpecialUnitary theta : QubitMatrix) = ry theta := by
  rfl

@[simp]
theorem coe_rzSpecialUnitary (alpha : ℝ) :
    (rzSpecialUnitary alpha : QubitMatrix) = rz alpha := by
  rfl

@[simp]
theorem coe_phaseShiftUnitary (delta : ℝ) :
    (phaseShiftUnitary delta : QubitMatrix) = phaseShift delta := by
  rfl

@[simp]
theorem coe_sigmaXUnitary : (sigmaXUnitary : QubitMatrix) = sigmaX := by
  rfl

/-- The certified semantic scalar phase retains its exact determinant. -/
theorem phaseShiftUnitary_det (delta : ℝ) :
    Matrix.det (phaseShiftUnitary delta : QubitMatrix) = cis (2 * delta) := by
  exact phaseShift_det delta

/-- The certified semantic Pauli-X retains determinant minus one. -/
@[simp]
theorem sigmaXUnitary_det : Matrix.det (sigmaXUnitary : QubitMatrix) = -1 := by
  exact sigmaX_det

end


end OneQubit

end Barenco
