import Barenco.OneQubit.Euler

/-!
# Pauli-X conjugates and the symmetric Euler family

This leaf proves the matrix classification used by Barenco et al., Lemmas 5.4
and 5.5. It intentionally has no dependency on circuit syntax or target-block
algebra.

The paper uses row vectors. In this library's standard-column convention its
conjugate is `A† * X * A`, and the transpose of the Lemma 5.4 active product is
`X * A† * X * A`. Thus the two classified families are respectively

* `X * (Rz alpha * Ry theta * Rz alpha)`, and
* `Rz alpha * Ry theta * Rz alpha`.

The forward proof is a complete algebraic classification, not a parameter
count: a Pauli conjugate is Hermitian and traceless, and unitarity makes its
first row `(r,z)` satisfy `r² + ‖z‖² = 1`. We choose
`theta = 2 * arcsin r` and `alpha = -arg z`. Mathlib's total polar identity at
`z = 0` handles the phase-degenerate cases without division or an unstated
nonzero hypothesis. The converse uses exactly the Stage-4 column `A` and `B`
factors, with `B = A†` when the outer Euler angles agree.
-/

namespace Barenco.ControlledCircuit

open Matrix

noncomputable section

open Barenco OneQubit

/-- Equal-outer-angle Euler family in the library's column convention. -/
def symmetricEuler (alpha theta : ℝ) : QubitMatrix :=
  rz alpha * ry theta * rz alpha

/-- Explicit entries of the column-oriented equal-outer-angle Euler family. -/
theorem symmetricEuler_eq_matrix2 (alpha theta : ℝ) :
    symmetricEuler alpha theta =
      matrix2 (cis alpha * Real.cos (theta / 2)) (-Real.sin (theta / 2))
        (Real.sin (theta / 2)) (cis (-alpha) * Real.cos (theta / 2)) := by
  rw [symmetricEuler, rz_eq_paperRz, ry_eq_paperRy_neg, paperRz, paperRy,
    matrix2_mul, matrix2_mul]
  simp only [neg_div, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_neg,
    mul_zero, zero_mul, add_zero, zero_add]
  have hplus : cis (alpha / 2) * cis (alpha / 2) = cis alpha := by
    rw [← cis_add]
    congr 1
    ring
  have hminus : cis (-(alpha / 2)) * cis (-(alpha / 2)) = cis (-alpha) := by
    rw [← cis_add]
    congr 1
    ring
  have hcancel : cis (alpha / 2) * cis (-(alpha / 2)) = 1 := by
    rw [← cis_add]
    rw [show alpha / 2 + -(alpha / 2) = 0 by ring, cis_zero]
  congr 1
  · calc
      cis (alpha / 2) * (Real.cos (theta / 2) : ℂ) * cis (alpha / 2) =
          (cis (alpha / 2) * cis (alpha / 2)) * Real.cos (theta / 2) := by ring
      _ = cis alpha * Real.cos (theta / 2) := by rw [hplus]
  · calc
      cis (alpha / 2) * (-Real.sin (theta / 2) : ℂ) * cis (-(alpha / 2)) =
          (cis (alpha / 2) * cis (-(alpha / 2))) * (-Real.sin (theta / 2)) := by ring
      _ = -Real.sin (theta / 2) := by rw [hcancel]; ring
  · calc
      cis (-(alpha / 2)) * (Real.sin (theta / 2) : ℂ) * cis (alpha / 2) =
          (cis (alpha / 2) * cis (-(alpha / 2))) * Real.sin (theta / 2) := by ring
      _ = Real.sin (theta / 2) := by rw [hcancel]; ring
  · calc
      cis (-(alpha / 2)) * (Real.cos (theta / 2) : ℂ) * cis (-(alpha / 2)) =
          (cis (-(alpha / 2)) * cis (-(alpha / 2))) * Real.cos (theta / 2) := by ring
      _ = cis (-alpha) * Real.cos (theta / 2) := by rw [hminus]

/-- Explicit entries after left multiplication by Pauli-X. -/
theorem sigmaX_mul_symmetricEuler_eq_matrix2 (alpha theta : ℝ) :
    sigmaX * symmetricEuler alpha theta =
      matrix2 (Real.sin (theta / 2)) (cis (-alpha) * Real.cos (theta / 2))
        (cis alpha * Real.cos (theta / 2)) (-Real.sin (theta / 2)) := by
  rw [symmetricEuler_eq_matrix2, sigmaX_eq_paperX, paperX, matrix2_mul]
  simp only [zero_mul, one_mul, zero_add, add_zero]

/-- Standard-column Pauli conjugate `A† * X * A`. -/
def pauliConjugate (A : QubitSpecialUnitary) : QubitMatrix :=
  star (A : QubitMatrix) * sigmaX * (A : QubitMatrix)

/-- Canonical phase parameter for the Pauli-conjugate classification. -/
def pauliConjugateAlpha (A : QubitSpecialUnitary) : ℝ :=
  -(pauliConjugate A false true).arg

/-- Canonical polar parameter for the Pauli-conjugate classification. -/
def pauliConjugateTheta (A : QubitSpecialUnitary) : ℝ :=
  2 * Real.arcsin (pauliConjugate A false false).re

private def specialAsUnitary (A : QubitSpecialUnitary) : QubitUnitary :=
  ⟨(A : QubitMatrix), A.prop.1⟩

/-- The Pauli conjugate with its inherited unitary certificate. -/
def pauliConjugateUnitary (A : QubitSpecialUnitary) : QubitUnitary :=
  (specialAsUnitary A)⁻¹ * sigmaXUnitary * specialAsUnitary A

@[simp]
theorem coe_pauliConjugateUnitary (A : QubitSpecialUnitary) :
    (pauliConjugateUnitary A : QubitMatrix) = pauliConjugate A := by
  rfl

/-- A conjugate of Pauli-X is Hermitian. -/
theorem star_pauliConjugate (A : QubitSpecialUnitary) :
    star (pauliConjugate A) = pauliConjugate A := by
  rw [pauliConjugate]
  simp only [star_mul, star_star, star_sigmaX]
  rw [Matrix.mul_assoc]

/-- The two diagonal entries of a Pauli conjugate are negatives. -/
theorem pauliConjugate_tt_eq_neg_ff (A : QubitSpecialUnitary) :
    pauliConjugate A true true = -pauliConjugate A false false := by
  have hstarstar (z : ℂ) :
      (starRingEnd ℂ) ((starRingEnd ℂ) z) = z := by
    simpa only [starRingEnd_apply] using star_star z
  rw [pauliConjugate, Barenco.OneQubit.specialUnitary_canonical A,
    Barenco.OneQubit.star_matrix2, Barenco.OneQubit.sigmaX_eq_paperX,
    Barenco.OneQubit.paperX, Barenco.OneQubit.matrix2_mul,
    Barenco.OneQubit.matrix2_mul]
  simp only [star_star, Barenco.OneQubit.matrix2_true_true,
    Barenco.OneQubit.matrix2_false_false]
  simp only [Complex.star_def, map_neg, hstarstar]
  ring

/-- Hermiticity relates the two off-diagonal entries. -/
theorem pauliConjugate_tf_eq_star_ft (A : QubitSpecialUnitary) :
    pauliConjugate A true false = star (pauliConjugate A false true) := by
  have h := star_pauliConjugate A
  have htf := congrArg (fun M : QubitMatrix => M true false) h
  simpa [Matrix.star_apply] using htf.symm

/-- A diagonal entry of a Pauli conjugate is real. -/
theorem pauliConjugate_ff_eq_re (A : QubitSpecialUnitary) :
    pauliConjugate A false false =
      ((pauliConjugate A false false).re : ℂ) := by
  have h := star_pauliConjugate A
  have hff := congrArg (fun M : QubitMatrix => M false false) h
  have hc : star (pauliConjugate A false false) =
      pauliConjugate A false false := by
    simpa [Matrix.star_apply] using hff
  exact (Complex.conj_eq_iff_re.mp hc).symm

/-- Squared norms in the `false` row of a two-dimensional unitary sum to one. -/
theorem unitary_first_row_norm_sq_add (U : QubitUnitary) :
    ‖(U : QubitMatrix) false false‖ ^ 2 +
      ‖(U : QubitMatrix) false true‖ ^ 2 = (1 : ℝ) := by
  have hu := Matrix.mem_unitaryGroup_iff.mp U.prop
  have hu00 := congrArg (fun M : QubitMatrix => M false false) hu
  simp only [Matrix.mul_apply, Matrix.star_apply, Fintype.sum_bool,
    Matrix.one_apply, if_pos] at hu00
  change (U : QubitMatrix) false true *
      (starRingEnd ℂ) ((U : QubitMatrix) false true) +
    (U : QubitMatrix) false false *
      (starRingEnd ℂ) ((U : QubitMatrix) false false) = 1 at hu00
  rw [Complex.mul_conj, Complex.mul_conj] at hu00
  have hre := congrArg Complex.re hu00
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.one_re,
    Complex.normSq_eq_norm_sq, add_comm] using hre

/-- The first row of a Pauli conjugate has unit Euclidean norm. -/
theorem pauliConjugate_norm_sq_add (A : QubitSpecialUnitary) :
    ‖pauliConjugate A false false‖ ^ 2 +
      ‖pauliConjugate A false true‖ ^ 2 = (1 : ℝ) := by
  simpa only [coe_pauliConjugateUnitary] using
    unitary_first_row_norm_sq_add (pauliConjugateUnitary A)

private theorem trigPolarClassify (z : ℂ) (r : ℝ)
    (h : r ^ 2 + ‖z‖ ^ 2 = (1 : ℝ)) :
    let t := Real.arcsin r
    let alpha := -z.arg
    Real.sin t = r ∧ Real.cos t = ‖z‖ ∧
      ((Real.cos t : ℂ) * cis (-alpha) = z) := by
  dsimp
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hrLower : -1 ≤ r := by
    nlinarith [sq_nonneg ‖z‖]
  have hrUpper : r ≤ 1 := by
    nlinarith [sq_nonneg ‖z‖]
  have hsin : Real.sin (Real.arcsin r) = r :=
    Real.sin_arcsin hrLower hrUpper
  have hcos : Real.cos (Real.arcsin r) = ‖z‖ := by
    rw [Real.cos_arcsin]
    have hsquare : 1 - r ^ 2 = ‖z‖ ^ 2 := by nlinarith
    rw [hsquare, Real.sqrt_sq hz0]
  refine ⟨hsin, hcos, ?_⟩
  rw [hcos]
  simpa only [neg_neg, cis] using Complex.norm_mul_exp_arg_mul_I z

/-- Every special-unitary Pauli conjugate belongs to the equal-outer-angle family. -/
theorem pauliConjugate_eq_sigmaX_mul_symmetricEuler (A : QubitSpecialUnitary) :
    pauliConjugate A =
      sigmaX * symmetricEuler (pauliConjugateAlpha A) (pauliConjugateTheta A) := by
  let r : ℝ := (pauliConjugate A false false).re
  let z : ℂ := pauliConjugate A false true
  have hreal : pauliConjugate A false false = (r : ℂ) := by
    simpa only [r] using pauliConjugate_ff_eq_re A
  have hnorm : r ^ 2 + ‖z‖ ^ 2 = (1 : ℝ) := by
    have h := pauliConjugate_norm_sq_add A
    rw [hreal] at h
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs, z] using h
  obtain ⟨hsin, hcos, hpolar⟩ := trigPolarClassify z r hnorm
  have hmatrix : pauliConjugate A =
      matrix2 (r : ℂ) z (star z) (-(r : ℂ)) := by
    ext i j
    cases i <;> cases j
    · exact hreal
    · rfl
    · exact pauliConjugate_tf_eq_star_ft A
    · simpa only [matrix2_true_true] using
        (pauliConjugate_tt_eq_neg_ff A).trans (congrArg Neg.neg hreal)
  rw [hmatrix, sigmaX_mul_symmetricEuler_eq_matrix2]
  congr 1
  · simpa [pauliConjugateTheta, r] using (congrArg Complex.ofReal hsin).symm
  · rw [show pauliConjugateTheta A / 2 = Real.arcsin r by
      simp [pauliConjugateTheta, r]]
    change z = cis (-(-z.arg)) * Real.cos (Real.arcsin r)
    simpa only [neg_neg, mul_comm] using hpolar.symm
  · rw [show pauliConjugateTheta A / 2 = Real.arcsin r by
      simp [pauliConjugateTheta, r]]
    change star z = cis (-z.arg) * Real.cos (Real.arcsin r)
    have hpolar' : (Real.cos (Real.arcsin r) : ℂ) * cis z.arg = z := by
      simpa only [neg_neg] using hpolar
    calc
      star z = star ((Real.cos (Real.arcsin r) : ℂ) * cis z.arg) :=
        congrArg star hpolar'.symm
      _ = cis (-z.arg) * Real.cos (Real.arcsin r) := by
        simp only [star_mul, star_cis, Complex.star_def, Complex.conj_ofReal,
          mul_comm]
  · simpa [pauliConjugateTheta, r] using
      congrArg (fun x : ℝ => -(x : ℂ)) hsin.symm

/-- Left multiplication by `X` gives the column-oriented form of Lemma 5.4. -/
theorem sigmaX_mul_star_mul_sigmaX_mul_eq_symmetricEuler
    (A : QubitSpecialUnitary) :
    sigmaX * star (A : QubitMatrix) * sigmaX * (A : QubitMatrix) =
      symmetricEuler (pauliConjugateAlpha A) (pauliConjugateTheta A) := by
  calc
    sigmaX * star (A : QubitMatrix) * sigmaX * (A : QubitMatrix) =
        sigmaX * pauliConjugate A := by
      simp only [pauliConjugate, Matrix.mul_assoc]
    _ = sigmaX *
        (sigmaX * symmetricEuler (pauliConjugateAlpha A) (pauliConjugateTheta A)) :=
      congrArg (fun M : QubitMatrix => sigmaX * M)
        (pauliConjugate_eq_sigmaX_mul_symmetricEuler A)
    _ = symmetricEuler (pauliConjugateAlpha A) (pauliConjugateTheta A) := by
      rw [← Matrix.mul_assoc, sigmaX_sq, one_mul]

/-- Existential form of the Pauli-conjugate classification. -/
theorem exists_pauliConjugate_eq_sigmaX_mul_symmetricEuler
    (A : QubitSpecialUnitary) :
    ∃ alpha theta : ℝ,
      star (A : QubitMatrix) * sigmaX * (A : QubitMatrix) =
        sigmaX * symmetricEuler alpha theta := by
  exact ⟨pauliConjugateAlpha A, pauliConjugateTheta A,
    pauliConjugate_eq_sigmaX_mul_symmetricEuler A⟩

/-- Existential form after leading multiplication by Pauli-X. -/
theorem exists_sigmaX_mul_star_mul_sigmaX_mul_eq_symmetricEuler
    (A : QubitSpecialUnitary) :
    ∃ alpha theta : ℝ,
      sigmaX * star (A : QubitMatrix) * sigmaX * (A : QubitMatrix) =
        symmetricEuler alpha theta := by
  exact ⟨pauliConjugateAlpha A, pauliConjugateTheta A,
    sigmaX_mul_star_mul_sigmaX_mul_eq_symmetricEuler A⟩

/-- At equal outer angles, the Stage-4 `B` factor is the adjoint of `A`. -/
theorem star_columnA_eq_columnB (alpha theta : ℝ) :
    star (columnA alpha theta) = columnB alpha theta alpha := by
  rw [columnA_eq, columnB_eq, star_mul, star_rz, star_ry]
  rw [show -(alpha + alpha) / 2 = -alpha by ring,
    show -theta / 2 = -(theta / 2) by ring]

/-- The Stage-4 `A/B` factors construct every member of the symmetric family. -/
theorem columnA_sigmaX_mul_star_mul_sigmaX_mul_eq_symmetricEuler
    (alpha theta : ℝ) :
    sigmaX * star (columnASpecialUnitary alpha theta : QubitMatrix) * sigmaX *
        (columnASpecialUnitary alpha theta : QubitMatrix) =
      symmetricEuler alpha theta := by
  have h := columnC_mul_X_mul_columnB_mul_X_mul_columnA alpha theta alpha
  simp only [columnC_eq, sub_self, zero_div, rz_zero, one_mul, columnEuler_eq] at h
  rw [coe_columnASpecialUnitary, star_columnA_eq_columnB]
  exact h

/-- Constructive converse to the Pauli-conjugate classification. -/
theorem columnA_pauliConjugate_eq_sigmaX_mul_symmetricEuler
    (alpha theta : ℝ) :
    pauliConjugate (columnASpecialUnitary alpha theta) =
      sigmaX * symmetricEuler alpha theta := by
  have h : sigmaX * pauliConjugate (columnASpecialUnitary alpha theta) =
      symmetricEuler alpha theta := by
    simpa only [pauliConjugate, coe_columnASpecialUnitary, Matrix.mul_assoc] using
      columnA_sigmaX_mul_star_mul_sigmaX_mul_eq_symmetricEuler alpha theta
  calc
    pauliConjugate (columnASpecialUnitary alpha theta) =
        sigmaX * (sigmaX * pauliConjugate (columnASpecialUnitary alpha theta)) := by
      rw [← Matrix.mul_assoc, sigmaX_sq, one_mul]
    _ = sigmaX * symmetricEuler alpha theta :=
      congrArg (fun M : QubitMatrix => sigmaX * M) h

/-- A Stage-4 `columnA` is an explicit witness for the conjugate family. -/
theorem exists_specialUnitary_pauliConjugate_eq_sigmaX_mul_symmetricEuler
    (alpha theta : ℝ) :
    ∃ A : QubitSpecialUnitary,
      star (A : QubitMatrix) * sigmaX * (A : QubitMatrix) =
        sigmaX * symmetricEuler alpha theta := by
  exact ⟨columnASpecialUnitary alpha theta,
    columnA_pauliConjugate_eq_sigmaX_mul_symmetricEuler alpha theta⟩

/-- A Stage-4 `columnA` is an explicit witness after the leading Pauli-X. -/
theorem exists_specialUnitary_sigmaX_mul_star_mul_sigmaX_mul_eq_symmetricEuler
    (alpha theta : ℝ) :
    ∃ A : QubitSpecialUnitary,
      sigmaX * star (A : QubitMatrix) * sigmaX * (A : QubitMatrix) =
        symmetricEuler alpha theta := by
  exact ⟨columnASpecialUnitary alpha theta,
    columnA_sigmaX_mul_star_mul_sigmaX_mul_eq_symmetricEuler alpha theta⟩

/-- Complete standard-column classification of special-unitary conjugates of `X`. -/
theorem exists_specialUnitary_pauliConjugate_iff (V : QubitMatrix) :
    (∃ A : QubitSpecialUnitary,
        star (A : QubitMatrix) * sigmaX * (A : QubitMatrix) = V) ↔
      ∃ alpha theta : ℝ, sigmaX * symmetricEuler alpha theta = V := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨pauliConjugateAlpha A, pauliConjugateTheta A,
      (pauliConjugate_eq_sigmaX_mul_symmetricEuler A).symm⟩
  · rintro ⟨alpha, theta, rfl⟩
    exact exists_specialUnitary_pauliConjugate_eq_sigmaX_mul_symmetricEuler
      alpha theta

/-- Complete standard-column classification after the leading Pauli-X. -/
theorem exists_specialUnitary_sigmaX_mul_pauliConjugate_iff (W : QubitMatrix) :
    (∃ A : QubitSpecialUnitary,
        sigmaX * star (A : QubitMatrix) * sigmaX * (A : QubitMatrix) = W) ↔
      ∃ alpha theta : ℝ, symmetricEuler alpha theta = W := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨pauliConjugateAlpha A, pauliConjugateTheta A,
      (sigmaX_mul_star_mul_sigmaX_mul_eq_symmetricEuler A).symm⟩
  · rintro ⟨alpha, theta, rfl⟩
    exact exists_specialUnitary_sigmaX_mul_star_mul_sigmaX_mul_eq_symmetricEuler
      alpha theta

end

end Barenco.ControlledCircuit
