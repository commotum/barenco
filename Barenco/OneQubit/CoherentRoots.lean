import Barenco.OneQubit.Roots
import Barenco.Equivalence.OperatorNorm
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Coherent principal power-of-two roots

The exact root constructor in `Roots` selects principal arguments independently
at every spectral value.  This leaf proves the two additional facts needed by
the approximation construction of Barenco Lemma 7.8:

* adjacent selected power-of-two roots square exactly;
* the depth-`m` root is at L² operator distance at most `pi / 2^m` from identity.

The norm theorem is valid for every finite-dimensional complex unitary matrix,
not only for one-qubit gates.  Its proof uses the same principal-eigenphase
choice as the exact root construction; an arbitrary collection of existential
roots would not satisfy either conclusion.

Mathlib currently gives the ordinary `Matrix` L² operator norm and the
continuous functional calculus on `CStarMatrix` through separate wrappers.  A
local `CStarAlgebra` instance and the identity star-algebra equivalence bridge
those wrappers below.  No new global instance or project axiom is introduced.
-/

namespace Barenco.OneQubit

open scoped ComplexOrder

noncomputable section

/-! ## Scalar coherence and decay -/

/-- Adjacent principal scalar power-of-two roots square exactly. -/
theorem unitaryRootScalar_pow_two_succ_sq (m : ℕ) (z : ℂ) :
    unitaryRootScalar (2 ^ (m + 1)) z ^ 2 =
      unitaryRootScalar (2 ^ m) z := by
  rw [unitaryRootScalar, unitaryRootScalar, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  rw [pow_succ]
  field_simp

/--
The principal scalar `2^m`th root is within `pi / 2^m` of one.

The estimate is valid for every scalar because `unitaryRootScalar` depends only
on its principal argument.  Later matrix use restricts the scalar to a unitary
spectrum.
-/
theorem unitaryRootScalar_pow_two_distance_one_le (m : ℕ) (z : ℂ) :
    ‖unitaryRootScalar (2 ^ m) z - 1‖ ≤
      Real.pi / (2 ^ m : ℝ) := by
  rw [unitaryRootScalar]
  calc
    ‖Complex.exp (((z.arg / (2 ^ m : ℕ) : ℝ) : ℂ) * Complex.I) - 1‖ ≤
        ‖z.arg / (2 ^ m : ℕ)‖ := by
      simpa [mul_comm] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le
          (x := z.arg / (2 ^ m : ℕ)))
    _ = |z.arg| / (2 ^ m : ℝ) := by
      have hdenom : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by
        exact_mod_cast Nat.two_pow_pos m
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hdenom]
      norm_num
    _ ≤ Real.pi / (2 ^ m : ℝ) := by
      exact div_le_div_of_nonneg_right (Complex.abs_arg_le_pi z) (by positivity)

/-! ## Certified finite-matrix coherence -/

/-- The selected coherent `2^m`th root sequence of a finite unitary matrix. -/
def powerTwoRoot {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : Matrix.unitaryGroup ι ℂ) : Matrix.unitaryGroup ι ℂ :=
  unitaryRoot (2 ^ m) U

/-- The zeroth member of the coherent sequence is the original unitary. -/
@[simp]
theorem powerTwoRoot_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) : powerTwoRoot 0 U = U := by
  simpa [powerTwoRoot] using unitaryRoot_pow 1 (by decide) U

private theorem unitaryRootScalar_continuousOn_cstarSpectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (U : CStarMatrix ι ι ℂ) :
    ContinuousOn (unitaryRootScalar k) (spectrum ℂ U) := by
  exact (Matrix.finite_spectrum (CStarMatrix.ofMatrix.symm U)).continuousOn _

/-- Adjacent selected finite-dimensional power-of-two roots square exactly. -/
theorem unitaryRoot_pow_two_succ_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : Matrix.unitaryGroup ι ℂ) :
    unitaryRoot (2 ^ (m + 1)) U ^ 2 = unitaryRoot (2 ^ m) U := by
  apply Subtype.ext
  change
    (CStarMatrix.ofMatrix.symm
      (cfc (unitaryRootScalar (2 ^ (m + 1)))
        (CStarMatrix.ofMatrix (U : Matrix ι ι ℂ)))) ^ 2 =
      CStarMatrix.ofMatrix.symm
        (cfc (unitaryRootScalar (2 ^ m))
          (CStarMatrix.ofMatrix (U : Matrix ι ι ℂ)))
  let CU : unitary (CStarMatrix ι ι ℂ) :=
    ⟨CStarMatrix.ofMatrix (U : Matrix ι ι ℂ), U.property⟩
  have hcfc :
      (cfc (unitaryRootScalar (2 ^ (m + 1)))
        (CU : CStarMatrix ι ι ℂ)) ^ 2 =
      cfc (unitaryRootScalar (2 ^ m)) (CU : CStarMatrix ι ι ℂ) := by
    rw [← cfc_pow (p := IsStarNormal)
      (unitaryRootScalar (2 ^ (m + 1))) 2
      (CU : CStarMatrix ι ι ℂ)
      (hf := unitaryRootScalar_continuousOn_cstarSpectrum
        (2 ^ (m + 1)) (CU : CStarMatrix ι ι ℂ))
      (ha := isStarNormal_of_mem_unitary CU.property)]
    apply cfc_congr
    intro z _hz
    exact unitaryRootScalar_pow_two_succ_sq m z
  exact congrArg
    (CStarMatrix.ofMatrix.symm : CStarMatrix ι ι ℂ → Matrix ι ι ℂ) hcfc

/-- Adjacent members of `powerTwoRoot` square exactly. -/
@[simp]
theorem powerTwoRoot_succ_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : Matrix.unitaryGroup ι ℂ) :
    powerTwoRoot (m + 1) U ^ 2 = powerTwoRoot m U := by
  exact unitaryRoot_pow_two_succ_sq m U

/-! ## L² operator-distance decay -/

section OperatorDistance

open scoped Matrix.Norms.L2Operator

/-
The L² operator-norm `Matrix` structure already has all fields needed for a
complex C-star algebra, but mathlib deliberately does not install this bundled
instance globally.  Keeping it local prevents norm-instance leakage.
-/
noncomputable local instance matrixCStarAlgebra
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    CStarAlgebra (Matrix ι ι ℂ) where

private theorem unitaryRootScalar_continuousOn_matrixSpectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (U : Matrix ι ι ℂ) :
    ContinuousOn (unitaryRootScalar k) (spectrum ℂ U) := by
  exact (Matrix.finite_spectrum U).continuousOn _

private theorem cfc_matrix_to_cstar
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (U : Matrix.unitaryGroup ι ℂ) :
    CStarMatrix.ofMatrix
        (cfc (unitaryRootScalar k) (U : Matrix ι ι ℂ) : Matrix ι ι ℂ) =
      cfc (unitaryRootScalar k)
        (CStarMatrix.ofMatrix (U : Matrix ι ι ℂ)) := by
  let e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] CStarMatrix ι ι ℂ :=
    CStarMatrix.ofMatrixStarAlgEquiv
  exact (e : Matrix ι ι ℂ →⋆ₐ[ℂ] CStarMatrix ι ι ℂ).map_cfc
    (unitaryRootScalar k) (U : Matrix ι ι ℂ)
    (hf := unitaryRootScalar_continuousOn_matrixSpectrum k
      (U : Matrix ι ι ℂ))
    (hφ := by
      change Continuous (fun M : Matrix ι ι ℂ => M)
      exact continuous_id)
    (ha := isStarNormal_of_mem_unitary U.property)
    (hφa := isStarNormal_of_mem_unitary
      (show CStarMatrix.ofMatrix (U : Matrix ι ι ℂ) ∈
        unitary (CStarMatrix ι ι ℂ) from U.property))

private theorem coe_unitaryRoot_eq_matrix_cfc
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (U : Matrix.unitaryGroup ι ℂ) :
    (unitaryRoot k U : Matrix ι ι ℂ) =
      cfc (unitaryRootScalar k) (U : Matrix ι ι ℂ) := by
  change
    CStarMatrix.ofMatrix.symm
      (cfc (unitaryRootScalar k)
        (CStarMatrix.ofMatrix (U : Matrix ι ι ℂ))) =
      cfc (unitaryRootScalar k) (U : Matrix ι ι ℂ)
  exact (congrArg
    (CStarMatrix.ofMatrix.symm : CStarMatrix ι ι ℂ → Matrix ι ι ℂ)
    (cfc_matrix_to_cstar k U)).symm

/--
The selected finite-dimensional `2^m`th root is at L² operator distance at most
`pi / 2^m` from identity.
-/
theorem unitaryRoot_pow_two_operatorDistance_one_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : Matrix.unitaryGroup ι ℂ) :
    Barenco.operatorDistance
      (unitaryRoot (2 ^ m) U : Matrix ι ι ℂ) 1 ≤
        Real.pi / (2 ^ m : ℝ) := by
  rw [Barenco.operatorDistance, coe_unitaryRoot_eq_matrix_cfc]
  have hnormal : IsStarNormal (U : Matrix ι ι ℂ) :=
    isStarNormal_of_mem_unitary U.property
  rw [← cfc_one ℂ (U : Matrix ι ι ℂ) (ha := hnormal)]
  rw [← cfc_sub (unitaryRootScalar (2 ^ m)) 1
    (U : Matrix ι ι ℂ)
    (hf := unitaryRootScalar_continuousOn_matrixSpectrum
      (2 ^ m) (U : Matrix ι ι ℂ))
    (hg := continuous_const.continuousOn)]
  exact norm_cfc_le (by positivity) fun z _hz =>
    unitaryRootScalar_pow_two_distance_one_le m z

/-- Operator-distance decay restated for the named coherent root sequence. -/
theorem powerTwoRoot_operatorDistance_one_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (U : Matrix.unitaryGroup ι ℂ) :
    Barenco.operatorDistance
      (powerTwoRoot m U : Matrix ι ι ℂ) 1 ≤
        Real.pi / (2 ^ m : ℝ) := by
  exact unitaryRoot_pow_two_operatorDistance_one_le m U

end OperatorDistance

end

end Barenco.OneQubit
