import Barenco.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Exact roots of finite-dimensional unitary matrices

This file constructs an exact `k`th root of every finite complex unitary matrix
when `0 < k`.  Although the paper only needs roots of one-qubit gates, the API is
indexed by an arbitrary finite type and is therefore also available for semantic
multi-qubit gates.

For a scalar on the unit circle, `unitaryRootScalar k` divides its principal
argument by `k`.  This scalar function is not globally continuous because of the
principal-argument branch cut.  That causes no problem for a fixed finite matrix:
its spectrum is finite, and every function is continuous on a finite subset of
`ℂ`.  The continuous functional calculus can therefore apply the chosen scalar
root independently at each spectral value.

The construction is total at `k = 0`, but its correctness theorem deliberately
requires `0 < k`: every zeroth power is the identity, so a zeroth root cannot
exist for an arbitrary unitary.  The principal branch also means that this file
makes no claim that the selected root varies continuously as the input matrix
varies.  These are exact semantic matrix roots, not circuit syntheses or resource
bounds.
-/

namespace Barenco.OneQubit

open scoped ComplexOrder

noncomputable section

/-! ## Scalar roots on the unit circle -/

/--
The selected scalar `k`th root, obtained by dividing the principal argument by
`k`.  Its root equation is asserted only for positive `k` and unit-modulus input.
-/
def unitaryRootScalar (k : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (((z.arg / k : ℝ) : ℂ) * Complex.I)

/-- The selected scalar root always has unit modulus, even when `k = 0`. -/
theorem unitaryRootScalar_star_mul (k : ℕ) (z : ℂ) :
    star (unitaryRootScalar k z) * unitaryRootScalar k z = 1 := by
  change (starRingEnd ℂ)
      (Complex.exp (((z.arg / k : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((z.arg / k : ℝ) : ℂ) * Complex.I) = 1
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

/-- On the unit circle, the selected scalar root has the required positive power. -/
theorem unitaryRootScalar_pow (k : ℕ) (hk : 0 < k) (z : ℂ)
    (hz : z ∈ unitary ℂ) : unitaryRootScalar k z ^ k = z := by
  have hk0 : (k : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk
  have hnorm : ‖z‖ = 1 := CStarRing.norm_of_mem_unitary hz
  rw [unitaryRootScalar, ← Complex.exp_nat_mul]
  calc
    Complex.exp ((k : ℂ) * (((z.arg / k : ℝ) : ℂ) * Complex.I)) =
        Complex.exp ((z.arg : ℂ) * Complex.I) := by
      congr 1
      push_cast
      field_simp
    _ = z := by
      simpa [hnorm] using Complex.norm_mul_exp_arg_mul_I z

/-! ## Proof-side continuous functional calculus construction -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
The selected scalar root is continuous on the spectrum of a finite matrix.  No
global continuity of `unitaryRootScalar` is used or claimed.
-/
private theorem unitaryRootScalar_continuousOn_spectrum
    (k : ℕ) (U : CStarMatrix ι ι ℂ) :
    ContinuousOn (unitaryRootScalar k) (spectrum ℂ U) := by
  exact (Matrix.finite_spectrum (CStarMatrix.ofMatrix.symm U)).continuousOn _

/-- The functional-calculus root before its unitarity certificate is attached. -/
private def cstarUnitaryRootRaw
    (k : ℕ) (U : CStarMatrix ι ι ℂ) : CStarMatrix ι ι ℂ :=
  cfc (unitaryRootScalar k) U

/-- The functional-calculus root of a unitary is again unitary. -/
private theorem cstarUnitaryRootRaw_mem_unitary
    (k : ℕ) (U : unitary (CStarMatrix ι ι ℂ)) :
    cstarUnitaryRootRaw k U ∈ unitary (CStarMatrix ι ι ℂ) := by
  rw [cstarUnitaryRootRaw]
  exact (cfc_unitary_iff (p := IsStarNormal) (unitaryRootScalar k)
    (U : CStarMatrix ι ι ℂ) (ha := isStarNormal_of_mem_unitary U.property)
    (hf := unitaryRootScalar_continuousOn_spectrum k
      (U : CStarMatrix ι ι ℂ))).2
        fun z _hz => unitaryRootScalar_star_mul k z

/-- The certified functional-calculus root on the proof-side matrix type. -/
private def cstarUnitaryRoot
    (k : ℕ) (U : unitary (CStarMatrix ι ι ℂ)) :
    unitary (CStarMatrix ι ι ℂ) :=
  ⟨cstarUnitaryRootRaw k U, cstarUnitaryRootRaw_mem_unitary k U⟩

/-- The proof-side certified root has the requested positive power. -/
private theorem cstarUnitaryRoot_pow (k : ℕ) (hk : 0 < k)
    (U : unitary (CStarMatrix ι ι ℂ)) :
    cstarUnitaryRoot k U ^ k = U := by
  apply Subtype.ext
  change (cstarUnitaryRootRaw k U : CStarMatrix ι ι ℂ) ^ k =
    (U : CStarMatrix ι ι ℂ)
  rw [cstarUnitaryRootRaw, ← cfc_pow (p := IsStarNormal)
    (unitaryRootScalar k) k (U : CStarMatrix ι ι ℂ)
    (hf := unitaryRootScalar_continuousOn_spectrum k
      (U : CStarMatrix ι ι ℂ))
    (ha := isStarNormal_of_mem_unitary U.property)]
  calc
    cfc (fun z => unitaryRootScalar k z ^ k) (U : CStarMatrix ι ι ℂ) =
        cfc (fun z : ℂ => z) (U : CStarMatrix ι ι ℂ) := by
      apply cfc_congr
      intro z hz
      exact unitaryRootScalar_pow k hk z
        (spectrum_subset_unitary_of_mem_unitary U.property hz)
    _ = (U : CStarMatrix ι ι ℂ) :=
      cfc_id' ℂ (U : CStarMatrix ι ι ℂ)
        (isStarNormal_of_mem_unitary U.property)

/-!
`CStarMatrix.ofMatrix` is the identity equivalence on the underlying functions,
and its multiplication, star, identity, and powers agree definitionally with the
ordinary `Matrix` operations.  These two private conversions isolate the analytic
implementation type from the public matrix API.
-/

/-- Proof-side conversion from an ordinary certified matrix to a C-star matrix. -/
private def toCStarUnitary (U : Matrix.unitaryGroup ι ℂ) :
    unitary (CStarMatrix ι ι ℂ) :=
  ⟨CStarMatrix.ofMatrix U, U.property⟩

/-- Proof-side conversion from a certified C-star matrix to an ordinary matrix. -/
private def fromCStarUnitary (U : unitary (CStarMatrix ι ι ℂ)) :
    Matrix.unitaryGroup ι ℂ :=
  ⟨CStarMatrix.ofMatrix.symm U, U.property⟩

private theorem fromCStarUnitary_toCStarUnitary
    (U : Matrix.unitaryGroup ι ℂ) :
    fromCStarUnitary (toCStarUnitary U) = U := rfl

private theorem toCStarUnitary_fromCStarUnitary
    (U : unitary (CStarMatrix ι ι ℂ)) :
    toCStarUnitary (fromCStarUnitary U) = U := rfl

private theorem fromCStarUnitary_pow
    (U : unitary (CStarMatrix ι ι ℂ)) (k : ℕ) :
    fromCStarUnitary (U ^ k) = fromCStarUnitary U ^ k := rfl

/-! ## Public finite-matrix root API -/

/--
The selected exact `k`th root of a finite complex unitary matrix.

Correctness requires `0 < k`; see `unitaryRoot_pow`.  The result is noncanonical
in the mathematical sense that unitary roots are generally not unique; this
definition selects the principal-argument branch.  No continuity in `U` is
claimed across that branch cut.
-/
def unitaryRoot (k : ℕ) (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup ι ℂ :=
  fromCStarUnitary (cstarUnitaryRoot k (toCStarUnitary U))

/-- Every positive power map on finite complex unitary matrices is surjective. -/
theorem unitaryRoot_pow (k : ℕ) (hk : 0 < k)
    (U : Matrix.unitaryGroup ι ℂ) : unitaryRoot k U ^ k = U := by
  apply Subtype.ext
  exact congrArg CStarMatrix.ofMatrix.symm
    (congrArg Subtype.val (cstarUnitaryRoot_pow k hk (toCStarUnitary U)))

/-- Existential form of `unitaryRoot_pow`. -/
theorem exists_unitary_pow_eq (k : ℕ) (hk : 0 < k)
    (U : Matrix.unitaryGroup ι ℂ) :
    ∃ V : Matrix.unitaryGroup ι ℂ, V ^ k = U :=
  ⟨unitaryRoot k U, unitaryRoot_pow k hk U⟩

/-- The selected exact square root of a finite complex unitary matrix. -/
def unitarySquareRoot (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup ι ℂ :=
  unitaryRoot 2 U

/-- Squaring the selected unitary square root recovers the original matrix. -/
@[simp]
theorem unitarySquareRoot_pow_two (U : Matrix.unitaryGroup ι ℂ) :
    unitarySquareRoot U ^ 2 = U :=
  unitaryRoot_pow 2 (by decide) U

/-- The general construction specializes exactly to every power-of-two root. -/
theorem unitaryRoot_pow_two_pow (m : ℕ) (U : Matrix.unitaryGroup ι ℂ) :
    unitaryRoot (2 ^ m) U ^ (2 ^ m) = U :=
  unitaryRoot_pow (2 ^ m) (Nat.two_pow_pos m) U

end

end Barenco.OneQubit
