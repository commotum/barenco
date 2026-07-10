import Barenco.OneQubit.Decomposition
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Euler decomposition of special-unitary one-qubit gates

This proof leaf formalizes the determinant-one case of Barenco et al., Lemma 4.1.
The paper-facing theorem uses the manuscript's row-vector/right-action matrices.
The standard-column theorem applies the paper theorem to the transpose and therefore
reverses the two outer Euler angles explicitly.

The proof first reindexes a Bool matrix to `Fin 2`.  For a unitary matrix of
determinant one, its conjugate transpose and its adjugate are both inverses.  The
explicit two-by-two adjugate then gives the canonical form
`[[a,b],[-star b,star a]]`.  We choose

* `t = arccos ‖a‖`,
* `p = arg a`, and
* `q = arg b`,

and use angles `p + q`, `2t`, and `p - q`.

There is no hidden nonzero-entry assumption.  Mathlib defines `arg 0 = 0`, and
`Complex.norm_mul_exp_arg_mul_I` is valid even at zero.  Thus the same proof covers
both endpoint degeneracies: `a = 0` gives the middle angle `pi`, while `b = 0`
gives the middle angle `0`; both entries cannot vanish because their squared norms
sum to one.

This module exports proof-side theorems only.  Its Fin-indexed transport and
coordinate calculations remain private.
-/

namespace Barenco.OneQubit

open Matrix

noncomputable section

private abbrev FinQubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

private def boolToFin : QubitMatrix ≃ₐ[ℂ] FinQubitMatrix :=
  Matrix.reindexAlgEquiv ℂ ℂ finTwoEquiv.symm

@[simp]
private theorem boolToFin_false_false (W : QubitMatrix) :
    boolToFin W 0 0 = W false false := by
  rfl

@[simp]
private theorem boolToFin_false_true (W : QubitMatrix) :
    boolToFin W 0 1 = W false true := by
  rfl

@[simp]
private theorem boolToFin_true_false (W : QubitMatrix) :
    boolToFin W 1 0 = W true false := by
  rfl

@[simp]
private theorem boolToFin_true_true (W : QubitMatrix) :
    boolToFin W 1 1 = W true true := by
  rfl

private theorem boolToFin_star (W : QubitMatrix) :
    star (boolToFin W) = boolToFin (star W) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem boolToFin_mem_unitaryGroup_iff (W : QubitMatrix) :
    boolToFin W ∈ Matrix.unitaryGroup (Fin 2) ℂ ↔
      W ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  rw [boolToFin_star, ← map_mul]
  have hone : boolToFin (1 : QubitMatrix) = (1 : FinQubitMatrix) :=
    map_one boolToFin
  constructor
  · intro h
    apply boolToFin.injective
    exact h.trans hone.symm
  · intro h
    exact (congrArg boolToFin h).trans hone

private theorem boolToFin_det (W : QubitMatrix) :
    Matrix.det (boolToFin W) = Matrix.det W := by
  exact Matrix.det_reindexAlgEquiv ℂ ℂ finTwoEquiv.symm W

private theorem boolToFin_matrix2 (a b c d : ℂ) :
    boolToFin (matrix2 a b c d) = !![a, b; c, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-! ## Canonical special-unitary form -/

private theorem fin_star_eq_adjugate (W : FinQubitMatrix)
    (hunitary : W ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hdet : Matrix.det W = 1) :
    star W = Matrix.adjugate W := by
  have hleft : star W * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hunitary
  have hright : W * Matrix.adjugate W = 1 := by
    rw [Matrix.mul_adjugate, hdet, one_smul]
  calc
    star W = star W * 1 := (mul_one _).symm
    _ = star W * (W * Matrix.adjugate W) := by rw [hright]
    _ = (star W * W) * Matrix.adjugate W := by rw [mul_assoc]
    _ = Matrix.adjugate W := by rw [hleft, one_mul]

private theorem fin_canonical_entries (W : FinQubitMatrix)
    (hunitary : W ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hdet : Matrix.det W = 1) :
    W 1 0 = -star (W 0 1) ∧ W 1 1 = star (W 0 0) := by
  have h := fin_star_eq_adjugate W hunitary hdet
  rw [Matrix.adjugate_fin_two] at h
  constructor
  · have h10 := congrArg (fun A : FinQubitMatrix => A 1 0) h
    have h10' : star (W 0 1) = -W 1 0 := by
      simpa [Matrix.star_apply] using h10
    simpa using (congrArg Neg.neg h10').symm
  · have h00 := congrArg (fun A : FinQubitMatrix => A 0 0) h
    simpa [Matrix.star_apply] using h00.symm

private theorem fin_canonical (W : FinQubitMatrix)
    (hunitary : W ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hdet : Matrix.det W = 1) :
    W = !![W 0 0, W 0 1; -star (W 0 1), star (W 0 0)] := by
  obtain ⟨hc, hd⟩ := fin_canonical_entries W hunitary hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

/--
Every certified one-qubit special unitary has the canonical entry form
`[[a,b],[-conj b,conj a]]` in the `false,true` basis order.
-/
theorem specialUnitary_canonical (W : QubitSpecialUnitary) :
    (W : QubitMatrix) =
      matrix2 (W.1 false false) (W.1 false true) (-star (W.1 false true))
        (star (W.1 false false)) := by
  have hspecial := Matrix.mem_specialUnitaryGroup_iff.mp W.prop
  have hunitary : boolToFin (W : QubitMatrix) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (boolToFin_mem_unitaryGroup_iff (W : QubitMatrix)).mpr hspecial.1
  have hdet : Matrix.det (boolToFin (W : QubitMatrix)) = 1 := by
    rw [boolToFin_det]
    exact hspecial.2
  apply boolToFin.injective
  rw [boolToFin_matrix2]
  simpa only [boolToFin_false_false, boolToFin_false_true] using
    fin_canonical (boolToFin (W : QubitMatrix)) hunitary hdet

private theorem fin_first_row_norm_sq_add (W : FinQubitMatrix)
    (hunitary : W ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ‖W 0 0‖ ^ 2 + ‖W 0 1‖ ^ 2 = (1 : ℝ) := by
  have hu := Matrix.mem_unitaryGroup_iff.mp hunitary
  have hu00 := congrArg (fun A : FinQubitMatrix => A 0 0) hu
  simp only [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two,
    Matrix.one_apply, if_pos] at hu00
  change W 0 0 * (starRingEnd ℂ) (W 0 0) +
    W 0 1 * (starRingEnd ℂ) (W 0 1) = 1 at hu00
  rw [Complex.mul_conj, Complex.mul_conj] at hu00
  have hre := congrArg Complex.re hu00
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.one_re,
    Complex.normSq_eq_norm_sq] using hre

/-- The squared norms of the first row of a one-qubit special unitary sum to one. -/
theorem specialUnitary_norm_sq_add (W : QubitSpecialUnitary) :
    ‖W.1 false false‖ ^ 2 + ‖W.1 false true‖ ^ 2 = (1 : ℝ) := by
  have hspecial := Matrix.mem_specialUnitaryGroup_iff.mp W.prop
  have hunitary : boolToFin (W : QubitMatrix) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (boolToFin_mem_unitaryGroup_iff (W : QubitMatrix)).mpr hspecial.1
  simpa only [boolToFin_false_false, boolToFin_false_true] using
    fin_first_row_norm_sq_add (boolToFin (W : QubitMatrix)) hunitary

/-! ## Polar coordinates and the parameterized Euler product -/

@[simp]
private theorem norm_mul_cis_arg (z : ℂ) : (‖z‖ : ℂ) * cis z.arg = z := by
  simpa only [cis] using Complex.norm_mul_exp_arg_mul_I z

private theorem cis_mul_middle (x y : ℝ) (z : ℂ) :
    cis x * z * cis y = z * cis (x + y) := by
  calc
    cis x * z * cis y = z * (cis x * cis y) := by ring
    _ = z * cis (x + y) := by rw [cis_add]

private theorem star_eq_norm_mul_cis_neg_arg (z : ℂ) :
    star z = (‖z‖ : ℂ) * cis (-z.arg) := by
  change (starRingEnd ℂ) z = (‖z‖ : ℂ) * cis (-z.arg)
  conv_lhs => rw [← norm_mul_cis_arg z]
  rw [map_mul, Complex.conj_ofReal, starRingEnd_apply, star_cis]

private theorem trig_of_norm_sq_add (a b : ℂ)
    (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = (1 : ℝ)) :
    Real.cos (Real.arccos ‖a‖) = ‖a‖ ∧
      Real.sin (Real.arccos ‖a‖) = ‖b‖ := by
  have hb0 : 0 ≤ ‖b‖ := norm_nonneg b
  have ha_le : ‖a‖ ≤ 1 := by nlinarith [sq_nonneg ‖b‖]
  constructor
  · exact Real.cos_arccos (by linarith [norm_nonneg a]) ha_le
  · rw [Real.sin_arccos]
    have hsquare : 1 - ‖a‖ ^ 2 = ‖b‖ ^ 2 := by nlinarith
    rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg hb0]

private theorem fin_two_mul (a b c d e f g h : ℂ) :
    !![a, b; c, d] * !![e, f; g, h] =
      !![a * e + b * g, a * f + b * h;
         c * e + d * g, c * f + d * h] := by
  exact (Matrix.mulᵣ_eq _ _).symm

private def finRz (x : ℝ) : FinQubitMatrix :=
  !![cis (x / 2), 0; 0, cis (-x / 2)]

private def finRy (x : ℝ) : FinQubitMatrix :=
  !![(Real.cos (x / 2) : ℂ), (Real.sin (x / 2) : ℂ);
     (-Real.sin (x / 2) : ℂ), (Real.cos (x / 2) : ℂ)]

private theorem fin_euler_product_param (p q t : ℝ) :
    finRz (p + q) * finRy (2 * t) * finRz (p - q) =
      !![((Real.cos t : ℂ) * cis p), ((Real.sin t : ℂ) * cis q);
         (-((Real.sin t : ℂ) * cis (-q))),
          ((Real.cos t : ℂ) * cis (-p))] := by
  rw [finRz, finRy, finRz, fin_two_mul, fin_two_mul]
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp
    ring_nf
    rw [cis_mul_middle]
    congr 2
    ring

private theorem canonical_eq_polar (a b : ℂ) :
    !![a, b; -star b, star a] =
      !![((‖a‖ : ℂ) * cis a.arg), ((‖b‖ : ℂ) * cis b.arg);
         (-((‖b‖ : ℂ) * cis (-b.arg))),
          ((‖a‖ : ℂ) * cis (-a.arg))] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [star_eq_norm_mul_cis_neg_arg]

private theorem fin_eq_euler_arg (W : FinQubitMatrix)
    (hunitary : W ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hdet : Matrix.det W = 1) :
    W = finRz ((W 0 0).arg + (W 0 1).arg) *
      finRy (2 * Real.arccos ‖W 0 0‖) *
      finRz ((W 0 0).arg - (W 0 1).arg) := by
  let a := W 0 0
  let b := W 0 1
  let t := Real.arccos ‖a‖
  have hnorm : ‖a‖ ^ 2 + ‖b‖ ^ 2 = (1 : ℝ) :=
    fin_first_row_norm_sq_add W hunitary
  have htrig := trig_of_norm_sq_add a b hnorm
  calc
    W = !![a, b; -star b, star a] := fin_canonical W hunitary hdet
    _ = !![((Real.cos t : ℂ) * cis a.arg), ((Real.sin t : ℂ) * cis b.arg);
           (-((Real.sin t : ℂ) * cis (-b.arg))),
            ((Real.cos t : ℂ) * cis (-a.arg))] := by
      rw [htrig.1, htrig.2]
      exact canonical_eq_polar a b
    _ = finRz (a.arg + b.arg) * finRy (2 * t) * finRz (a.arg - b.arg) :=
      (fin_euler_product_param a.arg b.arg t).symm

private theorem boolToFin_paperRz (x : ℝ) : boolToFin (paperRz x) = finRz x := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem boolToFin_paperRy (x : ℝ) : boolToFin (paperRy x) = finRy x := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem paperEuler_param (p q t : ℝ) :
    paperEuler (p + q) (2 * t) (p - q) =
      matrix2 ((Real.cos t : ℂ) * cis p) ((Real.sin t : ℂ) * cis q)
        (-((Real.sin t : ℂ) * cis (-q))) ((Real.cos t : ℂ) * cis (-p)) := by
  apply boolToFin.injective
  simpa only [paperEuler, map_mul, boolToFin_paperRz, boolToFin_paperRy,
    boolToFin_matrix2] using fin_euler_product_param p q t

/-- Entrywise formula for the paper's row-action Euler product. -/
theorem paperEuler_entry_formula (alpha theta beta : ℝ) :
    paperEuler alpha theta beta =
      matrix2
        ((Real.cos (theta / 2) : ℂ) * cis ((alpha + beta) / 2))
        ((Real.sin (theta / 2) : ℂ) * cis ((alpha - beta) / 2))
        (-((Real.sin (theta / 2) : ℂ) * cis ((beta - alpha) / 2)))
        ((Real.cos (theta / 2) : ℂ) * cis (-(alpha + beta) / 2)) := by
  convert paperEuler_param ((alpha + beta) / 2) ((alpha - beta) / 2)
    (theta / 2) using 1 <;> ring_nf

/-! ## Exact paper-row and standard-column Euler existence -/

/--
The total `Complex.arg` choice gives an exact paper-row Euler expression, including
when either of the two phase-carrying entries is zero.
-/
theorem specialUnitary_eq_paperEuler_arg (W : QubitSpecialUnitary) :
    (W : QubitMatrix) =
      paperEuler
        ((W.1 false false).arg + (W.1 false true).arg)
        (2 * Real.arccos ‖W.1 false false‖)
        ((W.1 false false).arg - (W.1 false true).arg) := by
  have hspecial := Matrix.mem_specialUnitaryGroup_iff.mp W.prop
  have hunitary : boolToFin (W : QubitMatrix) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (boolToFin_mem_unitaryGroup_iff (W : QubitMatrix)).mpr hspecial.1
  have hdet : Matrix.det (boolToFin (W : QubitMatrix)) = 1 := by
    rw [boolToFin_det]
    exact hspecial.2
  apply boolToFin.injective
  simpa only [paperEuler, map_mul, boolToFin_paperRz, boolToFin_paperRy,
    boolToFin_false_false, boolToFin_false_true] using
      fin_eq_euler_arg (boolToFin (W : QubitMatrix)) hunitary hdet

/-- The chosen middle Euler angle always lies in the canonical interval `[0, pi]`. -/
theorem specialUnitary_eulerTheta_mem_Icc (W : QubitSpecialUnitary) :
    2 * Real.arccos ‖W.1 false false‖ ∈ Set.Icc 0 Real.pi := by
  have ht0 : 0 ≤ Real.arccos ‖W.1 false false‖ :=
    Real.arccos_nonneg ‖W.1 false false‖
  have htpi : Real.arccos ‖W.1 false false‖ ≤ Real.pi / 2 :=
    Real.arccos_le_pi_div_two.mpr (norm_nonneg _)
  constructor <;> linarith

/--
Every one-qubit special unitary has an exact paper-row `Rz Ry Rz` decomposition.
The middle angle can be chosen in `[0, pi]`.
-/
theorem specialUnitary_exists_paperEuler (W : QubitSpecialUnitary) :
    ∃ alpha theta beta : ℝ,
      theta ∈ Set.Icc 0 Real.pi ∧ (W : QubitMatrix) = paperEuler alpha theta beta := by
  exact ⟨(W.1 false false).arg + (W.1 false true).arg,
    2 * Real.arccos ‖W.1 false false‖,
    (W.1 false false).arg - (W.1 false true).arg,
    specialUnitary_eulerTheta_mem_Icc W, specialUnitary_eq_paperEuler_arg W⟩

private def transposeSpecialUnitary (W : QubitSpecialUnitary) : QubitSpecialUnitary := by
  have hspecial := Matrix.mem_specialUnitaryGroup_iff.mp W.prop
  have hunitary : fromPaper (W : QubitMatrix) ∈ Matrix.unitaryGroup Bool ℂ :=
    (fromPaper_mem_unitaryGroup_iff (W : QubitMatrix)).mpr hspecial.1
  have hdet : Matrix.det (fromPaper (W : QubitMatrix)) = 1 := by
    simpa only [fromPaper, Matrix.det_transpose] using hspecial.2
  exact ⟨fromPaper (W : QubitMatrix), hunitary, hdet⟩

/--
Every one-qubit special unitary is a `columnEuler`.  These witnesses retain the
paper-facing names: `columnEuler alpha theta beta` is
`rz beta * ry theta * rz alpha`, so the outer factors are explicitly reversed.
-/
theorem specialUnitary_exists_columnEuler (W : QubitSpecialUnitary) :
    ∃ alpha theta beta : ℝ,
      theta ∈ Set.Icc 0 Real.pi ∧ (W : QubitMatrix) = columnEuler alpha theta beta := by
  obtain ⟨alpha, theta, beta, htheta, hpaper⟩ :=
    specialUnitary_exists_paperEuler (transposeSpecialUnitary W)
  refine ⟨alpha, theta, beta, htheta, ?_⟩
  have hcolumn := congrArg fromPaper hpaper
  simpa [transposeSpecialUnitary, columnEuler] using hcolumn

/--
Standard-column Euler existence in ordinary matrix-product order.  It is obtained
from `specialUnitary_exists_columnEuler` by swapping the paper's outer witnesses.
-/
theorem specialUnitary_exists_rz_mul_ry_mul_rz (W : QubitSpecialUnitary) :
    ∃ alpha theta beta : ℝ,
      theta ∈ Set.Icc 0 Real.pi ∧
        (W : QubitMatrix) = rz alpha * ry theta * rz beta := by
  obtain ⟨paperAlpha, theta, paperBeta, htheta, hcolumn⟩ :=
    specialUnitary_exists_columnEuler W
  refine ⟨paperBeta, theta, paperAlpha, htheta, ?_⟩
  rw [hcolumn, columnEuler_eq]

end

end Barenco.OneQubit
